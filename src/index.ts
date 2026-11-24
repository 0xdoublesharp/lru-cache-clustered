import cluster from 'node:cluster';
import { randomUUID } from 'node:crypto';
import { EventEmitter } from 'node:events';
import { LRUCache } from 'lru-cache';
import {
  caches,
  BULK_BROADCAST_OPS,
  dispatchAndBroadcast,
  getOrCreateCache,
  getNamespaceVersion,
  installClusterListener,
  type ExecPayload,
} from './primary.js';
import { getDefaultClient } from './worker.js';
import { subscribeInvalidations, emitInvalidation } from './invalidation.js';
import {
  SOURCE,
  type InvalidationPush,
  type DispatchResult,
  type SerializableLruOptions,
  type Stats,
} from './messages.js';
import { LocalL1Cache, encodeL1Key, type L1Stats, type L1Read } from './l1.js';

if (cluster.isPrimary) installClusterListener();

const FETCH_POLL_MS = 5;

type LocalResponse<T> = DispatchResult<T> & { ttlStart?: number };

// lru-cache@11 constrains generic K and V to non-nullish; mirror that locally
// so the registry's stored type lines up with the public getCache() return.
// eslint-disable-next-line @typescript-eslint/no-empty-object-type
type NonNullish = {};

type FetchClaimResult<T> =
  { kind: 'value'; value: T } | { kind: 'leader'; token: string } | { kind: 'follower'; generation: string };

export interface WriteOptions {
  ttl?: number;
  size?: number;
  updateL1?: boolean;
}

export interface ReadOptions {
  bypassL1?: boolean;
}

// eslint-disable-next-line @typescript-eslint/no-empty-object-type
export type MSetEntry<K extends {}, V extends {}> = [K, V] | [K, V, WriteOptions];

export interface FetchOptions extends WriteOptions {
  forceRefresh?: boolean;
  bypassL1?: boolean;
}

export type LocalL1Options = {
  enabled?: boolean;
  max?: number;
  maxSize?: number;
  ttl?: number;
  updateAgeOnGet?: boolean;
  allowStale?: boolean;
  cacheUndefined?: boolean;
  invalidation?: 'broadcast' | 'ttl-only';
  methods?: {
    get?: boolean;
    has?: boolean;
    fetch?: boolean;
  };
  experimental?: boolean;
};

export interface LRUCacheClusterOptions extends SerializableLruOptions {
  namespace?: string;
  timeout?: number;
  failsafe?: 'resolve' | 'reject';
  localL1?: false | LocalL1Options;
}

interface InternalOptions {
  noInit?: boolean;
}

const DEFAULT_L1_TTL_MS = 5_000;
const DEFAULT_L1_MAX = 1_000;

type NormalizedL1 = {
  max: number;
  maxSize?: number;
  ttl: number;
  updateAgeOnGet: boolean;
  allowStale: boolean;
  invalidation: 'broadcast' | 'ttl-only';
  methods: { get: boolean; has: boolean; fetch: boolean };
};

function shouldEmitLocalInvalidation(payload: ExecPayload, value: unknown): boolean {
  switch (payload.op) {
    case 'set':
    case 'mSet':
    case 'mDelete':
    case 'clear':
    case 'load':
    case 'incr':
    case 'decr':
      return true;
    case 'delete':
    case 'setIfAbsent':
    case 'purgeStale':
    case 'fetchStore':
    case 'destroy':
      return value === true;
    case 'max':
    case 'ttl':
      return typeof payload.value === 'number';
    default:
      return false;
  }
}

function buildLocalInvalidation(
  namespace: string,
  payload: ExecPayload,
  version: number,
  value: unknown,
): InvalidationPush | undefined {
  if (!shouldEmitLocalInvalidation(payload, value)) return undefined;
  if (BULK_BROADCAST_OPS.has(payload.op)) {
    return { source: SOURCE, push: 'l1:invalidate-namespace', namespace, version };
  }
  const key = (payload as { key?: unknown }).key;
  /* c8 ignore next -- all current local single-key invalidations validate a non-nullish key before this point. */
  if (key === undefined || key === null) return undefined;
  return { source: SOURCE, push: 'l1:invalidate', namespace, key, version };
}

function normalizeL1(
  raw: false | LocalL1Options | undefined,
  primary: SerializableLruOptions,
): NormalizedL1 | undefined {
  if (raw === undefined || raw === false) return undefined;
  const opts: LocalL1Options = raw;
  if (opts.enabled === false) return undefined;
  if (!opts.experimental) {
    throw new Error('localL1 is experimental. Pass `localL1: { experimental: true }` to opt in.');
  }

  // Default L1 ttl: min(primaryTtl * 0.1, 5000), with 100ms floor before clamping
  // to primaryTtl. An unset or zero primary ttl means no expiration, so default
  // to 5000. Explicit localL1.ttl values are honored directly (clamped to primaryTtl).
  // Population also caps each entry at its remaining primary lifetime.
  if (opts.ttl !== undefined && (!Number.isFinite(opts.ttl) || opts.ttl <= 0)) {
    throw new TypeError('invalid localL1.ttl');
  }
  const primaryTtl = primary.ttl || Infinity;
  const requestedTtl = opts.ttl ?? Math.max(100, Math.min(primaryTtl * 0.1, DEFAULT_L1_TTL_MS));
  const ttl = Math.max(1, Math.floor(Math.min(requestedTtl, primaryTtl)));

  const m = opts.methods;
  const methods = m
    ? { get: m.get === true, has: m.has === true, fetch: m.fetch === true }
    : { get: true, has: true, fetch: true };

  return {
    max: opts.max ?? DEFAULT_L1_MAX,
    maxSize: opts.maxSize,
    ttl,
    updateAgeOnGet: opts.updateAgeOnGet ?? true,
    allowStale: opts.allowStale ?? false,
    invalidation: opts.invalidation ?? 'broadcast',
    methods,
  };
}

function assertPrimary(method: string): void {
  if (cluster.isWorker) throw new Error(`LRUCacheClustered.${method}() must not be called from a worker`);
}

function encodeL1KeyOrUndefined(key: unknown): string | undefined {
  if (key === undefined || key === null) return undefined;
  try {
    return encodeL1Key(key);
  } catch {
    return undefined;
  }
}

// K and V are constrained to non-nullish to mirror lru-cache@11's own signature
// (`class LRUCache<K extends {}, V extends {}>`), since the primary enforces
// non-nullish at runtime via requireNonNullish(). Without the constraint, a
// caller could write `cache.set(undefined, ...)` and TypeScript would accept it
// only to fail at the IPC boundary. The {} default for V mirrors lru-cache's
// own default and means "any non-nullish value".
// eslint-disable-next-line @typescript-eslint/no-empty-object-type
export class LRUCacheClustered<K extends {} = string, V extends {} = {}> {
  readonly namespace: string;
  readonly timeout: number;
  readonly failsafe: 'resolve' | 'reject';
  readonly ready: Promise<void>;
  #lruOptions: SerializableLruOptions;
  // Per-instance in-flight dedup for fetch(). Concurrent callers within the
  // same instance piggyback locally before the primary-side single-flight lock
  // engages across instances and workers.
  readonly #inFlight = new Map<K, { promise: Promise<V> }>();
  readonly #emitter = new EventEmitter();
  readonly #l1?: LocalL1Cache<V & NonNullish>;
  readonly #l1Methods: { get: boolean; has: boolean; fetch: boolean };
  readonly #l1Invalidation: 'broadcast' | 'ttl-only';
  #unsubscribeL1?: () => void;
  #publishingOwnMutation = false;
  #destroyed = false;

  constructor(options: LRUCacheClusterOptions & InternalOptions = {}) {
    this.namespace = options.namespace ?? 'default';
    this.timeout = options.timeout ?? 100;
    this.failsafe = options.failsafe === 'reject' ? 'reject' : 'resolve';
    const { namespace: _n, timeout: _t, failsafe: _f, noInit: _ni, localL1: _l1, ...lruOpts } = options;
    void _n;
    void _t;
    void _f;
    void _ni;
    void _l1;
    this.#lruOptions = lruOpts;

    const l1Config = normalizeL1(options.localL1, lruOpts);
    this.#l1Methods = l1Config?.methods ?? { get: false, has: false, fetch: false };
    this.#l1Invalidation = l1Config?.invalidation ?? 'broadcast';
    if (l1Config) {
      this.#l1 = new LocalL1Cache<V & NonNullish>({
        max: l1Config.max,
        maxSize: l1Config.maxSize,
        ttl: l1Config.ttl,
        updateAgeOnGet: l1Config.updateAgeOnGet,
        allowStale: l1Config.allowStale,
        emit: (event, payload) => {
          this.#emitter.emit(`l1:${event}`, { namespace: this.namespace, ...payload });
        },
      });
    }

    if (cluster.isPrimary) {
      getOrCreateCache(this.namespace, this.#lruOptions);
      this.#l1?.advanceLatestSeen(getNamespaceVersion(this.namespace));
      this.#installL1Subscription();
    }
    // Swallow rejection so consumers can `await cache.ready` purely for
    // ordering without unhandled-rejection noise.
    this.ready = !cluster.isPrimary && !options.noInit ? this.#initWorker().catch(() => undefined) : Promise.resolve();
  }

  // eslint-disable-next-line @typescript-eslint/no-empty-object-type
  static async getInstance<K extends {} = string, V extends {} = {}>(
    options: LRUCacheClusterOptions = {},
  ): Promise<LRUCacheClustered<K, V>> {
    const instance = new LRUCacheClustered<K, V>({
      ...options,
      noInit: true,
    });
    if (cluster.isWorker) await instance.#initWorker();
    return instance;
  }

  static bootstrap(): void {
    if (cluster.isPrimary) installClusterListener();
  }

  static getAllCaches(): Map<string, LRUCache<NonNullish, NonNullish>> {
    assertPrimary('getAllCaches');
    return caches;
  }

  getCache(): LRUCache<K & NonNullish, V & NonNullish> | undefined {
    assertPrimary('getCache');
    return caches.get(this.namespace) as LRUCache<K & NonNullish, V & NonNullish> | undefined;
  }

  // Per-method API:
  get(key: K, opts?: ReadOptions): Promise<V | undefined> {
    return this.#readLocal('get', key, opts);
  }
  async set(key: K, value: V, opts?: WriteOptions): Promise<boolean> {
    this.#deleteLocal(key);
    const read = this.#l1 && opts?.updateL1 ? this.#trackLocalRead(key) : undefined;
    try {
      const r = await this.#dispatchWithMeta<boolean>(
        { op: 'set', key, value, ttl: opts?.ttl, size: opts?.size, includeTTL: !!this.#l1 && opts?.updateL1 },
        this.failsafe,
      );
      if (this.#l1 && opts?.updateL1 && r.value === true) {
        this.#setLocalFromPrimary(key, value, r, 0, read);
      }
      return r.value;
    } finally {
      read?.release();
    }
  }
  delete(key: K): Promise<boolean> {
    this.#deleteLocal(key);
    return this.#dispatch<boolean>({ op: 'delete', key });
  }
  async has(key: K, opts?: ReadOptions): Promise<boolean> {
    const useL1 = this.#l1 && this.#l1Methods.has && !opts?.bypassL1;
    if (useL1) {
      const hit = this.#getLocal(key, 'has');
      if (hit !== undefined) return true;
    }
    return this.#dispatch<boolean>({ op: 'has', key });
  }
  peek(key: K, opts?: ReadOptions): Promise<V | undefined> {
    return this.#readLocal('peek', key, opts);
  }
  clear(): Promise<void> {
    this.#l1?.clear();
    return this.#dispatch<void>({ op: 'clear' });
  }
  purgeStale(): Promise<boolean> {
    this.#l1?.clear();
    return this.#dispatch<boolean>({ op: 'purgeStale' });
  }

  async mGet(keys: K[], opts?: ReadOptions): Promise<Map<K, V | undefined>> {
    const values = new Map<K, V | undefined>();
    const useL1 = this.#l1 && this.#l1Methods.get && !opts?.bypassL1;
    const remainingKeys: K[] = useL1 ? [] : keys;
    if (useL1) {
      for (const k of keys) {
        const hit = this.#getLocal(k);
        if (hit !== undefined) values.set(k, hit);
        else remainingKeys.push(k);
      }
    }
    // Hits were inserted in input order, so a fully warm batch is ready.
    if (remainingKeys.length === 0) return values;

    const reads = useL1
      ? new Map([...new Set(remainingKeys)].map((key) => [key, this.#trackLocalRead(key)]))
      : undefined;
    try {
      const r = await this.#dispatchWithMeta<Array<[K, V | undefined]> | undefined>(
        { op: 'mGet', keys: remainingKeys, includeTTL: !!useL1 },
        this.failsafe,
      );
      // Default cluster IPC uses JSON serialization, which rewrites
      // `undefined` inside arrays to `null`. Cache values are non-nullish, so
      // a null on this wire can only mean "the primary returned undefined for
      // a missing key". Normalize so the public Map<K, V | undefined> contract
      // holds in both primary and worker mode. The `?? []` covers the
      // failsafe='resolve' + IPC timeout case where dispatch resolves to
      // undefined; matches the previous `new Map(undefined)` empty-Map result.
      for (const [index, [k, v]] of (r.value ?? []).entries()) {
        const value = v === null ? undefined : v;
        values.set(k, value);
        if (useL1 && value !== undefined) {
          this.#setLocalFromPrimary(k, value, r, index, reads?.get(k));
        }
      }
      const out = new Map<K, V | undefined>();
      for (const k of keys) {
        if (values.has(k)) out.set(k, values.get(k));
      }
      return out;
    } finally {
      if (reads) for (const read of reads.values()) read?.release();
    }
  }
  mSet(entries: Iterable<MSetEntry<K, V>>, opts?: WriteOptions): Promise<void> {
    this.#l1?.clear();
    return this.#dispatch<void>({ op: 'mSet', entries: [...entries], ttl: opts?.ttl, size: opts?.size });
  }
  mDelete(keys: K[]): Promise<void> {
    this.#l1?.clear();
    return this.#dispatch<void>({ op: 'mDelete', keys });
  }

  keys() {
    return this.#dispatch<K[]>({ op: 'keys' });
  }
  values() {
    return this.#dispatch<V[]>({ op: 'values' });
  }
  entries() {
    return this.#dispatch<Array<[K, V]>>({ op: 'entries' });
  }
  dump() {
    return this.#dispatch<Array<[K, LRUCache.Entry<V>]>>({ op: 'dump' });
  }
  size() {
    return this.#dispatch<number>({ op: 'size' });
  }

  incr(key: K, amount?: number, opts?: WriteOptions): Promise<number> {
    this.#deleteLocal(key);
    return this.#dispatch<number>({ op: 'incr', key, amount, ttl: opts?.ttl, size: opts?.size });
  }
  decr(key: K, amount?: number, opts?: WriteOptions): Promise<number> {
    this.#deleteLocal(key);
    return this.#dispatch<number>({ op: 'decr', key, amount, ttl: opts?.ttl, size: opts?.size });
  }

  allowStale(value?: boolean): Promise<boolean> {
    return this.#tune('allowStale', value);
  }
  max(value?: number): Promise<number> {
    return this.#tune('max', value);
  }
  ttl(value?: number): Promise<number> {
    return this.#tune('ttl', value);
  }

  async getRemainingTTL(key: K): Promise<number> {
    // Default cluster IPC uses JSON serialization, which rewrites `Infinity`
    // (lru-cache@11's "no TTL" sentinel) to `null`. Missing keys return 0,
    // and any active entry returns a positive number, so a null on this wire
    // can only mean Infinity. Normalize so the public Promise<number>
    // contract holds in both primary and worker mode. Strict `=== null` so
    // failsafe='resolve' timeouts (which dispatch undefined) still propagate
    // as undefined, matching the pattern for every other op under that mode.
    const ttl = await this.#dispatch<number | null>({ op: 'getRemainingTTL', key });
    return ttl === null ? Infinity : ttl;
  }
  setIfAbsent(key: K, value: V, opts?: WriteOptions): Promise<boolean> {
    this.#deleteLocal(key);
    return this.#dispatch<boolean>({ op: 'setIfAbsent', key, value, ttl: opts?.ttl, size: opts?.size });
  }
  load(entries: Array<[K, LRUCache.Entry<V>]>): Promise<void> {
    this.#l1?.clear();
    return this.#dispatch<void>({ op: 'load', entries });
  }
  destroy(): Promise<boolean> {
    this.#destroyed = true;
    this.#inFlight.clear();
    this.#unsubscribeL1?.();
    this.#unsubscribeL1 = undefined;
    this.#l1?.destroy();
    return this.#dispatch<boolean>({ op: 'destroy' });
  }
  healthCheck() {
    return this.#dispatch<void>({ op: 'healthCheck' }, 'reject');
  }
  stats() {
    return this.#dispatch<Stats>({ op: 'stats' });
  }

  localStats(): L1Stats | undefined {
    return this.#l1?.stats();
  }

  on(event: string, listener: (...args: unknown[]) => void): this {
    this.#emitter.on(event, listener);
    return this;
  }

  off(event: string, listener: (...args: unknown[]) => void): this {
    this.#emitter.off(event, listener);
    return this;
  }

  once(event: string, listener: (...args: unknown[]) => void): this {
    this.#emitter.once(event, listener);
    return this;
  }

  clearLocal(): void {
    this.#l1?.clear();
  }

  invalidateLocal(key: K): void {
    this.#deleteLocal(key);
  }

  // Returns a proxy that shares all state with this instance but forces
  // bypassL1: true on every L1-eligible read. Write methods pass through to
  // the real instance so set/delete/etc still self-invalidate the underlying
  // L1. Calling withoutLocal() on the returned proxy is idempotent - it
  // returns the same proxy object.
  //
  // Implementation note: all method calls are routed through the Proxy target
  // (the real instance) because private fields (#l1, etc.) are inaccessible
  // on objects that are not genuine class instances. The Proxy get trap returns
  // either a bypassL1-injecting override for read methods or the real
  // instance's method bound to itself for everything else.
  withoutLocal(): LRUCacheClustered<K, V> {
    // Using `t` (the Proxy target = the real instance) inside the trap avoids
    // a no-this-alias violation. All calls go through `t` so private fields
    // (#l1, etc.) remain accessible on the real instance.
    let wrapper: LRUCacheClustered<K, V>;
    wrapper = new Proxy(this, {
      // eslint-disable-next-line @typescript-eslint/no-explicit-any
      get(t, prop): any {
        if (prop === 'withoutLocal') return () => wrapper;
        const v = Reflect.get(t, prop, t);
        if (prop === 'get' || prop === 'has' || prop === 'peek' || prop === 'mGet') {
          return (arg: unknown, opts?: ReadOptions) =>
            (v as (a: unknown, o?: ReadOptions) => unknown).call(t, arg, { ...opts, bypassL1: true });
        }
        if (prop === 'fetch') {
          return (key: K, fetcher: (k: K) => V | Promise<V>, opts?: FetchOptions) =>
            t.fetch(key, fetcher, { ...opts, bypassL1: true });
        }
        // All other properties: reflect from the real instance bound to it so
        // private fields remain accessible.
        return typeof v === 'function' ? (v as (...a: unknown[]) => unknown).bind(t) : v;
      },
    });
    return wrapper;
  }

  // Materializes the full entries array up front, then yields — simpler than
  // streaming over IPC at the cost of a single large payload per iteration.
  async *[Symbol.asyncIterator](): AsyncIterableIterator<[K, V]> {
    const all = await this.entries();
    for (const pair of all ?? []) yield pair;
  }

  async fetch(key: K, fetcher: (key: K) => Promise<V> | V, opts?: FetchOptions): Promise<V> {
    const useFetchL1 = this.#l1 && this.#l1Methods.fetch && !opts?.bypassL1;
    if (!opts?.forceRefresh) {
      if (useFetchL1) {
        const cachedLocal = this.#getLocal(key);
        if (cachedLocal !== undefined) return cachedLocal;
      }

      const existing = this.#inFlight.get(key);
      if (existing) return existing.promise;
    }

    const read = useFetchL1 ? this.#trackLocalRead(key) : undefined;
    let slot!: { promise: Promise<V> };
    const requestId = randomUUID();
    let generation: string | undefined;
    let claimPending = false;
    const run = async (): Promise<V> => {
      let forceRefresh = opts?.forceRefresh === true;

      while (true) {
        claimPending = true;
        const response = await this.#dispatchWithMeta<FetchClaimResult<V>>(
          {
            op: 'fetchClaim',
            key,
            forceRefresh,
            requestId,
            generation,
            includeTTL: !!useFetchL1,
          },
          'reject',
        );
        claimPending = false;
        const claim = response.value;

        if (claim.kind === 'value') {
          generation = undefined; // The primary has released this follower.
          if (useFetchL1) this.#setLocalFromPrimary(key, claim.value, response, 0, read);
          return claim.value;
        }
        if (claim.kind === 'leader') {
          try {
            const v = (await fetcher(key)) as V;
            const stored = await this.#dispatchWithMeta<boolean>(
              {
                op: 'fetchStore',
                includeTTL: !!useFetchL1,
                key,
                token: claim.token,
                value: v,
                ttl: opts?.ttl,
                size: opts?.size,
              },
              'reject',
            );
            if (!stored.value) {
              const newer = await this.#dispatch<V | undefined>({ op: 'get', key, existingOnly: true }, 'reject');
              if (newer === undefined)
                throw new Error('Fetch was superseded by a cache mutation and no current value remains');
              return newer;
            }
            generation = undefined; // Successful store removes the entire group.
            // Populate the leader's L1 with the fresh value and the version
            // returned by fetchStore. bypassL1 skips the populate so the caller
            // sees the fresh L2 result without repopulating their L1.
            if (useFetchL1) {
              this.#deleteLocal(key, stored.version);
              this.#setLocalFromPrimary(key, v, stored, 0, read);
            } else {
              this.#deleteLocal(key);
            }
            return v;
          } catch (error) {
            try {
              await this.#dispatch<boolean>({ op: 'fetchAbort', key, token: claim.token }, 'reject');
            } catch {
              // Ignore cleanup failures and preserve the fetcher's error.
            }
            throw error;
          }
        }

        generation = claim.generation;
        forceRefresh = false;
        await new Promise((resolve) => setTimeout(resolve, FETCH_POLL_MS));
      }
    };

    slot = { promise: run() };
    this.#inFlight.set(key, slot);
    try {
      return await slot.promise;
    } finally {
      // Identity check — a newer forceRefresh fetch may have replaced our
      // slot. Only clear if this slot is still current.
      if (this.#inFlight.get(key) === slot) this.#inFlight.delete(key);
      read?.release();
      if (generation !== undefined || claimPending) {
        try {
          await this.#dispatch<boolean>({ op: 'fetchRelease', key, generation, requestId }, 'reject');
        } catch {
          // Cleanup must preserve the original result or fetcher error.
        }
      }
    }
  }

  async #tune<O extends 'allowStale' | 'max' | 'ttl'>(
    op: O,
    value?: SerializableLruOptions[O],
  ): Promise<NonNullable<SerializableLruOptions[O]>> {
    const next = await this.#dispatch<NonNullable<SerializableLruOptions[O]>>({ op, value } as ExecPayload);
    if (next !== undefined) this.#lruOptions[op] = next;
    if (value !== undefined && op !== 'allowStale') this.#l1?.clear();
    return next;
  }

  async #initWorker(): Promise<void> {
    const r = await this.#dispatchWithMeta<{ version: number }>({ op: 'init', options: this.#lruOptions }, 'reject');
    this.#l1?.advanceLatestSeen(r.value.version);
    if (!this.#destroyed) this.#installL1Subscription();
  }

  async #readLocal(op: 'get' | 'peek', key: K, opts?: ReadOptions): Promise<V | undefined> {
    const useL1 = this.#l1 && this.#l1Methods.get && !opts?.bypassL1;
    if (useL1) {
      const hit = this.#getLocal(key, op);
      if (hit !== undefined) return hit;
    }
    const read = useL1 ? this.#trackLocalRead(key) : undefined;
    try {
      const r = await this.#dispatchWithMeta<V | undefined>({ op, key, includeTTL: !!useL1 }, this.failsafe);
      if (useL1 && r.value !== undefined) this.#setLocalFromPrimary(key, r.value, r, 0, read);
      return r.value;
    } finally {
      read?.release();
    }
  }

  #installL1Subscription(): void {
    if (!this.#l1 || this.#l1Invalidation !== 'broadcast' || this.#unsubscribeL1) return;
    const handle = (msg: InvalidationPush) => this.#applyL1Invalidation(msg);
    const unsubscribeLocal = subscribeInvalidations(this.namespace, handle);
    const unsubscribeIpc = cluster.isPrimary
      ? undefined
      : getDefaultClient().subscribeInvalidations(this.namespace, handle);
    this.#unsubscribeL1 = () => {
      unsubscribeLocal();
      unsubscribeIpc?.();
    };
  }

  #applyL1Invalidation(msg: InvalidationPush): void {
    // Emit broadcast-reason event before the L1 mutation so listeners can
    // distinguish broadcast-driven invalidations from local-write ones.
    try {
      if (!this.#publishingOwnMutation) {
        this.#emitter.emit('l1:invalidate', {
          namespace: this.namespace,
          key: msg.push === 'l1:invalidate' ? msg.key : '*',
          reason: 'broadcast',
        });
      }
    } finally {
      // Event handlers may throw. They must not prevent coherence updates.
      if (msg.push === 'l1:invalidate') this.#deleteLocal(msg.key as K, msg.version);
      else this.#l1!.clear(false, msg.version);
    }
  }

  #setLocalFromPrimary(key: K, value: V, response: LocalResponse<unknown>, index = 0, read?: L1Read): void {
    const enc = encodeL1KeyOrUndefined(key);
    const remaining = response.ttls?.[index];
    // Older primaries may omit TTL metadata. Serve the result without caching
    // it locally rather than guessing an expiration.
    if (enc === undefined || remaining === undefined) return;
    const ttl = remaining === null ? undefined : remaining - (globalThis.performance.now() - response.ttlStart!);
    this.#l1!.set(enc, value, response.version, ttl, key, read);
  }

  #trackLocalRead(key: K): L1Read | undefined {
    const enc = encodeL1KeyOrUndefined(key);
    return enc === undefined ? undefined : this.#l1!.trackRead(enc);
  }

  #getLocal(key: K, mode: 'get' | 'peek' | 'has' = 'get'): V | undefined {
    const enc = encodeL1KeyOrUndefined(key);
    return enc === undefined ? undefined : this.#l1!.get(enc, key, mode);
  }

  #deleteLocal(key: K, version?: number): void {
    if (!this.#l1) return;
    const enc = encodeL1KeyOrUndefined(key);
    if (enc !== undefined) this.#l1.delete(enc, key, version === undefined, version);
  }

  #emitLocalInvalidation(payload: ExecPayload, value: unknown, version: number): void {
    const msg = buildLocalInvalidation(this.namespace, payload, version, value);
    if (msg) {
      this.#publishingOwnMutation = true;
      try {
        emitInvalidation(msg);
      } finally {
        this.#publishingOwnMutation = false;
      }
    }
  }

  #invalidateOwnEvictions(result: DispatchResult<unknown>): void {
    for (const key of result.evictedKeys ?? []) this.#deleteLocal(key as K, result.version);
  }

  #dispatch<T>(payload: ExecPayload, failsafe = this.failsafe): Promise<T> {
    return this.#dispatchWithMeta<T>(payload, failsafe).then((r) => r.value);
  }

  async #dispatchWithMeta<T>(payload: ExecPayload, failsafe: 'resolve' | 'reject'): Promise<LocalResponse<T>> {
    // destroy() releases subscriptions. Reusing the instance must restore
    // invalidation delivery before another read can warm its local cache.
    if (payload.op !== 'destroy' && payload.op !== 'init') {
      this.#destroyed = false;
      this.#installL1Subscription();
    }
    const ttlStart = payload.includeTTL ? globalThis.performance.now() : undefined;
    const request = { ...payload, cacheOptions: this.#lruOptions } as ExecPayload;
    if (cluster.isPrimary) {
      this.#publishingOwnMutation = true;
      try {
        const r = dispatchAndBroadcast(this.namespace, request);
        this.#invalidateOwnEvictions(r);
        return { ...r, value: r.value as T, ttlStart };
      } catch (e) {
        // Primary-mode errors always reject; failsafe only applies to IPC
        // timeouts in worker mode.
        throw e instanceof Error ? e : new Error(String(e));
      } finally {
        this.#publishingOwnMutation = false;
      }
    }
    const r = await getDefaultClient().sendToPrimaryWithMeta<T>(
      { namespace: this.namespace, timeout: this.timeout, failsafe },
      request,
    );
    this.#invalidateOwnEvictions(r);
    if (r.version > 0) this.#emitLocalInvalidation(request, r.value, r.version);
    return { ...r, ttlStart };
  }
}

// Backward-compatible alias — `LRUCacheClustered` is the canonical name.
export { LRUCacheClustered as LRUCacheForClustersAsPromised };

export type { L1Stats } from './l1.js';
export type { SerializableLruOptions, Stats } from './messages.js';
export { memoize, type MemoizeOptions } from './memoize.js';
export { wrap, type Codec, type WrappedCache } from './codec.js';

export default LRUCacheClustered;
