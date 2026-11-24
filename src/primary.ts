import cluster from 'node:cluster';
import type { Worker } from 'node:cluster';
import Debug from 'debug';
import { LRUCache } from 'lru-cache';
import { emitInvalidation } from './invalidation.js';
import {
  DEBUG_PREFIX,
  SOURCE,
  isOurMessage,
  serializeError,
  type Request,
  type DispatchResult,
  type Response,
  type SerializableLruOptions,
  type Stats,
  type InvalidationPush,
} from './messages.js';

// Distributive Omit so each member of the Request union keeps its own shape.
type DistributiveOmit<T, K extends keyof never> = T extends unknown ? Omit<T, K> : never;
export type ExecPayload = DistributiveOmit<Request, 'id' | 'namespace' | 'source'>;

const debug = Debug(`${DEBUG_PREFIX}-primary`);
const messagesDebug = Debug(`${DEBUG_PREFIX}-messages`);

// Public registry: namespace -> LRUCache. Keys/values constrained to non-nullish
// per lru-cache@11 signature; we operate on `unknown` at the IPC boundary and
// trust the runtime to filter undefined/null inputs.
// eslint-disable-next-line @typescript-eslint/no-empty-object-type
type NonNullish = {};
type AnyCache = LRUCache<NonNullish, NonNullish>;

type DispatchContext = {
  workerId?: number;
};

type FetchLock = {
  token?: string;
  generation: string;
  followers: Map<string, number | undefined>;
  ownerWorkerId?: number;
  requestId?: string;
  claimedAt: number;
};

// Lease window for a fetch claim. If the leader hasn't called fetchStore
// or fetchAbort within this many ms, a new fetchClaim will overwrite the
// stale lock and become the new leader. Bounds tail latency when a leader
// hangs without process exit (which would otherwise be released by the
// cluster.on('exit') handler). 30s is generous for typical user fetchers
// and short enough that hung-leader incidents do not park requests forever.
export const FETCH_LEASE_MS = 30_000;
export const SUPERSEDED_ERROR = 'Fetch was superseded by a cache mutation and no current value remains';

type PrimaryState = {
  caches: Map<string, AnyCache>;
  stats: Map<string, Stats>;
  fetchLocks: Map<string, Map<NonNullish, FetchLock>>;
  versions: Map<string, number>;
  clusterListenerInstalled: boolean;
  nextFetchToken: number;
  nextMutationVersion: number;
  activeEvictions?: { namespace: string; keys: NonNullish[] };
};

// The scoped and legacy package names can coexist during the migration window.
// Share primary-side state process-wide so both names use one IPC listener and
// one namespace registry when they are installed together.
const STATE_KEY = Symbol.for('lru-cache-clustered.primary');
const primaryState = ((globalThis as Record<PropertyKey, unknown>)[STATE_KEY] ??= {
  caches: new Map<string, AnyCache>(),
  stats: new Map<string, Stats>(),
  fetchLocks: new Map<string, Map<NonNullish, FetchLock>>(),
  versions: new Map<string, number>(),
  clusterListenerInstalled: false,
  nextFetchToken: 0,
  nextMutationVersion: 0,
}) as PrimaryState;

export const caches = primaryState.caches;
export const stats = primaryState.stats;
export const versions = primaryState.versions;
const fetchLocks = primaryState.fetchLocks;

export function getNamespaceVersion(namespace: string): number {
  return primaryState.versions.get(namespace) ?? 0;
}

function bumpNamespaceVersion(namespace: string): number {
  const next = (primaryState.nextMutationVersion ?? 0) + 1;
  primaryState.nextMutationVersion = next;
  primaryState.versions.set(namespace, next);
  return next;
}

function getStats(namespace: string): Stats {
  let s = stats.get(namespace);
  if (!s) {
    s = { namespace, hits: 0, misses: 0, sets: 0, deletes: 0, evictions: 0, size: 0 };
    stats.set(namespace, s);
  }
  return s;
}

function getCacheForPayload(namespace: string, payload: ExecPayload): AnyCache {
  return caches.get(namespace) ?? getOrCreateCache(namespace, payload.cacheOptions);
}

function assertOptionsCompatible(namespace: string, cache: AnyCache, options?: SerializableLruOptions): void {
  if (!options) return;

  const current = cache as unknown as Required<SerializableLruOptions>;
  const mismatches: string[] = [];

  for (const [key, value] of Object.entries(options) as Array<
    [keyof SerializableLruOptions, SerializableLruOptions[keyof SerializableLruOptions]]
  >) {
    if (value === undefined) continue;
    const expected = key === 'maxEntrySize' && !value ? current.maxSize : value;
    if (current[key] !== expected) {
      mismatches.push(`${key}=${String(current[key])} (existing) != ${String(value)} (incoming)`);
    }
  }

  if (mismatches.length > 0) {
    throw new Error(`Conflicting options for namespace '${namespace}': ${mismatches.join(', ')}`);
  }
}

function requireNonNullish(label: string, value: unknown): NonNullish {
  if (value === null || value === undefined) {
    throw new TypeError(`${label} must not be null or undefined`);
  }
  return value;
}

const requireKey = (key: unknown): NonNullish => requireNonNullish('cache key', key);
const requireValue = (value: unknown): NonNullish => requireNonNullish('cache value', value);

function validateTtl(ttl: number | undefined): void {
  if (ttl !== undefined && (!Number.isInteger(ttl) || ttl < 0)) throw new TypeError('invalid ttl');
}

function recordKeyWrite(namespace: string, key: NonNullish, stored: boolean): void {
  supersedeFetch(namespace, key);
  if (stored) getStats(namespace).sets += 1;
  bumpNamespaceVersion(namespace);
}

function writeEntry(
  cache: AnyCache,
  key: NonNullish,
  value: NonNullish,
  opts: { ttl?: number; size?: number },
): boolean {
  const { ttl, size } = opts;
  validateTtl(ttl);
  if (
    cache.maxSize &&
    Number.isInteger(size) &&
    (size as number) > 0 &&
    cache.peek(key, { allowStale: true }) === value &&
    cache.info(key)?.size !== size
  ) {
    cache.delete(key);
  }
  cache.set(key, value, { ttl, size });
  return cache.peek(key, { allowStale: true }) !== undefined;
}

function supersedeFetch(namespace: string, key: NonNullish): boolean {
  const locks = fetchLocks.get(namespace);
  const removed = locks?.delete(key) ?? false;
  if (locks?.size === 0) fetchLocks.delete(namespace);
  return removed;
}

function pruneFetchLock(namespace: string, key: NonNullish, lock: FetchLock): void {
  if (!lock.token && lock.followers.size === 0) supersedeFetch(namespace, key);
}

function releaseFetchLocksForWorker(workerId: number): void {
  for (const [namespace, locks] of fetchLocks) {
    for (const [key, lock] of locks) {
      for (const [requestId, owner] of lock.followers) {
        if (owner === workerId) lock.followers.delete(requestId);
      }
      if (lock.ownerWorkerId === workerId) lock.token = lock.requestId = undefined;
      pruneFetchLock(namespace, key, lock);
    }
  }
}

function buildCache(options: SerializableLruOptions, s: Stats): AnyCache {
  if (options.maxSize && options.maxEntrySize && options.maxEntrySize > options.maxSize) {
    throw new TypeError('maxEntrySize must not exceed maxSize');
  }
  const opts: SerializableLruOptions & {
    dispose: (_value: NonNullish, key: NonNullish, reason: LRUCache.DisposeReason) => void;
  } = {
    ...options,
    dispose: (_value, key, reason) => {
      if (reason === 'evict') {
        s.evictions += 1;
        supersedeFetch(s.namespace, key);
        if (primaryState.activeEvictions?.namespace === s.namespace) primaryState.activeEvictions.keys.push(key);
      }
    },
  };
  if (opts.max === undefined && opts.maxSize === undefined && opts.ttl === undefined) opts.max = 1000;
  return new LRUCache(opts as ConstructorParameters<typeof LRUCache>[0]);
}

export function getOrCreateCache(namespace: string, options?: SerializableLruOptions): AnyCache {
  let cache = caches.get(namespace);
  if (!cache) {
    stats.delete(namespace);
    cache = buildCache(options ?? {}, getStats(namespace));
    caches.set(namespace, cache);
    debug(`Created LRUCache for namespace '${namespace}'`);
  } else {
    assertOptionsCompatible(namespace, cache, options);
  }
  return cache;
}

// Pure dispatch: returns the value for the op or throws. Single source of truth
// for op semantics; both `handleRequest` (IPC entry point) and the in-process
// primary fast-path in `index.ts` call this. Avoids object/promise allocation
// per call when no IPC is involved.
export function dispatchOp(namespace: string, payload: ExecPayload, context: DispatchContext = {}): unknown {
  switch (payload.op) {
    case 'init': {
      const isNew = !caches.has(namespace);
      const cache = getOrCreateCache(namespace, payload.options);
      return { namespace, isNew, max: cache.max, version: getNamespaceVersion(namespace) };
    }
    case 'healthCheck':
      getOrCreateCache(namespace, payload.cacheOptions);
      return undefined;
    case 'destroy': {
      caches.get(namespace)?.clear();
      const existed = [caches, stats, fetchLocks].filter((m) => m.delete(namespace)).length > 0;
      if (existed) bumpNamespaceVersion(namespace);
      return existed;
    }
    case 'get': {
      const key = requireKey(payload.key);
      const cache = payload.existingOnly ? caches.get(namespace) : getCacheForPayload(namespace, payload);
      if (!cache) return undefined;
      const value = cache.get(key);
      getStats(namespace)[value !== undefined ? 'hits' : 'misses'] += 1;
      return value;
    }
    case 'set': {
      const key = requireKey(payload.key);
      const stored = writeEntry(getCacheForPayload(namespace, payload), key, requireValue(payload.value), payload);
      recordKeyWrite(namespace, key, stored);
      return stored;
    }
    case 'setIfAbsent': {
      const cache = getCacheForPayload(namespace, payload);
      const key = requireKey(payload.key);
      if (cache.peek(key, { allowStale: false }) !== undefined) return false;
      const stored = writeEntry(cache, key, requireValue(payload.value), payload);
      if (stored) recordKeyWrite(namespace, key, true);
      return stored;
    }
    case 'delete': {
      const key = requireKey(payload.key);
      const deleted = getCacheForPayload(namespace, payload).delete(key);
      const superseded = supersedeFetch(namespace, key);
      if (deleted) getStats(namespace).deletes += 1;
      if (deleted || superseded) bumpNamespaceVersion(namespace);
      return deleted;
    }
    case 'has':
    case 'peek':
    case 'getRemainingTTL':
      return getCacheForPayload(namespace, payload)[payload.op](requireKey(payload.key));
    case 'clear':
      getCacheForPayload(namespace, payload).clear();
      fetchLocks.delete(namespace);
      bumpNamespaceVersion(namespace);
      return undefined;
    case 'mGet': {
      const cache = getCacheForPayload(namespace, payload);
      const s = getStats(namespace);
      return payload.keys.map(requireKey).map((key) => {
        const value = cache.get(key);
        s[value !== undefined ? 'hits' : 'misses'] += 1;
        return [key, value] as [unknown, unknown];
      });
    }
    case 'mSet': {
      const cache = getCacheForPayload(namespace, payload);
      const s = getStats(namespace);
      const entries = payload.entries.map(([key, value, entryOpts]) => {
        const ttl = entryOpts?.ttl ?? payload.ttl;
        validateTtl(ttl);
        return [requireKey(key), requireValue(value), ttl, entryOpts?.size ?? payload.size] as const;
      });
      let changed = false;
      try {
        for (const [key, value, ttl, size] of entries) {
          if (writeEntry(cache, key, value, { ttl, size })) s.sets += 1;
          supersedeFetch(namespace, key);
          changed = true;
        }
      } finally {
        if (changed || entries.length === 0) bumpNamespaceVersion(namespace);
      }
      return undefined;
    }
    case 'mDelete': {
      const cache = getCacheForPayload(namespace, payload);
      const s = getStats(namespace);
      const keys = payload.keys.map(requireKey);
      for (const key of keys) {
        if (cache.delete(key)) s.deletes += 1;
        supersedeFetch(namespace, key);
      }
      bumpNamespaceVersion(namespace);
      return undefined;
    }
    case 'keys':
    case 'values':
    case 'entries':
      return [...getCacheForPayload(namespace, payload)[payload.op]()];
    case 'dump':
      return getCacheForPayload(namespace, payload).dump();
    case 'load': {
      const cache = getCacheForPayload(namespace, payload);
      const entries = payload.entries.map(([key, entry]) => {
        const safeKey = requireKey(key);
        const safeEntry = requireNonNullish('cache entry', entry) as { value?: unknown };
        requireValue(safeEntry.value);
        // Shallow-copy each entry because lru-cache@11 rewrites `entry.start`
        // in place from Date.now() to performance.now() during load().
        return [safeKey, { ...safeEntry }] as [NonNullish, LRUCache.Entry<NonNullish>];
      });
      // load() clears first and can then fail on a later entry's size.
      // Publication must cover both that clear and any entries already loaded.
      fetchLocks.delete(namespace);
      try {
        cache.load(entries);
      } finally {
        bumpNamespaceVersion(namespace);
      }
      return undefined;
    }
    case 'size':
      return getCacheForPayload(namespace, payload).size;
    case 'stats': {
      const s = getStats(namespace);
      s.size = getCacheForPayload(namespace, payload).size;
      return { ...s };
    }
    case 'purgeStale': {
      const purged = getCacheForPayload(namespace, payload).purgeStale();
      if (purged) bumpNamespaceVersion(namespace);
      return purged;
    }
    case 'incr':
    case 'decr': {
      const cache = getCacheForPayload(namespace, payload);
      const key = requireKey(payload.key);
      const amount = payload.amount === undefined ? 1 : payload.amount;
      const current = cache.peek(key, { allowStale: false });
      const existed = current !== undefined;
      const base = typeof current === 'number' ? current : 0;
      const next = base + amount * (payload.op === 'decr' ? -1 : 1);
      if (!Number.isFinite(amount) || !Number.isFinite(next)) throw new TypeError('invalid amount');
      if (!existed) validateTtl(payload.ttl);
      const size = payload.size ?? (existed ? cache.info(key)?.size : undefined);
      cache.set(key, next, existed ? { size, noUpdateTTL: true } : { ttl: payload.ttl, size });
      recordKeyWrite(namespace, key, cache.peek(key, { allowStale: true }) !== undefined);
      return next;
    }
    case 'fetchClaim': {
      const key = requireKey(payload.key);
      const existing = fetchLocks.get(namespace)?.get(key);
      if (payload.generation !== undefined && existing?.generation !== payload.generation) {
        const value = caches.get(namespace)?.get(key);
        if (value !== undefined) return { kind: 'value', value };
        throw new Error(SUPERSEDED_ERROR);
      }
      const cache = getCacheForPayload(namespace, payload);
      const now = Date.now();
      if (!payload.forceRefresh) {
        const value = cache.get(key);
        const s = getStats(namespace);
        if (value !== undefined) {
          if (payload.requestId) existing?.followers.delete(payload.requestId);
          if (existing) pruneFetchLock(namespace, key, existing);
          s.hits += 1;
          return { kind: 'value', value };
        }
        if (payload.generation === undefined) s.misses += 1;
        if (existing?.token && now - existing.claimedAt < FETCH_LEASE_MS) {
          if (payload.requestId) existing.followers.set(payload.requestId, context.workerId);
          return payload.requestId ? { kind: 'follower', generation: existing.generation } : { kind: 'follower' };
        }
      }
      const token = `fetch-${++primaryState.nextFetchToken}`;
      if (payload.requestId) existing?.followers.delete(payload.requestId);
      let nsLocks = fetchLocks.get(namespace);
      if (!nsLocks) fetchLocks.set(namespace, (nsLocks = new Map<NonNullish, FetchLock>()));
      nsLocks.set(key, {
        token,
        generation: existing?.generation ?? token,
        followers: existing?.followers ?? new Map<string, number | undefined>(),
        ownerWorkerId: context.workerId,
        requestId: payload.requestId,
        claimedAt: now,
      });
      return { kind: 'leader', token };
    }
    case 'fetchStore': {
      const key = requireKey(payload.key);
      const lock = fetchLocks.get(namespace)?.get(key);
      if (!lock || lock.token !== payload.token) return false;
      const stored = writeEntry(getCacheForPayload(namespace, payload), key, requireValue(payload.value), payload);
      recordKeyWrite(namespace, key, stored);
      return true;
    }
    case 'fetchAbort': {
      const key = requireKey(payload.key);
      const lock = fetchLocks.get(namespace)?.get(key);
      if (!lock || lock.token !== payload.token) return false;
      lock.token = lock.requestId = undefined;
      pruneFetchLock(namespace, key, lock);
      return true;
    }
    case 'fetchRelease': {
      const key = requireKey(payload.key);
      const lock = fetchLocks.get(namespace)?.get(key);
      if (!lock || (payload.generation !== undefined && lock.generation !== payload.generation)) return false;
      let removed = lock.followers.delete(payload.requestId);
      if (lock.requestId !== undefined && lock.requestId === payload.requestId) {
        lock.token = lock.requestId = undefined;
        removed = true;
      }
      pruneFetchLock(namespace, key, lock);
      return removed;
    }
    case 'max': {
      const cache = getCacheForPayload(namespace, payload);
      if (typeof payload.value === 'number' && payload.value !== cache.max) {
        const s = getStats(namespace);
        const opts: SerializableLruOptions = { max: payload.value };
        for (const k of 'maxSize maxEntrySize ttl allowStale updateAgeOnGet updateAgeOnHas noDeleteOnStaleGet ttlAutopurge'.split(
          ' ',
        )) {
          (opts as Record<string, unknown>)[k] = (cache as unknown as Record<string, unknown>)[k];
        }
        const replacement = buildCache(opts, s);
        const dumped = cache.dump();
        if (opts.ttl) for (const [, e] of dumped) if (e.ttl === undefined) e.ttl = 0;
        replacement.load(dumped);
        caches.set(namespace, replacement);
        cache.clear();
        bumpNamespaceVersion(namespace);
        return replacement.max;
      }
      return cache.max;
    }
    case 'ttl': {
      const cache = getCacheForPayload(namespace, payload);
      if (typeof payload.value === 'number') {
        validateTtl(payload.value);
        if (!payload.value && !cache.max && !cache.maxSize) throw new TypeError('invalid ttl');
        if (payload.value !== cache.ttl) {
          cache.ttl = payload.value;
          bumpNamespaceVersion(namespace);
        }
      }
      return cache.ttl;
    }
    case 'allowStale': {
      const cache = getCacheForPayload(namespace, payload);
      if (typeof payload.value === 'boolean') cache.allowStale = payload.value;
      return cache.allowStale;
    }
    default: {
      const op = (payload as { op: string }).op;
      throw new Error(`unhandled op: ${op}`);
    }
  }
}

// Bulk ops broadcast a namespace-wide invalidate; single-key ops broadcast the
// specific key. Reasoning in spec section 5.3.
const BULK_BROADCAST_OPS: ReadonlySet<string> = new Set(
  'destroy clear purgeStale mSet mDelete load max ttl'.split(' '),
);

export function buildInvalidation(
  namespace: string,
  payload: ExecPayload,
  version: number,
): InvalidationPush | undefined {
  if (BULK_BROADCAST_OPS.has(payload.op)) {
    return { source: SOURCE, push: 'l1:invalidate-namespace', namespace, version };
  }
  // Single-key mutating ops carry `key`. Read ops don't reach here because
  // dispatchAndBroadcast checks the version-bump signal before invoking us.
  const key = (payload as { key?: unknown }).key;
  /* c8 ignore next -- all current version-bumping single-key ops validate a non-nullish key before this point. */
  if (key === undefined || key === null) return undefined;
  return { source: SOURCE, push: 'l1:invalidate', namespace, key, version };
}

function sendToWorker(worker: Worker, msg: Response | InvalidationPush): void {
  if (!worker.isConnected()) return;
  const logFailure = (error: unknown) => debug(`worker ${worker.id} send failed: %s`, error);
  try {
    worker.send(msg, (error: Error | null) => {
      if (error) logFailure(error);
    });
  } catch (err) {
    logFailure(err);
  }
}

const EVICTING_OPS: ReadonlySet<string> = new Set('set setIfAbsent mSet load incr decr fetchStore max'.split(' '));

function publishInvalidation(msg: InvalidationPush): void {
  emitInvalidation(msg);
  for (const worker of Object.values(cluster.workers ?? {})) {
    if (worker) sendToWorker(worker, msg);
  }
}

export function dispatchAndBroadcast(
  namespace: string,
  payload: ExecPayload,
  context: DispatchContext = {},
): DispatchResult<unknown> {
  const before = getNamespaceVersion(namespace);
  const capture = EVICTING_OPS.has(payload.op) ? { namespace, keys: [] as NonNullish[] } : undefined;
  const previousCapture = primaryState.activeEvictions;
  primaryState.activeEvictions = capture;
  let value: unknown;
  let after: number;
  try {
    value = dispatchOp(namespace, payload, context);
  } finally {
    primaryState.activeEvictions = previousCapture;
    after = getNamespaceVersion(namespace);
    if (after !== before) {
      const msg = buildInvalidation(namespace, payload, after);
      if (msg) publishInvalidation(msg);
      // A single-key write can evict other entries. Fence those keys too,
      // without clearing unrelated hot L1 entries in the namespace.
      if (msg?.push !== 'l1:invalidate-namespace') {
        for (const key of capture?.keys ?? []) {
          publishInvalidation({ source: SOURCE, push: 'l1:invalidate', namespace, key, version: after });
        }
      }
    }
    // Keep the final version in this response and push, then release metadata.
    if (payload.op === 'destroy') versions.delete(namespace);
  }
  const result: DispatchResult<unknown> = { value, version: after };
  if (capture?.keys.length) result.evictedKeys = capture.keys;
  if (payload.includeTTL) {
    const keys = payload.op === 'mGet' ? payload.keys : 'key' in payload ? [payload.key] : [];
    const cache = caches.get(namespace);
    result.ttls = keys.map((key) => {
      const ttl = cache?.getRemainingTTL(requireKey(key)) ?? 0;
      return Number.isFinite(ttl) ? ttl : null;
    });
  }
  return result;
}

export function handleRequest(request: Request, context: DispatchContext = {}): Response {
  if (!request || typeof request !== 'object') {
    return err(request, 'invalid request: not an object');
  }
  // Validate the full Request shape before dispatching. Without this guard,
  // a malformed payload reaching handleRequest directly (the IPC entry point
  // already filters via isOurRequest, but the function is exported and could
  // be called from anywhere) would call dispatchOp with undefined fields and
  // could mutate the namespace registry under non-string keys.
  if (!isOurRequest(request)) {
    return err(request, 'invalid request: missing required fields');
  }
  try {
    const result = dispatchAndBroadcast(request.namespace, request, context);
    return { id: request.id, source: SOURCE, ok: true, ...result };
  } catch (e) {
    return err(request, e);
  }
}

function err(request: unknown, cause: unknown): Response {
  const id =
    typeof request === 'object' && request !== null && typeof (request as { id?: unknown }).id === 'string'
      ? (request as { id: string }).id
      : '';
  return { id, source: SOURCE, ok: false, error: serializeError(cause) };
}

// Caller must check `cluster.isPrimary` — this only runs on the primary.
export function installClusterListener(): void {
  if (primaryState.clusterListenerInstalled) return;
  primaryState.clusterListenerInstalled = true;

  const release = (worker: Worker) => releaseFetchLocksForWorker(worker.id);
  cluster.on('disconnect', release);
  cluster.on('exit', release);
  cluster.on('fork', attachWorkerHandler);
  // Cover workers that already exist when the listener is installed late
  // (e.g. bootstrap() called after some forks). cluster.on('fork') only
  // fires for future workers, so without this those would never get a
  // message handler and their IPC requests would silently time out.
  for (const worker of Object.values(cluster.workers ?? {})) {
    if (worker) attachWorkerHandler(worker);
  }
}

function attachWorkerHandler(worker: Worker): void {
  worker.on('message', (raw: unknown) => {
    if (!isOurRequest(raw)) return;
    messagesDebug(`primary <- worker ${worker.id}`, raw);
    const response = handleRequest(raw, { workerId: worker.id });
    // The worker can disconnect between sending a request and us sending the
    // response. send() in that window throws synchronously; left unhandled,
    // it would propagate out of this listener and crash the primary, taking
    // every other worker with it.
    sendToWorker(worker, response);
  });
}

function isOurRequest(value: unknown): value is Request {
  return (
    isOurMessage(value) &&
    typeof value.id === 'string' &&
    typeof value.namespace === 'string' &&
    typeof value.op === 'string'
  );
}
