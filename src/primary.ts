import cluster from 'node:cluster';
import type { Worker } from 'node:cluster';
import { LRUCache } from 'lru-cache';
import { emitInvalidation } from './invalidation.js';
import {
  SOURCE,
  isOurMessage,
  makeDebug,
  serializeError,
  type Request,
  type DispatchResult,
  type Response,
  type SerializableLruOptions,
  type Stats,
  type InvalidationPush,
} from './messages.js';

export { cluster };

// Distributive Omit so each member of the Request union keeps its own shape.
type DistributiveOmit<T, K extends keyof never> = T extends unknown ? Omit<T, K> : never;
export type ExecPayload = DistributiveOmit<Request, 'id' | 'namespace' | 'source'>;

const debug = makeDebug('primary');
const messagesDebug = makeDebug('messages');

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
  resolved?: Map<string, [NonNullish, number | undefined]>;
};

// Lease window for a fetch claim. If the leader hasn't called fetchStore
// or fetchAbort within this many ms, a new fetchClaim will overwrite the
// stale lock and become the new leader. Bounds tail latency when a leader
// hangs without process exit (which would otherwise be released by the
// cluster.on('exit') handler). 30s is generous for typical user fetchers
// and short enough that hung-leader incidents do not park requests forever.
export const FETCH_LEASE_MS = 30_000;
export const SUPERSEDED_ERROR = 'Fetch was superseded: no current value';

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
const attachedWorkers = new WeakSet<Worker>();

export function getNamespaceVersion(namespace: string): number {
  return versions.get(namespace) ?? 0;
}

function bumpNamespaceVersion(namespace: string): number {
  const next = (primaryState.nextMutationVersion ?? 0) + 1;
  primaryState.nextMutationVersion = next;
  versions.set(namespace, next);
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

function assertOptionsCompatible(namespace: string, cache: AnyCache, options?: SerializableLruOptions): void {
  if (!options) return;
  const current = cache as unknown as Required<SerializableLruOptions>;
  for (const [key, value] of Object.entries(options) as Array<
    [keyof SerializableLruOptions, SerializableLruOptions[keyof SerializableLruOptions]]
  >) {
    if (value !== undefined && current[key] !== (key === 'maxEntrySize' && !value ? current.maxSize : value)) {
      throw new Error(`Conflicting options (${namespace}): ${key}`);
    }
  }
}

function requireNonNullish(label: string, value: unknown): NonNullish {
  if (value === null || value === undefined) {
    throw new TypeError(`cache ${label} must not be null or undefined`);
  }
  return value;
}

const requireKey = (key: unknown): NonNullish => requireNonNullish('key', key);
const requireValue = (value: unknown): NonNullish => requireNonNullish('value', value);

function validateTtl(ttl: number | undefined, autopurge?: boolean): void {
  if (ttl !== undefined && (!Number.isInteger(ttl) || ttl < 0 || (autopurge && ttl > 0x7ffffffe))) {
    throw new TypeError('invalid ttl');
  }
}

const exceedsEntrySize = (cache: AnyCache, size: unknown): boolean =>
  !!cache.maxEntrySize && Number.isInteger(size) && (size as number) > cache.maxEntrySize;

function recordKeyWrite(namespace: string, key: NonNullish, stored: boolean): void {
  supersedeFetch(namespace, key);
  if (stored) getStats(namespace).sets += 1;
  bumpNamespaceVersion(namespace);
}

const ALLOW_STALE = { allowStale: true } as const;
const FRESH = { allowStale: false } as const;

function writeEntry(
  cache: AnyCache,
  key: NonNullish,
  value: NonNullish,
  opts: { ttl?: number; size?: number },
  keepTTL = false,
): boolean {
  const { ttl, size } = opts;
  if (!keepTTL) validateTtl(ttl, cache.ttlAutopurge);
  let setOpts: LRUCache.SetOptions<NonNullish, NonNullish, unknown> = keepTTL
    ? { size, noUpdateTTL: true }
    : { ttl, size };
  if (
    cache.maxEntrySize &&
    Number.isInteger(size) &&
    (size as number) > 0 &&
    cache.peek(key, ALLOW_STALE) === value &&
    cache.info(key)?.size !== size
  ) {
    const status: LRUCache.Status<NonNullish, NonNullish> = {};
    if (keepTTL) {
      cache.has(key, { updateAgeOnHas: false, status });
      setOpts = { ttl: status.ttl ?? 0, start: status.start, size };
    }
    cache.delete(key);
  }
  cache.set(key, value, setOpts);
  return cache.peek(key, ALLOW_STALE) !== undefined;
}

function clearLeader(lock: FetchLock): void {
  lock.token = lock.requestId = undefined;
}

function supersedeFetch(namespace: string, key: NonNullish): boolean {
  const locks = fetchLocks.get(namespace);
  const removed = locks?.delete(key) ?? false;
  if (locks?.size === 0) fetchLocks.delete(namespace);
  return removed;
}

function pruneFetchLock(namespace: string, key: NonNullish, lock?: FetchLock): void {
  if (lock && !lock.token && !lock.followers.size && !lock.resolved?.size) supersedeFetch(namespace, key);
}

function releaseFetchLocksForWorker(workerId: number): void {
  for (const [namespace, locks] of fetchLocks) {
    for (const [key, lock] of locks) {
      for (const [id, owner] of lock.followers) if (owner === workerId) lock.followers.delete(id);
      for (const [id, [, owner]] of lock.resolved ?? []) if (owner === workerId) lock.resolved!.delete(id);
      if (lock.ownerWorkerId === workerId) clearLeader(lock);
      pruneFetchLock(namespace, key, lock);
    }
  }
}

function buildCache(options: SerializableLruOptions, s: Stats): AnyCache {
  if (options.maxSize && options.maxEntrySize && options.maxEntrySize > options.maxSize) {
    throw new TypeError('invalid maxEntrySize');
  }
  if (options.ttlAutopurge) validateTtl(options.ttl, true);
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
    debug('%s', namespace);
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
  const getCache = () => caches.get(namespace) ?? getOrCreateCache(namespace, payload.cacheOptions);
  const getLock = (k: NonNullish) => fetchLocks.get(namespace)?.get(k);
  switch (payload.op) {
    case 'init':
      return {
        namespace,
        isNew: !caches.has(namespace),
        max: getOrCreateCache(namespace, payload.options).max,
        version: getNamespaceVersion(namespace),
      };
    case 'healthCheck':
      getOrCreateCache(namespace, payload.cacheOptions);
      return undefined;
    case 'destroy': {
      caches.get(namespace)?.clear();
      const existed = Boolean(+caches.delete(namespace) | +stats.delete(namespace) | +fetchLocks.delete(namespace));
      if (existed) bumpNamespaceVersion(namespace);
      return existed;
    }
    case 'get': {
      const key = requireKey(payload.key);
      const cache = payload.existingOnly ? caches.get(namespace) : getCache();
      if (!cache) return undefined;
      const value = cache.get(key);
      getStats(namespace)[value !== undefined ? 'hits' : 'misses'] += 1;
      return value;
    }
    case 'set': {
      const key = requireKey(payload.key);
      const stored = writeEntry(getCache(), key, requireValue(payload.value), payload);
      recordKeyWrite(namespace, key, stored);
      return stored;
    }
    case 'setIfAbsent': {
      const cache = getCache();
      const key = requireKey(payload.key);
      if (cache.peek(key, FRESH) !== undefined) return false;
      const value = requireValue(payload.value);
      validateTtl(payload.ttl, cache.ttlAutopurge);
      if (exceedsEntrySize(cache, payload.size)) return false;
      writeEntry(cache, key, value, payload);
      recordKeyWrite(namespace, key, true);
      return true;
    }
    case 'delete': {
      const key = requireKey(payload.key);
      const deleted = getCache().delete(key);
      const superseded = supersedeFetch(namespace, key);
      if (deleted) getStats(namespace).deletes += 1;
      if (deleted || superseded) bumpNamespaceVersion(namespace);
      return deleted;
    }
    case 'has':
    case 'peek':
    case 'getRemainingTTL':
      return getCache()[payload.op](requireKey(payload.key));
    case 'clear':
      getCache().clear();
      fetchLocks.delete(namespace);
      bumpNamespaceVersion(namespace);
      return undefined;
    case 'mGet': {
      const cache = getCache();
      const s = getStats(namespace);
      return payload.keys.map(requireKey).map((key) => {
        const value = cache.get(key);
        s[value !== undefined ? 'hits' : 'misses'] += 1;
        return [key, value] as [unknown, unknown];
      });
    }
    case 'mSet': {
      const cache = getCache();
      const s = getStats(namespace);
      const entries = payload.entries.map(([key, value, entryOpts]) => {
        const ttl = entryOpts?.ttl === undefined ? payload.ttl : entryOpts.ttl;
        validateTtl(ttl, cache.ttlAutopurge);
        return [
          requireKey(key),
          requireValue(value),
          ttl,
          entryOpts?.size === undefined ? payload.size : entryOpts.size,
        ] as const;
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
      const cache = getCache();
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
      return [...getCache()[payload.op]()];
    case 'dump':
      return getCache().dump();
    case 'load': {
      const cache = getCache();
      const entries = payload.entries.map(([key, entry]) => {
        const safeKey = requireKey(key);
        const safeEntry = requireNonNullish('entry', entry) as { value?: unknown; ttl?: number };
        requireValue(safeEntry.value);
        validateTtl(safeEntry.ttl, cache.ttlAutopurge);
        // Shallow-copy each entry because lru-cache@11 rewrites `entry.start`
        // in place from Date.now() to performance.now() during load().
        const copy = { ...safeEntry } as LRUCache.Entry<NonNullish>;
        if (cache.ttl && copy.ttl === undefined) copy.ttl = 0;
        return [safeKey, copy] as [NonNullish, LRUCache.Entry<NonNullish>];
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
      return getCache().size;
    case 'stats': {
      const s = getStats(namespace);
      s.size = getCache().size;
      return { ...s };
    }
    case 'purgeStale': {
      const purged = getCache().purgeStale();
      if (purged) bumpNamespaceVersion(namespace);
      return purged;
    }
    case 'incr':
    case 'decr': {
      const cache = getCache();
      const key = requireKey(payload.key);
      const amount = payload.amount === undefined ? 1 : payload.amount;
      const current = cache.peek(key, FRESH);
      const existed = current !== undefined;
      const next = (typeof current === 'number' ? current : 0) + amount * (payload.op === 'decr' ? -1 : 1);
      if (!Number.isFinite(amount) || !Number.isFinite(next)) throw new TypeError('invalid amount');
      const size = payload.size === undefined ? (existed ? cache.info(key)?.size : undefined) : payload.size;
      if (exceedsEntrySize(cache, size)) throw new RangeError('invalid size');
      writeEntry(cache, key, next, { ttl: payload.ttl, size }, existed);
      recordKeyWrite(namespace, key, true);
      return next;
    }
    case 'fetchClaim': {
      const key = requireKey(payload.key);
      const existing = getLock(key);
      const reqId = payload.requestId;
      const delivered = reqId ? existing?.resolved?.get(reqId) : undefined;
      if (delivered) {
        existing!.resolved!.delete(reqId!);
        pruneFetchLock(namespace, key, existing);
        getStats(namespace).hits += 1;
        return { kind: 'value', value: delivered[0] };
      }
      if (payload.generation !== undefined && existing?.generation !== payload.generation) {
        const value = caches.get(namespace)?.get(key);
        if (value !== undefined) return { kind: 'value', value };
        throw new Error(SUPERSEDED_ERROR);
      }
      const cache = getCache();
      const now = Date.now();
      if (!payload.forceRefresh) {
        const value = cache.get(key);
        const s = getStats(namespace);
        if (value !== undefined) {
          if (reqId) existing?.followers.delete(reqId);
          pruneFetchLock(namespace, key, existing);
          s.hits += 1;
          return { kind: 'value', value };
        }
        if (payload.generation === undefined) s.misses += 1;
        if (existing?.token && now - existing.claimedAt < FETCH_LEASE_MS) {
          if (reqId) {
            existing.followers.set(reqId, context.workerId);
            return { kind: 'follower', generation: existing.generation };
          }
          return { kind: 'follower' };
        }
      }
      const token = `fetch-${++primaryState.nextFetchToken}`;
      if (reqId) existing?.followers.delete(reqId);
      let nsLocks = fetchLocks.get(namespace);
      if (!nsLocks) fetchLocks.set(namespace, (nsLocks = new Map<NonNullish, FetchLock>()));
      nsLocks.set(key, {
        token,
        generation: existing?.token || existing?.followers.size ? existing.generation : token,
        followers: existing?.followers ?? new Map<string, number | undefined>(),
        resolved: existing?.resolved,
        ownerWorkerId: context.workerId,
        requestId: reqId,
        claimedAt: now,
      });
      return { kind: 'leader', token };
    }
    case 'fetchStore': {
      const key = requireKey(payload.key);
      const lock = getLock(key);
      if (!lock || lock.token !== payload.token) return false;
      const value = requireValue(payload.value);
      const stored = writeEntry(getCache(), key, value, payload);
      if (stored) getStats(namespace).sets += 1;
      else if (lock.followers.size) {
        const resolved = (lock.resolved ??= new Map());
        for (const [id, wid] of lock.followers) resolved.set(id, [value, wid]);
      }
      lock.followers.clear();
      clearLeader(lock);
      pruneFetchLock(namespace, key, lock);
      bumpNamespaceVersion(namespace);
      return true;
    }
    case 'fetchAbort': {
      const key = requireKey(payload.key);
      const lock = getLock(key);
      if (!lock || lock.token !== payload.token) return false;
      clearLeader(lock);
      pruneFetchLock(namespace, key, lock);
      return true;
    }
    case 'fetchRelease': {
      const key = requireKey(payload.key);
      const lock = getLock(key);
      if (!lock) return false;
      let removed = lock.resolved?.delete(payload.requestId) ?? false;
      if (payload.generation === undefined || lock.generation === payload.generation) {
        if (lock.followers.delete(payload.requestId)) removed = true;
        if (lock.requestId !== undefined && lock.requestId === payload.requestId) {
          clearLeader(lock);
          removed = true;
        }
      }
      pruneFetchLock(namespace, key, lock);
      return removed;
    }
    case 'max': {
      const cache = getCache();
      if (payload.value !== undefined && payload.value !== cache.max) {
        const opts: SerializableLruOptions = { max: payload.value };
        for (const k of 'maxSize maxEntrySize ttl allowStale updateAgeOnGet updateAgeOnHas noDeleteOnStaleGet ttlAutopurge'.split(
          ' ',
        )) {
          (opts as Record<string, unknown>)[k] = (cache as unknown as Record<string, unknown>)[k];
        }
        const replacement = buildCache(opts, getStats(namespace));
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
      const cache = getCache();
      if (payload.value !== undefined) {
        validateTtl(payload.value, cache.ttlAutopurge);
        if (!payload.value && !cache.max && !cache.maxSize) throw new TypeError('invalid ttl');
        if (payload.value !== cache.ttl) {
          cache.ttl = payload.value;
          bumpNamespaceVersion(namespace);
        }
      }
      return cache.ttl;
    }
    case 'allowStale': {
      const cache = getCache();
      if (typeof payload.value === 'boolean') cache.allowStale = payload.value;
      return cache.allowStale;
    }
    default: {
      const op = (payload as { op: string }).op;
      throw new Error(`unhandled op: ${op}`);
    }
  }
}

export const hasOp = (list: string, op: string): boolean => list.includes(` ${op} `);

export function buildInvalidation(
  namespace: string,
  payload: ExecPayload,
  version: number,
): InvalidationPush | undefined {
  if (hasOp(' destroy clear purgeStale mSet mDelete load max ttl ', payload.op)) {
    return { source: SOURCE, push: 'l1:invalidate-namespace', namespace, version };
  }
  const key = (payload as { key?: unknown }).key;
  /* c8 ignore next -- all current version-bumping single-key ops validate a non-nullish key before this point. */
  if (key === undefined || key === null) return undefined;
  return { source: SOURCE, push: 'l1:invalidate', namespace, key, version };
}

function sendToWorker(worker: Worker, msg: Response | InvalidationPush): void {
  if (!worker.isConnected()) return;
  const onErr = (e: unknown) => {
    if (e) debug('%s', e);
  };
  try {
    worker.send(msg, onErr);
  } catch (e) {
    onErr(e);
  }
}

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
  const capture = hasOp(' set setIfAbsent mSet load incr decr fetchStore max ', payload.op)
    ? { namespace, keys: [] as NonNullish[] }
    : undefined;
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
    // Keep the final version in this response and push, then release metadata
    // unless a reentrant invalidation listener already recreated the namespace.
    if (payload.op === 'destroy' && versions.get(namespace) === after) versions.delete(namespace);
  }
  const result: DispatchResult<unknown> = { value, version: after };
  if (capture?.keys.length) result.evictedKeys = capture.keys;
  if (payload.includeTTL) {
    const keys = payload.op === 'mGet' ? payload.keys : 'key' in payload ? [payload.key] : [];
    const cache = caches.get(namespace);
    result.ttls = keys.map((key) => {
      const info = cache?.info(requireKey(key));
      return info ? (info.ttl ?? null) : 0;
    });
    if (value === true && (payload.op === 'set' || payload.op === 'fetchStore')) result.l1Value = payload.value;
  }
  return result;
}

export function handleRequest(request: Request, context: DispatchContext = {}): Response {
  if (!request || typeof request !== 'object') {
    return err(request, 'not an object');
  }
  if (!isOurRequest(request)) {
    return err(request, 'invalid request');
  }
  try {
    return { id: request.id, source: SOURCE, ok: true, ...dispatchAndBroadcast(request.namespace, request, context) };
  } catch (e) {
    return err(request, e);
  }
}

function err(request: unknown, cause: unknown): Response {
  const id =
    request && typeof request === 'object' && typeof (request as { id?: unknown }).id === 'string'
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
  if (attachedWorkers.has(worker)) return;
  attachedWorkers.add(worker);
  worker.on('message', (raw: unknown) => {
    if (!isOurRequest(raw)) return;
    messagesDebug('%d', worker.id, raw);
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
