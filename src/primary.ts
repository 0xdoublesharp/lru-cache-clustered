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
const FETCH_LEASE_MS = 30_000;

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

function freshStats(namespace: string): Stats {
  return { namespace, hits: 0, misses: 0, sets: 0, deletes: 0, evictions: 0, size: 0 };
}

function getStats(namespace: string): Stats {
  let s = stats.get(namespace);
  if (!s) {
    s = freshStats(namespace);
    stats.set(namespace, s);
  }
  return s;
}

function readOptions(cache: AnyCache): SerializableLruOptions {
  const c = cache as unknown as {
    max: number;
    maxSize: number;
    maxEntrySize: number;
    ttl: number;
    allowStale: boolean;
    updateAgeOnGet: boolean;
    updateAgeOnHas: boolean;
    noDeleteOnStaleGet: boolean;
    ttlAutopurge: boolean;
  };
  return {
    max: c.max,
    maxSize: c.maxSize,
    maxEntrySize: c.maxEntrySize,
    ttl: c.ttl,
    allowStale: c.allowStale,
    updateAgeOnGet: c.updateAgeOnGet,
    updateAgeOnHas: c.updateAgeOnHas,
    noDeleteOnStaleGet: c.noDeleteOnStaleGet,
    ttlAutopurge: c.ttlAutopurge,
  };
}

function getCacheForPayload(namespace: string, payload: ExecPayload): AnyCache {
  const existing = caches.get(namespace);
  if (existing) return existing;
  return getOrCreateCache(namespace, payload.cacheOptions);
}

function assertOptionsCompatible(namespace: string, cache: AnyCache, options?: SerializableLruOptions): void {
  if (!options) return;

  const current = readOptions(cache);
  const mismatches: string[] = [];

  for (const [key, value] of Object.entries(options) as Array<
    [keyof SerializableLruOptions, SerializableLruOptions[keyof SerializableLruOptions]]
  >) {
    if (value === undefined) continue;
    if (current[key] !== value) {
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

function recordKeyWrite(namespace: string, key: NonNullish): void {
  supersedeFetch(namespace, key);
  getStats(namespace).sets += 1;
  bumpNamespaceVersion(namespace);
}

function readEntrySize(cache: AnyCache, key: NonNullish): number | undefined {
  const info = (
    cache as unknown as {
      info: (key: NonNullish) => LRUCache.Entry<NonNullish> | undefined;
    }
  ).info(key);
  return typeof info?.size === 'number' ? info.size : undefined;
}

function getFetchNamespaceLocks(namespace: string): Map<NonNullish, FetchLock> {
  let locks = fetchLocks.get(namespace);
  if (!locks) {
    locks = new Map();
    fetchLocks.set(namespace, locks);
  }
  return locks;
}

function supersedeFetch(namespace: string, key: NonNullish): boolean {
  const removed = fetchLocks.get(namespace)?.delete(key) ?? false;
  cleanupFetchNamespaceLocks(namespace);
  return removed;
}

function cleanupFetchNamespaceLocks(namespace: string): void {
  if (fetchLocks.get(namespace)?.size === 0) fetchLocks.delete(namespace);
}

function pruneFetchLock(namespace: string, key: NonNullish, lock: FetchLock): void {
  if (!lock.token && lock.followers.size === 0) fetchLocks.get(namespace)?.delete(key);
  cleanupFetchNamespaceLocks(namespace);
}

function releaseFetchLocksForWorker(workerId: number): void {
  for (const [namespace, locks] of fetchLocks) {
    for (const [key, lock] of locks) {
      for (const [requestId, owner] of lock.followers) {
        if (owner === workerId) lock.followers.delete(requestId);
      }
      if (lock.ownerWorkerId === workerId) {
        lock.token = undefined;
        lock.requestId = undefined;
      }
      if (!lock.token && lock.followers.size === 0) locks.delete(key);
    }
    cleanupFetchNamespaceLocks(namespace);
  }
}

function buildCache(options: SerializableLruOptions, s: Stats): AnyCache {
  const cacheOptions = {
    ...options,
    dispose: (_value: NonNullish, key: NonNullish, reason: LRUCache.DisposeReason) => {
      if (reason === 'evict') {
        s.evictions += 1;
        supersedeFetch(s.namespace, key);
        if (primaryState.activeEvictions?.namespace === s.namespace) primaryState.activeEvictions.keys.push(key);
      }
    },
  } as SerializableLruOptions & {
    dispose: (_value: NonNullish, _key: NonNullish, reason: LRUCache.DisposeReason) => void;
  };
  const defaultedOptions =
    cacheOptions.max === undefined && cacheOptions.maxSize === undefined && cacheOptions.ttl === undefined
      ? { ...cacheOptions, max: 1000 }
      : cacheOptions;
  return new LRUCache(defaultedOptions as ConstructorParameters<typeof LRUCache>[0]);
}

export function getOrCreateCache(namespace: string, options?: SerializableLruOptions): AnyCache {
  let cache = caches.get(namespace);
  if (!cache) {
    const s = freshStats(namespace);
    stats.set(namespace, s);
    cache = buildCache(options ?? {}, s);
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
      const existingCache = caches.get(namespace);
      const cacheExisted = caches.delete(namespace);
      existingCache?.clear();
      const statsExisted = stats.delete(namespace);
      const locksExisted = fetchLocks.delete(namespace);
      const existed = cacheExisted || statsExisted || locksExisted;
      if (existed) bumpNamespaceVersion(namespace);
      return existed;
    }
    case 'get': {
      const key = requireKey(payload.key);
      const cache = payload.existingOnly ? caches.get(namespace) : getCacheForPayload(namespace, payload);
      if (!cache) return undefined;
      const value = cache.get(key);
      const s = getStats(namespace);
      if (value !== undefined) s.hits += 1;
      else s.misses += 1;
      return value;
    }
    case 'set': {
      const key = requireKey(payload.key);
      getCacheForPayload(namespace, payload).set(key, requireValue(payload.value), {
        ttl: payload.ttl,
        size: payload.size,
      });
      recordKeyWrite(namespace, key);
      return true;
    }
    case 'setIfAbsent': {
      const cache = getCacheForPayload(namespace, payload);
      const key = requireKey(payload.key);
      if (cache.peek(key, { allowStale: false }) !== undefined) return false;
      cache.set(key, requireValue(payload.value), { ttl: payload.ttl, size: payload.size });
      recordKeyWrite(namespace, key);
      return true;
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
      return payload.keys.map((key) => {
        const value = cache.get(requireKey(key));
        if (value !== undefined) s.hits += 1;
        else s.misses += 1;
        return [key, value] as [unknown, unknown];
      });
    }
    case 'mSet': {
      const cache = getCacheForPayload(namespace, payload);
      const s = getStats(namespace);
      const entries = payload.entries.map(([key, value, entryOpts]) => ({
        key: requireKey(key),
        value: requireValue(value),
        entryOpts,
      }));
      let changed = false;
      try {
        for (const { key, value, entryOpts } of entries) {
          cache.set(key, value, {
            ttl: entryOpts?.ttl ?? payload.ttl,
            size: entryOpts?.size ?? payload.size,
          });
          supersedeFetch(namespace, key);
          changed = true;
          s.sets += 1;
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
      const cache = getCacheForPayload(namespace, payload);
      const s = getStats(namespace);
      s.size = cache.size;
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
      const current = cache.peek(key, { allowStale: false });
      const existed = current !== undefined;
      const base = typeof current === 'number' ? current : 0;
      const delta = (payload.amount ?? 1) * (payload.op === 'decr' ? -1 : 1);
      const next = base + delta;
      const size = payload.size ?? (existed ? readEntrySize(cache, key) : undefined);
      cache.set(key, next, existed ? { size, noUpdateTTL: true } : { ttl: payload.ttl, size });
      recordKeyWrite(namespace, key);
      return next;
    }
    case 'fetchClaim': {
      const key = requireKey(payload.key);
      const existing = fetchLocks.get(namespace)?.get(key);
      if (payload.generation !== undefined && existing?.generation !== payload.generation) {
        const value = caches.get(namespace)?.get(key);
        if (value !== undefined) return { kind: 'value', value };
        throw new Error('Fetch was superseded by a cache mutation and no current value remains');
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
      getFetchNamespaceLocks(namespace).set(key, {
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
      const locks = fetchLocks.get(namespace);
      const lock = locks?.get(key);
      if (!lock || lock.token !== payload.token) return false;
      getCacheForPayload(namespace, payload).set(key, requireValue(payload.value), {
        ttl: payload.ttl,
        size: payload.size,
      });
      recordKeyWrite(namespace, key);
      return true;
    }
    case 'fetchAbort': {
      const key = requireKey(payload.key);
      const lock = fetchLocks.get(namespace)?.get(key);
      if (!lock || lock.token !== payload.token) return false;
      lock.token = undefined;
      lock.requestId = undefined;
      pruneFetchLock(namespace, key, lock);
      return true;
    }
    case 'fetchRelease': {
      const key = requireKey(payload.key);
      const lock = fetchLocks.get(namespace)?.get(key);
      if (!lock || (payload.generation !== undefined && lock.generation !== payload.generation)) return false;
      let removed = lock.followers.delete(payload.requestId);
      if (lock.requestId !== undefined && lock.requestId === payload.requestId) {
        lock.token = undefined;
        lock.requestId = undefined;
        removed = true;
      }
      pruneFetchLock(namespace, key, lock);
      return removed;
    }
    case 'max': {
      const cache = getCacheForPayload(namespace, payload);
      if (typeof payload.value === 'number' && payload.value !== cache.max) {
        const s = getStats(namespace);
        const opts = { ...readOptions(cache), max: payload.value };
        const replacement = buildCache(opts, s);
        replacement.load(cache.dump());
        caches.set(namespace, replacement);
        cache.clear();
        bumpNamespaceVersion(namespace);
        return replacement.max;
      }
      return cache.max;
    }
    case 'ttl': {
      const cache = getCacheForPayload(namespace, payload);
      const current = (cache as unknown as { ttl: number }).ttl;
      if (typeof payload.value === 'number') {
        if (!Number.isInteger(payload.value) || payload.value < 0 || (!payload.value && !cache.max && !cache.maxSize)) {
          throw new TypeError('invalid ttl');
        }
        if (payload.value !== current) {
          (cache as unknown as { ttl: number }).ttl = payload.value;
          bumpNamespaceVersion(namespace);
        }
      }
      return (cache as unknown as { ttl: number }).ttl;
    }
    case 'allowStale': {
      const cache = getCacheForPayload(namespace, payload);
      if (typeof payload.value === 'boolean') (cache as unknown as { allowStale: boolean }).allowStale = payload.value;
      return (cache as unknown as { allowStale: boolean }).allowStale;
    }
    default: {
      const op = (payload as { op: string }).op;
      throw new Error(`unhandled op: ${op}`);
    }
  }
}

// Bulk ops broadcast a namespace-wide invalidate; single-key ops broadcast the
// specific key. Reasoning in spec section 5.3.
export const BULK_BROADCAST_OPS: ReadonlySet<string> = new Set([
  'destroy',
  'clear',
  'purgeStale',
  'mSet',
  'mDelete',
  'load',
  'max',
  'ttl',
]);

function buildInvalidation(namespace: string, payload: ExecPayload, version: number): InvalidationPush | undefined {
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
  try {
    worker.send(msg, (error: Error | null) => {
      if (error) debug(`worker ${worker.id} send failed: %s`, error);
    });
  } catch (err) {
    debug(`worker ${worker.id} send failed: %s`, err);
  }
}

function broadcastInvalidation(msg: InvalidationPush): void {
  for (const worker of Object.values(cluster.workers ?? {})) {
    if (worker) sendToWorker(worker, msg);
  }
}

const EVICTING_OPS: ReadonlySet<string> = new Set([
  'set',
  'setIfAbsent',
  'mSet',
  'load',
  'incr',
  'decr',
  'fetchStore',
  'max',
]);

function publishInvalidation(msg: InvalidationPush): void {
  emitInvalidation(msg);
  broadcastInvalidation(msg);
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
  if (typeof request !== 'object' || request === null) {
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

  cluster.on('disconnect', (worker: Worker) => {
    releaseFetchLocksForWorker(worker.id);
  });
  cluster.on('exit', (worker: Worker) => {
    releaseFetchLocksForWorker(worker.id);
  });
  cluster.on('fork', (worker: Worker) => {
    attachWorkerHandler(worker);
  });
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
