import Debug from 'debug';

// Short sentinel for IPC payload filtering. Each request and response carries
// this string so the listener can ignore foreign messages on the shared cluster
// IPC channel. Kept short (6 bytes) to minimize wire overhead — at 10k ops/sec
// the savings versus a long package-name string add up to ~500KB/sec.
export const SOURCE = 'lcfcap' as const;
type Source = typeof SOURCE;

// Keep the debug namespace unscoped so it stays ergonomic in `DEBUG=...` and
// stable across the canonical scoped package and the mirrored legacy publish.
export const makeDebug = (suffix: string) => Debug(`lru-cache-clustered-${suffix}`);
export const perfNow = () => globalThis.performance.now();

type RequestBase = {
  id: string;
  namespace: string;
  source: Source;
  cacheOptions?: SerializableLruOptions;
  includeTTL?: boolean;
};

export type Request = RequestBase &
  (
    | { op: 'init'; options: SerializableLruOptions }
    | { op: 'healthCheck' }
    | { op: 'destroy' }
    | { op: 'get'; key: unknown; existingOnly?: boolean }
    | { op: 'set'; key: unknown; value: unknown; ttl?: number; size?: number }
    | { op: 'setIfAbsent'; key: unknown; value: unknown; ttl?: number; size?: number }
    | { op: 'delete'; key: unknown }
    | { op: 'has'; key: unknown }
    | { op: 'peek'; key: unknown }
    | { op: 'getRemainingTTL'; key: unknown }
    | { op: 'clear' }
    | { op: 'purgeStale' }
    | { op: 'mGet'; keys: unknown[] }
    | {
        op: 'mSet';
        entries: Array<[unknown, unknown] | [unknown, unknown, { ttl?: number; size?: number }]>;
        ttl?: number;
        size?: number;
      }
    | { op: 'mDelete'; keys: unknown[] }
    | { op: 'keys' }
    | { op: 'values' }
    | { op: 'entries' }
    | { op: 'dump' }
    | { op: 'load'; entries: Array<[unknown, unknown]> }
    | { op: 'size' }
    | { op: 'stats' }
    | { op: 'incr'; key: unknown; amount?: number; ttl?: number; size?: number }
    | { op: 'decr'; key: unknown; amount?: number; ttl?: number; size?: number }
    | { op: 'fetchClaim'; key: unknown; forceRefresh?: boolean; generation?: string; requestId?: string }
    | { op: 'fetchRelease'; key: unknown; generation?: string; requestId: string }
    | { op: 'fetchStore'; key: unknown; token: string; value: unknown; ttl?: number; size?: number }
    | { op: 'fetchAbort'; key: unknown; token: string }
    | { op: 'allowStale'; value?: boolean }
    | { op: 'max'; value?: number }
    | { op: 'ttl'; value?: number }
  );

// Errors flow over IPC as a structured payload so consumers can branch on
// `name`/`code`/`cause` instead of regex-matching a `message` string. Internal
// to the wire format — workers receive a reconstructed `Error` via
// `deserializeError`, never this raw shape.
type SerializedError = {
  name: string;
  message: string;
  code?: string | number;
  stack?: string;
  cause?: SerializedError;
};

// TTLs align with the requested keys. null represents Infinity on JSON IPC.
export type DispatchResult<T> = {
  value: T;
  version: number;
  ttls?: Array<number | null>;
  evictedKeys?: unknown[];
  l1Value?: unknown;
};

export type Response = { id: string; source: Source } & (
  | {
      ok: true;
      value: unknown;
      version?: number;
      ttls?: Array<number | null>;
      evictedKeys?: unknown[];
      l1Value?: unknown;
    }
  | { ok: false; error: SerializedError }
);

// Subset of LRUCache.Options that survives IPC structured-clone — no functions.
export type SerializableLruOptions = {
  max?: number;
  maxSize?: number;
  maxEntrySize?: number;
  ttl?: number;
  allowStale?: boolean;
  updateAgeOnGet?: boolean;
  updateAgeOnHas?: boolean;
  noDeleteOnStaleGet?: boolean;
  ttlAutopurge?: boolean;
};

export type Stats = {
  namespace: string;
  hits: number;
  misses: number;
  sets: number;
  deletes: number;
  evictions: number;
  size: number;
};

// Cause chains are walked recursively. Cap depth and detect cycles so a
// pathological error (self-referential cause, or a chain dozens deep)
// cannot stack-overflow the primary's IPC message handler and crash the
// cluster.
const SERIALIZE_CAUSE_MAX_DEPTH = 8;

export function serializeError(err: unknown, depth = 0, seen = new Set<object>()): SerializedError {
  if (err instanceof Error) {
    const { name, message, stack, code, cause } = err as Error & { code?: unknown; cause?: unknown };
    if (seen.has(err)) return { name, message: '[circular cause]' };
    seen.add(err);
    const out: SerializedError = { name, message };
    if (stack) out.stack = stack;
    if (typeof code === 'string' || typeof code === 'number') out.code = code;
    if (cause !== undefined) {
      out.cause =
        depth + 1 >= SERIALIZE_CAUSE_MAX_DEPTH
          ? { name: 'Error', message: '[cause chain truncated]' }
          : serializeError(cause, depth + 1, seen);
    }
    return out;
  }
  return { name: 'Error', message: typeof err === 'string' ? err : String(err) };
}

export function deserializeError(payload: SerializedError): Error {
  const { name, message, stack, code, cause } = payload;
  const err = new Error(message);
  err.name = name;
  if (stack) err.stack = stack;
  if (code !== undefined) (err as { code?: unknown }).code = code;
  if (cause !== undefined) (err as { cause?: unknown }).cause = deserializeError(cause);
  return err;
}

// Pushes are primary-to-worker fire-and-forget messages with no `id` and no
// matching response. The wire layer recognises them by the `push` discriminator
// (and the shared SOURCE filter); they never collide with `Request`/`Response`.
export type InvalidationPush =
  | { source: Source; push: 'l1:invalidate'; namespace: string; key: unknown; version: number }
  | { source: Source; push: 'l1:invalidate-namespace'; namespace: string; version: number };

export function isOurMessage(value: unknown): value is Record<string, unknown> {
  return !!value && typeof value === 'object' && (value as { source?: unknown }).source === SOURCE;
}

export function isInvalidationPush(value: unknown): value is InvalidationPush {
  return (
    isOurMessage(value) &&
    typeof value.namespace === 'string' &&
    Number.isFinite(value.version) &&
    (value.push === 'l1:invalidate' || value.push === 'l1:invalidate-namespace')
  );
}
