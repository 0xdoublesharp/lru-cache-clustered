import { LRUCache } from 'lru-cache';
import { subscribeMap } from './invalidation.js';
import { perfNow } from './messages.js';

export type L1Stats = {
  enabled: true;
  hits: number;
  misses: number;
  sets: number;
  invalidations: number;
  evictions: number;
  staleHits: number;
  size: number;
  ipcAvoided: number;
};

export type L1Read = { version: number; cancelled: boolean; release: () => void };

type L1Envelope<V> = {
  value: V;
  version: number;
  expiresAt?: number;
  key: unknown;
};

type L1EmitEvent = 'hit' | 'miss' | 'set' | 'invalidate' | 'evict' | 'stale-hit';

type L1EmitPayload = {
  key?: unknown;
  version?: number;
  reason?: string;
};

type L1EmitFn = (event: L1EmitEvent, payload: L1EmitPayload) => void;

type L1ConstructorOptions = {
  max?: number;
  maxSize?: number;
  ttl?: number;
  updateAgeOnGet?: boolean;
  allowStale?: boolean;
  emit?: L1EmitFn; // optional; defaults to no-op
};

const objectKeyIds = new WeakMap<object, number>();
let nextObjectKeyId = 0;

function objectKeyId(key: object): number {
  let id = objectKeyIds.get(key);
  if (!id) objectKeyIds.set(key, (id = ++nextObjectKeyId));
  return id;
}

// Encode arbitrary cache keys into a string the L1 LRUCache can index by.
// Primitives use a typed prefix so 1 (number) and "1" (string) do not collide.
// Objects and functions use WeakMap-backed identity IDs so L1 mirrors
// lru-cache's SameValueZero key semantics instead of structural equality.
// Symbol keys are rejected because Symbol.toString is not stable across realms
// and the L1 would dedup by description, which is wrong.
//
// eslint-disable-next-line @typescript-eslint/no-empty-object-type
export function encodeL1Key(key: {}): string {
  const t = typeof key;
  if (t === 'symbol') throw new Error('symbol keys unsupported');
  return t === 'object' || t === 'function'
    ? `${t[0]}:${objectKeyId(key)}`
    : `${t === 'bigint' ? 'i' : t[0]}:${key as string | number | boolean | bigint}`;
}

// Per-instance L1 cache. One LocalL1Cache per LRUCacheClustered.
// Namespace clears establish a version floor. Key invalidations remove only
// their entry and fence pending fills; releasing each fill reclaims its metadata.
//
// eslint-disable-next-line @typescript-eslint/no-empty-object-type
export class LocalL1Cache<V extends {} = {}> {
  readonly #cache: LRUCache<string, L1Envelope<V>>;
  readonly #ttl?: number;
  #latestSeen = 0;
  readonly #pending = new Map<string, Set<L1Read>>();
  readonly #stats: Omit<L1Stats, 'size'> = {
    enabled: true,
    hits: 0,
    misses: 0,
    sets: 0,
    invalidations: 0,
    evictions: 0,
    staleHits: 0,
    ipcAvoided: 0,
  };
  readonly #emit: L1EmitFn;

  constructor(opts: L1ConstructorOptions) {
    this.#emit = opts.emit ?? (() => undefined);
    this.#ttl = opts.ttl;
    this.#cache = new LRUCache({
      max: opts.max ?? 1000,
      ttl: opts.ttl,
      updateAgeOnGet: opts.updateAgeOnGet ?? true,
      allowStale: opts.allowStale ?? false,
      maxSize: opts.maxSize,
      // sizeCalculation is required when maxSize is set, but for v1 we don't
      // expose it in the public LocalL1Options. If a caller passes maxSize,
      // we use a 1-per-entry calculation as a placeholder.
      sizeCalculation: opts.maxSize !== undefined ? () => 1 : undefined,
      disposeAfter: (value: L1Envelope<V>, key: string, reason: LRUCache.DisposeReason) => {
        if (reason === 'evict') {
          this.#stats.evictions += 1;
          this.#emit('evict', { key: value.key ?? key, reason: 'lru' });
        }
      },
    });
  }

  get(encodedKey: string, eventKey: unknown = encodedKey, mode: 'get' | 'peek' | 'has' = 'get'): V | undefined {
    const status: { returnedStale?: true } = {};
    let entry =
      mode === 'get'
        ? this.#cache.get(encodedKey, { status })
        : this.#cache.peek(encodedKey, { allowStale: mode !== 'has' && this.#cache.allowStale });
    if (mode === 'peek' && entry && this.#cache.getRemainingTTL(encodedKey) < 0) status.returnedStale = true;
    if (entry) {
      const expired =
        entry.version < this.#latestSeen || (entry.expiresAt !== undefined && perfNow() >= entry.expiresAt);
      if (expired || status.returnedStale) {
        // Neither a local sliding TTL nor allowStale may extend the primary's
        // expiration deadline or revive a value invalidated by a write.
        this.#stats.staleHits += 1;
        this.#emit('stale-hit', { key: entry.key });
        if (expired) {
          this.#cache.delete(encodedKey);
          entry = undefined;
        }
      }
    }
    if (!entry) {
      this.#stats.misses += 1;
      this.#emit('miss', { key: eventKey });
      return undefined;
    }
    this.#stats.hits += 1;
    this.#stats.ipcAvoided += 1;
    this.#emit('hit', { key: entry.key });
    return entry.value;
  }

  set(
    encodedKey: string,
    value: V,
    version: number,
    ttl?: number,
    eventKey: unknown = encodedKey,
    read?: L1Read,
  ): void {
    const existing = this.#cache.peek(encodedKey, { allowStale: true });
    if (
      version < this.#latestSeen ||
      (existing && version < existing.version) ||
      (read && (read.cancelled || version < read.version))
    ) {
      // Don't store an entry already known to be stale.
      return;
    }
    let setOpts: { ttl: number } | undefined;
    let expiresAt: number | undefined;
    if (Number.isFinite(ttl)) {
      const capped = this.#ttl === undefined ? (ttl as number) : Math.min(ttl as number, this.#ttl);
      if (capped <= 0) return;
      setOpts = { ttl: capped };
      expiresAt = perfNow() + (ttl as number);
    }
    this.#cache.set(encodedKey, { value, version, expiresAt, key: eventKey }, setOpts);
    this.#stats.sets += 1;
    this.#emit('set', { key: eventKey, version });
  }

  trackRead(encodedKey: string): L1Read {
    const read = { version: this.#latestSeen, cancelled: false } as L1Read;
    read.release = subscribeMap(this.#pending, encodedKey, read);
    return read;
  }

  delete(encodedKey: string, eventKey: unknown = encodedKey, emit = true, version?: number): void {
    for (const read of this.#pending.get(encodedKey) ?? []) {
      if (version === undefined) read.cancelled = true;
      else read.version = Math.max(read.version, version);
    }
    const entry = this.#cache.peek(encodedKey, { allowStale: true });
    if (entry && (version === undefined || entry.version < version) && this.#cache.delete(encodedKey)) {
      this.#stats.invalidations += 1;
      if (emit) this.#emit('invalidate', { key: eventKey, reason: 'self' });
    }
  }

  clear(emit = true, version?: number): void {
    let invalidated = false;
    if (version === undefined) {
      for (const pending of this.#pending.values()) {
        for (const read of pending) read.cancelled = true;
      }
      invalidated = this.#cache.size > 0;
      this.#cache.clear();
    } else {
      this.advanceLatestSeen(version);
      if (!this.#cache.allowStale) this.#cache.purgeStale();
      for (const [key, entry] of this.#cache.entries()) {
        if (entry.version < version) {
          this.#cache.delete(key);
          invalidated = true;
        }
      }
    }
    if (invalidated) this.#stats.invalidations += 1;
    if (emit) this.#emit('invalidate', { key: '*', reason: 'clear' });
  }

  advanceLatestSeen(version: number): void {
    if (version > this.#latestSeen) this.#latestSeen = version;
  }

  latestSeen(): number {
    return this.#latestSeen;
  }

  stats(): L1Stats {
    return { ...this.#stats, size: this.#cache.size };
  }

  // For tests / explicit teardown.
  destroy(): void {
    this.clear(false);
  }
}
