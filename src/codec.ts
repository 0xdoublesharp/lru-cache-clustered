import type { Stats } from './messages.js';
import type { FetchOptions, LRUCacheClustered, MSetEntry, ReadOptions, WriteOptions } from './index.js';

// A codec is a symmetric encode/decode pair. Both directions may be sync or
// async — gzip/brotli's sync flavours work fine, and so do MessagePack-style
// libraries that return Buffers, or async streams. The library never inspects
// or assumes anything about the encoded form beyond "lru-cache@11 accepts it",
// which means non-nullish.
export interface Codec<V, U> {
  encode(value: V): U | Promise<U>;
  decode(raw: U): V | Promise<V>;
}

// Methods that operate on or return cache values are wrapped through the
// codec; everything else (keys, lifecycle, metrics) passes through. We
// deliberately omit `incr`/`decr` (numeric ops that would not survive most
// codecs) and `dump`/`load` (which speak the raw stored form). Reach those
// via `wrapped.cache` when needed.
// eslint-disable-next-line @typescript-eslint/no-empty-object-type
export interface WrappedCache<K extends {}, V extends {}> {
  readonly cache: LRUCacheClustered<K, never>;
  readonly namespace: string;
  readonly ready: Promise<void>;

  get(key: K, opts?: ReadOptions): Promise<V | undefined>;
  set(key: K, value: V, opts?: WriteOptions): Promise<boolean>;
  setIfAbsent(key: K, value: V, opts?: WriteOptions): Promise<boolean>;
  has(key: K, opts?: ReadOptions): Promise<boolean>;
  peek(key: K, opts?: ReadOptions): Promise<V | undefined>;
  delete(key: K): Promise<boolean>;
  getRemainingTTL(key: K): Promise<number>;

  mGet(keys: K[], opts?: ReadOptions): Promise<Map<K, V | undefined>>;
  mSet(entries: Iterable<MSetEntry<K, V>>, opts?: WriteOptions): Promise<void>;
  mDelete(keys: K[]): Promise<void>;

  keys(): Promise<K[]>;
  values(): Promise<V[]>;
  entries(): Promise<Array<[K, V]>>;
  size(): Promise<number>;
  [Symbol.asyncIterator](): AsyncIterableIterator<[K, V]>;

  clear(): Promise<void>;
  destroy(): Promise<boolean>;
  healthCheck(): Promise<void>;
  purgeStale(): Promise<boolean>;
  stats(): Promise<Stats>;

  fetch(key: K, fetcher: (key: K) => Promise<V> | V, opts?: FetchOptions): Promise<V>;
}

// eslint-disable-next-line @typescript-eslint/no-empty-object-type
export function wrap<K extends {}, V extends {}, U extends {}>(
  cache: LRUCacheClustered<K, U>,
  codec: Codec<V, U>,
): WrappedCache<K, V> {
  const enc = (v: V): U | Promise<U> => codec.encode(v);
  const dec = (u: U): V | Promise<V> => codec.decode(u);
  const decOpt = async (u: U | undefined): Promise<V | undefined> => (u === undefined ? undefined : dec(u));

  // Cast once to a `never`-valued surface for the public `cache` field. Users
  // who want to bypass the codec can drop in via `wrapped.cache as any` — we
  // don't try to make that ergonomic, since doing so is the whole point of an
  // escape hatch.
  const underlying = cache as unknown as LRUCacheClustered<K, never>;

  const passthroughs = Object.fromEntries(
    'has delete getRemainingTTL mDelete keys size clear destroy healthCheck purgeStale stats'
      .split(' ')
      .map((m) => [m, (cache[m as keyof LRUCacheClustered<K, U>] as (...args: unknown[]) => unknown).bind(cache)]),
  ) as Pick<
    WrappedCache<K, V>,
    | 'has'
    | 'delete'
    | 'getRemainingTTL'
    | 'mDelete'
    | 'keys'
    | 'size'
    | 'clear'
    | 'destroy'
    | 'healthCheck'
    | 'purgeStale'
    | 'stats'
  >;

  const wrapped: WrappedCache<K, V> = {
    ...passthroughs,
    cache: underlying,
    namespace: cache.namespace,
    ready: cache.ready,

    async get(key, opts) {
      return decOpt(await cache.get(key, opts));
    },
    async set(key, value, opts) {
      return cache.set(key, await enc(value), opts);
    },
    async setIfAbsent(key, value, opts) {
      return cache.setIfAbsent(key, await enc(value), opts);
    },
    async peek(key, opts) {
      return decOpt(await cache.peek(key, opts));
    },

    async mGet(keys, opts) {
      const out = new Map<K, V | undefined>();
      for (const [k, v] of await cache.mGet(keys, opts)) out.set(k, await decOpt(v));
      return out;
    },
    async mSet(entries, opts) {
      const encoded: Array<MSetEntry<K, U>> = [];
      for (const [k, v, entryOpts] of entries) {
        const ev = await enc(v);
        encoded.push(entryOpts === undefined ? [k, ev] : [k, ev, entryOpts]);
      }
      return cache.mSet(encoded, opts);
    },

    async values() {
      return Promise.all(((await cache.values()) ?? []).map(async (v) => dec(v)));
    },
    async entries() {
      return Promise.all(((await cache.entries()) ?? []).map(async ([k, v]): Promise<[K, V]> => [k, await dec(v)]));
    },
    async *[Symbol.asyncIterator]() {
      for (const pair of await this.entries()) yield pair;
    },

    async fetch(key, fetcher, opts) {
      // Reuse the underlying cache.fetch single-flight path. Pass an inner
      // fetcher that encodes the produced value — the cache stores and returns
      // the encoded form, then we decode on the way out.
      return dec(await cache.fetch(key, async (k) => enc(await fetcher(k)), opts));
    },
  };

  return wrapped;
}
