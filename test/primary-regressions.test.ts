import assert from 'node:assert/strict';
import { execFile } from 'node:child_process';
import cluster from 'node:cluster';
import { performance } from 'node:perf_hooks';
import { promisify } from 'node:util';
import test from 'node:test';
import { fileURLToPath } from 'node:url';
import { LRUCacheClustered } from '../src/index.ts';
import { SOURCE, type Request } from '../src/messages.ts';
import { caches, dispatchAndBroadcast, getNamespaceVersion, handleRequest, versions } from '../src/primary.ts';

const runFile = promisify(execFile);
function request(namespace: string, op: string, extra: object = {}) {
  return handleRequest({ id: 'primary-regression', source: SOURCE, namespace, op, ...extra } as Request);
}
function claim(namespace: string, key = 'key') {
  const response = request(namespace, 'fetchClaim', { key });
  assert.ok(response.ok);
  return (response.value as { token: string }).token;
}

for (const op of ['mSet', 'load'] as const) {
  void test(`partial ${op} failure publishes changed primary state`, async () => {
    const namespace = `primary-partial-${op}`;
    const options = { namespace, maxSize: 10, failsafe: 'reject' as const };
    const reader = new LRUCacheClustered<string, string>({ ...options, localL1: { experimental: true, ttl: 5000 } });
    const writer = new LRUCacheClustered<string, string>(options);
    try {
      await writer.set('key', 'old', { size: 1 });
      await reader.get('key');
      const before = getNamespaceVersion(namespace);
      const entries =
        op === 'mSet'
          ? [
              ['key', 'new', { size: 1 }],
              ['bad', 'invalid', { size: 0 }],
            ]
          : [
              ['key', { value: 'new', size: 1 }],
              ['bad', { value: 'invalid', size: 0 }],
            ];
      const response = request(namespace, op, { entries });
      assert.equal(response.ok, false);
      assert.equal(caches.get(namespace)?.get('key'), 'new');
      assert.ok(getNamespaceVersion(namespace) > before, 'partial mutations must advance the version');
      assert.equal(await reader.get('key'), 'new', 'retained primary L1 must receive failed-operation invalidations');
    } finally {
      await reader.destroy();
      await writer.destroy();
    }
  });
}

void test('destroy reclaims namespace version records and recreated writes exceed old responses', () => {
  const baseline = versions.size;
  for (let i = 0; i < 100; i++) {
    const namespace = `primary-churn-${i}`;
    const old = dispatchAndBroadcast(namespace, { op: 'set', key: 'key', value: 'old' }).version;
    const destroyed = dispatchAndBroadcast(namespace, { op: 'destroy' });
    assert.ok(destroyed.version > old);
    assert.equal(versions.has(namespace), false, 'destroy must release the namespace version record');
    assert.equal(getNamespaceVersion(namespace), 0);
    const recreated = dispatchAndBroadcast(namespace, { op: 'set', key: 'key', value: 'new' });
    assert.ok(recreated.version > destroyed.version, 'recreation must reject earlier-generation responses');
    dispatchAndBroadcast(namespace, { op: 'destroy' });
  }
  assert.equal(versions.size, baseline);
});

for (const [op, extra] of [
  ['set', { key: 'key', value: 'explicit' }],
  ['delete', { key: 'key' }],
  ['mSet', { entries: [['key', 'explicit']] }],
  ['mDelete', { keys: ['key'] }],
  ['clear', {}],
  ['load', { entries: [] }],
  ['destroy', {}],
] as const) {
  void test(`${op} supersedes an earlier fetch claim`, () => {
    const namespace = `primary-fetch-supersede-${op}`;
    const token = claim(namespace);
    request(namespace, op, extra);
    const response = request(namespace, 'fetchStore', { key: 'key', value: 'stale', token });
    assert.ok(response.ok);
    assert.equal(response.value, false, 'superseded fetch must not store its result');
    assert.notEqual(caches.get(namespace)?.get('key'), 'stale');
    request(namespace, 'destroy');
  });
}

void test('failed set leaves a fetch claim usable; oversized set supersedes it', () => {
  const namespace = 'primary-fetch-rejected-set';
  request(namespace, 'init', { options: { maxSize: 5 } });
  const token = claim(namespace);
  assert.equal(request(namespace, 'set', { key: 'key', value: 'bad', size: 0 }).ok, false);
  const stored = request(namespace, 'fetchStore', { key: 'key', value: 'fetched', size: 1, token });
  assert.ok(stored.ok);
  assert.equal(stored.value, true);
  request(namespace, 'delete', { key: 'key' });
  const nextToken = claim(namespace);
  request(namespace, 'set', { key: 'key', value: 'too big', size: 6 });
  const superseded = request(namespace, 'fetchStore', { key: 'key', value: 'stale', size: 1, token: nextToken });
  assert.ok(superseded.ok);
  assert.equal(superseded.value, false);
  request(namespace, 'destroy');
});

void test('partial batch failure broadcasts to workers', () => {
  const original = cluster.workers;
  const sent: unknown[] = [];
  (cluster as unknown as { workers: unknown }).workers = {
    '9999': { id: 9999, isConnected: () => true, send: (msg: unknown) => sent.push(msg) },
  };
  try {
    const namespace = 'primary-partial-worker';
    request(namespace, 'init', { options: { maxSize: 5 } });
    const response = request(namespace, 'mSet', {
      entries: [
        ['key', 'new', { size: 1 }],
        ['bad', 'bad', { size: 0 }],
      ],
    });
    assert.equal(response.ok, false);
    assert.equal(sent.length, 1);
    assert.equal((sent[0] as { push: string }).push, 'l1:invalidate-namespace');
  } finally {
    (cluster as unknown as { workers: unknown }).workers = original;
  }
});

for (const mode of ['response', 'broadcast']) {
  void test(`real worker disconnect during ${mode} send does not crash primary`, { timeout: 20000 }, async () => {
    const result = await runFile(
      process.execPath,
      ['--import', 'tsx', fileURLToPath(new URL('./fixtures/primary-disconnect-child.ts', import.meta.url)), mode],
      { timeout: 18000 },
    );
    assert.match(result.stdout, /survived all disconnects/);
    assert.equal(result.stderr, '');
  });
}

void test('a rejected fetchStore after destroy does not recreate namespace state', () => {
  const namespace = 'primary-destroy-late-fetch';
  const token = claim(namespace);
  request(namespace, 'destroy');
  const result = request(namespace, 'fetchStore', { key: 'key', value: 'stale', token });
  assert.ok(result.ok);
  assert.equal(result.value, false);
  assert.equal(caches.has(namespace), false);
});

void test('a capacity eviction invalidates retained L1 and revokes an evicted-key refresh', async () => {
  const namespace = 'primary-eviction-side-effect';
  const reader = new LRUCacheClustered<string, string>({
    namespace,
    max: 1,
    failsafe: 'reject',
    localL1: { experimental: true, ttl: 5000 },
  });
  try {
    await reader.set('key', 'old');
    await reader.get('key');
    const response = request(namespace, 'fetchClaim', { key: 'key', forceRefresh: true });
    assert.ok(response.ok);
    const token = (response.value as { token: string }).token;
    request(namespace, 'set', { key: 'other', value: 'new' });
    assert.equal(await reader.get('key'), undefined, 'capacity eviction must invalidate the removed key');
    const stored = request(namespace, 'fetchStore', { key: 'key', token, value: 'stale' });
    assert.ok(stored.ok);
    assert.equal(stored.value, false);
  } finally {
    await reader.destroy();
  }
});

void test('partial mSet supersedes applied keys but leaves an unapplied key claim usable', () => {
  const namespace = 'primary-batch-partial-claims';
  request(namespace, 'init', { options: { maxSize: 5 } });
  const first = claim(namespace, 'first');
  const failed = claim(namespace, 'failed');
  const result = request(namespace, 'mSet', {
    entries: [
      ['first', 'new', { size: 1 }],
      ['failed', 'bad', { size: 0 }],
    ],
  });
  assert.equal(result.ok, false);
  const stale = request(namespace, 'fetchStore', { key: 'first', token: first, value: 'stale', size: 1 });
  assert.ok(stale.ok);
  assert.equal(stale.value, false);
  const valid = request(namespace, 'fetchStore', { key: 'failed', token: failed, value: 'valid', size: 1 });
  assert.ok(valid.ok);
  assert.equal(valid.value, true);
  request(namespace, 'destroy');
});

void test('capacity eviction preserves an unrelated retained hot key', async () => {
  const namespace = 'primary-targeted-eviction';
  const reader = new LRUCacheClustered<string, string>({
    namespace,
    max: 2,
    failsafe: 'reject',
    localL1: { experimental: true, ttl: 5000 },
  });
  try {
    await reader.set('evicted', 'old');
    await reader.set('hot', 'retained');
    await reader.get('evicted');
    await reader.get('hot');
    const before = reader.localStats()!.ipcAvoided;
    request(namespace, 'set', { key: 'other', value: 'new' });
    assert.equal(await reader.get('hot'), 'retained');
    assert.equal(reader.localStats()!.ipcAvoided, before + 1, 'evict only the keys removed from authoritative storage');
    assert.equal(await reader.get('evicted'), undefined);
  } finally {
    await reader.destroy();
  }
});

void test('existingOnly get does not recreate a destroyed namespace', () => {
  const namespace = 'primary-existing-only';
  request(namespace, 'set', { key: 'key', value: 'old' });
  request(namespace, 'destroy');
  const response = request(namespace, 'get', { key: 'key', existingOnly: true });
  assert.ok(response.ok);
  assert.equal(response.value, undefined);
  assert.equal(caches.has(namespace), false);
});

void test('fetchRelease clears a timed-out leader lock by ownerRequestId', () => {
  const namespace = 'primary-fetch-release-leader';
  try {
    const first = request(namespace, 'fetchClaim', { key: 'key', requestId: 'req-leader' });
    assert.ok(first.ok);
    const firstVal = first.value as { kind: string; token: string };
    assert.equal(firstVal.kind, 'leader');

    // Simulate worker IPC timeout on fetchClaim: worker never received the token
    // and only sends fetchRelease with its requestId.
    const released = request(namespace, 'fetchRelease', { key: 'key', requestId: 'req-leader' });
    assert.ok(released.ok);
    assert.equal(released.value, true, 'fetchRelease must release a leader lock owned by requestId');

    // Another caller must immediately be able to claim leadership without waiting 30s.
    const next = request(namespace, 'fetchClaim', { key: 'key', requestId: 'req-next' });
    assert.ok(next.ok);
    assert.equal((next.value as { kind: string }).kind, 'leader');
  } finally {
    request(namespace, 'destroy');
  }
});

void test('load does not mutate caller dump entries across repeated primary-mode loads', () => {
  const srcNs = 'primary-load-immut-src';
  const dstA = 'primary-load-immut-a';
  const dstB = 'primary-load-immut-b';
  try {
    request(srcNs, 'init', { options: { max: 10, ttl: 60_000 } });
    request(srcNs, 'set', { key: 'k', value: 'v', ttl: 60_000 });
    const dumpResp = request(srcNs, 'dump');
    assert.ok(dumpResp.ok);
    const dump = dumpResp.value as Array<[string, { value: string; ttl?: number; start?: number }]>;
    const originalStart = dump[0]?.[1].start;
    assert.equal(typeof originalStart, 'number');

    request(dstA, 'init', { options: { max: 10, ttl: 60_000 } });
    request(dstB, 'init', { options: { max: 10, ttl: 60_000 } });

    assert.equal(request(dstA, 'load', { entries: dump }).ok, true);
    assert.equal(dump[0]?.[1].start, originalStart, 'load must not mutate caller entry.start in place');
    assert.equal(request(dstB, 'load', { entries: dump }).ok, true);

    assert.equal((request(dstA, 'get', { key: 'k' }) as { value: unknown }).value, 'v');
    assert.equal((request(dstB, 'get', { key: 'k' }) as { value: unknown }).value, 'v');
    const remB = (request(dstB, 'getRemainingTTL', { key: 'k' }) as { value: number }).value;
    assert.ok(remB > 0 && remB <= 60_000, `expected positive remaining TTL on second load, got ${remB}`);
  } finally {
    request(srcNs, 'destroy');
    request(dstA, 'destroy');
    request(dstB, 'destroy');
  }
});

void test('load rejects nullish entry metadata cleanly', () => {
  const namespace = 'primary-load-null-entry';
  try {
    request(namespace, 'init', { options: { max: 10 } });
    const resp = request(namespace, 'load', { entries: [['k', null]] });
    assert.equal(resp.ok, false);
    if (!resp.ok) assert.match(resp.error.message, /cache entry must not be null or undefined/);
  } finally {
    request(namespace, 'destroy');
  }
});

void test('destroy and max rebuild clear discarded caches so autopurge timers are released', () => {
  const namespace = 'primary-clear-discarded';
  try {
    request(namespace, 'init', { options: { max: 5, ttl: 60_000, ttlAutopurge: true } });
    request(namespace, 'set', { key: 'a', value: 1 });
    const initialCache = caches.get(namespace);
    assert.ok(initialCache);
    assert.equal(initialCache.size, 1);

    request(namespace, 'max', { value: 10 });
    assert.equal(initialCache.size, 0, 'max rebuild must clear the replaced cache and its timers');
    const rebuiltCache = caches.get(namespace);
    assert.ok(rebuiltCache);
    assert.notEqual(rebuiltCache, initialCache);
    assert.equal(rebuiltCache.size, 1);

    request(namespace, 'destroy');
    assert.equal(rebuiltCache.size, 0, 'destroy must clear the removed cache and its timers');
  } finally {
    request(namespace, 'destroy');
  }
});

void test('ttl setter validates nonnegative integers and prevents unbounding a ttl-only cache', () => {
  const boundedNs = 'primary-ttl-validate-bounded';
  const ttlOnlyNs = 'primary-ttl-validate-only';
  try {
    request(boundedNs, 'init', { options: { max: 10, ttl: 1000 } });
    for (const bad of [-1, 1.5, Number.NaN, Number.POSITIVE_INFINITY]) {
      const resp = request(boundedNs, 'ttl', { value: bad });
      assert.equal(resp.ok, false, `expected ttl=${String(bad)} to be rejected`);
    }
    // 0 is allowed when max > 0 (disables default TTL).
    const zeroOk = request(boundedNs, 'ttl', { value: 0 });
    assert.equal(zeroOk.ok, true);
    assert.equal((zeroOk as { value: number }).value, 0);

    // 0 must be rejected when neither max nor maxSize is set.
    request(ttlOnlyNs, 'init', { options: { ttl: 1000, ttlAutopurge: true } });
    const zeroUnbounded = request(ttlOnlyNs, 'ttl', { value: 0 });
    assert.equal(zeroUnbounded.ok, false);
  } finally {
    request(boundedNs, 'destroy');
    request(ttlOnlyNs, 'destroy');
  }
});

void test('polling followers do not inflate primary miss stats on repeated poll cycles', () => {
  const namespace = 'primary-follower-poll-misses';
  try {
    request(namespace, 'init', { options: { max: 10 } });
    const leader = request(namespace, 'fetchClaim', { key: 'k', requestId: 'leader' });
    assert.ok(leader.ok);
    const firstFollow = request(namespace, 'fetchClaim', { key: 'k', requestId: 'f1' });
    assert.ok(firstFollow.ok);
    const generation = (firstFollow.value as { generation: string }).generation;
    // Simulate 5 poll retries from the same follower.
    for (let i = 0; i < 5; i++) {
      const poll = request(namespace, 'fetchClaim', { key: 'k', requestId: 'f1', generation });
      assert.ok(poll.ok);
      assert.equal((poll.value as { kind: string }).kind, 'follower');
    }
    const statsResp = request(namespace, 'stats');
    assert.ok(statsResp.ok);
    assert.equal(
      (statsResp.value as { misses: number }).misses,
      2,
      'only initial misses (leader + first follower lookup) should count toward misses',
    );
  } finally {
    request(namespace, 'destroy');
  }
});

void test('promoting a follower to leader removes its follower registration so fetchAbort prunes the lock immediately', () => {
  const namespace = 'primary-promoted-follower-prune';
  const state = (globalThis as Record<PropertyKey, unknown>)[Symbol.for('lru-cache-clustered.primary')] as {
    fetchLocks: Map<string, Map<unknown, { followers: Map<string, unknown> }>>;
  };
  try {
    request(namespace, 'init', { options: { max: 10 } });
    const l1 = request(namespace, 'fetchClaim', { key: 'k', requestId: 'req-1' });
    assert.ok(l1.ok);
    const f2 = request(namespace, 'fetchClaim', { key: 'k', requestId: 'req-2' });
    assert.ok(f2.ok);
    const generation = (f2.value as { generation: string }).generation;
    assert.equal(request(namespace, 'fetchAbort', { key: 'k', token: (l1.value as { token: string }).token }).ok, true);

    // Follower req-2 takes over as leader; it must no longer remain registered in followers.
    const promoted = request(namespace, 'fetchClaim', { key: 'k', requestId: 'req-2', generation });
    assert.ok(promoted.ok);
    assert.equal((promoted.value as { kind: string }).kind, 'leader');
    assert.equal(state.fetchLocks.get(namespace)?.get('k')?.followers.has('req-2'), false);

    // Aborting the promoted leader with no other followers must immediately prune the lock.
    assert.equal(
      request(namespace, 'fetchAbort', { key: 'k', token: (promoted.value as { token: string }).token }).ok,
      true,
    );
    assert.equal(state.fetchLocks.has(namespace), false, 'lock must be pruned immediately on abort');
  } finally {
    request(namespace, 'destroy');
  }
});

void test('mGet validates all keys before mutating stats on invalid input', () => {
  const namespace = 'primary-mget-atomic-validate';
  try {
    request(namespace, 'init', { options: { max: 10 } });
    request(namespace, 'set', { key: 'a', value: 1 });
    const resp = request(namespace, 'mGet', { keys: ['a', null] });
    assert.equal(resp.ok, false);
    if (!resp.ok) assert.match(resp.error.message, /cache key must not be null or undefined/);
    const statsResp = request(namespace, 'stats');
    assert.ok(statsResp.ok);
    assert.equal((statsResp.value as { hits: number }).hits, 0, 'failed mGet must not mutate hit stats');
    assert.equal((statsResp.value as { misses: number }).misses, 0, 'failed mGet must not mutate miss stats');
  } finally {
    request(namespace, 'destroy');
  }
});

void test('incr and decr reject non-finite amount values instead of storing NaN/Infinity', () => {
  const namespace = 'primary-incr-decr-finite-amount';
  try {
    request(namespace, 'init', { options: { max: 10 } });
    request(namespace, 'set', { key: 'c', value: 5 });
    for (const op of ['incr', 'decr'] as const) {
      for (const bad of [
        Number.NaN,
        Number.POSITIVE_INFINITY,
        Number.NEGATIVE_INFINITY,
        null as unknown as number,
        '2' as unknown as number,
      ]) {
        const resp = request(namespace, op, { key: 'c', amount: bad });
        assert.equal(resp.ok, false, `expected ${op} with amount=${String(bad)} to fail`);
        if (!resp.ok) assert.match(resp.error.message, /invalid amount/i);
      }
    }
    assert.equal((request(namespace, 'get', { key: 'c' }) as { value: unknown }).value, 5);

    // Overflow past finite double range must reject instead of storing Infinity.
    request(namespace, 'set', { key: 'big', value: Number.MAX_VALUE });
    const overflow = request(namespace, 'incr', { key: 'big', amount: Number.MAX_VALUE });
    assert.equal(overflow.ok, false);
    assert.equal((request(namespace, 'get', { key: 'big' }) as { value: unknown }).value, Number.MAX_VALUE);
  } finally {
    request(namespace, 'destroy');
  }
});

void test('oversized writes do not report admission or inflate sets, and invalid per-write ttl rejects', () => {
  const namespace = 'primary-oversize-and-neg-ttl';
  try {
    request(namespace, 'init', { options: { maxSize: 10, maxEntrySize: 5 } });

    // Oversized setIfAbsent must not claim key or count as a set.
    const sia = request(namespace, 'setIfAbsent', { key: 'claim', value: 'v1', size: 6 });
    assert.ok(sia.ok);
    assert.equal(sia.value, false);
    assert.equal((request(namespace, 'stats') as { value: { sets: number } }).value.sets, 0);

    // Normal set followed by oversized set removes old value, returns false, and does not increment sets.
    assert.equal((request(namespace, 'set', { key: 'k', value: 'v1', size: 2 }) as { value: boolean }).value, true);
    assert.equal((request(namespace, 'stats') as { value: { sets: number } }).value.sets, 1);
    const overSet = request(namespace, 'set', { key: 'k', value: 'v2', size: 6 });
    assert.ok(overSet.ok);
    assert.equal(overSet.value, false);
    assert.equal((request(namespace, 'has', { key: 'k' }) as { value: boolean }).value, false);
    assert.equal((request(namespace, 'stats') as { value: { sets: number } }).value.sets, 1);

    // Oversized mSet does not inflate sets.
    assert.equal(request(namespace, 'mSet', { entries: [['m', 'v', { size: 6 }]] }).ok, true);
    assert.equal((request(namespace, 'stats') as { value: { sets: number } }).value.sets, 1);

    // Oversized fetchStore still acknowledges token (returns true) without inflating sets.
    const claim = request(namespace, 'fetchClaim', { key: 'f', requestId: 'r1' });
    assert.ok(claim.ok);
    const tok = (claim.value as { token: string }).token;
    const fstore = request(namespace, 'fetchStore', { key: 'f', token: tok, value: 'v', size: 6 });
    assert.ok(fstore.ok);
    assert.equal(fstore.value, true);
    assert.equal((request(namespace, 'stats') as { value: { sets: number } }).value.sets, 1);

    // Negative / non-integer per-write TTL rejects across all write paths.
    for (const badTtl of [-1, 1.5, Number.NaN, Number.POSITIVE_INFINITY]) {
      assert.equal(request(namespace, 'set', { key: 't', value: 'v', size: 1, ttl: badTtl }).ok, false);
      assert.equal(request(namespace, 'setIfAbsent', { key: 't', value: 'v', size: 1, ttl: badTtl }).ok, false);
      assert.equal(request(namespace, 'mSet', { entries: [['t', 'v', { size: 1, ttl: badTtl }]] }).ok, false);
      assert.equal(request(namespace, 'incr', { key: 't', amount: 1, size: 1, ttl: badTtl }).ok, false);
    }
  } finally {
    request(namespace, 'destroy');
  }
});

void test('maxEntrySize > maxSize is rejected and identical maxEntrySize=0 options stay compatible', () => {
  const badNs = 'primary-bad-max-entry-size';
  const compatNs = 'primary-compat-zero-max-entry-size';
  try {
    const bad = request(badNs, 'init', { options: { max: 2, maxSize: 4, maxEntrySize: 8 } });
    assert.equal(bad.ok, false);
    if (!bad.ok) assert.match(bad.error.message, /maxEntrySize/i);

    assert.equal(request(compatNs, 'init', { options: { maxSize: 10, maxEntrySize: 0 } }).ok, true);
    assert.equal(request(compatNs, 'init', { options: { maxSize: 10, maxEntrySize: 0 } }).ok, true);
  } finally {
    request(badNs, 'destroy');
    request(compatNs, 'destroy');
  }
});

void test('same-value write updates entry size and max() preserves non-expiring keys after ttl()', () => {
  const sizeNs = 'primary-same-value-size-update';
  const maxTtlNs = 'primary-max-after-ttl-infinity';
  try {
    request(sizeNs, 'init', { options: { maxSize: 10 } });
    request(sizeNs, 'set', { key: 'a', value: 'same', size: 1 });
    request(sizeNs, 'set', { key: 'a', value: 'same', size: 9 });
    request(sizeNs, 'set', { key: 'b', value: 'other', size: 2 });
    assert.equal((request(sizeNs, 'has', { key: 'a' }) as { value: boolean }).value, false);
    assert.equal((request(sizeNs, 'has', { key: 'b' }) as { value: boolean }).value, true);

    request(maxTtlNs, 'init', { options: { max: 2 } });
    request(maxTtlNs, 'set', { key: 'forever', value: 'v' });
    assert.equal((request(maxTtlNs, 'getRemainingTTL', { key: 'forever' }) as { value: number }).value, Infinity);
    request(maxTtlNs, 'ttl', { value: 1000 });
    request(maxTtlNs, 'max', { value: 3 });
    assert.equal(
      (request(maxTtlNs, 'getRemainingTTL', { key: 'forever' }) as { value: number }).value,
      Infinity,
      'max() rebuild must not assign default ttl to previously non-expiring entries',
    );
  } finally {
    request(sizeNs, 'destroy');
    request(maxTtlNs, 'destroy');
  }
});

void test('late worker attachment deduplicates fork events so requests never execute twice', async () => {
  const { default: cluster } = await import('node:cluster');
  const namespace = 'primary-dedup-worker-attach';
  const listeners: Array<(msg: unknown) => void> = [];
  const responses: unknown[] = [];
  const fakeWorker = {
    id: 99_123,
    isConnected: () => true,
    on(event: string, cb: (msg: unknown) => void) {
      if (event === 'message') listeners.push(cb);
    },
    send(msg: unknown, cb?: (err: Error | null) => void) {
      responses.push(msg);
      cb?.(null);
      return true;
    },
  };
  try {
    // Emitting fork twice for the same worker object (or late install + fork) must attach once.
    cluster.emit('fork', fakeWorker);
    cluster.emit('fork', fakeWorker);
    assert.equal(listeners.length, 1, 'same worker must not receive duplicate IPC handlers');
    listeners[0]?.({ id: '1', namespace, source: SOURCE, op: 'incr', key: 'counter' });
    assert.equal(responses.length, 1);
    assert.equal((request(namespace, 'get', { key: 'counter' }) as { value: number }).value, 1);
  } finally {
    request(namespace, 'destroy');
  }
});

void test('oversize fetchStore delivers computed value to registered followers and prunes lock', () => {
  const namespace = 'primary-oversize-fetch-followers';
  const state = (globalThis as Record<PropertyKey, unknown>)[Symbol.for('lru-cache-clustered.primary')] as {
    fetchLocks: Map<string, Map<unknown, unknown>>;
  };
  try {
    request(namespace, 'init', { options: { maxSize: 5 } });
    const l = request(namespace, 'fetchClaim', { key: 'k', requestId: 'leader' });
    assert.ok(l.ok);
    const f = request(namespace, 'fetchClaim', { key: 'k', requestId: 'follower' });
    assert.ok(f.ok);
    const tok = (l.value as { token: string }).token;
    const gen = (f.value as { generation: string }).generation;

    const stored = request(namespace, 'fetchStore', { key: 'k', token: tok, value: 'big-val', size: 6 });
    assert.ok(stored.ok);
    assert.equal(stored.value, true);

    // Registered follower must receive 'big-val' instead of failing as superseded, then lock prunes.
    const fRes = request(namespace, 'fetchClaim', { key: 'k', requestId: 'follower', generation: gen });
    assert.ok(fRes.ok);
    assert.deepEqual(fRes.value, { kind: 'value', value: 'big-val' });
    assert.equal(state.fetchLocks.has(namespace), false, 'lock must prune after last follower consumes value');
  } finally {
    request(namespace, 'destroy');
  }
});

void test('oversize incr rejects without deleting existing counter, and same-value size updates cover maxEntrySize and incr(0)', () => {
  const counterNs = 'primary-oversize-incr';
  const maxEntryNs = 'primary-same-value-maxentrysize';
  try {
    request(counterNs, 'init', { options: { maxSize: 10 } });
    assert.equal((request(counterNs, 'incr', { key: 'c', amount: 3, size: 1 }) as { value: number }).value, 3);
    const over = request(counterNs, 'incr', { key: 'c', amount: 1, size: 11 });
    assert.equal(over.ok, false);
    assert.equal((request(counterNs, 'get', { key: 'c' }) as { value: number }).value, 3);

    // Same-value counter size update (no TTL and with TTL).
    assert.equal((request(counterNs, 'incr', { key: 'c', amount: 0, size: 8 }) as { value: number }).value, 3);
    assert.equal(caches.get(counterNs)?.info('c')?.size, 8);
    assert.equal(
      (request(counterNs, 'incr', { key: 'ct', amount: 1, size: 1, ttl: 10_000 }) as { value: number }).value,
      1,
    );
    assert.equal((request(counterNs, 'incr', { key: 'ct', amount: 0, size: 2 }) as { value: number }).value, 1);
    const ctInfo = caches.get(counterNs)?.info('ct');
    assert.equal(ctInfo?.size, 2);
    assert.ok(typeof ctInfo?.ttl === 'number' && ctInfo.ttl > 0 && ctInfo.ttl <= 10_000);

    // Same-value size update with { max, maxEntrySize } (no maxSize).
    request(maxEntryNs, 'init', { options: { max: 5, maxEntrySize: 10 } });
    request(maxEntryNs, 'set', { key: 'a', value: 'same', size: 1 });
    request(maxEntryNs, 'set', { key: 'a', value: 'same', size: 8 });
    assert.equal(caches.get(maxEntryNs)?.info('a')?.size, 8);
  } finally {
    request(counterNs, 'destroy');
    request(maxEntryNs, 'destroy');
  }
});

void test('oversize setIfAbsent preserves readable stale entries when allowStale and noDeleteOnStaleGet are enabled', (t) => {
  let now = 1000;
  t.mock.method(performance, 'now', () => now);
  const namespace = 'primary-oversize-sia-stale';
  try {
    request(namespace, 'init', {
      options: { maxEntrySize: 5, max: 10, ttl: 50, allowStale: true, noDeleteOnStaleGet: true },
    });
    request(namespace, 'set', { key: 'k', value: 'stale-val', size: 1 });
    now += 100;
    assert.equal((request(namespace, 'peek', { key: 'k' }) as { value: unknown }).value, 'stale-val');

    const sia = request(namespace, 'setIfAbsent', { key: 'k', value: 'too-big', size: 6 });
    assert.ok(sia.ok);
    assert.equal(sia.value, false);
    assert.equal(
      (request(namespace, 'peek', { key: 'k' }) as { value: unknown }).value,
      'stale-val',
      'oversize setIfAbsent must not delete a readable stale value',
    );
  } finally {
    request(namespace, 'destroy');
  }
});

void test('JSON null ttl/max inputs, load ttl validation/non-expiring preservation, and autopurge overflow guard', () => {
  const ns = 'primary-json-null-and-load';
  const apNs = 'primary-autopurge-overflow';
  try {
    request(ns, 'init', { options: { max: 10, ttl: 5000 } });
    request(ns, 'set', { key: 'keep', value: 'v' });

    // JSON IPC converts NaN/Infinity to null; mSet, ttl(), and max() must reject null.
    assert.equal(request(ns, 'mSet', { entries: [['k', 'v', { ttl: null }]] }).ok, false);
    assert.equal(request(ns, 'ttl', { value: null }).ok, false);
    assert.equal(request(ns, 'max', { value: null }).ok, false);

    // load() rejects negative/invalid ttl without clearing existing entries.
    assert.equal(request(ns, 'load', { entries: [['bad', { value: 'v', ttl: -1 }]] }).ok, false);
    assert.equal((request(ns, 'get', { key: 'keep' }) as { value: unknown }).value, 'v');

    // load() preserves non-expiring snapshot entries (omitted ttl) even on a TTL cache.
    assert.equal(request(ns, 'load', { entries: [['forever', { value: 'v' }]] }).ok, true);
    assert.equal((request(ns, 'getRemainingTTL', { key: 'forever' }) as { value: number }).value, Infinity);

    // 30-day TTL with ttlAutopurge=true must reject instead of spinning 1ms overflow timers.
    const thirtyDays = 30 * 24 * 60 * 60 * 1000;
    assert.equal(request(apNs, 'init', { options: { max: 10, ttl: thirtyDays, ttlAutopurge: true } }).ok, false);
    assert.equal(request(apNs, 'init', { options: { max: 10, ttl: 1000, ttlAutopurge: true } }).ok, true);
    assert.equal(request(apNs, 'ttl', { value: thirtyDays }).ok, false);
    assert.equal(request(apNs, 'set', { key: 'x', value: 1, ttl: thirtyDays }).ok, false);
  } finally {
    request(ns, 'destroy');
    request(apNs, 'destroy');
  }
});

void test('reentrant write during destroy preserves the recreated namespace version', async () => {
  const { LRUCacheClustered } = await import('../src/index.ts');
  const namespace = 'primary-reentrant-destroy-version';
  const first = new LRUCacheClustered<string, string>({
    namespace,
    max: 10,
    localL1: { experimental: true, ttl: 5000 },
  });
  const second = new LRUCacheClustered<string, string>({
    namespace,
    max: 10,
    localL1: { experimental: true, ttl: 5000 },
  });
  try {
    await first.set('k', 'old');
    await second.get('k');
    let writePromise: Promise<boolean> | undefined;
    second.once('l1:invalidate', () => {
      writePromise = second.set('k', 'new');
    });
    await first.destroy();
    await writePromise;

    assert.equal(await second.get('k'), 'new');
    const hitsBefore = second.localStats()!.hits;
    assert.equal(await second.get('k'), 'new');
    assert.equal(second.localStats()!.hits, hitsBefore + 1, 'recreated namespace must retain its version for L1 fills');
  } finally {
    await second.destroy();
  }
});
