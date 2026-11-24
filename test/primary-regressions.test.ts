import assert from 'node:assert/strict';
import { execFile } from 'node:child_process';
import cluster from 'node:cluster';
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
