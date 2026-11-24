import assert from 'node:assert/strict';
import cluster from 'node:cluster';
import { setTimeout } from 'node:timers/promises';
import { LRUCacheClustered } from '../../src/index.ts';
import { getDefaultClient } from '../../src/worker.ts';

if (!cluster.isWorker) throw new Error('coverage fixture requires a cluster worker');

async function exerciseSiblingInvalidations() {
  const options = {
    namespace: 'coverage-worker-sibling-mutations',
    max: 10,
    ttl: 60_000,
    localL1: { experimental: true, ttl: 5000 },
  };
  const writer = await LRUCacheClustered.getInstance<string, string>(options);
  const reader = await LRUCacheClustered.getInstance<string, string>(options);
  const warm = async (key: string, expected: string) => {
    assert.equal(await reader.get(key), expected);
    const hits = reader.localStats()!.hits;
    assert.equal(await reader.get(key), expected);
    assert.equal(reader.localStats()!.hits, hits + 1);
  };
  try {
    await writer.set('key', 'before');
    await warm('key', 'before');
    let invalidations = reader.localStats()!.invalidations;
    assert.equal(await writer.delete('missing'), false);
    assert.equal(reader.localStats()!.invalidations, invalidations);
    await warm('key', 'before');
    assert.equal(await writer.delete('key'), true);
    assert.equal(reader.localStats()!.size, 0);
    assert.equal(await reader.get('key'), undefined);

    assert.equal(await writer.setIfAbsent('key', 'inserted'), true);
    await warm('key', 'inserted');
    invalidations = reader.localStats()!.invalidations;
    assert.equal(await writer.setIfAbsent('key', 'must-not-overwrite'), false);
    assert.equal(reader.localStats()!.invalidations, invalidations);
    await warm('key', 'inserted');

    invalidations = reader.localStats()!.invalidations;
    assert.equal(await writer.purgeStale(), false);
    assert.equal(reader.localStats()!.invalidations, invalidations);
    await warm('key', 'inserted');
    await writer.set('stale', 'expired', { ttl: 1 });
    await setTimeout(30);
    assert.equal(await writer.purgeStale(), true);
    assert.equal(reader.localStats()!.size, 0);
    assert.equal(await reader.get('stale'), undefined);
    await warm('key', 'inserted');

    invalidations = reader.localStats()!.invalidations;
    assert.equal(await writer.max(), 10);
    assert.equal(await writer.ttl(), 60_000);
    assert.equal(reader.localStats()!.invalidations, invalidations);
    await warm('key', 'inserted');
    assert.equal(await writer.max(2), 2);
    assert.equal(reader.localStats()!.size, 0);
    await warm('key', 'inserted');
    assert.equal(await writer.ttl(30_000), 30_000);
    assert.equal(reader.localStats()!.size, 0);
    await warm('key', 'inserted');
  } finally {
    await reader.destroy();
    await writer.destroy();
  }
}

async function exerciseFailedFollowerCleanup() {
  const namespace = 'coverage-worker-failed-release';
  const options = { namespace, max: 10 };
  const leader = await LRUCacheClustered.getInstance<string, string>(options);
  const follower = await LRUCacheClustered.getInstance<string, string>(options);
  let release!: () => void;
  let started!: () => void;
  const gate = new Promise<void>((resolve) => {
    release = resolve;
  });
  const start = new Promise<void>((resolve) => {
    started = resolve;
  });
  const leaderFailure = new Error('original leader failure');
  const pendingLeader = leader
    .fetch('key', async () => {
      started();
      await gate;
      throw leaderFailure;
    })
    .catch((error: unknown) => error);
  await start;

  const client = getDefaultClient();
  const originalSend = client.sendToPrimaryWithMeta;
  const timeoutFailure = new Error('lost follower acknowledgement');
  let generation: string | undefined;
  let releaseAttempts = 0;
  let followerCalls = 0;
  client.sendToPrimaryWithMeta = async <T>(...args: Parameters<typeof originalSend>) => {
    if (args[1].op === 'fetchRelease') {
      releaseAttempts++;
      throw new Error('cleanup transport unavailable');
    }
    const response = await originalSend<T>(...args);
    const claim = response.value as { kind?: string; generation?: string };
    if (args[1].op === 'fetchClaim' && claim.kind === 'follower') {
      generation = claim.generation;
      throw timeoutFailure;
    }
    return response;
  };
  try {
    await assert.rejects(
      follower.fetch('key', () => {
        followerCalls++;
        return 'must-not-run';
      }),
      (error: unknown) => error === timeoutFailure,
    );
    assert.equal(releaseAttempts, 1);
    assert.equal(followerCalls, 0);
    assert.equal(typeof generation, 'string');
  } finally {
    client.sendToPrimaryWithMeta = originalSend;
    release();
    assert.equal(await pendingLeader, leaderFailure);
  }
  // Leave the registered follower to the real primary disconnect handler.
  return { namespace, generation };
}

async function exerciseWorkerInitL1SubscriptionCleanup() {
  const localSubs = (globalThis as Record<PropertyKey, unknown>)[
    Symbol.for('lru-cache-clustered.invalidations')
  ] as Map<string, Set<unknown>>;

  // Case 1: destroy() called before constructor's async init completes must not leave a leaked subscription.
  const nsImmediate = 'coverage-worker-destroy-before-init';
  const eager = new LRUCacheClustered<string, string>({
    namespace: nsImmediate,
    max: 10,
    localL1: { experimental: true, ttl: 5000 },
  });
  await eager.destroy();
  await eager.ready;
  assert.equal(localSubs.get(nsImmediate)?.size ?? 0, 0, 'destroy before init must not leak L1 subscription');

  // Case 2: failed getInstance() with conflicting options must clean up its L1 subscription.
  const nsConflict = 'coverage-worker-failed-init-l1';
  const owner = await LRUCacheClustered.getInstance<string, string>({
    namespace: nsConflict,
    max: 10,
  });
  try {
    await assert.rejects(
      LRUCacheClustered.getInstance<string, string>({
        namespace: nsConflict,
        max: 20,
        localL1: { experimental: true, ttl: 5000 },
      }),
      /Conflicting options/,
    );
    assert.equal(localSubs.get(nsConflict)?.size ?? 0, 0, 'failed init must not leak L1 subscription');
  } finally {
    await owner.destroy();
  }
}

async function exerciseWorkerL1SnapshotAndCounterJsonIpc() {
  const namespace = 'coverage-worker-l1-snapshot-and-counter';
  const cache = await LRUCacheClustered.getInstance<string, { nested: number } | number>({
    namespace,
    max: 10,
    localL1: { experimental: true, ttl: 5000 },
  });
  try {
    // Mutating the caller's object while set({ updateL1: true }) is in flight must not diverge L1 from primary.
    const obj = { nested: 1 };
    const pSet = cache.set('obj', obj, { updateL1: true });
    obj.nested = 2;
    await pSet;
    assert.deepEqual(await cache.get('obj'), { nested: 1 });
    assert.deepEqual(await cache.withoutLocal().get('obj'), { nested: 1 });

    // Same isolation for fetch() leader populating L1.
    const fetchedObj = { nested: 10 };
    await cache.fetch('fetched', () => fetchedObj);
    fetchedObj.nested = 99;
    assert.deepEqual(await cache.get('fetched'), { nested: 10 });
    assert.deepEqual(await cache.withoutLocal().get('fetched'), { nested: 10 });

    // JSON-serializable objects with toJSON() must work with updateL1: true under JSON IPC.
    const customJson = {
      secret: 'omit',
      toJSON() {
        return { n: 1 };
      },
    };
    assert.equal(await cache.set('tojson', customJson as unknown as { nested: number }, { updateL1: true }), true);
    assert.deepEqual(await cache.get('tojson'), { n: 1 });
    assert.deepEqual(await cache.withoutLocal().get('tojson'), { n: 1 });

    // JSON IPC serializes Infinity/NaN to null; primary must still reject instead of incrementing by 1.
    await assert.rejects(cache.incr('counter', Number.POSITIVE_INFINITY), /invalid amount/i);
    await assert.rejects(cache.incr('counter', Number.NaN), /invalid amount/i);
    assert.equal(await cache.get('counter'), undefined);
  } finally {
    await cache.destroy();
  }
}

try {
  await exerciseSiblingInvalidations();
  await exerciseWorkerInitL1SubscriptionCleanup();
  await exerciseWorkerL1SnapshotAndCounterJsonIpc();
  const cleanup = await exerciseFailedFollowerCleanup();
  process.send?.({ kind: 'result', cleanup }, () => process.disconnect?.());
} catch (error) {
  process.send?.({ kind: 'error', message: String(error) }, () => process.disconnect?.());
}
