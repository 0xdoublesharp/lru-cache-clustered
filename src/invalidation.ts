import { makeDebug, type InvalidationPush } from './messages.js';

type Handler = (msg: InvalidationPush) => void;
const key = Symbol.for('lru-cache-clustered.invalidations');
const subscribers = ((globalThis as Record<PropertyKey, unknown>)[key] ??= new Map<string, Set<Handler>>()) as Map<
  string,
  Set<Handler>
>;
const debug = makeDebug('invalidations');

export function subscribeMap<T>(map: Map<string, Set<T>>, namespace: string, handler: T): () => void {
  let handlers = map.get(namespace);
  if (!handlers) map.set(namespace, (handlers = new Set()));
  handlers.add(handler);
  return () => {
    handlers.delete(handler);
    if (handlers.size === 0 && map.get(namespace) === handlers) map.delete(namespace);
  };
}

export function emitMap(map: Map<string, Set<Handler>>, msg: InvalidationPush, log = debug): void {
  for (const handler of map.get(msg.namespace) ?? []) {
    try {
      handler(msg);
    } catch (error) {
      log('%s', error);
    }
  }
}

export const subscribeInvalidations = (namespace: string, handler: Handler): (() => void) =>
  subscribeMap(subscribers, namespace, handler);

export const emitInvalidation = (msg: InvalidationPush): void => emitMap(subscribers, msg);
