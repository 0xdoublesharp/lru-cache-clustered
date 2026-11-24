import { emitMap, subscribeMap } from './invalidation.js';
import {
  SOURCE,
  deserializeError,
  isInvalidationPush,
  isOurMessage,
  makeDebug,
  type InvalidationPush,
  type Request,
  type DispatchResult,
  type Response,
} from './messages.js';

const messagesDebug = makeDebug('messages');

// ESM, CommonJS, scoped and legacy copies all receive the same process IPC
// messages. Share the counter across copies so their response listeners cannot
// consume one another's responses, while keeping monotonically increasing IDs.
const STATE_KEY = Symbol.for('lru-cache-clustered.worker');
const workerState = ((globalThis as Record<PropertyKey, unknown>)[STATE_KEY] ??= { nextRequestId: 0 }) as {
  nextRequestId: number;
};

type SendOptions = {
  namespace: string;
  timeout: number;
  failsafe: 'resolve' | 'reject';
};

type ProcessLike = {
  send: (msg: unknown, callback: (error: Error | null) => void) => boolean | void;
  on: (event: 'message', cb: (msg: unknown) => void) => void;
};

// Distributive Omit so each member of the Request discriminated union keeps its own shape.
type DistributiveOmit<T, K extends keyof never> = T extends unknown ? Omit<T, K> : never;
type RequestPayload = DistributiveOmit<Request, 'id' | 'namespace' | 'source'>;

type InvalidationHandler = (msg: InvalidationPush) => void;

interface IpcClient {
  sendToPrimary: <T = unknown>(opts: SendOptions, payload: RequestPayload) => Promise<T>;
  sendToPrimaryWithMeta: <T = unknown>(opts: SendOptions, payload: RequestPayload) => Promise<DispatchResult<T>>;
  subscribeInvalidations: (namespace: string, handler: InvalidationHandler) => () => void;
}

export function createIpcClient(proc: ProcessLike): IpcClient {
  const callbacks = new Map<string, (response: Response) => void>();
  const subscribers = new Map<string, Set<InvalidationHandler>>();

  proc.on('message', (raw: unknown) => {
    if (isOurResponse(raw)) {
      const cb = callbacks.get(raw.id);
      if (!cb) return;
      callbacks.delete(raw.id);
      cb(raw);
      return;
    }
    if (isInvalidationPush(raw)) emitMap(subscribers, raw, messagesDebug);
  });

  function send<T>(opts: SendOptions, payload: RequestPayload): Promise<DispatchResult<T>> {
    const id = String(++workerState.nextRequestId);
    const request = { id, namespace: opts.namespace, source: SOURCE, ...payload } as Request;

    return new Promise((resolve, reject) => {
      const timer = setTimeout(() => {
        callbacks.delete(id);
        if (opts.failsafe === 'reject') reject(new Error('IPC timeout'));
        else resolve({ value: undefined as T, version: 0 });
      }, opts.timeout);

      callbacks.set(id, (response) => {
        clearTimeout(timer);
        if (response.ok) {
          const { value, version = 0, ttls, evictedKeys, l1Value } = response;
          resolve({ value: value as T, version, ttls, evictedKeys, l1Value });
        } else reject(deserializeError(response.error));
      });

      messagesDebug('%O', request);
      const fail = (error: unknown) => {
        if (!callbacks.delete(id)) return;
        clearTimeout(timer);
        reject(error instanceof Error ? error : new Error(String(error)));
      };
      try {
        // A false return means the channel is congested, not that the message
        // was dropped. Keep waiting for its response; only the send callback
        // can report delivery failure. Retrying here could duplicate mutations.
        proc.send(request, (error) => {
          if (error) fail(error);
        });
      } catch (error) {
        fail(error);
      }
    });
  }

  return {
    sendToPrimary: <T>(opts: SendOptions, payload: RequestPayload): Promise<T> =>
      send<T>(opts, payload).then((r) => r.value),
    sendToPrimaryWithMeta: send,
    subscribeInvalidations: (namespace: string, handler: InvalidationHandler): (() => void) =>
      subscribeMap(subscribers, namespace, handler),
  };
}

function isOurResponse(value: unknown): value is Response {
  if (!isOurMessage(value) || typeof value.id !== 'string' || typeof value.ok !== 'boolean') {
    return false;
  }
  // When ok=false, validate the error payload shape too. Without this guard a
  // malformed error from a misbehaving primary would crash the message
  // listener in deserializeError(undefined) and take the worker down.
  if (!value.ok) {
    let error: unknown = value.error;
    // serializeError emits at most eight causes plus the root. Bound the
    // entire chain, including cycles, before recursive reconstruction.
    for (let depth = 0; ; depth++) {
      if (
        depth > 8 ||
        !error ||
        typeof error !== 'object' ||
        typeof (error as { name?: unknown }).name !== 'string' ||
        typeof (error as { message?: unknown }).message !== 'string'
      ) {
        return false;
      }
      error = (error as { cause?: unknown }).cause;
      if (error === undefined) break;
    }
  }
  return true;
}

// Lazy singleton for the actual worker process. Constructing the client
// attaches a `process.on('message')` listener and captures `process.send`,
// neither of which is meaningful in primary mode — so we defer creation
// until a worker-side dispatch actually needs it.
let cachedDefaultClient: IpcClient | undefined;

export function getDefaultClient(): IpcClient {
  if (!cachedDefaultClient) {
    if (typeof process.send !== 'function') {
      throw new Error('not a cluster worker');
    }
    cachedDefaultClient = createIpcClient(process as unknown as ProcessLike);
  }
  return cachedDefaultClient;
}
