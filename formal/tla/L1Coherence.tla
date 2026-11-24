---------------------------- MODULE L1Coherence ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  Workers,   \* Finite set of worker IDs, e.g. {"w1", "w2"}
  Keys,      \* Finite set of cache keys, e.g. {"k1", "k2"}
  Vals,      \* Finite set of non-nullish cache values, e.g. {"v1", "v2"}
  MaxVer,    \* Upper bound on global mutation versions for bounded model checking
  NONE       \* Model value representing absence (undefined)

VARIABLES
  nsExists,    \* BOOLEAN: whether the namespace cache exists on primary
  pCache,      \* [Keys -> Vals \cup {NONE}]: authoritative primary cache
  pKeyVer,     \* [Keys -> 0..MaxVer]: version of last mutation affecting each key
  pVer,        \* 0..MaxVer: primary versions.get(ns) ?? 0 (reset to 0 on destroy)
  nextVer,     \* 0..MaxVer: global primaryState.nextMutationVersion (monotonic)
  l1,          \* [Workers -> [Keys -> [present: BOOLEAN, val: Vals \cup {NONE}, ver: 0..MaxVer]]]
  latestSeen,  \* [Workers -> 0..MaxVer]: per-worker LocalL1Cache.#latestSeen
  pending,     \* [Workers -> [active: BOOLEAN, key: Keys, minVer: 0..MaxVer,
               \*             cancelled: BOOLEAN, respVal: Vals \cup {NONE}, respVer: 0..MaxVer]]
  invQ         \* [Workers -> Seq([kind: {"key", "ns"}, key: Keys \cup {NONE}, ver: 0..MaxVer])]

vars == <<nsExists, pCache, pKeyVer, pVer, nextVer, l1, latestSeen, pending, invQ>>

Max(a, b) == IF a >= b THEN a ELSE b

EmptyEntry == [present |-> FALSE, val |-> NONE, ver |-> 0]
IdlePending(k) == [active |-> FALSE, key |-> k, minVer |-> 0, cancelled |-> FALSE,
                   respVal |-> NONE, respVer |-> 0]

AnyKey == CHOOSE k \in Keys : TRUE

Init ==
  /\ nsExists = TRUE
  /\ pCache = [k \in Keys |-> NONE]
  /\ pKeyVer = [k \in Keys |-> 0]
  /\ pVer = 0
  /\ nextVer = 0
  /\ l1 = [w \in Workers |-> [k \in Keys |-> EmptyEntry]]
  /\ latestSeen = [w \in Workers |-> 0]
  /\ pending = [w \in Workers |-> IdlePending(AnyKey)]
  /\ invQ = [w \in Workers |-> <<>>]

EnqueueAll(msg) ==
  [w \in Workers |-> Append(invQ[w], msg)]

\* Primary-side single-key write (set / incr / decr / setIfAbsent / fetchStore)
PrimarySet(k, v) ==
  /\ nextVer < MaxVer
  /\ LET vNext == nextVer + 1
     IN /\ nsExists' = TRUE
        /\ pCache' = [pCache EXCEPT ![k] = v]
        /\ pKeyVer' = [pKeyVer EXCEPT ![k] = vNext]
        /\ pVer' = vNext
        /\ nextVer' = vNext
        /\ invQ' = EnqueueAll([kind |-> "key", key |-> k, ver |-> vNext])
        /\ UNCHANGED <<l1, latestSeen, pending>>

\* Primary-side single-key delete or capacity eviction
PrimaryDelete(k) ==
  /\ nextVer < MaxVer
  /\ pCache[k] /= NONE
  /\ LET vNext == nextVer + 1
     IN /\ pCache' = [pCache EXCEPT ![k] = NONE]
        /\ pKeyVer' = [pKeyVer EXCEPT ![k] = vNext]
        /\ pVer' = vNext
        /\ nextVer' = vNext
        /\ invQ' = EnqueueAll([kind |-> "key", key |-> k, ver |-> vNext])
        /\ UNCHANGED <<nsExists, l1, latestSeen, pending>>

\* Primary-side namespace-wide clear / mSet / mDelete / load
PrimaryClear ==
  /\ nextVer < MaxVer
  /\ LET vNext == nextVer + 1
     IN /\ nsExists' = TRUE
        /\ pCache' = [k \in Keys |-> NONE]
        /\ pKeyVer' = [k \in Keys |-> vNext]
        /\ pVer' = vNext
        /\ nextVer' = vNext
        /\ invQ' = EnqueueAll([kind |-> "ns", key |-> NONE, ver |-> vNext])
        /\ UNCHANGED <<l1, latestSeen, pending>>

\* Primary-side destroy: deletes namespace cache & resets pVer to 0 while keeping nextVer monotonic
PrimaryDestroy ==
  /\ nsExists
  /\ nextVer < MaxVer
  /\ LET vNext == nextVer + 1
     IN /\ nsExists' = FALSE
        /\ pCache' = [k \in Keys |-> NONE]
        /\ pKeyVer' = [k \in Keys |-> vNext]
        /\ pVer' = 0
        /\ nextVer' = vNext
        /\ invQ' = EnqueueAll([kind |-> "ns", key |-> NONE, ver |-> vNext])
        /\ UNCHANGED <<l1, latestSeen, pending>>

\* Worker starts an L1-tracked read on cache miss; primary snapshot is captured in flight
WorkerStartRead(w, k) ==
  /\ ~pending[w].active
  /\ ~l1[w][k].present
  /\ pending' = [pending EXCEPT ![w] = [
       active |-> TRUE,
       key |-> k,
       minVer |-> latestSeen[w],
       cancelled |-> FALSE,
       respVal |-> pCache[k],
       respVer |-> pVer
     ]]
  /\ UNCHANGED <<nsExists, pCache, pKeyVer, pVer, nextVer, l1, latestSeen, invQ>>

\* Worker receives primary read response and applies LocalL1Cache.set fencing rules:
\*   1. respVal /= NONE (no negative caching)
\*   2. respVer >= latestSeen[w] (namespace floor)
\*   3. ~cancelled /\ respVer >= minVer (in-flight read fence)
\*   4. ~existing.present \/ respVer >= existing.ver (monotonic per-key L1 version)
WorkerFinishRead(w) ==
  /\ pending[w].active
  /\ LET r == pending[w]
         k == r.key
         cur == l1[w][k]
         allow == /\ r.respVal /= NONE
                  /\ r.respVer >= latestSeen[w]
                  /\ ~r.cancelled
                  /\ r.respVer >= r.minVer
                  /\ (~cur.present \/ r.respVer >= cur.ver)
     IN /\ l1' = IF allow
                 THEN [l1 EXCEPT ![w][k] = [present |-> TRUE, val |-> r.respVal, ver |-> r.respVer]]
                 ELSE l1
        /\ pending' = [pending EXCEPT ![w] = IdlePending(k)]
        /\ UNCHANGED <<nsExists, pCache, pKeyVer, pVer, nextVer, latestSeen, invQ>>

\* Worker delivers head of its FIFO IPC invalidation push queue
WorkerDeliverInv(w) ==
  /\ Len(invQ[w]) > 0
  /\ LET msg == Head(invQ[w])
     IN /\ invQ' = [invQ EXCEPT ![w] = Tail(@)]
        /\ IF msg.kind = "key"
           THEN /\ LET k == msg.key
                   IN /\ l1' = IF l1[w][k].present /\ l1[w][k].ver < msg.ver
                               THEN [l1 EXCEPT ![w][k] = EmptyEntry]
                               ELSE l1
                      /\ pending' = IF pending[w].active /\ pending[w].key = k
                                    THEN [pending EXCEPT ![w].minVer = Max(@, msg.ver)]
                                    ELSE pending
                      /\ UNCHANGED latestSeen
           ELSE /\ latestSeen' = [latestSeen EXCEPT ![w] = Max(@, msg.ver)]
                /\ l1' = [l1 EXCEPT ![w] = [k \in Keys |->
                           IF l1[w][k].present /\ l1[w][k].ver < msg.ver
                           THEN EmptyEntry
                           ELSE l1[w][k]]]
                /\ UNCHANGED pending
        /\ UNCHANGED <<nsExists, pCache, pKeyVer, pVer, nextVer>>

\* Worker calls invalidateLocal(k): removes local entry and cancels active read for k
WorkerLocalInvalidate(w, k) ==
  /\ (l1[w][k].present \/ (pending[w].active /\ pending[w].key = k /\ ~pending[w].cancelled))
  /\ l1' = [l1 EXCEPT ![w][k] = EmptyEntry]
  /\ pending' = IF pending[w].active /\ pending[w].key = k
                THEN [pending EXCEPT ![w].cancelled = TRUE]
                ELSE pending
  /\ UNCHANGED <<nsExists, pCache, pKeyVer, pVer, nextVer, latestSeen, invQ>>

\* Worker calls clearLocal(): clears local L1 and cancels any active read
WorkerLocalClear(w) ==
  /\ ((\E k \in Keys : l1[w][k].present) \/ (pending[w].active /\ ~pending[w].cancelled))
  /\ l1' = [l1 EXCEPT ![w] = [k \in Keys |-> EmptyEntry]]
  /\ pending' = IF pending[w].active
                THEN [pending EXCEPT ![w].cancelled = TRUE]
                ELSE pending
  /\ UNCHANGED <<nsExists, pCache, pKeyVer, pVer, nextVer, latestSeen, invQ>>

Next ==
  \/ \E k \in Keys, v \in Vals : PrimarySet(k, v)
  \/ \E k \in Keys : PrimaryDelete(k)
  \/ PrimaryClear
  \/ PrimaryDestroy
  \/ \E w \in Workers, k \in Keys : WorkerStartRead(w, k)
  \/ \E w \in Workers : WorkerFinishRead(w)
  \/ \E w \in Workers : WorkerDeliverInv(w)
  \/ \E w \in Workers, k \in Keys : WorkerLocalInvalidate(w, k)
  \/ \E w \in Workers : WorkerLocalClear(w)

Fairness ==
  /\ \A w \in Workers : WF_vars(WorkerDeliverInv(w))
  /\ \A w \in Workers : WF_vars(WorkerFinishRead(w))

Spec == Init /\ [][Next]_vars /\ Fairness

\* ---- Safety Invariants ----

TypeOK ==
  /\ nsExists \in BOOLEAN
  /\ pCache \in [Keys -> Vals \cup {NONE}]
  /\ pKeyVer \in [Keys -> 0..MaxVer]
  /\ pVer \in 0..MaxVer
  /\ nextVer \in 0..MaxVer
  /\ latestSeen \in [Workers -> 0..MaxVer]
  /\ \A w \in Workers, k \in Keys :
       /\ l1[w][k].present \in BOOLEAN
       /\ l1[w][k].val \in Vals \cup {NONE}
       /\ l1[w][k].ver \in 0..MaxVer
       /\ l1[w][k].present => l1[w][k].val /= NONE

VersionBounds ==
  /\ pVer <= nextVer
  /\ \A k \in Keys : pKeyVer[k] <= nextVer
  /\ \A w \in Workers :
       /\ latestSeen[w] <= nextVer
       /\ \A k \in Keys : l1[w][k].ver <= nextVer

\* Core coherence invariant: once a worker's FIFO invalidation queue has drained,
\* every entry remaining in its L1 must match the authoritative primary state.
NoStaleAfterDrain ==
  \A w \in Workers :
    Len(invQ[w]) = 0 =>
      \A k \in Keys :
        l1[w][k].present =>
          /\ nsExists
          /\ pCache[k] /= NONE
          /\ l1[w][k].val = pCache[k]
          /\ l1[w][k].ver >= pKeyVer[k]

\* Every entry in L1 is at least as recent as the worker's namespace floor.
RespectsNamespaceFloor ==
  \A w \in Workers, k \in Keys :
    l1[w][k].present => l1[w][k].ver >= latestSeen[w]

\* ---- Liveness Property ----

AllDrained ==
  \A w \in Workers : Len(invQ[w]) = 0

\* Under delivery fairness, invalidation queues eventually drain and every
\* worker's L1 converges to the authoritative primary state.
EventualConvergence ==
  []<>(AllDrained /\ NoStaleAfterDrain)

=============================================================================
