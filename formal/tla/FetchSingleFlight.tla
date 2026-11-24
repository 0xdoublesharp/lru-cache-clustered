-------------------------- MODULE FetchSingleFlight --------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
  Callers,    \* Finite set of caller/request IDs, e.g. {"c1", "c2"}
  Vals,       \* Finite set of non-nullish values, e.g. {"v1", "v2"}
  MaxTokens,  \* Upper bound on allocated fetch tokens for bounded checking
  NONE        \* Model value representing absence (undefined)

VARIABLES
  nsExists,        \* BOOLEAN: whether the namespace cache exists on primary
  cacheVal,        \* Vals \cup {NONE}: authoritative cached value for the key
  lockPresent,     \* BOOLEAN: whether fetchLocks has an entry for this key
  lockHasToken,    \* BOOLEAN: whether lock.token is active (FALSE after abort/disconnect/release)
  lockToken,       \* 0..MaxTokens: current leader token
  lockGen,         \* 0..MaxTokens: current fetch group generation
  lockOwner,       \* Callers \cup {NONE}: ownerRequestId of active leader
  lockFollowers,   \* SUBSET Callers: registered follower request IDs
  lockExpired,     \* BOOLEAN: whether 30s fetch lease has expired
  nextTok,         \* 0..MaxTokens: monotonic primaryState.nextFetchToken
  cState,          \* [Callers -> {"idle", "claimPending", "leader", "follower",
                   \*              "doneVal", "doneSuperseded", "doneFailed"}]
  cTok,            \* [Callers -> 0..MaxTokens]: leader token held by caller
  cGen,            \* [Callers -> 0..MaxTokens]: follower generation held by caller (0 = none)
  cForce,          \* [Callers -> BOOLEAN]: forceRefresh flag
  cVal             \* [Callers -> Vals \cup {NONE}]: resolved value (when doneVal)

vars == <<nsExists, cacheVal, lockPresent, lockHasToken, lockToken, lockGen,
          lockOwner, lockFollowers, lockExpired, nextTok,
          cState, cTok, cGen, cForce, cVal>>

ClearLock ==
  /\ lockPresent' = FALSE
  /\ lockHasToken' = FALSE
  /\ lockToken' = 0
  /\ lockGen' = 0
  /\ lockOwner' = NONE
  /\ lockFollowers' = {}
  /\ lockExpired' = FALSE

Init ==
  /\ nsExists = TRUE
  /\ cacheVal = NONE
  /\ lockPresent = FALSE
  /\ lockHasToken = FALSE
  /\ lockToken = 0
  /\ lockGen = 0
  /\ lockOwner = NONE
  /\ lockFollowers = {}
  /\ lockExpired = FALSE
  /\ nextTok = 0
  /\ cState = [c \in Callers |-> "idle"]
  /\ cTok = [c \in Callers |-> 0]
  /\ cGen = [c \in Callers |-> 0]
  /\ cForce = [c \in Callers |-> FALSE]
  /\ cVal = [c \in Callers |-> NONE]

\* Caller initiates fetch(key, fetcher, { forceRefresh })
StartFetch(c, force) ==
  /\ cState[c] = "idle"
  /\ cState' = [cState EXCEPT ![c] = "claimPending"]
  /\ cForce' = [cForce EXCEPT ![c] = force]
  /\ UNCHANGED <<nsExists, cacheVal, lockPresent, lockHasToken, lockToken, lockGen,
                 lockOwner, lockFollowers, lockExpired, nextTok, cTok, cGen, cVal>>

\* Primary executes dispatchOp(..., 'fetchClaim') for an initial or polling caller
ProcessClaim(c) ==
  /\ cState[c] \in {"claimPending", "follower"}
  /\ IF cGen[c] /= 0 /\ (~lockPresent \/ lockGen /= cGen[c])
     THEN \* Revoked generation: never grant leadership or recreate namespace
       /\ IF nsExists /\ cacheVal /= NONE
          THEN /\ cState' = [cState EXCEPT ![c] = "doneVal"]
               /\ cVal' = [cVal EXCEPT ![c] = cacheVal]
          ELSE /\ cState' = [cState EXCEPT ![c] = "doneSuperseded"]
               /\ UNCHANGED cVal
       /\ cGen' = [cGen EXCEPT ![c] = 0]
       /\ UNCHANGED <<nsExists, cacheVal, lockPresent, lockHasToken, lockToken, lockGen,
                      lockOwner, lockFollowers, lockExpired, nextTok, cTok, cForce>>
     ELSE \* Initial claim or matching active generation
       /\ IF ~cForce[c] /\ cacheVal /= NONE
          THEN \* Cache hit: unregister follower and clean up idle lock
            LET remFollowers == lockFollowers \ {c}
                removeLock == lockPresent /\ ~lockHasToken /\ remFollowers = {}
            IN /\ nsExists' = TRUE
               /\ IF removeLock
                  THEN ClearLock
                  ELSE /\ lockFollowers' = remFollowers
                       /\ UNCHANGED <<lockPresent, lockHasToken, lockToken, lockGen, lockOwner, lockExpired>>
               /\ cState' = [cState EXCEPT ![c] = "doneVal"]
               /\ cVal' = [cVal EXCEPT ![c] = cacheVal]
               /\ cGen' = [cGen EXCEPT ![c] = 0]
               /\ UNCHANGED <<cacheVal, nextTok, cTok, cForce>>
          ELSE IF ~cForce[c] /\ lockPresent /\ lockHasToken /\ ~lockExpired
          THEN \* Active unexpired leader exists: register as follower
            /\ nsExists' = TRUE
            /\ lockFollowers' = lockFollowers \cup {c}
            /\ cState' = [cState EXCEPT ![c] = "follower"]
            /\ cGen' = [cGen EXCEPT ![c] = lockGen]
            /\ cForce' = [cForce EXCEPT ![c] = FALSE]
            /\ UNCHANGED <<cacheVal, lockPresent, lockHasToken, lockToken, lockGen,
                           lockOwner, lockExpired, nextTok, cTok, cVal>>
          ELSE \* Grant leadership (fresh miss, forceRefresh, aborted leader, or expired lease)
            /\ nextTok < MaxTokens
            /\ LET tok == nextTok + 1
                   gen == IF lockPresent THEN lockGen ELSE tok
               IN /\ nsExists' = TRUE
                  /\ nextTok' = tok
                  /\ lockPresent' = TRUE
                  /\ lockHasToken' = TRUE
                  /\ lockToken' = tok
                  /\ lockGen' = gen
                  /\ lockOwner' = c
                  /\ lockFollowers' = lockFollowers \ {c}
                  /\ lockExpired' = FALSE
                  /\ cState' = [cState EXCEPT ![c] = "leader"]
                  /\ cTok' = [cTok EXCEPT ![c] = tok]
                  /\ cForce' = [cForce EXCEPT ![c] = FALSE]
                  /\ UNCHANGED <<cacheVal, cGen, cVal>>

\* Leader completes fetcher and executes fetchStore (plus existingOnly fallback on supersede)
LeaderStore(c, v) ==
  /\ cState[c] = "leader"
  /\ IF lockPresent /\ lockHasToken /\ lockToken = cTok[c]
     THEN \* Token matches: store value and delete entire fetch group
       /\ nsExists' = TRUE
       /\ cacheVal' = v
       /\ ClearLock
       /\ cState' = [cState EXCEPT ![c] = "doneVal"]
       /\ cVal' = [cVal EXCEPT ![c] = v]
       /\ cTok' = [cTok EXCEPT ![c] = 0]
       /\ cGen' = [cGen EXCEPT ![c] = 0]
       /\ UNCHANGED <<nextTok, cForce>>
     ELSE \* Superseded: never overwrite cache or recreate destroyed namespace;
          \* finally block still runs fetchRelease(key, gen, c) if cGen[c] /= 0.
       /\ LET remFollowers == IF lockPresent /\ cGen[c] /= 0 /\ lockGen = cGen[c]
                              THEN lockFollowers \ {c}
                              ELSE lockFollowers
              removeLock == lockPresent /\ ~lockHasToken /\ remFollowers = {}
          IN /\ IF removeLock
                THEN ClearLock
                ELSE /\ lockFollowers' = remFollowers
                     /\ UNCHANGED <<lockPresent, lockHasToken, lockToken, lockGen, lockOwner, lockExpired>>
       /\ IF nsExists /\ cacheVal /= NONE
          THEN /\ cState' = [cState EXCEPT ![c] = "doneVal"]
               /\ cVal' = [cVal EXCEPT ![c] = cacheVal]
          ELSE /\ cState' = [cState EXCEPT ![c] = "doneSuperseded"]
               /\ UNCHANGED cVal
       /\ cTok' = [cTok EXCEPT ![c] = 0]
       /\ cGen' = [cGen EXCEPT ![c] = 0]
       /\ UNCHANGED <<nsExists, cacheVal, nextTok, cForce>>

\* Leader's fetcher throws -> fetchAbort + finally fetchRelease (if promoted from follower)
LeaderAbort(c) ==
  /\ cState[c] = "leader"
  /\ LET matchTok == lockPresent /\ lockHasToken /\ lockToken = cTok[c]
         newHasTok == IF matchTok THEN FALSE ELSE lockHasToken
         newOwner == IF matchTok THEN NONE ELSE lockOwner
         remFollowers == IF lockPresent /\ cGen[c] /= 0 /\ lockGen = cGen[c]
                         THEN lockFollowers \ {c}
                         ELSE lockFollowers
         removeLock == lockPresent /\ ~newHasTok /\ remFollowers = {}
     IN /\ IF removeLock
           THEN ClearLock
           ELSE /\ lockHasToken' = newHasTok
                /\ lockOwner' = newOwner
                /\ lockFollowers' = remFollowers
                /\ UNCHANGED <<lockPresent, lockToken, lockGen, lockExpired>>
        /\ cState' = [cState EXCEPT ![c] = "doneFailed"]
        /\ cTok' = [cTok EXCEPT ![c] = 0]
        /\ cGen' = [cGen EXCEPT ![c] = 0]
        /\ UNCHANGED <<nsExists, cacheVal, nextTok, cForce, cVal>>

\* IPC timeout on fetchClaim (after primary granted leadership or follower) -> fetchRelease(reqId)
\* Directly models the ownerRequestId release fix so timed-out leaders never orphan locks for 30s.
TimeoutAndRelease(c) ==
  /\ cState[c] \in {"leader", "follower"}
  /\ LET genMatch == lockPresent /\ (cGen[c] = 0 \/ lockGen = cGen[c])
         isOwner == genMatch /\ lockOwner = c
         newHasTok == IF isOwner THEN FALSE ELSE lockHasToken
         newOwner == IF isOwner THEN NONE ELSE lockOwner
         remFollowers == IF genMatch THEN lockFollowers \ {c} ELSE lockFollowers
         removeLock == lockPresent /\ ~newHasTok /\ remFollowers = {}
     IN /\ IF removeLock
           THEN ClearLock
           ELSE /\ lockHasToken' = newHasTok
                /\ lockOwner' = newOwner
                /\ lockFollowers' = remFollowers
                /\ UNCHANGED <<lockPresent, lockToken, lockGen, lockExpired>>
        /\ cState' = [cState EXCEPT ![c] = "doneFailed"]
        /\ cTok' = [cTok EXCEPT ![c] = 0]
        /\ cGen' = [cGen EXCEPT ![c] = 0]
        /\ UNCHANGED <<nsExists, cacheVal, nextTok, cForce, cVal>>

\* Worker disconnect / exit -> releaseFetchLocksForWorker
WorkerExit(c) ==
  /\ cState[c] \in {"claimPending", "leader", "follower"}
  /\ LET isOwner == lockPresent /\ lockOwner = c
         newHasTok == IF isOwner THEN FALSE ELSE lockHasToken
         newOwner == IF isOwner THEN NONE ELSE lockOwner
         remFollowers == IF lockPresent THEN lockFollowers \ {c} ELSE {}
         removeLock == lockPresent /\ ~newHasTok /\ remFollowers = {}
     IN /\ IF removeLock
           THEN ClearLock
           ELSE /\ lockHasToken' = newHasTok
                /\ lockOwner' = newOwner
                /\ lockFollowers' = remFollowers
                /\ UNCHANGED <<lockPresent, lockToken, lockGen, lockExpired>>
        /\ cState' = [cState EXCEPT ![c] = "doneFailed"]
        /\ cTok' = [cTok EXCEPT ![c] = 0]
        /\ cGen' = [cGen EXCEPT ![c] = 0]
        /\ UNCHANGED <<nsExists, cacheVal, nextTok, cForce, cVal>>

\* 30-second fetch claim lease expires
LeaseExpire ==
  /\ lockPresent
  /\ lockHasToken
  /\ ~lockExpired
  /\ lockExpired' = TRUE
  /\ UNCHANGED <<nsExists, cacheVal, lockPresent, lockHasToken, lockToken, lockGen,
                 lockOwner, lockFollowers, nextTok, cState, cTok, cGen, cForce, cVal>>

\* Explicit mutations supersede the active fetch lock
ExplicitSet(v) ==
  /\ nsExists' = TRUE
  /\ cacheVal' = v
  /\ ClearLock
  /\ UNCHANGED <<nextTok, cState, cTok, cGen, cForce, cVal>>

ExplicitDelete ==
  /\ nsExists' = TRUE
  /\ cacheVal' = NONE
  /\ ClearLock
  /\ UNCHANGED <<nextTok, cState, cTok, cGen, cForce, cVal>>

ExplicitDestroy ==
  /\ nsExists
  /\ nsExists' = FALSE
  /\ cacheVal' = NONE
  /\ ClearLock
  /\ UNCHANGED <<nextTok, cState, cTok, cGen, cForce, cVal>>

Next ==
  \/ \E c \in Callers, f \in BOOLEAN : StartFetch(c, f)
  \/ \E c \in Callers : ProcessClaim(c)
  \/ \E c \in Callers, v \in Vals : LeaderStore(c, v)
  \/ \E c \in Callers : LeaderAbort(c)
  \/ \E c \in Callers : TimeoutAndRelease(c)
  \/ \E c \in Callers : WorkerExit(c)
  \/ LeaseExpire
  \/ \E v \in Vals : ExplicitSet(v)
  \/ ExplicitDelete
  \/ ExplicitDestroy

Spec == Init /\ [][Next]_vars

\* ---- Safety Invariants ----

TypeOK ==
  /\ nsExists \in BOOLEAN
  /\ cacheVal \in Vals \cup {NONE}
  /\ lockPresent \in BOOLEAN
  /\ lockHasToken \in BOOLEAN
  /\ lockToken \in 0..MaxTokens
  /\ lockGen \in 0..MaxTokens
  /\ lockOwner \in Callers \cup {NONE}
  /\ lockFollowers \subseteq Callers
  /\ lockExpired \in BOOLEAN
  /\ nextTok \in 0..MaxTokens
  /\ cState \in [Callers -> {"idle", "claimPending", "leader", "follower",
                             "doneVal", "doneSuperseded", "doneFailed"}]
  /\ cTok \in [Callers -> 0..MaxTokens]
  /\ cGen \in [Callers -> 0..MaxTokens]
  /\ cForce \in [Callers -> BOOLEAN]
  /\ cVal \in [Callers -> Vals \cup {NONE}]

IsLiveLeader(c) ==
  /\ cState[c] = "leader"
  /\ lockPresent
  /\ lockHasToken
  /\ lockToken = cTok[c]

\* At most one caller holds the active matching leader token at any time.
AtMostOneLiveLeader ==
  \A c1, c2 \in Callers : (IsLiveLeader(c1) /\ IsLiveLeader(c2)) => c1 = c2

\* A live lock always references an active leader holding that exact token.
LockOwnerConsistent ==
  (lockPresent /\ lockHasToken) =>
    /\ lockOwner \in Callers
    /\ cState[lockOwner] = "leader"
    /\ cTok[lockOwner] = lockToken

\* A destroyed namespace never has a cached value or an active fetch lock.
DestroyedNamespaceClean ==
  ~nsExists => (cacheVal = NONE /\ ~lockPresent)

\* When every caller has settled (idle / done*), no orphaned fetch lock remains.
NoOrphanedLockWhenSettled ==
  (\A c \in Callers : cState[c] \in {"idle", "doneVal", "doneSuperseded", "doneFailed"})
    => ~lockPresent

\* A non-empty lock always has either a live token or at least one registered follower.
NoEmptyLock ==
  lockPresent => (lockHasToken \/ lockFollowers /= {})

\* An active leader is never simultaneously registered in its own follower set.
LeaderNotInFollowers ==
  (lockPresent /\ lockHasToken) => lockOwner \notin lockFollowers

=============================================================================
