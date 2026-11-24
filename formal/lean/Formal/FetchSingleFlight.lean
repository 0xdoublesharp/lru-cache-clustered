namespace LruCacheClustered.Fetch

/-- Primary-side single-flight lock (`FetchLock` in `src/primary.ts`). -/
structure FetchLock (V : Type) where
  token : Option Nat
  generation : Nat
  ownerRequestId : Option Nat
  followers : List Nat
  resolved : List (Nat × V) := []
  deriving Repr, DecidableEq

/-- Primary namespace slice for a single key's fetch coordination. -/
structure NamespaceState (V : Type) where
  existsNs : Bool
  cached : Option V
  lock : Option (FetchLock V)
  nextToken : Nat
  deriving Repr, DecidableEq

inductive ClaimOutcome (V : Type) where
  | value (v : V)
  | leader (tok : Nat)
  | follower (gen : Nat)
  | superseded
  deriving Repr, DecidableEq

/-- Explicit mutation (`set`, `delete`, `clear`, `destroy`, `evict`) supersedes the lock. -/
def supersedeLock {V : Type} (s : NamespaceState V) : NamespaceState V :=
  { s with lock := none }

def applySet {V : Type} (s : NamespaceState V) (v : V) : NamespaceState V :=
  { s with existsNs := true, cached := some v, lock := none }

def applyDelete {V : Type} (s : NamespaceState V) : NamespaceState V :=
  { s with existsNs := true, cached := none, lock := none }

def applyDestroy {V : Type} (s : NamespaceState V) : NamespaceState V :=
  { s with existsNs := false, cached := none, lock := none }

/-- `dispatchOp(..., 'fetchStore')` (`src/primary.ts`). When `admitted = false`
    (oversize entry) and followers are waiting, their owed results are recorded
    per-follower in `lock.resolved` so a subsequent `forceRefresh` cannot discard them. -/
def fetchStore {V : Type} (s : NamespaceState V) (tok : Nat) (v : V) (admitted : Bool := true) :
    Bool × NamespaceState V :=
  match s.lock with
  | some lk =>
    if lk.token == some tok then
      let nextResolved :=
        if !admitted && !lk.followers.isEmpty then
          lk.followers.map (fun r => (r, v)) ++ lk.resolved.filter (fun p => !lk.followers.contains p.1)
        else
          lk.resolved
      let nextLock :=
        if nextResolved.isEmpty then none
        else some { lk with token := none, ownerRequestId := none, followers := [], resolved := nextResolved }
      (true, { s with
        existsNs := true,
        cached := if admitted then some v else none,
        lock := nextLock
      })
    else
      (false, s)
  | none => (false, s)

/-- `dispatchOp(..., 'fetchAbort')` (`src/primary.ts`). -/
def fetchAbort {V : Type} (s : NamespaceState V) (tok : Nat) : Bool × NamespaceState V :=
  match s.lock with
  | some lk =>
    if lk.token == some tok then
      let nextLock :=
        if lk.followers.isEmpty && lk.resolved.isEmpty then none
        else some { lk with token := none, ownerRequestId := none }
      (true, { s with lock := nextLock })
    else
      (false, s)
  | none => (false, s)

/-- `dispatchOp(..., 'fetchRelease')` with `ownerRequestId` and `resolved` cleanup (`src/primary.ts`). -/
def fetchRelease {V : Type} (s : NamespaceState V) (reqId : Nat) (gen : Option Nat) : Bool × NamespaceState V :=
  match s.lock with
  | none => (false, s)
  | some lk =>
    let hadResolved := lk.resolved.any (fun p => p.1 == reqId)
    let remResolved := lk.resolved.filter (fun p => p.1 != reqId)
    let genMatch := match gen with
      | some g => lk.generation == g
      | none => true
    let wasFollower := genMatch && lk.followers.contains reqId
    let remFollowers := if genMatch then lk.followers.filter (· != reqId) else lk.followers
    let isOwner := genMatch && (lk.ownerRequestId == some reqId)
    let nextToken := if isOwner then none else lk.token
    let nextOwner := if isOwner then none else lk.ownerRequestId
    let removed := hadResolved || wasFollower || isOwner
    let nextLock :=
      if nextToken.isNone && remFollowers.isEmpty && remResolved.isEmpty then none
      else some { lk with
        token := nextToken,
        ownerRequestId := nextOwner,
        followers := remFollowers,
        resolved := remResolved
      }
    (removed, { s with lock := nextLock })

/-- `dispatchOp(..., 'fetchClaim')` (`src/primary.ts`). -/
def fetchClaim {V : Type} (s : NamespaceState V) (reqId : Nat) (gen : Option Nat)
    (forceRefresh : Bool) (leaseActive : Bool) : ClaimOutcome V × NamespaceState V :=
  match s.lock.bind (fun lk => (lk.resolved.find? (fun p => p.1 == reqId)).map (fun p => (lk, p.2))) with
  | some (lk, v) =>
    let remResolved := lk.resolved.filter (fun p => p.1 != reqId)
    let nextLock :=
      if lk.token.isNone && lk.followers.isEmpty && remResolved.isEmpty then none
      else some { lk with resolved := remResolved }
    (ClaimOutcome.value v, { s with lock := nextLock })
  | none =>
    let revoked := match gen, s.lock with
      | some _, none => true
      | some g, some lk => lk.generation != g
      | none, _ => false
    if revoked then
      match s.existsNs, s.cached with
      | true, some v => (ClaimOutcome.value v, s)
      | _, _ => (ClaimOutcome.superseded, s)
    else
      let sNs := { s with existsNs := true }
      if !forceRefresh then
        match sNs.cached with
        | some v =>
          let nextLock := match sNs.lock with
            | none => none
            | some lk =>
              let rem := lk.followers.filter (· != reqId)
              if lk.token.isNone && rem.isEmpty && lk.resolved.isEmpty then none
              else some { lk with followers := rem }
          (ClaimOutcome.value v, { sNs with lock := nextLock })
        | none =>
          match sNs.lock with
          | some lk =>
            if lk.token.isSome && leaseActive then
              let nextFollowers := if lk.followers.contains reqId then lk.followers else reqId :: lk.followers
              (ClaimOutcome.follower lk.generation, { sNs with lock := some { lk with followers := nextFollowers } })
            else
              let tok := sNs.nextToken + 1
              let remFollowers := lk.followers.filter (· != reqId)
              let nextGen := if lk.token.isSome || !lk.followers.isEmpty then lk.generation else tok
              let newLk : FetchLock V := {
                token := some tok,
                generation := nextGen,
                ownerRequestId := some reqId,
                followers := remFollowers,
                resolved := lk.resolved
              }
              (ClaimOutcome.leader tok, { sNs with lock := some newLk, nextToken := tok })
          | none =>
            let tok := sNs.nextToken + 1
            let newLk : FetchLock V :=
              { token := some tok, generation := tok, ownerRequestId := some reqId, followers := [] }
            (ClaimOutcome.leader tok, { sNs with lock := some newLk, nextToken := tok })
      else
        let tok := sNs.nextToken + 1
        let (newGen, newFollowers, newResolved) := match sNs.lock with
          | some lk =>
            let nextGen := if lk.token.isSome || !lk.followers.isEmpty then lk.generation else tok
            (nextGen, lk.followers.filter (· != reqId), lk.resolved)
          | none => (tok, [], [])
        let newLk : FetchLock V := {
          token := some tok,
          generation := newGen,
          ownerRequestId := some reqId,
          followers := newFollowers,
          resolved := newResolved
        }
        (ClaimOutcome.leader tok, { sNs with lock := some newLk, nextToken := tok })

/-- A superseded `fetchStore` (after any explicit mutation clears the lock) returns `false`
    and leaves the namespace state completely unchanged. -/
theorem fetchStore_after_set_does_not_overwrite {V : Type}
    (s : NamespaceState V) (explicitVal staleVal : V) (oldTok : Nat) :
    fetchStore (applySet s explicitVal) oldTok staleVal = (false, applySet s explicitVal) := by
  rfl

theorem fetchStore_after_delete_does_not_resurrect {V : Type}
    (s : NamespaceState V) (staleVal : V) (oldTok : Nat) :
    fetchStore (applyDelete s) oldTok staleVal = (false, applyDelete s) := by
  rfl

theorem fetchStore_after_destroy_does_not_recreate {V : Type}
    (s : NamespaceState V) (staleVal : V) (oldTok : Nat) :
    fetchStore (applyDestroy s) oldTok staleVal = (false, applyDestroy s) := by
  rfl

theorem fetchStore_mismatched_token_no_mutation {V : Type}
    (s : NamespaceState V) (lk : FetchLock V) (tok : Nat) (v : V) (admitted : Bool)
    (hlk : s.lock = some lk) (hne : lk.token ≠ some tok) :
    fetchStore s tok v admitted = (false, s) := by
  have hbeq : (lk.token == some tok) = false := beq_false_of_ne hne
  simp [fetchStore, hlk, hbeq]

/-- A polling follower whose generation was revoked by `delete` or `destroy` can never
    take leadership or recreate a destroyed namespace. -/
theorem revoked_follower_after_delete_cannot_lead {V : Type}
    (s : NamespaceState V) (reqId g : Nat) (force leaseActive : Bool) :
    fetchClaim (applyDelete s) reqId (some g) force leaseActive =
      (ClaimOutcome.superseded, applyDelete s) := by
  rfl

theorem revoked_follower_after_destroy_cannot_recreate {V : Type}
    (s : NamespaceState V) (reqId g : Nat) (force leaseActive : Bool) :
    let (outcome, s') := fetchClaim (applyDestroy s) reqId (some g) force leaseActive
    outcome = ClaimOutcome.superseded ∧ s'.existsNs = false ∧ s'.lock = none := by
  simp [fetchClaim, applyDestroy]

/-- A polling follower whose generation was superseded by `set` returns the newer value
    without starting a fetcher. -/
theorem revoked_follower_after_set_returns_newer_value {V : Type}
    (s : NamespaceState V) (v : V) (reqId g : Nat) (force leaseActive : Bool) :
    fetchClaim (applySet s v) reqId (some g) force leaseActive =
      (ClaimOutcome.value v, applySet s v) := by
  rfl

/-- If a cold `fetchClaim` granted leadership to `reqId` and the worker's IPC call timed out,
    its `finally` `fetchRelease(reqId, none)` clears the orphaned leader lock immediately. -/
theorem fetchRelease_clears_timed_out_leader {V : Type}
    (s : NamespaceState V) (reqId : Nat)
    (hMiss : s.cached = none) (hNoLock : s.lock = none) :
    let (_, sClaimed) := fetchClaim s reqId none false true
    let (removed, sReleased) := fetchRelease sClaimed reqId none
    removed = true ∧ sReleased.lock = none := by
  simp [fetchClaim, fetchRelease, hMiss, hNoLock]

/-- When the sole waiting follower is promoted to leader after the previous leader aborted,
    its follower entry is removed immediately so a subsequent `fetchAbort` prunes the lock. -/
theorem promoted_follower_abort_prunes_lock {V : Type}
    (s : NamespaceState V) (reqId gen : Nat)
    (hMiss : s.cached = none)
    (hLock : s.lock = some { token := none, generation := gen, ownerRequestId := none, followers := [reqId] }) :
    let (outcome, sPromoted) := fetchClaim s reqId (some gen) false true
    match outcome with
    | ClaimOutcome.leader tok =>
      let (aborted, sAborted) := fetchAbort sPromoted tok
      aborted = true ∧ sAborted.lock = none
    | _ => False := by
  simp [fetchClaim, fetchAbort, hMiss, hLock]

/-- When an oversize `fetchStore` (`admitted = false`) finishes with a waiting follower,
    that follower receives the computed value on its next poll and the lock prunes cleanly. -/
theorem oversize_fetchStore_delivers_to_follower_and_prunes {V : Type}
    (s : NamespaceState V) (tok gen leaderReq followerReq : Nat) (v : V)
    (hLock : s.lock = some {
      token := some tok, generation := gen, ownerRequestId := some leaderReq, followers := [followerReq]
    }) :
    let (ok, sStored) := fetchStore s tok v false
    let (outcome, sFinal) := fetchClaim sStored followerReq (some gen) false true
    ok = true ∧ outcome = ClaimOutcome.value v ∧ sFinal.cached = none ∧ sFinal.lock = none := by
  simp [fetchStore, fetchClaim, hLock]

/-- Even if a `forceRefresh` claim starts and stores a different value before the registered
    follower polls, the follower still receives its owed oversize result and prunes the lock. -/
theorem oversize_fetchStore_survives_forceRefresh_for_registered_follower {V : Type}
    (s : NamespaceState V) (tok gen leaderReq followerReq refreshReq : Nat) (vBig vRefresh : V)
    (hNe : refreshReq ≠ followerReq)
    (hLock : s.lock = some {
      token := some tok, generation := gen, ownerRequestId := some leaderReq, followers := [followerReq]
    }) :
    let (_, sOversize) := fetchStore s tok vBig false
    let (refreshOutcome, sClaimed) := fetchClaim sOversize refreshReq none true true
    match refreshOutcome with
    | ClaimOutcome.leader refreshTok =>
      let (_, sRefreshed) := fetchStore sClaimed refreshTok vRefresh true
      let (followerOutcome, sFinal) := fetchClaim sRefreshed followerReq (some gen) false true
      followerOutcome = ClaimOutcome.value vBig ∧ sFinal.cached = some vRefresh ∧ sFinal.lock = none
    | _ => False := by
  have hbeq : (followerReq == refreshReq) = false := beq_false_of_ne (Ne.symm hNe)
  simp [fetchStore, fetchClaim, hLock, hbeq]

end LruCacheClustered.Fetch
