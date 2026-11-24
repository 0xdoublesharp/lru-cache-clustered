namespace LruCacheClustered.Fetch

/-- Primary-side single-flight lock (`FetchLock` in `src/primary.ts`). -/
structure FetchLock where
  token : Option Nat
  generation : Nat
  ownerRequestId : Option Nat
  followers : List Nat
  deriving Repr, DecidableEq

/-- Primary namespace slice for a single key's fetch coordination. -/
structure NamespaceState (V : Type) where
  existsNs : Bool
  cached : Option V
  lock : Option FetchLock
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

/-- `dispatchOp(..., 'fetchStore')` (`src/primary.ts`). -/
def fetchStore {V : Type} (s : NamespaceState V) (tok : Nat) (v : V) : Bool × NamespaceState V :=
  match s.lock with
  | some lk =>
    if lk.token == some tok then
      (true, { s with existsNs := true, cached := some v, lock := none })
    else
      (false, s)
  | none => (false, s)

/-- `dispatchOp(..., 'fetchAbort')` (`src/primary.ts`). -/
def fetchAbort {V : Type} (s : NamespaceState V) (tok : Nat) : Bool × NamespaceState V :=
  match s.lock with
  | some lk =>
    if lk.token == some tok then
      let nextLock :=
        if lk.followers.isEmpty then none
        else some { lk with token := none, ownerRequestId := none }
      (true, { s with lock := nextLock })
    else
      (false, s)
  | none => (false, s)

/-- `dispatchOp(..., 'fetchRelease')` with `ownerRequestId` cleanup (`src/primary.ts`). -/
def fetchRelease {V : Type} (s : NamespaceState V) (reqId : Nat) (gen : Option Nat) : Bool × NamespaceState V :=
  match s.lock with
  | none => (false, s)
  | some lk =>
    let genMismatch := match gen with
      | some g => lk.generation != g
      | none => false
    if genMismatch then
      (false, s)
    else
      let wasFollower := lk.followers.contains reqId
      let remFollowers := lk.followers.filter (· != reqId)
      let isOwner := lk.ownerRequestId == some reqId
      let nextToken := if isOwner then none else lk.token
      let nextOwner := if isOwner then none else lk.ownerRequestId
      let removed := wasFollower || isOwner
      let nextLock :=
        if nextToken.isNone && remFollowers.isEmpty then none
        else some { lk with token := nextToken, ownerRequestId := nextOwner, followers := remFollowers }
      (removed, { s with lock := nextLock })

/-- `dispatchOp(..., 'fetchClaim')` (`src/primary.ts`). -/
def fetchClaim {V : Type} (s : NamespaceState V) (reqId : Nat) (gen : Option Nat)
    (forceRefresh : Bool) (leaseActive : Bool) : ClaimOutcome V × NamespaceState V :=
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
            if lk.token.isNone && rem.isEmpty then none
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
            let newLk : FetchLock :=
              { token := some tok, generation := lk.generation, ownerRequestId := some reqId, followers := lk.followers }
            (ClaimOutcome.leader tok, { sNs with lock := some newLk, nextToken := tok })
        | none =>
          let tok := sNs.nextToken + 1
          let newLk : FetchLock :=
            { token := some tok, generation := tok, ownerRequestId := some reqId, followers := [] }
          (ClaimOutcome.leader tok, { sNs with lock := some newLk, nextToken := tok })
    else
      let tok := sNs.nextToken + 1
      let (newGen, newFollowers) := match sNs.lock with
        | some lk => (lk.generation, lk.followers)
        | none => (tok, [])
      let newLk : FetchLock :=
        { token := some tok, generation := newGen, ownerRequestId := some reqId, followers := newFollowers }
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
    (s : NamespaceState V) (lk : FetchLock) (tok : Nat) (v : V)
    (hlk : s.lock = some lk) (hne : lk.token ≠ some tok) :
    fetchStore s tok v = (false, s) := by
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

end LruCacheClustered.Fetch
