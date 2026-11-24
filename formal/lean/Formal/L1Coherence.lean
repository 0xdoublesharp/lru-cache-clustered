namespace LruCacheClustered.L1

/-- Minimal model of an entry stored in `LocalL1Cache` (`src/l1.ts`). -/
structure L1Entry (V : Type) where
  value : V
  version : Nat
  deriving Repr, DecidableEq

/-- In-flight read fence (`L1Read` in `src/l1.ts`). -/
structure L1Read where
  version : Nat
  cancelled : Bool
  deriving Repr, DecidableEq

/-- Single-key slice of `LocalL1Cache` state. -/
structure L1State (V : Type) where
  entry : Option (L1Entry V)
  latestSeen : Nat
  deriving Repr, DecidableEq

/-- Exact fencing predicate from `LocalL1Cache.set` (`src/l1.ts`). -/
def allowSet {V : Type} (s : L1State V) (version : Nat) (read : Option L1Read) : Bool :=
  if version < s.latestSeen then false
  else
    let existingOk := match s.entry with
      | none => true
      | some e => !(version < e.version)
    let readOk := match read with
      | none => true
      | some r => !r.cancelled && !(version < r.version)
    existingOk && readOk

/-- Functional transition for `LocalL1Cache.set`. -/
def l1Set {V : Type} (s : L1State V) (value : V) (version : Nat) (read : Option L1Read) : L1State V :=
  if allowSet s version read then
    { s with entry := some { value, version } }
  else
    s

/-- Functional transition for versioned key invalidation (`LocalL1Cache.delete` with `version`). -/
def l1DeleteVersioned {V : Type} (s : L1State V) (invVer : Nat) : L1State V :=
  match s.entry with
  | some e => if e.version < invVer then { s with entry := none } else s
  | none => s

/-- Update a tracked in-flight read fence upon versioned key invalidation. -/
def fenceReadVersioned (r : L1Read) (invVer : Nat) : L1Read :=
  { r with version := max r.version invVer }

/-- Cancel a tracked in-flight read upon local invalidation (`invalidateLocal` / `clearLocal`). -/
def cancelRead (r : L1Read) : L1Read :=
  { r with cancelled := true }

/-- Functional transition for versioned namespace invalidation (`LocalL1Cache.clear` with `version`). -/
def l1ClearVersioned {V : Type} (s : L1State V) (invVer : Nat) : L1State V :=
  let nextSeen := max s.latestSeen invVer
  let nextEntry := match s.entry with
    | some e => if e.version < invVer then none else some e
    | none => none
  { entry := nextEntry, latestSeen := nextSeen }

/-- Primary global version counter (`primaryState.nextMutationVersion` + `versions.get(ns)`). -/
structure PrimaryVersions where
  nextMutationVersion : Nat
  nsVersion : Nat
  deriving Repr, DecidableEq

def bumpVersion (p : PrimaryVersions) : PrimaryVersions :=
  let next := p.nextMutationVersion + 1
  { nextMutationVersion := next, nsVersion := next }

/-- `destroy` bumps the global counter, broadcasts `next`, then deletes the namespace record (`nsVersion := 0`). -/
def destroyNamespace (p : PrimaryVersions) : PrimaryVersions × Nat :=
  let next := p.nextMutationVersion + 1
  ({ nextMutationVersion := next, nsVersion := 0 }, next)

theorem l1Set_rejects_older_than_latestSeen {V : Type}
    (s : L1State V) (v : V) (ver : Nat) (r : Option L1Read)
    (h : ver < s.latestSeen) :
    l1Set s v ver r = s := by
  simp [l1Set, allowSet, h]

theorem l1Set_rejects_older_than_existing {V : Type}
    (s : L1State V) (e : L1Entry V) (v : V) (ver : Nat) (r : Option L1Read)
    (he : s.entry = some e) (h : ver < e.version) :
    l1Set s v ver r = s := by
  unfold l1Set allowSet
  by_cases hls : ver < s.latestSeen
  · simp [hls]
  · simp [hls, he, h]

theorem l1Set_rejects_cancelled_read {V : Type}
    (s : L1State V) (v : V) (ver : Nat) (r : L1Read)
    (hc : r.cancelled = true) :
    l1Set s v ver (some r) = s := by
  unfold l1Set allowSet
  by_cases hls : ver < s.latestSeen
  · simp [hls]
  · simp [hls, hc]

theorem l1Set_rejects_older_than_read_fence {V : Type}
    (s : L1State V) (v : V) (ver : Nat) (r : L1Read)
    (hf : ver < r.version) :
    l1Set s v ver (some r) = s := by
  unfold l1Set allowSet
  by_cases hls : ver < s.latestSeen
  · simp [hls]
  · simp [hls, hf]

/-- After a versioned key invalidation at `invVer`, any in-flight read from `snapVer < invVer`
    is fenced and cannot repopulate L1. -/
theorem fenced_read_cannot_repopulate_after_key_invalidation {V : Type}
    (s : L1State V) (v : V) (snapVer invVer : Nat) (r : L1Read)
    (h : snapVer < invVer) :
    l1Set (l1DeleteVersioned s invVer) v snapVer (some (fenceReadVersioned r invVer)) =
      l1DeleteVersioned s invVer := by
  apply l1Set_rejects_older_than_read_fence
  simp only [fenceReadVersioned]
  omega

/-- After a local invalidation cancels an in-flight read, the read can never repopulate L1. -/
theorem cancelled_read_cannot_repopulate {V : Type}
    (s : L1State V) (v : V) (ver : Nat) (r : L1Read) :
    l1Set s v ver (some (cancelRead r)) = s := by
  apply l1Set_rejects_cancelled_read
  rfl

/-- `l1Set` never downgrades the version of a cached entry. -/
theorem l1Set_monotonic_version {V : Type}
    (s : L1State V) (e e' : L1Entry V) (v : V) (ver : Nat) (r : Option L1Read)
    (he : s.entry = some e) (he' : (l1Set s v ver r).entry = some e') :
    e.version ≤ e'.version := by
  unfold l1Set at he'
  by_cases hall : allowSet s ver r = true
  · simp only [hall, ↓reduceIte, Option.some.injEq] at he'
    rw [← he']
    unfold allowSet at hall
    by_cases hls : ver < s.latestSeen
    · simp [hls] at hall
    · simp only [hls, ↓reduceIte, he, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hall
      dsimp only
      omega
  · simp only [hall, Bool.false_eq_true, ↓reduceIte, he, Option.some.injEq] at he'
    rw [← he']
    exact Nat.le_refl _

/-- Any surviving entry after `l1DeleteVersioned s invVer` has `version ≥ invVer`. -/
theorem l1DeleteVersioned_removes_older {V : Type}
    (s : L1State V) (invVer : Nat) (e : L1Entry V)
    (he : (l1DeleteVersioned s invVer).entry = some e) :
    invVer ≤ e.version := by
  unfold l1DeleteVersioned at he
  cases hcur : s.entry with
  | none => simp [hcur] at he
  | some cur =>
    simp only [hcur] at he
    by_cases hlt : cur.version < invVer
    · simp [hlt] at he
    · simp only [hlt, ↓reduceIte, hcur, Option.some.injEq] at he
      rw [← he]
      omega

/-- Any surviving entry after `l1ClearVersioned s invVer` has `version ≥ invVer`
    and `latestSeen ≥ invVer`. -/
theorem l1ClearVersioned_enforces_floor {V : Type}
    (s : L1State V) (invVer : Nat) :
    invVer ≤ (l1ClearVersioned s invVer).latestSeen ∧
    ∀ e, (l1ClearVersioned s invVer).entry = some e → invVer ≤ e.version := by
  constructor
  · simp only [l1ClearVersioned]
    omega
  · intro e he
    simp only [l1ClearVersioned] at he
    cases hcur : s.entry with
    | none => simp [hcur] at he
    | some cur =>
      simp only [hcur] at he
      by_cases hlt : cur.version < invVer
      · simp [hlt] at he
      · simp only [hlt, ↓reduceIte, Option.some.injEq] at he
        rw [← he]
        omega

/-- Destroy followed by recreation strictly exceeds both the pre-destroy version
    and the destroy broadcast version, preventing generation-reuse ABA bugs. -/
theorem destroy_then_recreate_strictly_increases_version (p : PrimaryVersions)
    (hInv : p.nsVersion ≤ p.nextMutationVersion) :
    let (pDestroyed, destroyVer) := destroyNamespace p
    let pRecreated := bumpVersion pDestroyed
    p.nsVersion < destroyVer ∧ destroyVer < pRecreated.nsVersion := by
  simp only [destroyNamespace, bumpVersion]
  omega

end LruCacheClustered.L1
