namespace LruCacheClustered.Ttl

def defaultL1TtlMs : Nat := 5000
def defaultL1FloorMs : Nat := 100

/-- Exact integer model of `normalizeL1`'s TTL calculation (`src/index.ts`),
    where `primaryTtl = 0` represents no primary expiration (`undefined` or `0`). -/
def normalizeL1Ttl (primaryTtl : Nat) (optsTtl : Option Nat) : Nat :=
  match primaryTtl with
  | 0 =>
    match optsTtl with
    | some t => max 1 t
    | none => defaultL1TtlMs
  | p + 1 =>
    let pPos := p + 1
    let requested := match optsTtl with
      | some t => t
      | none => max defaultL1FloorMs (min (pPos / 10) defaultL1TtlMs)
    max 1 (min requested pPos)

/-- Per-entry effective L1 TTL (`LocalL1Cache.#setOptions` in `src/l1.ts`).
    Returns `none` when the entry is already expired (`remaining = 0`). -/
def effectiveEntryTtl (l1Ttl : Nat) (remaining : Nat) : Option Nat :=
  if min remaining l1Ttl > 0 then some (min remaining l1Ttl) else none

theorem normalizeL1Ttl_positive (primaryTtl : Nat) (optsTtl : Option Nat) :
    1 ≤ normalizeL1Ttl primaryTtl optsTtl := by
  cases primaryTtl with
  | zero =>
    cases optsTtl with
    | none => decide
    | some t => simp only [normalizeL1Ttl]; omega
  | succ p =>
    simp only [normalizeL1Ttl]
    omega

/-- For every positive `primaryTtl`, the normalized L1 TTL never exceeds `primaryTtl`. -/
theorem normalizeL1Ttl_le_primary (primaryTtl : Nat) (optsTtl : Option Nat)
    (hp : 0 < primaryTtl) :
    normalizeL1Ttl primaryTtl optsTtl ≤ primaryTtl := by
  cases primaryTtl with
  | zero => omega
  | succ p =>
    simp only [normalizeL1Ttl]
    omega

/-- Explicit `localL1.ttl` within `[1, primaryTtl]` is honored verbatim (never inflated to 100ms). -/
theorem normalizeL1Ttl_honors_explicit (primaryTtl t : Nat)
    (ht : 1 ≤ t) (hle : primaryTtl = 0 ∨ t ≤ primaryTtl) :
    normalizeL1Ttl primaryTtl (some t) = t := by
  cases primaryTtl with
  | zero =>
    simp only [normalizeL1Ttl]
    omega
  | succ p =>
    simp only [normalizeL1Ttl]
    rcases hle with h0 | hle'
    · omega
    · omega

/-- Default L1 TTL never exceeds 5000ms. -/
theorem normalizeL1Ttl_default_le_5000 (primaryTtl : Nat) :
    normalizeL1Ttl primaryTtl none ≤ defaultL1TtlMs := by
  cases primaryTtl with
  | zero => decide
  | succ p =>
    simp only [normalizeL1Ttl, defaultL1TtlMs, defaultL1FloorMs]
    omega

/-- Per-entry L1 TTL never exceeds either the primary's remaining TTL or the configured L1 TTL. -/
theorem effectiveEntryTtl_bounded (l1Ttl remaining eff : Nat)
    (h : effectiveEntryTtl l1Ttl remaining = some eff) :
    eff ≤ remaining ∧ eff ≤ l1Ttl ∧ 0 < eff := by
  unfold effectiveEntryTtl at h
  by_cases hpos : min remaining l1Ttl > 0
  · simp only [hpos, ↓reduceIte, Option.some.injEq] at h
    omega
  · simp [hpos] at h

/-- An expired primary entry (`remaining = 0`) is never cached in L1. -/
theorem effectiveEntryTtl_rejects_expired (l1Ttl : Nat) :
    effectiveEntryTtl l1Ttl 0 = none := by
  simp [effectiveEntryTtl]

end LruCacheClustered.Ttl
