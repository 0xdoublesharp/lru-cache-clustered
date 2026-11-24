namespace LruCacheClustered.KeyEncoding

/-- Key domain tags mirroring `encodeL1Key` in `src/l1.ts`:
    `s:` (string), `n:` (number), `b:` (boolean), `i:` (bigint), `f:` (function), `o:` (object). -/
inductive KeyTag where
  | str
  | num
  | bool
  | bigint
  | fn
  | obj
  deriving Repr, DecidableEq

/-- Single-character tag prefix for each key domain (`src/l1.ts:63-80`). -/
def tagChar : KeyTag → Char
  | .str => 's'
  | .num => 'n'
  | .bool => 'b'
  | .bigint => 'i'
  | .fn => 'f'
  | .obj => 'o'

/-- Tagged key representation carrying its domain tag and canonical string payload. -/
structure TaggedKey where
  tag : KeyTag
  payload : String
  deriving Repr, DecidableEq

/-- Exact prefix encoding from `encodeL1Key` (`src/l1.ts`). -/
def encodeTaggedKey (k : TaggedKey) : String :=
  String.ofList [tagChar k.tag, ':'] ++ k.payload

theorem tagChar_injective {t1 t2 : KeyTag} (h : tagChar t1 = tagChar t2) : t1 = t2 := by
  cases t1 <;> cases t2 <;> simp [tagChar] at h <;> rfl

/-- `encodeL1Key` is strictly injective on `(tag, payload)`:
    distinct key types (e.g., string `"1"` vs number `1` vs boolean `true` vs bigint `1n`
    vs function/object WeakMap IDs) can never collide, even when their string payloads match
    or contain `':'`. -/
theorem encodeTaggedKey_injective {k1 k2 : TaggedKey}
    (h : encodeTaggedKey k1 = encodeTaggedKey k2) : k1 = k2 := by
  have hlist : (encodeTaggedKey k1).toList = (encodeTaggedKey k2).toList := congrArg String.toList h
  simp only [encodeTaggedKey, String.toList_append, String.toList_ofList, List.cons_append, List.nil_append] at hlist
  injection hlist with hchar hrest
  injection hrest with _ hpay
  have htag : k1.tag = k2.tag := tagChar_injective hchar
  have hp : k1.payload = k2.payload := String.ext hpay
  cases k1; cases k2
  simp only at htag hp
  subst htag; subst hp
  rfl

/-- Concrete corollary: string `"1"` and number `1` never collide. -/
theorem string_one_ne_number_one :
    encodeTaggedKey ⟨.str, "1"⟩ ≠ encodeTaggedKey ⟨.num, "1"⟩ := by
  intro h
  have := encodeTaggedKey_injective h
  cases this

/-- Concrete corollary: string `"n:1"` (containing a tag-like prefix) and number `1` never collide. -/
theorem embedded_prefix_never_collides :
    encodeTaggedKey ⟨.str, "n:1"⟩ ≠ encodeTaggedKey ⟨.num, "1"⟩ := by
  intro h
  have := encodeTaggedKey_injective h
  cases this

/-- Concrete corollary: distinct function and object domains never collide even for the same ID. -/
theorem fn_and_obj_domains_disjoint (id : String) :
    encodeTaggedKey ⟨.fn, id⟩ ≠ encodeTaggedKey ⟨.obj, id⟩ := by
  intro h
  have := encodeTaggedKey_injective h
  cases this

/-- Decimal digit encoder/decoder for WeakMap `Nat` identity IDs. -/
def digitChar : Nat → Char
  | 0 => '0'
  | 1 => '1'
  | 2 => '2'
  | 3 => '3'
  | 4 => '4'
  | 5 => '5'
  | 6 => '6'
  | 7 => '7'
  | 8 => '8'
  | _ => '9'

def charDigit : Char → Nat
  | '0' => 0
  | '1' => 1
  | '2' => 2
  | '3' => 3
  | '4' => 4
  | '5' => 5
  | '6' => 6
  | '7' => 7
  | '8' => 8
  | _ => 9

private theorem charDigit_digitChar (d : Nat) (hd : d < 10) : charDigit (digitChar d) = d := by
  match d with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | 9 => rfl
  | _ + 10 => omega

/-- Base-10 serialization of natural numbers (used for WeakMap object/function IDs). -/
def natToDecChars (n : Nat) : List Char :=
  if _ : n < 10 then [digitChar n]
  else natToDecChars (n / 10) ++ [digitChar (n % 10)]

/-- Exact left-inverse parser for base-10 digit lists. -/
def decCharsToNatAux (acc : Nat) : List Char → Nat
  | [] => acc
  | c :: cs => decCharsToNatAux (acc * 10 + charDigit c) cs

private theorem decCharsToNatAux_append (acc : Nat) (xs ys : List Char) :
    decCharsToNatAux acc (xs ++ ys) = decCharsToNatAux (decCharsToNatAux acc xs) ys := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, decCharsToNatAux]
    exact ih _

theorem decCharsToNatAux_natToDecChars (n : Nat) :
    decCharsToNatAux 0 (natToDecChars n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [natToDecChars]
    by_cases h : n < 10
    · simp only [h, ↓reduceDIte, decCharsToNatAux, Nat.zero_mul, Nat.zero_add]
      exact charDigit_digitChar n h
    · simp only [h, ↓reduceDIte]
      rw [decCharsToNatAux_append]
      have hlt : n / 10 < n := Nat.div_lt_self (by omega) (by omega)
      rw [ih (n / 10) hlt]
      simp only [decCharsToNatAux]
      rw [charDigit_digitChar (n % 10) (Nat.mod_lt n (by omega))]
      omega

/-- Base-10 WeakMap ID encoding is strictly injective on all `Nat`. -/
theorem natToDecChars_injective {m n : Nat}
    (h : natToDecChars m = natToDecChars n) : m = n := by
  have h1 := decCharsToNatAux_natToDecChars m
  have h2 := decCharsToNatAux_natToDecChars n
  rw [h] at h1
  omega

/-- Full typed key model for `encodeL1Key` (`src/l1.ts`), including WeakMap `Nat` IDs
    and `Bool` values. -/
inductive L1Key where
  | str (s : String)
  | bool (b : Bool)
  | fn (id : Nat)
  | obj (id : Nat)
  deriving Repr, DecidableEq

def encodeL1Key : L1Key → String
  | .str s => encodeTaggedKey ⟨.str, s⟩
  | .bool b => encodeTaggedKey ⟨.bool, if b then "true" else "false"⟩
  | .fn id => encodeTaggedKey ⟨.fn, String.ofList (natToDecChars id)⟩
  | .obj id => encodeTaggedKey ⟨.obj, String.ofList (natToDecChars id)⟩

theorem encodeL1Key_injective {k1 k2 : L1Key}
    (h : encodeL1Key k1 = encodeL1Key k2) : k1 = k2 := by
  cases k1 <;> cases k2 <;> simp only [encodeL1Key] at h
  · have ht := encodeTaggedKey_injective h
    injection ht with _ hs
    subst hs; rfl
  all_goals
    try (
      have ht := encodeTaggedKey_injective h
      cases ht
    )
  · rename_i b1 b2
    have ht := encodeTaggedKey_injective h
    injection ht with _ hs
    cases b1 <;> cases b2 <;> simp at hs ⊢
  · rename_i id1 id2
    have ht := encodeTaggedKey_injective h
    injection ht with _ hs
    have hlist : (String.ofList (natToDecChars id1)).toList = (String.ofList (natToDecChars id2)).toList :=
      congrArg String.toList hs
    simp only [String.toList_ofList] at hlist
    rw [natToDecChars_injective hlist]
  · rename_i id1 id2
    have ht := encodeTaggedKey_injective h
    injection ht with _ hs
    have hlist : (String.ofList (natToDecChars id1)).toList = (String.ofList (natToDecChars id2)).toList :=
      congrArg String.toList hs
    simp only [String.toList_ofList] at hlist
    rw [natToDecChars_injective hlist]

end LruCacheClustered.KeyEncoding
