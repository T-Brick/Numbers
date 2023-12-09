/- Encoding of defintion WASM's definition of integers:
    https://webassembly.github.io/spec/core/syntax/values.html#integers
-/
import Std
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Numbers

def Unsigned (n : {i : Nat // 0 < i}) := Fin (2 ^ n.val)
instance : Inhabited (Unsigned n) := ⟨0, by simp⟩

namespace Unsigned

def ofNat (u : Nat) : Unsigned n :=
  Fin.ofNat' u (Nat.pos_pow_of_pos n (Nat.zero_lt_succ 1))
def toNat (u : Unsigned n) : Nat := u.val

def MAX_VALUE : Unsigned n := ofNat (2 ^ n.val - 1)
def MIN_VALUE : Unsigned n := ofNat 0
def MAX (n : { i // 0 < i }) : Nat := 2 ^ n.val
def MIN (_ : { i // 0 < i }) : Nat := 0

def toInt (i : Unsigned n) : Int := i.toNat
def toUInt32 (i : Unsigned ⟨32, by simp⟩) : UInt32 := UInt32.ofNat' (i.toNat) (by
  have h : 4294967296 = 2 ^ 32 := by linarith
  rw [UInt32.size, h, toNat]
  exact i.isLt
)
def ofInt (i : Int) : Unsigned n := ofNat (i.toNat)
def ofInt? (i : Int) : Option (Unsigned n) :=
  let size := 2 ^ (n : Nat)
  if i < size then i.toNat'.map .ofNat else .none

instance : OfNat (Unsigned n) m where
  ofNat := Unsigned.ofNat m
instance : Coe (Unsigned ⟨32, by simp⟩) Int := ⟨toInt⟩
instance : Coe (Unsigned ⟨32, by simp⟩) UInt32 := ⟨toUInt32⟩
instance : Coe (Unsigned ⟨64, by simp⟩) Int := ⟨toInt⟩
instance : Repr (Unsigned n) := ⟨reprPrec ∘ toNat⟩

nonrec def toString : Unsigned n → String := toString ∘ toNat
instance : ToString (Unsigned n) := ⟨toString⟩

nonrec def compare (i j : Unsigned n) : Ordering := compare i.val j.val
instance : Ord (Unsigned n)  := ⟨compare⟩
instance : LT  (Unsigned n)  := ltOfOrd
instance : LE  (Unsigned n)  := leOfOrd

def deq (i j : Unsigned n) :=
  match decEq i.val j.val with
  | isTrue h  => isTrue (Fin.eq_of_val_eq h)
  | isFalse h => isFalse (Fin.ne_of_val_ne h)
instance : DecidableEq (Unsigned n) := deq

def ofLEB128 (N : { i // 0 < i }) (seq : List UInt8)
    : Option (Unsigned N × List UInt8) := do
  match seq with
  | [] => .none
  | n :: rest =>
    if n < 128 && n.toNat < MAX N then
      return (ofNat n.toNat, rest)
    else if h : n ≥ 128 ∧ N.val > 7 then
      let (m, after) ← ofLEB128 ⟨N.val - 7, by simp [h]⟩ rest
      return (ofNat (m.toNat * 128 + (n.toNat - 128)), after)
    else .none

end Unsigned


/- Derived to a generic bit size from C0deine -/
def Signed (n : {i : Nat // 0 < i}) := Unsigned n
instance : Inhabited (Signed n) := ⟨0, Nat.pos_pow_of_pos n (Nat.zero_lt_succ 1)⟩

namespace Signed

@[inline] def ofUnsignedN : Unsigned n → Signed n :=
  cast (by unfold Signed; rfl) id
@[inline] def toUnsignedN : Signed n → Unsigned n :=
  cast (by unfold Signed; rfl) id

def MAX_VALUE : Signed n  := ofUnsignedN <| .ofNat (2^(n.val - 1) - 1)
def MIN_VALUE : Signed n  := ofUnsignedN <| .ofNat (2^(n.val - 1))

def toInt (i : Signed n) : Int :=
  if i.toUnsignedN < MIN_VALUE.toUnsignedN
  then i.toUnsignedN.toNat -- i pos
  else i.toUnsignedN.toInt - Int.ofNat (2 ^ n.val)

def ofInt? (i : Int) : Option (Signed n) :=
  let offset := i + (2 ^ (n.val - 1) : Nat)
  if h : 0 ≤ offset && offset < Unsigned.MAX n then
    let offset : Signed n := ⟨offset.natAbs, by
      simp at *
      have := Int.natAbs_lt_natAbs_of_nonneg_of_lt h.1 h.2
      rw [Unsigned.MAX] at *
      exact this⟩
    .some <| ofUnsignedN (Unsigned.ofNat (offset.val + (2 ^ (n.val - 1))))
  else
    none

def ofInt (i : Int) : Signed n :=
  let offset := i + (2 ^ (n.val - 1) : Nat)
  if h : 0 ≤ offset && offset < Unsigned.MAX n then
    let offset : Unsigned n := ⟨offset.natAbs, by
      simp at *
      have := Int.natAbs_lt_natAbs_of_nonneg_of_lt h.1 h.2
      rw [Unsigned.MAX] at *
      exact this⟩
    ofUnsignedN (Unsigned.ofNat (offset.val + (2 ^ (n.val - 1))))
  else
    ⟨0, by simp⟩

def ofNat? (n : Nat) : Option (Signed m) := ofInt? n
instance : OfNat (Signed n) m := ⟨.ofUnsignedN <| .ofNat m⟩

instance : Coe (Signed ⟨32, by simp⟩) Int := ⟨toInt⟩
instance : Coe (Signed ⟨32, by simp⟩) UInt32 := ⟨Unsigned.toUInt32⟩
instance : Coe (Signed ⟨64, by simp⟩) Int := ⟨toInt⟩
instance : Repr (Signed n) := ⟨reprPrec ∘ toInt⟩

nonrec def toString : Signed n → String := toString ∘ toInt
instance : ToString (Signed n) := ⟨toString⟩


def deq (i j : Signed n) :=
  match decEq i.val j.val with
  | isTrue h  => isTrue (Fin.eq_of_val_eq h)
  | isFalse h => isFalse (Fin.ne_of_val_ne h)

instance : DecidableEq (Signed n) := deq

nonrec def compare (i j : Signed n) : Ordering :=
  let i := i.toInt
  let j := j.toInt
  if i < (Signed.MIN_VALUE : Signed n).toInt then -- i pos
    if j < (Signed.MIN_VALUE : Signed n).toInt
    then compare i j -- j pos
    else .gt -- j neg
  else -- i neg
    if j < (Signed.MIN_VALUE : Signed n).toInt
    then .lt -- j pos
    else compare i j -- j neg

instance : Ord (Signed n)  := ⟨compare⟩
instance : LT  (Signed n)  := ltOfOrd
instance : LE  (Signed n)  := leOfOrd

def ofLEB128 (N : { i // 0 < i }) (seq : List UInt8)
    : Option (Signed N × List UInt8) := do
  Unsigned.ofLEB128 N seq |>.map (fun (n, rem) => (Signed.ofUnsignedN n, rem))
  -- match seq with
  -- | [] => .none
  -- | n :: rest =>
    -- let max : Nat := 2 ^ (N - 1)
    -- if n < 64 && n.toNat < max then
      -- return ofInt n.toNat
    -- else if 64 ≤ n.toNat && n.toNat < 128 && n.toNat ≥ 128 - max then
      -- return ofInt (n.toNat - 128)
    -- else if h : n ≥ 128 ∧ N.val > 7 then
      -- let m ← ofLEB128 ⟨N.val - 7, by simp [h]⟩ rest
      -- return ofInt (m.toNat * 128 + (n.toNat - 128))
    -- else .none

end Signed

@[reducible] def Uninterpreted := Unsigned -- 'iN' in the reference
