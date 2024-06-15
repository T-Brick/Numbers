/- Encoding of defintion WASM's definition of integers:
    https://webassembly.github.io/spec/core/syntax/values.html#integers
-/
namespace Numbers

theorem zero_lt_bit_length : ∀ n : {i : Nat // 0 < i}, 0 < 2 ^ n.val := by
  intro n
  induction n.val with
  | zero => decide
  | succ n ih =>
    rw [←Nat.pow_eq, Nat.pow]
    exact Nat.mul_lt_mul_of_lt_of_le' ih (by decide) (Nat.lt_succ_self 0)

def Unsigned (n : {i : Nat // 0 < i}) := Fin (2 ^ n.val)
instance : Inhabited (Unsigned n) := ⟨0, zero_lt_bit_length _⟩

namespace Unsigned

def ofNat (u : Nat) : Unsigned n :=
  Fin.ofNat' u (Nat.pos_pow_of_pos n (Nat.zero_lt_succ 1))
def toNat (u : Unsigned n) : Nat := u.val

def MAX_VALUE : Unsigned n := ofNat (2 ^ n.val - 1)
def MIN_VALUE : Unsigned n := ofNat 0
def MAX (n : { i // 0 < i }) : Nat := 2 ^ n.val
def MIN (_ : { i // 0 < i }) : Nat := 0

def toInt (i : Unsigned n) : Int := i.toNat
def toUInt32 (i : Unsigned ⟨32, Nat.zero_lt_succ 31⟩) : UInt32 :=
  UInt32.ofNat' (i.toNat) (by
    have h : 4294967296 = 2 ^ 32 := by decide
    rw [UInt32.size, h, toNat]
    exact i.isLt
  )

def ofInt (i : Int) : Unsigned n := ofNat (i.toNat)
def ofInt? (i : Int) : Option (Unsigned n) :=
  let size := Int.ofNat (2 ^ (n : Nat))
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
    ⟨0, zero_lt_bit_length _⟩

def ofNat? (m : Nat) : Option (Signed n) := ofInt? m
def ofNat : Nat → Signed n := .ofUnsignedN ∘ .ofNat
instance : OfNat (Signed n) m := ⟨ofNat m⟩

instance : Coe (Signed ⟨32, by decide⟩) Int := ⟨toInt⟩
instance : Coe (Signed ⟨32, by decide⟩) UInt32 := ⟨Unsigned.toUInt32⟩
instance : Coe (Signed ⟨64, by decide⟩) Int := ⟨toInt⟩
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

end Signed

@[reducible] def Uninterpreted := Unsigned -- 'iN' in the reference

abbrev Unsigned8     := Unsigned ⟨8 , by decide⟩
abbrev Unsigned16    := Unsigned ⟨16, by decide⟩
abbrev Unsigned32    := Unsigned ⟨32, by decide⟩
abbrev Unsigned64    := Unsigned ⟨64, by decide⟩

abbrev Signed8       := Signed ⟨8 , by decide⟩
abbrev Signed16      := Signed ⟨16, by decide⟩
abbrev Signed32      := Signed ⟨32, by decide⟩
abbrev Signed64      := Signed ⟨64, by decide⟩

abbrev Int8  := Signed8
abbrev Int16 := Signed16
abbrev Int32 := Signed32
abbrev Int64 := Signed64
