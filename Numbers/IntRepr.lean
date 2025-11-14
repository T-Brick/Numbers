/- Encoding of defintion WASM's definition of integers:
    https://webassembly.github.io/spec/core/syntax/values.html#integers
-/
namespace Numbers

def Unsigned (n : Nat) := Fin (2 ^ n)
instance : Inhabited (Unsigned n) :=
  ⟨0, Nat.pow_pos (a:=2) (by decide)⟩

namespace Unsigned

def ofNat (u : Nat) : Unsigned n := Fin.ofNat (2 ^ n) u
def toNat(u : Unsigned n) : Nat := u.val

def MAX_VALUE : Unsigned n := ofNat (2 ^ n - 1)
def MIN_VALUE : Unsigned n := ofNat 0
def MAX (n : Nat) : Nat := 2 ^ n
def MIN (_ : Nat) : Nat := 0

def toInt (i : Unsigned n) : Int := i.toNat
def toUInt32 (i : Unsigned 32) : UInt32 :=
  UInt32.ofNatLT (i.toNat) (by
    have h : 4294967296 = 2 ^ 32 := by decide
    rw [UInt32.size, h, toNat]
    exact i.isLt
  )

def ofInt (i : Int) : Unsigned n := ofNat (i.toNat)
def ofInt? (i : Int) : Option (Unsigned n) :=
  let size := Int.ofNat (2 ^ (n : Nat))
  if i < size then i.toNat?.map .ofNat else .none

instance : OfNat (Unsigned n) m where
  ofNat := Unsigned.ofNat m
instance : Coe (Unsigned 32) Int := ⟨toInt⟩
instance : Coe (Unsigned 32) UInt32 := ⟨toUInt32⟩
instance : Coe (Unsigned 64) Int := ⟨toInt⟩
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
def Signed (n : Nat) := Unsigned n
instance : Inhabited (Signed n) :=
  ⟨0, Nat.pow_pos (a:=2) (by decide)⟩

namespace Signed

@[inline] def ofUnsignedN : Unsigned n → Signed n :=
  cast (by unfold Signed; rfl) id
@[inline] def toUnsignedN : Signed n → Unsigned n :=
  cast (by unfold Signed; rfl) id

def MAX_VALUE : Signed n  := ofUnsignedN <| .ofNat (2^(n - 1) - 1)
def MIN_VALUE : Signed n  := ofUnsignedN <| .ofNat (2^(n - 1))

def toInt (i : Signed n) : Int :=
  if i.toUnsignedN < MIN_VALUE.toUnsignedN
  then i.toUnsignedN.toNat -- i pos
  else i.toUnsignedN.toInt - Int.ofNat (2 ^ n)

def ofInt? (i : Int) : Option (Signed n) :=
  let offset := i + (2 ^ (n - 1) : Nat)
  if h : 0 ≤ offset && offset < Unsigned.MAX n then
    let offset : Signed n := ⟨offset.natAbs, by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      have := Int.natAbs_lt_natAbs_of_nonneg_of_lt h.1 h.2
      rw [Unsigned.MAX] at this
      exact this⟩
    .some <| ofUnsignedN (Unsigned.ofNat (offset.val + (2 ^ (n - 1))))
  else
    none

def ofInt (i : Int) : Signed n :=
  let offset := i + (2 ^ (n - 1) : Nat)
  if h : 0 ≤ offset && offset < Unsigned.MAX n then
    let offset : Unsigned n := ⟨offset.natAbs, by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      have := Int.natAbs_lt_natAbs_of_nonneg_of_lt h.1 h.2
      rw [Unsigned.MAX] at this
      exact this⟩
    ofUnsignedN (Unsigned.ofNat (offset.val + (2 ^ (n - 1))))
  else
    ⟨0, Nat.pow_pos (a:=2) (by decide)⟩

def ofNat?(m : Nat) : Option (Signed n) := ofInt? m
def ofNat : Nat → Signed n := .ofUnsignedN ∘ .ofNat
instance : OfNat (Signed n) m := ⟨ofNat m⟩

instance : Coe (Signed 32) Int := ⟨toInt⟩
instance : Coe (Signed 32) UInt32 := ⟨Unsigned.toUInt32⟩
instance : Coe (Signed 64) Int := ⟨toInt⟩
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

abbrev Unsigned8     := Unsigned 8
abbrev Unsigned16    := Unsigned 16
abbrev Unsigned32    := Unsigned 32
abbrev Unsigned64    := Unsigned 64

abbrev Signed8       := Signed 8
abbrev Signed16      := Signed 16
abbrev Signed32      := Signed 32
abbrev Signed64      := Signed 64

abbrev Int8  := Signed8
abbrev Int16 := Signed16
abbrev Int32 := Signed32
abbrev Int64 := Signed64
