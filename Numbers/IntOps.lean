/- Operations as defined in the WASM specification:
    https://webassembly.github.io/spec/core/exec/numerics.html#integer-operations
-/
import Numbers.IntRepr

private def hexstring := "0123456789ABCDEF"

def Nat.toHexNumString (v : Nat) : String :=
  Nat.toDigits 16 v |>.foldl (· ++ ·.toUpper.toString) ""

namespace Numbers.Unsigned

def sat (i : Int) : Unsigned n :=
  if i > (@MAX_VALUE n).toNat then MAX_VALUE
  else if i < 0 then 0
  else ofInt i

theorem mod_size : x % MAX n < Nat.pow 2 n := by
  rw [MAX]
  exact Nat.mod_lt x (Nat.pow_pos (a:=2) (by decide))

def add(i₁ i₂ : Unsigned n) : Unsigned n :=
  ⟨(i₁.val + i₂.val) % MAX n, mod_size⟩
instance : HAdd (Unsigned n) (Unsigned n) (Unsigned n) := ⟨add⟩
instance : HAdd (Unsigned n) Nat (Unsigned n) := ⟨(add · <| Unsigned.ofNat ·)⟩
instance : HAdd Nat (Unsigned n) (Unsigned n) := ⟨(add <| Unsigned.ofNat ·)⟩

def sub (i₁ i₂ : Unsigned n) : Unsigned n :=
  ⟨(i₁.val - i₂.val + MAX n) % MAX n, mod_size⟩
instance : HSub (Unsigned n) (Unsigned n) (Unsigned n) := ⟨sub⟩
instance : HSub (Unsigned n) Nat (Unsigned n) := ⟨(sub · <| Unsigned.ofNat ·)⟩
instance : HSub Nat (Unsigned n) (Unsigned n) := ⟨(sub <| Unsigned.ofNat ·)⟩

def neg (i : Unsigned n) : Unsigned n :=
  ⟨(MAX n - i.val) % MAX n, mod_size⟩
instance : Neg (Unsigned n) := ⟨neg⟩

def mul (i₁ i₂ : Unsigned n) : Unsigned n :=
  ⟨(i₁.val * i₂.val) % MAX n, mod_size⟩
instance : HMul (Unsigned n) (Unsigned n) (Unsigned n) := ⟨mul⟩
instance : HMul (Unsigned n) Nat (Unsigned n) := ⟨(mul · <| Unsigned.ofNat ·)⟩
instance : HMul Nat (Unsigned n) (Unsigned n) := ⟨(mul <| Unsigned.ofNat ·)⟩

def divOpt (i j : Unsigned n) : Option (Unsigned n) :=
  if j.toNat = 0 then .none else .some <| ofNat (i.toNat / j.toNat)
instance : HDiv (Unsigned n) (Unsigned n) (Option (Unsigned n)) := ⟨divOpt⟩
instance : HDiv (Unsigned n) Nat (Option (Unsigned n)) :=
  ⟨(divOpt · <| Unsigned.ofNat ·)⟩
instance : HDiv Nat (Unsigned n) (Option (Unsigned n)) :=
  ⟨(divOpt <| Unsigned.ofNat ·)⟩

def div (i j : Unsigned n) (neqz : j.toNat ≠ 0) : Unsigned n :=
  match h : divOpt i j with
  | .none   => by simp only [ divOpt, ite_eq_left_iff, reduceCtorEq, imp_false,
                              Decidable.not_not] at h; contradiction
  | .some k => k

def remOpt (i j : Unsigned n) : Option (Unsigned n) :=
  if j.toNat = 0
  then .none
  else .some <| ofNat (i.toNat - j.toNat * (i.toNat / j.toNat))
instance : HMod (Unsigned n) (Unsigned n) (Option (Unsigned n)) := ⟨remOpt⟩
instance : HMod (Unsigned n) Nat (Option (Unsigned n)) :=
  ⟨(remOpt · <| Unsigned.ofNat ·)⟩
instance : HMod Nat (Unsigned n) (Option (Unsigned n)) :=
  ⟨(remOpt <| Unsigned.ofNat ·)⟩

def rem (i j : Unsigned n) (neqz : j.toNat ≠ 0) : Unsigned n :=
  match h : remOpt i j with
  | .none   => by simp only [ remOpt, ite_eq_left_iff, reduceCtorEq, imp_false,
                              Decidable.not_not] at h; contradiction
  | .some k => k

def and (i₁ i₂ : Unsigned n) : Unsigned n :=
  ⟨(i₁.val &&& i₂.val) % MAX n, mod_size⟩
instance : HAnd (Unsigned n) (Unsigned n) (Unsigned n) := ⟨and⟩
instance : HAnd (Unsigned n) Nat (Unsigned n) := ⟨(and · <| Unsigned.ofNat ·)⟩
instance : HAnd Nat (Unsigned n) (Unsigned n) := ⟨(and <| Unsigned.ofNat ·)⟩
instance : HAnd (Unsigned n) Int (Unsigned n) := ⟨(and · <| Unsigned.ofInt ·)⟩
instance : HAnd Int (Unsigned n) (Unsigned n) := ⟨(and <| Unsigned.ofInt ·)⟩

def or (i₁ i₂ : Unsigned n) : Unsigned n :=
  ⟨(i₁.val ||| i₂.val) % MAX n, mod_size⟩
instance : HOr (Unsigned n) (Unsigned n) (Unsigned n) := ⟨or⟩
instance : HOr (Unsigned n) Nat (Unsigned n) := ⟨(or · <| Unsigned.ofNat ·)⟩
instance : HOr Nat (Unsigned n) (Unsigned n) := ⟨(or <| Unsigned.ofNat ·)⟩
instance : HOr (Unsigned n) Int (Unsigned n) := ⟨(or · <| Unsigned.ofInt ·)⟩
instance : HOr Int (Unsigned n) (Unsigned n) := ⟨(or <| Unsigned.ofInt ·)⟩

def xor (i₁ i₂ : Unsigned n) : Unsigned n :=
  ⟨(i₁.val ^^^ i₂.val) % MAX n, mod_size⟩
instance : HXor (Unsigned n) (Unsigned n) (Unsigned n) := ⟨xor⟩
instance : HXor (Unsigned n) Nat (Unsigned n) := ⟨(xor · <| Unsigned.ofNat ·)⟩
instance : HXor Nat (Unsigned n) (Unsigned n) := ⟨(xor <| Unsigned.ofNat ·)⟩
instance : HXor (Unsigned n) Int (Unsigned n) := ⟨(xor · <| Unsigned.ofInt ·)⟩
instance : HXor Int (Unsigned n) (Unsigned n) := ⟨(xor <| Unsigned.ofInt ·)⟩

def not (i : Unsigned n) : Unsigned n :=
  ⟨(i.val ^^^ (MAX_VALUE : Unsigned n).val) % MAX n, mod_size⟩
instance : Complement (Unsigned n) := ⟨not⟩

def andnot (i₁ i₂ : Unsigned n) : Unsigned n :=
  ⟨(i₁.val &&& (~~~i₂).val) % MAX n, mod_size⟩
  -- ⟨(Unsigned.and i₁ (Unsigned.not i₂)) % MAX n, mod_size⟩

def shl (i₁ i₂ : Unsigned n) : Unsigned n :=
  ⟨(i₁.val <<< i₂.val) % MAX n, mod_size⟩
instance : HShiftLeft (Unsigned n) (Unsigned n) (Unsigned n) := ⟨shl⟩
instance : HShiftLeft (Unsigned n) Nat (Unsigned n) :=
  ⟨(shl · <| Unsigned.ofNat ·)⟩
instance : HShiftLeft Nat (Unsigned n) (Unsigned n) :=
  ⟨(shl <| Unsigned.ofNat ·)⟩

def shr (i₁ i₂ : Unsigned n) : Unsigned n :=
  ⟨(i₁.val >>> i₂.val) % MAX n, mod_size⟩
instance : HShiftRight (Unsigned n) (Unsigned n) (Unsigned n) := ⟨shr⟩
instance : HShiftRight (Unsigned n) Nat (Unsigned n) :=
  ⟨(shr · <| Unsigned.ofNat ·)⟩
instance : HShiftRight Nat (Unsigned n) (Unsigned n) :=
  ⟨(shr <| Unsigned.ofNat ·)⟩

-- stolen from my WASM interpreter I wrote in C
def rotl (i₁ i₂ : Unsigned n) : Unsigned n :=
  ⟨((i₁.val <<< i₂.val) ||| (i₁.val >>> (n - i₂.val))) % MAX n, mod_size⟩

def rotr (i₁ i₂ : Unsigned n) : Unsigned n :=
  ⟨((i₁.val >>> i₂.val) ||| (i₁.val <<< (n - i₂.val))) % MAX n, mod_size⟩

-- not doing the efficient datalab solution, also a little scuffed anyway
def clz (i : Unsigned n) : Unsigned n :=
  Unsigned.ofNat (n - (clz_helper i n))
where clz_helper (i : Unsigned n) (c : Nat) : Nat :=
  if h : c = 0
  then c
  else if (rotl i (ofNat (n - c + 1))) &&& 1 = 1
  then c
  else clz_helper i (c - 1)

def ctz (i : Unsigned n) : Unsigned n :=
  Unsigned.ofNat (n - (ctz_helper i n))
where ctz_helper (i : Unsigned n) (c : Nat) : Nat :=
  if h : c = 0
  then c
  else if (i >>> (ofNat (n - c) : Unsigned n)) &&& 1 = 1
  then c
  else ctz_helper i (c - 1)

-- people really made a log n algorithm for an O(32) problem
def popcnt (i : Unsigned n) : Unsigned n :=
  Unsigned.ofNat (popcnt_helper n i 0)
where popcnt_helper (f : Nat) (i : Unsigned n) (c : Nat) : Nat :=
  if h : f = 0
  then c
  else if (i >>> (ofNat (n - f) : Unsigned n)) &&& 1 = 1
  then popcnt_helper (f - 1) i (c + 1)
  else popcnt_helper (f - 1) i c


-- COMPARISON FUNCTIONS

def eqz (i : Unsigned n) : Unsigned n :=
  if i = .ofNat 0 then .ofNat 1 else .ofNat 0
def eq (i₁ i₂ : Unsigned n) : Unsigned n :=
  if i₁ = i₂ then .ofNat 1 else .ofNat 0
def ne (i₁ i₂ : Unsigned n) : Unsigned n :=
  if i₁ ≠ i₂ then .ofNat 1 else .ofNat 0
def lt (i₁ i₂ : Unsigned n) : Unsigned n :=
  if i₁ < i₂ then .ofNat 1 else .ofNat 0
def gt (i₁ i₂ : Unsigned n) : Unsigned n :=
  if i₁ > i₂ then .ofNat 1 else .ofNat 0
def le (i₁ i₂ : Unsigned n) : Unsigned n :=
  if i₁ ≤ i₂ then .ofNat 1 else .ofNat 0
def ge (i₁ i₂ : Unsigned n) : Unsigned n :=
  if i₁ ≥ i₂ then .ofNat 1 else .ofNat 0

-- CONVERSION

def extend (i : Unsigned n) : Unsigned m := .ofNat i.toNat
def wrap   (i : Unsigned n) : Unsigned m := .ofNat (i.val % MAX n)

-- MISC FUNCTIONS

def bitselect (i₁ i₂ i₃ : Unsigned n) : Unsigned n :=
  ⟨((i₁.val &&& i₃.val) ||| (i₂.val &&& (~~~i₃).val)) % MAX n, mod_size⟩

def min (i₁ i₂ : Unsigned n) : Unsigned n :=
  if i₁ < i₂ then i₁ else i₂
instance : Max (Unsigned n) := ⟨min⟩

def max (i₁ i₂ : Unsigned n) : Unsigned n :=
  if i₁ > i₂ then i₁ else i₂
instance : Max (Unsigned n) := ⟨min⟩

def addsat (i₁ i₂ : Unsigned n) : Unsigned n := sat (i₁.val + i₂.val)
def subsat (i₁ i₂ : Unsigned n) : Unsigned n := sat (i₁.val - i₂.val)
def avgr (i₁ i₂ : Unsigned n)   : Unsigned n :=
  Unsigned.ofNat ((i₁.val + i₂.val + 1) / 2)

theorem toNat_ofNat_neq_zero
    (u : Nat)
    (h : u % 2 ^ n ≠ 0)
    : toNat ((ofNat u) : Unsigned n) ≠ 0 := by
  simp only [toNat, ofNat, Fin.val_ofNat]
  exact h

partial def toLEB128 (n : Unsigned N) : List UInt8 :=
  if n_size : n.val < 128 then [UInt8.ofNat n.toNat] else
    UInt8.ofNat (n.toNat % 128 + 128) :: toLEB128 (div n 128 (by
      have : 128 % 2 ^ N ≠ 0 := by
        if h : N < 8 then
          have := n.isLt
          sorry
        else
          sorry
      have := toNat_ofNat_neq_zero (n := N) 128 this
      simp only [OfNat.ofNat, this, ne_eq, not_false_eq_true]
    ))

def ofLEB128 (N : Nat) (seq : List UInt8)
    : Option (Unsigned N × List UInt8) := do
  match seq with
  | [] => .none
  | n :: rest =>
    if n < 128 && n.toNat < MAX N then
      return (ofNat n.toNat, rest)
    else if n ≥ 128 ∧ N - 7 > 0 then
      let ⟨m, h_after⟩ ← ofLEB128 (N - 7) rest
      return (ofNat (m.toNat * 128 + (n.toNat - 128)), h_after)
    else .none

end Unsigned

namespace Signed

def sat (i : Int) : Signed n :=
  if i < (@MIN_VALUE n).toInt then MIN_VALUE
  else if i > (@MAX_VALUE n).toInt then MAX_VALUE
  else ofInt i

def add : Signed n → Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.add
instance : HAdd (Signed n) (Signed n) (Signed n) := ⟨add⟩
instance : HAdd (Signed n) Nat (Signed n) := ⟨(add · <| Signed.ofNat ·)⟩
instance : HAdd Nat (Signed n) (Signed n) := ⟨(add <| Signed.ofNat ·)⟩
instance : HAdd (Signed n) Int (Signed n) := ⟨(add · <| Signed.ofInt ·)⟩
instance : HAdd Int (Signed n) (Signed n) := ⟨(add <| Signed.ofInt ·)⟩

def sub : Signed n → Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.sub
instance : HSub (Signed n) (Signed n) (Signed n) := ⟨sub⟩
instance : HSub (Signed n) Nat (Signed n) := ⟨(sub · <| Signed.ofNat ·)⟩
instance : HSub Nat (Signed n) (Signed n) := ⟨(sub <| Signed.ofNat ·)⟩
instance : HSub (Signed n) Int (Signed n) := ⟨(sub · <| Signed.ofInt ·)⟩
instance : HSub Int (Signed n) (Signed n) := ⟨(sub <| Signed.ofInt ·)⟩

def neg : Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.neg
instance : Neg (Signed n) := ⟨neg⟩

def mul : Signed n → Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.mul
instance : HMul (Signed n) (Signed n) (Signed n) := ⟨mul⟩
instance : HMul (Signed n) Nat (Signed n) := ⟨(mul · <| Signed.ofNat ·)⟩
instance : HMul Nat (Signed n) (Signed n) := ⟨(mul <| Signed.ofNat ·)⟩
instance : HMul (Signed n) Int (Signed n) := ⟨(mul · <| Signed.ofInt ·)⟩
instance : HMul Int (Signed n) (Signed n) := ⟨(mul <| Signed.ofInt ·)⟩

def divOpt (i j : Signed n) : Option (Signed n) :=
  if j = 0 then .none else validate (i.toInt / j.toInt)
where validate (res : Int) : Option (Signed n) :=
  if res = -(MIN_VALUE : Signed n).toInt
  then .none
  else .some (.ofInt res)
instance : HDiv (Signed n) (Signed n) (Option (Signed n)) := ⟨divOpt⟩
instance : HDiv (Signed n) Nat (Option (Signed n)) :=
  ⟨(divOpt · <| Signed.ofNat ·)⟩
instance : HDiv Nat (Signed n) (Option (Signed n)) :=
  ⟨(divOpt <| Signed.ofNat ·)⟩
instance : HDiv (Signed n) Int (Option (Signed n)) :=
  ⟨(divOpt · <| Signed.ofInt ·)⟩
instance : HDiv Int (Signed n) (Option (Signed n)) :=
  ⟨(divOpt <| Signed.ofInt ·)⟩

def div (i j : Signed n) (neqz : j ≠ 0)
    (repr : i.toInt / j.toInt ≠ -(MIN_VALUE : Signed n).toInt)
    : Signed n :=
  match h : divOpt i j with
  | .none   => by
    simp only [ divOpt, divOpt.validate, ite_eq_left_iff, reduceCtorEq,
                imp_false, Decidable.not_not ] at h
    have := h neqz
    contradiction
  | .some k => k

def remOpt (i j : Signed n) : Option (Signed n) :=
  if j = 0
  then .none
  else .some <| (i.toInt - j.toInt * (i.toInt / j.toInt)) |> .ofInt
instance : HMod (Signed n) (Signed n) (Option (Signed n)) := ⟨remOpt⟩
instance : HMod (Signed n) Nat (Option (Signed n)) :=
  ⟨(remOpt · <| Signed.ofNat ·)⟩
instance : HMod Nat (Signed n) (Option (Signed n)) :=
  ⟨(remOpt <| Signed.ofNat ·)⟩
instance : HMod (Signed n) Int (Option (Signed n)) :=
  ⟨(remOpt · <| Signed.ofInt ·)⟩
instance : HMod Int (Signed n) (Option (Signed n)) :=
  ⟨(remOpt <| Signed.ofInt ·)⟩

def rem (i j : Signed n) (neqz : j ≠ 0) : Signed n :=
  match h : remOpt i j with
  | .none   => by simp only [ remOpt, ite_eq_left_iff, reduceCtorEq, imp_false,
                              Decidable.not_not ] at h; contradiction
  | .some k => k


def and : Signed n → Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.and
instance : HAnd (Signed n) (Signed n) (Signed n) := ⟨and⟩
instance : HAnd (Signed n) Nat (Signed n) := ⟨(and · <| Signed.ofNat ·)⟩
instance : HAnd Nat (Signed n) (Signed n) := ⟨(and <| Signed.ofNat ·)⟩
instance : HAnd (Signed n) Int (Signed n) := ⟨(and · <| Signed.ofInt ·)⟩
instance : HAnd Int (Signed n) (Signed n) := ⟨(and <| Signed.ofInt ·)⟩

def or : Signed n → Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.or
instance : HOr (Signed n) (Signed n) (Signed n) := ⟨or⟩
instance : HOr (Signed n) Nat (Signed n) := ⟨(or · <| Signed.ofNat ·)⟩
instance : HOr Nat (Signed n) (Signed n) := ⟨(or <| Signed.ofNat ·)⟩
instance : HOr (Signed n) Int (Signed n) := ⟨(or · <| Signed.ofInt ·)⟩
instance : HOr Int (Signed n) (Signed n) := ⟨(or <| Signed.ofInt ·)⟩

def xor : Signed n → Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.xor
instance : HXor (Signed n) (Signed n) (Signed n) := ⟨xor⟩
instance : HXor (Signed n) Nat (Signed n) := ⟨(xor · <| Signed.ofNat ·)⟩
instance : HXor Nat (Signed n) (Signed n) := ⟨(xor <| Signed.ofNat ·)⟩
instance : HXor (Signed n) Int (Signed n) := ⟨(xor · <| Signed.ofInt ·)⟩
instance : HXor Int (Signed n) (Signed n) := ⟨(xor <| Signed.ofInt ·)⟩

def not : Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.not
instance : Complement (Signed n) := ⟨not⟩

def andnot : Signed n → Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.andnot

def shl : Signed n → Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.shl
instance : HShiftLeft (Signed n) (Signed n) (Signed n) := ⟨shl⟩
instance : HShiftLeft (Signed n) Nat (Signed n) := ⟨(shl · <| Signed.ofNat ·)⟩
instance : HShiftLeft Nat (Signed n) (Signed n) := ⟨(shl <| Signed.ofNat ·)⟩
instance : HShiftLeft Int (Signed n) (Signed n) := ⟨(shl <| Signed.ofInt ·)⟩

def shr (i₁ i₂ : Signed n) : Signed n :=
  Signed.ofInt (i₁.toInt >>> i₂.toNat)
instance : HShiftRight (Signed n) (Signed n) (Signed n) := ⟨shr⟩
instance : HShiftRight (Signed n) Nat (Signed n) := ⟨(shr · <| Signed.ofNat ·)⟩
instance : HShiftRight Nat (Signed n) (Signed n) := ⟨(shr <| Signed.ofNat ·)⟩
instance : HShiftRight Int (Signed n) (Signed n) := ⟨(shr <| Signed.ofInt ·)⟩

def rotl : Signed n → Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.rotl

def rotr : Signed n → Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.rotr

def clz : Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.clz

def ctz : Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.ctz

def popcnt : Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.popcnt


-- COMPARISON FUNCTIONS

def eqz : Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.eqz
def eq : Signed n → Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.eq
def neq : Signed n → Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.ne
def lt (i₁ i₂ : Signed n) : Signed n :=
  if i₁.toInt < i₂.toInt then .ofNat 1 else .ofNat 0
def gt (i₁ i₂ : Signed n) : Signed n :=
  if i₁.toInt > i₂.toInt then .ofNat 1 else .ofNat 0
def le (i₁ i₂ : Signed n) : Signed n :=
  if i₁.toInt ≤ i₂.toInt then .ofNat 1 else .ofNat 0
def ge (i₁ i₂ : Signed n) : Signed n :=
  if i₁.toInt ≥ i₂.toInt then .ofNat 1 else .ofNat 0

-- CONVERSION FUNCTIONS

def extend (i : Signed n) : Signed m := .ofInt i.toInt
def wrap : Signed n → Signed m :=
  cast (by unfold Signed; rfl) Unsigned.wrap

-- MISC FUNCTIONS

def bitselect : Signed n → Signed n → Signed n → Signed n :=
  cast (by unfold Signed; rfl) Unsigned.bitselect

def abs (i : Signed n) : Signed n :=
  if i ≥ 0 then i else -i

def min (i₁ i₂ : Signed n) : Signed n :=
  if lt i₁ i₂ = 1 then i₁ else i₂
instance : Min (Signed n) := ⟨min⟩

def max (i₁ i₂ : Signed n) : Signed n :=
  if gt i₁ i₂ = 1 then i₁ else i₂
instance : Max (Signed n) := ⟨min⟩

def addsat (i₁ i₂ : Signed n) : Signed n := sat (i₁.toInt + i₂.toInt)
def subsat (i₁ i₂ : Signed n) : Signed n := sat (i₁.toInt - i₂.toInt)

partial def toLEB128 (n : Signed N) : List UInt8 :=
  let n'   := n >>> (7 : Signed N)
  let byte := n &&& 0x7F
  if (n' == 0 && byte &&& 0x40 == 0) || (n' == -1 && byte &&& 0x40 != 0)
  then UInt8.ofNat byte.toUnsignedN.toNat :: []
  else UInt8.ofNat (byte ||| (0x80 : Signed N)).toNat :: toLEB128 n'

def ofLEB128 (N : Nat) (seq : List UInt8)
    : Option (Signed N × List UInt8) :=
  process seq 0 0
where process (seq : List UInt8)
              (result : Signed N)
              (shift : Signed N)
              : Option (Signed N × List UInt8) :=
  match seq with
  | []        => .none
  | byte :: rest =>
    let byte_data : Signed N := Signed.ofNat (byte.toNat &&& 0x7F)
    let result' := result ||| (byte_data <<< shift)
    let shift' := shift + 7
    if byte &&& 0x80 != 0
    then process rest result' shift'
    else if shift'.toNat < N && byte &&& 0x40 != 0
    then
      let sign_ext := (Signed.ofInt (-1) : Signed N) <<< shift'
      .some (result' ||| sign_ext, rest)
    else .some (result', rest)


end Signed
