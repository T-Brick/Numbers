import Numbers

def main : IO Unit := return ()

/-
namespace Test

open Numbers

def x : Unsigned16 := -150
  -- should be 1111111101101010 (2's comp), i.e. 65386 when unsigned
def y : Unsigned16 := 4
def z : Signed16 := -150

#eval x
#eval -x
#eval z.toUnsignedN
#eval -z.toUnsignedN

#eval -x % (2 : Unsigned16)

#eval (Unsigned.MAX_VALUE : Unsigned32)

#eval ((Signed.ofInt ((-65213 : Int) >>> 5)) : Signed32)

#eval (4294967288 : Unsigned32).toLEB128
#eval (624485 : Signed32).toLEB128
#eval (([0xC0, 0xBB, 0x78] |> Signed.ofLEB128 ⟨32, by simp⟩))
#eval [0x9b, 0xf1, 0x59]
#eval (((-624485 : Signed32).toLEB128) |> Signed.ofLEB128 ⟨32, by simp⟩)
-/
