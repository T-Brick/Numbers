import Numbers

open Numbers

def x : Unsigned16 := -150
  -- should be 1111111101101010 (2's comp), i.e. 65386 when unsigned
def y : Unsigned16 := 4
def z : Signed16 := -150

/-- info: 65386 -/
#guard_msgs in #eval x
/-- info: 150 -/
#guard_msgs in #eval -x

/-- info: 65386 -/
#guard_msgs in #eval z.toUnsignedN
/-- info: 150 -/
#guard_msgs in #eval -z.toUnsignedN

/-- info: some 0 -/
#guard_msgs in #eval -x % (2 : Unsigned16)

/-- info: 4294967295 -/
#guard_msgs in #eval (Unsigned.MAX_VALUE : Unsigned32)

/-- info: -2038 -/
#guard_msgs in #eval ((Signed.ofInt ((-65213 : Int) >>> 5)) : Signed32)

/-- info: [248, 255, 255, 255, 15] -/
#guard_msgs in #eval (4294967288 : Unsigned32).toLEB128
/-- info: [229, 142, 38] -/
#guard_msgs in #eval (624485 : Signed32).toLEB128
/-- info: some (-123456, []) -/
#guard_msgs in #eval (([0xC0, 0xBB, 0x78] |> Signed.ofLEB128 ⟨32, by simp⟩))
/-- info: [155, 241, 89] -/
#guard_msgs in #eval [0x9b, 0xf1, 0x59]
/-- info: some (-624485, []) -/
#guard_msgs in #eval (((-624485 : Signed32).toLEB128) |> Signed.ofLEB128 ⟨32, by simp⟩)
