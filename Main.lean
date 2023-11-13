import Numbers

def main : IO Unit := return ()

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

#eval (Signed.MIN_VALUE : Signed32) / (-1 : Signed32)
