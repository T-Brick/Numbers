import Numbers.IntRepr

namespace Numbers.Notation

scoped syntax "u8%"  num : term
scoped syntax "u16%" num : term
scoped syntax "u32%" num : term
scoped syntax "u64%" num : term

scoped syntax "s8%"  num : term
scoped syntax "s16%" num : term
scoped syntax "s32%" num : term
scoped syntax "s64%" num : term

macro_rules
| `(u8% $n:num)  => `(Unsigned.ofNat (n := 8)  $n)
| `(u16% $n:num) => `(Unsigned.ofNat (n := 16) $n)
| `(u32% $n:num) => `(Unsigned.ofNat (n := 32) $n)
| `(u64% $n:num) => `(Unsigned.ofNat (n := 64) $n)

macro_rules
| `(s8% $n:num)  => `(Signed.ofNat (n := 8)  $n)
| `(s16% $n:num) => `(Signed.ofNat (n := 16) $n)
| `(s32% $n:num) => `(Signed.ofNat (n := 32) $n)
| `(s64% $n:num) => `(Signed.ofNat (n := 64) $n)
