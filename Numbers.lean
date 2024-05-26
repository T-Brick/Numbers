import Numbers.IntRepr
import Numbers.IntOps
import Numbers.Notation

open Numbers

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
