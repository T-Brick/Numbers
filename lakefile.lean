import Lake
open Lake DSL

package number {
  -- add package configuration options here
}

lean_lib Number {
  -- add library configuration options here
}

-- @[defaultTarget]
lean_exe number {
  root := `Main
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.3.0-rc1"
