import Lake
open Lake DSL

package numbers {
  -- add package configuration options here
}

lean_lib Numbers {
  -- add library configuration options here
}

-- @[defaultTarget]
lean_exe numbers {
  root := `Main
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.5.0"
