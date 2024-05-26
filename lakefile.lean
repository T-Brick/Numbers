import Lake
open Lake DSL

package numbers {
  -- add package configuration options here
}

lean_lib Numbers {
  -- add library configuration options here
}

@[default_target]
lean_exe numbers {
  root := `Main
}

require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.7.0"
