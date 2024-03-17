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

require std from git "https://github.com/leanprover/std4" @ "v4.6.1"
