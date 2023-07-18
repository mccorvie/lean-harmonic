import Lake
open Lake DSL

package «lean-harmonic» {
  -- add package configuration options here
}

lean_lib «LeanHarmonic» {
  -- add library configuration options here
}
require mathlib from git
  "https://github.com/leanprover-community/mathlib4"



@[default_target]
lean_exe «lean-harmonic» {
  root := `Main
}
