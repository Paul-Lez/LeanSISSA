import Lake

open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.31.0"

require «verso-slides» from git
  "https://github.com/leanprover/verso-slides.git"@"f3a071c24d67e5ca812cdb929a77e0aefd627bf5"

package LeanSISSASite where
  version := v!"0.1.0"

@[default_target]
lean_exe leanSISSASite where
  root := `Main
