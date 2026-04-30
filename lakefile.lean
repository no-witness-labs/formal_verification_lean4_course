import Lake
open Lake DSL

package "FormalVerification" where
  version := v!"0.1.0"

require Blaster from git
  "https://github.com/input-output-hk/Lean-blaster.git" @ "main"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.24.0"

@[default_target]
lean_lib «FormalVerification» where
  -- add library configuration options here
