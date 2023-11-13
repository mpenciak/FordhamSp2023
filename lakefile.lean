import Lake
open Lake DSL

package fordham

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.2.0"

require ffc from git
  "https://github.com/mpenciak/FFaCiL" @ "main"

@[default_target]
lean_lib Fordham
