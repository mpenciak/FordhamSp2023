import Lake
open Lake DSL

package fordham 

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require YatimaStdLib from git
  "https://github.com/lurk-lab/YatimaStdLib.lean" @ "main"

@[default_target]
lean_lib Fordham 
