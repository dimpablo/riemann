import Lake
open Lake DSL

package «cascade»

lean_lib «Cascade» where
  -- add any library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

lean_exe «cascade» where
  root := `Main
