import Lake
open Lake DSL

package proostLean 

lean_lib ProostLean 

@[default_target]
lean_exe proostLean where
  root := `Main

require std from git "https://github.com/leanprover/std4" @ "main"