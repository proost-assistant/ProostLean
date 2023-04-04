import Lake
open Lake DSL

package proost

lean_lib Proost

@[default_target]
lean_exe proost where
  root := `Main

require std from git "https://github.com/leanprover/std4" @ "main"