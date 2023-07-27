import Lake
open Lake DSL

package proost

lean_lib Proost

@[default_target]
lean_exe proost where
  root := `Main
  supportInterpreter := true --needed to run the parser
  moreLeanArgs := #[
    "-DautoImplicit=false"]

lean_exe debug where
  root := `Main
  buildType := .debug
  supportInterpreter := true
  moreLeanArgs := #[
    "-DautoImplicit=false"]


require std from git "https://github.com/leanprover/std4" @ "dff883c55395438ae2a5c65ad5ddba084b600feb"