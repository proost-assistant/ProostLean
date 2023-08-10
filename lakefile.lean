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
  moreLeancArgs := #["-pg","-O0","-g"]


require Std from git "https://github.com/leanprover/std4" @ "17c3833ab170ce20fd065ae3fb550300b3d85f23"

require Cli from git "https://github.com/mhuisi/lean4-cli" @ "nightly"