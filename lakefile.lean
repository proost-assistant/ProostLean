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


require std from git "https://github.com/leanprover/std4" @ "28459f72f3190b0f540b49ab769745819eeb1c5e"

require Cli from git "https://github.com/mhuisi/lean4-cli" @ "21dac2e9cc7e3cf7da5800814787b833e680b2fd"
