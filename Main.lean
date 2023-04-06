import Proost
open Lean

def type_check_file (file : String): IO Unit := do
  let code ← IO.FS.readFile ⟨file⟩ 
  initSearchPath (← Lean.findSysroot) ["build/lib"]
  let env ← importModules [{ module := `Proost.Parser.ParseToRaw }] {}
  println! "parsing {file}"
  let raw ← IO.ofExcept $ parse code env
  println! "parsing succeeded !"
  println! "elaborating"
  let core ← IO.ofExcept $ raw.toCore
  println! "elaboration succeeded !\n Term produced:\n  {repr core}"
  let eval_commands := evalCommands core default
  if let .error e _ := eval_commands then
    throw $ IO.Error.userError $ ToString.toString e
  println! "success"


def main : List String → IO Unit
  | [] => return
  | h::t => do
    type_check_file h
    main t

#eval main ["tests\\connectives.mdln"]