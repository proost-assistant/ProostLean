import Proost
open Lean

def type_check_file (file : String) (debug : Bool): IO Unit := do
  let code ← IO.FS.readFile ⟨file⟩ 
  initSearchPath (← Lean.findSysroot) ["build/lib"]
  let env ← importModules [{ module := `Proost.Parser.ParseToRaw }] {}
  println! "parsing {file}"
  let raw ← IO.ofExcept $ parse code env
  println! "parsing succeeded !\n Term produced:\n  {raw}"
  println! "elaborating"
  let core ← IO.ofExcept $ raw.toCore
  println! "elaboration succeeded !\n Term produced:\n  {core}"
  let ctx : TCContext:= ⟨default,default,debug⟩
  let eval_commands := evalCommands core (pure ()) ctx
  if let .error e := eval_commands then
    throw $ IO.Error.userError $ ToString.toString e
  println! "success"

def main (args : List String) : IO Unit :=
  match args with
  | [] => return
  | h::t => do
    type_check_file h ("--debug" ∈ args)
    main t

#eval main ["tests\\connectives.mdln","--debug"]
