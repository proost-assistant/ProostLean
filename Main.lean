import Proost
open Lean

def type_check_file (file : String): IO Unit := do
  let code ← IO.FS.readFile ⟨file⟩ 
  initSearchPath (← Lean.findSysroot) ["build/lib"]
  let env ← importModules [{ module := `Proost.Parser.ParseToRaw }] {}
  println! "parsing {file}"
  let _stx ← IO.ofExcept $ parse code env
  println! "parsing succeeded !"
  return

def main : List String → IO Unit
  | [] => return
  | h::t => do
    type_check_file h
    main t

#eval main ["tests\\classical.mdln"]