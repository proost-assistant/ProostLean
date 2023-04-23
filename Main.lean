import Proost
open Lean

def type_check_file (file : String) (opts : CallOptions): IO Unit := do
  let code ← IO.FS.readFile ⟨file⟩ 
  initSearchPath (← Lean.findSysroot) ["build/lib"]
  let env ← importModules [{ module := `Proost.Parser.ParseToRaw }] {}
  println! "parsing {file}"
  let raw ← IO.ofExcept $ parse code env
  println! "parsing succeeded !\n Term produced:\n  {raw}"
  println! "elaborating"
  let core ← IO.ofExcept $ raw.toCore
  println! "elaboration succeeded !\n Term produced:\n  {core}"
  let ctx : TCContext:= ⟨default,default,opts.debug⟩
  let eval_commands := evalCommands core ctx
  if let .error e := eval_commands then
    throw $ IO.Error.userError $ ToString.toString e
  println! "success"

structure Main_call where
  files : List String
  options : List (String × List String)

def get_options (input : String) : Main_call := Id.run do
  let split := input.splitOn "--" |>.map (·.splitOn)
  let files::options := split | ⟨[],[]⟩
  let options := options.map (λ l => match l with
    | opt::args => (opt,args)
    | [] => panic! "unexpected input"
  ) 
  ⟨files,options⟩

def main : IO Unit := do
  let line ← IO.getStdin
  let line ← line.getLine
  let ⟨files,_options⟩ := get_options line
  let options := default
  for file in  files  do
    type_check_file file options

--#eval main ["tests/connectives.mdln"]
