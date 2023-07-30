import Proost
open Lean

def type_check_file (file : String) (opts : CallOptions): IO Unit := do
  let code ← timeit "Reading file:" $ IO.FS.readFile ⟨file⟩ 
  initSearchPath (← Lean.findSysroot) ["build/lib"]
  let env ← importModules [{ module := `Proost.Parser.ParseToRaw }] {}
  --println! "parsing {file}"
  let raw ← timeit "Parsing :" $ IO.ofExcept $ parse code env
  --println! "parsing succeeded !\n Commands produced:\n  {raw}"
  --println! "elaborating"
  let core ← timeit "Elaborating:" $  IO.ofExcept $ raw.toCore
  --println! "elaboration succeeded !\n Term produced:\n  {core}"
  timeit "Type-checking :" $ do
    let ctx : TCContext := {debug := opts.1}
    let eval_commands := 
      (with_initialize_env_axioms <| evalCommands core)
      ctx
    if let .error e := eval_commands then
      throw $ IO.Error.userError $ ToString.toString e
    else println! s!"Successfully type-checked {file}."

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

def main (args : List String) : IO Unit := do
  let options := ⟨["all","print"]⟩
  for file in  args  do
    --println! s!"checking {file}"
    type_check_file file options

