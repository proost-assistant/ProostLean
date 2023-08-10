import Proost
import Cli
open Cli

open Lean

def type_check_file (file : String) (opts : Array String): IO Unit := do
  let code ← timeit "Reading file:" $ IO.FS.readFile ⟨file⟩ 
  initSearchPath (← Lean.findSysroot) ["build/lib"]
  let env ← importModules [{ module := `Proost.Parser.ParseToRaw }] {}
  --println! "parsing {file}"
  let raw ← timeit "Parsing :" $ IO.ofExcept $ parse code env
  --println! "parsing succeeded !\n Commands produced:\n  {raw}"
  --println! "elaborating"
  let core ← timeit "Elaborating:" $  IO.ofExcept $ raw.toCore
  println! "elaboration succeeded !\n Term produced:\n  {core}"
  timeit "Type-checking :" $ do
    let ctx : TCContext := {debug := opts}
    let eval_commands := 
      (with_initialize_env_axioms <| evalCommands core)
      ctx
    if let .error e := eval_commands then
      throw $ IO.Error.userError $ ToString.toString e
    else println! s!"Successfully type-checked {file}."

def runProostCmd (p : Parsed) : IO UInt32 := do
  let args := p.positionalArg! "input" |>.as! (Array String)
  let flags := Id.run do
    let some flags := p.flag? "priority"  | #[]
      flags.as! (Array String)
  for file in  args  do
    --println! s!"checking {file}"
    type_check_file file flags
  return  0

def proostCmd : Cmd := `[Cli|
  proostCmd VIA runProostCmd; ["0.0.1"]
  "This string denotes the description of `exampleCmd`."

  FLAGS:
    v, verbose : Array String; "Add verbose flags" ++
                               "flags : all, tc, cmd, print, nbe"

  ARGS:
    inputs : Array String; "Declares a positional argument <input> " ++
                           "that takes an argument of type `String`."

  -- The EXTENSIONS section denotes features that
  -- were added as an external extension to the library.
  -- `./Cli/Extensions.lean` provides some commonly useful examples.
  EXTENSIONS:
    author "arthur-adjedj";
    defaultValues! #[("priority", "0")]
]




def main (args : List String) : IO UInt32 := do
  proostCmd.validate args

