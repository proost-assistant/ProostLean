inductive RawLevel : Type :=
  | num : Nat → RawLevel
  | var : String → RawLevel
  | plus : RawLevel → Nat → RawLevel
  | max : RawLevel → RawLevel → RawLevel
  | imax : RawLevel → RawLevel → RawLevel
deriving Repr

inductive RawTerm : Type :=
  | prop
  | type : Option RawLevel → RawTerm
  | sort : Option RawLevel → RawTerm
  -- either a var or a const, this will get determined when translating to the core syntax
  | varconst : String → Array RawLevel → RawTerm
  | lam : String → Option RawTerm → RawTerm → RawTerm
  | pi : String → RawTerm → RawTerm → RawTerm
  | app : RawTerm → RawTerm → RawTerm
  | let : String → Option RawTerm → RawTerm → RawTerm → RawTerm
  | ann : RawTerm → RawTerm → RawTerm  
deriving Repr

inductive RawCommand : Type :=
  | def : String → List String → Option RawTerm → RawTerm → RawCommand
  | axiom : String → List String → RawTerm → RawCommand
  | check : RawTerm → RawCommand
  | eval : RawTerm → RawCommand
deriving Repr

def RawCommands := List RawCommand

inductive RawError : Type :=
  | duplicateUniverseVar : String → RawError
  | unboundLevelVar : String → RawError
deriving Repr

instance : ToString RawError where
  toString
    | .duplicateUniverseVar s => s!"Error : duplicate universe variable {s}"
    | .unboundLevelVar s => s!"Error : unbound universe variable {s}"
