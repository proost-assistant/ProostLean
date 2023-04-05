inductive RawLevel : Type :=
  | num : Nat → RawLevel
  | var : String → RawLevel
  | plus : RawLevel → Nat → RawLevel
  | max : RawLevel → RawLevel → RawLevel
  | imax : RawLevel → RawLevel → RawLevel

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

inductive RawCommand : Type :=
  | def : String → Array String → Option RawTerm → RawTerm → RawCommand
  | axiom : String → Array String → RawTerm → RawCommand
  | check : RawTerm → RawCommand
  | eval : RawTerm → RawCommand

inductive RawError : Type :=
  | unboundLevelVar : String → RawError
