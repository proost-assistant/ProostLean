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
  | varconst : String → Option (List RawLevel) → RawTerm
  | lam : String → Option RawTerm → RawTerm → RawTerm
  | pi : String → RawTerm → RawTerm → RawTerm
  | app : RawTerm → RawTerm → RawTerm
  | let : String → Option RawTerm → RawTerm → RawTerm → RawTerm
  | ann : RawTerm → RawTerm → RawTerm  

inductive RawError : Type :=
  | unboundLevelVar : String → RawError
