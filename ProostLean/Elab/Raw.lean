inductive RawLevel : Type :=
  | num : Nat → RawLevel
  | var : String → RawLevel
  | plus : RawLevel → Nat → RawLevel
  | max : RawLevel → RawLevel → RawLevel
  | imax : RawLevel → RawLevel → RawLevel

inductive RawSyntax : Type :=
  | prop
  | type : Option RawLevel → RawSyntax
  | sort : Option RawLevel → RawSyntax
  -- either a var or a const, this will get determined when translating to the core syntax
  | varconst : String → Option (List RawLevel) → RawSyntax
  | lam : String → Option RawSyntax → RawSyntax → RawSyntax
  | pi : String → RawSyntax → RawSyntax → RawSyntax
  | app : RawSyntax → RawSyntax → RawSyntax
  | let : String → Option RawSyntax → RawSyntax → RawSyntax → RawSyntax
  | ann : RawSyntax → RawSyntax → RawSyntax  
