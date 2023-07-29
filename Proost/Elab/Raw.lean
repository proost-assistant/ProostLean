import Proost.Util.Misc

inductive RawLevel : Type :=
  | num : Nat → RawLevel
  | var : String → RawLevel
  | plus : RawLevel → Nat → RawLevel
  | max : RawLevel → RawLevel → RawLevel
  | imax : RawLevel → RawLevel → RawLevel
deriving Repr

def RawLevel.toString : RawLevel → String
  | num n => s!"{n}"
  | var i => s!"{i}"
  | plus l n => s!"{l.toString} + {n}"
  | max l1 l2 => s!"max ({l1.toString}) ({l2.toString})"
  | imax l1 l2 => s!"imax ({l1.toString}) ({l2.toString})"

instance : ToString RawLevel := ⟨RawLevel.toString⟩  

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
deriving Repr, Inhabited

def RawTerm.toString : RawTerm → String
    | prop | sort none => "Prop"
    | type none => "Type"
    | type (some l) => s!"Type {l}"
    | sort (some l) => s!"Sort {l}"
    | varconst s #[] => s
    | varconst s arr => s ++ Array.toString₂ ".{" "," "}" arr
    | lam x none body => s!"λ {x} => {body.toString} "
    | lam x (some ty) body => s!"λ {x} : {ty.toString} => {body.toString}"
    | pi "_" ty body => s!"{ty.toString} → {body.toString}"
    | pi x ty body => s!"({x} : {ty.toString}) → {body.toString}"
    | app t1 t2 => s!"({t1.toString}) ({t2.toString})"
    | «let» x none t body => s!"let {x} := {t.toString} in {body.toString}"
    | «let» x (some ty) t body => s!"let {x}: {ty.toString} := {t.toString} in {body.toString}"
    | ann t ty => s!"({t.toString} : {ty.toString})"

instance : ToString RawTerm := ⟨RawTerm.toString⟩  

inductive RawCommand : Type :=
  | def : String → Array String → List (Array String × RawTerm) → Option RawTerm → RawTerm → RawCommand
  | axiom : String → Array String → RawTerm → RawCommand
  | check : RawTerm → RawCommand
  | eval : RawTerm → RawCommand
deriving Repr

instance : ToString RawCommand where
  toString 
    | .def s _ _todo none t => s!"def {s} := {t}"
    | .def s _ _todo (some ty) t => s!"def {s} : {ty} := {t}"
    | .axiom s _ ty => s!"axiom {s} : {ty}"
    | .check t => s!"check {t}"
    | .eval t => s!"eval {t}"

abbrev RawCommands := List RawCommand

inductive RawError : Type :=
  | duplicateUniverseVar : String → RawError
  | unboundLevelVar : String → RawError
deriving Repr

instance : ToString RawError where
  toString
    | .duplicateUniverseVar s => s!"Error : duplicate universe variable {s}"
    | .unboundLevelVar s => s!"Error : unbound universe variable {s}"
