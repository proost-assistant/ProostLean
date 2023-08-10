import Proost.Kernel.Term

inductive Trace := 
  | Left
  | Right

class Traceable (A) where
  apply : A → Array Trace → A

class TraceableError (A) where
  trace_error : A → Trace → A

inductive TCKind : Type :=
  | unboundDeBruijnIndex : Nat → List Term → TCKind
  | unknownConstant : Name → TCKind
  | notASort : Term → TCKind
  | notDefEq : Term → Term → TCKind
  | wrongArgumentType : Term → Term → TypedTerm → TCKind
  --| notAFunction : Value → Value → TCError  
  -- meant for NBE, which is currently dead
  | notAFunction₂ : TypedTerm → Term → TCKind
  | unTypedVariable : Nat → VarContext → TCKind
  | cannotInfer : Term → TCKind
  | wrongNumberOfUniverse : Name → Nat → Nat → TCKind
  | alreadyDefined : Name → TCKind
deriving Repr

instance : ToString TCKind where
  toString
    | .unboundDeBruijnIndex n con => s!"unbound De Bruijn index {n} in context {con}"
    | .unknownConstant c => s!"unknown constant {c}"
    | .notASort t => s!"expected a sort, found {t}"
    | .notDefEq t₁ t₂ => s!"{t₁} \nand \n{t₂} \nare not definitionally equal"
    | .wrongArgumentType f exp (t,ty)=> s!"function {f} expects an argument of type {exp}, received argument {t} of type {ty}"
    | .cannotInfer t => s!"cannot infer type of term {t}"
    | .alreadyDefined s => s!"{s} is already defined"
    | .wrongNumberOfUniverse s n k => s!"wrong number of universes given, {s} expect {n} universes, received {k}"
    | .unTypedVariable v ctx => s!"unable to infer the type of variable {v} in context {ctx}"
    --| .notAFunction f x => s!"{f} is not a function but was given an argument {x}"
    | .notAFunction₂ (f,ty) x => s!"{f} : {ty} is not a function but was given an argument {x}"
      

structure WithTrace (A) where
  kind : A
  trace : Array Trace

instance [ToString A] : ToString (WithTrace A) where
  toString a := toString a.kind

abbrev TCError := WithTrace TCKind


instance : Coe A (WithTrace A) where
  -- Note : Array size initialized at 0, might be better to make it bigger ?
  coe := λ k => ⟨k,Array.empty⟩ 

abbrev Result := Except TCError

instance : TraceableError (Result A) where
  trace_error a tr :=
    a.mapError (λ err => {err with trace := err.trace.push tr})
    