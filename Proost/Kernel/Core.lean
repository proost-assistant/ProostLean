import Proost.Kernel.Level
import Std.Data.HashMap
import Proost.Util.Misc

open Std

inductive Term : Type :=
  | var   : Nat → Term
  | sort  : Level → Term
  | app   : Term → Term → Term
  | abs   : Option Term → Term → Term
  | prod  : Term → Term → Term
  | const : String → Array Level →  Term
  | ann   : Term → Term → Term
deriving Repr, Inhabited, BEq

def Term.n_of_univ : Term → Nat 
  | .var _ => 0
  | .abs t₁ t₂ => 
    let t₁_univ := match t₁ with | some t => t.n_of_univ | none => 0
    max t₁_univ t₂.n_of_univ
  | .app t₁ t₂ 
  | .ann t₁ t₂
  | .prod t₁ t₂ => max t₁.n_of_univ t₂.n_of_univ
  | .const _ arr => arr.foldl (fun acc l => max acc l.n_of_univ) 0
  | .sort l => l.n_of_univ

def Term.prop : Term := .sort 0
def Term.type (l : Level) : Term := .sort l.succ

def Term.toString : Term → String
    | .var i => ToString.toString i
    | .sort l => "Sort "++ ToString.toString l
    | .app t1 t2 => "(" ++ t1.toString ++ ") (" ++ t2.toString ++ ")"
    | .abs (some t1) t2 => "λ " ++ t1.toString ++ " => " ++ t2.toString
    | .abs _ t2 => "λ _ => "++ t2.toString
    | .prod t1 t2  => "Π " ++ t1.toString ++ "." ++ t2.toString
    | .const s #[]=> s
    | .const s l => s ++ ToString.toString l
    | .ann t ty => "(" ++ t.toString ++ " : " ++ ty.toString ++ ")"

instance : ToString Term := ⟨Term.toString⟩

structure Axiom where
  name : String
  type : Term
  n_of_univ : Nat := type.n_of_univ
deriving BEq, Repr

structure AppClosure (Values : Type): Type where
  term : Term
  closure : List Values
deriving BEq,Repr

inductive Neutral : Type :=
  | var : Nat → Neutral
  | ax : Axiom → Array Level → Neutral
deriving BEq, Repr

inductive Value : Type :=
  | neutral : Neutral → List Value → Value
  | sort : Level → Value
  | abs : Option Value → AppClosure Value → Value
  | prod : Value → AppClosure Value → Value
deriving Inhabited, BEq, Repr

instance : ToString Value := ⟨reprStr⟩

def Value.var (n : Nat) : Value := .neutral (.var n) []

structure Decl : Type where
  type : Term
  n_of_univ : Nat
  term : Term

inductive Const  : Type:=
  | ax : Axiom → Const
  | de : Decl  → Const

def Const.type : Const → Term
  | .ax a | .de a => a.type

def Const.n_of_univ : Const → Nat
  | .ax a | .de a => a.n_of_univ

abbrev ConstContext := HashMap String Const
abbrev VarContext := Array $ Option Term

structure TCContext where
  const_con : ConstContext
  var_cont : VarContext
  debug : Bool := false
deriving Inhabited


abbrev TypedTerm := Term × Term

inductive TCError : Type :=
  | unboundDeBruijnIndex : Nat → List Term → TCError
  | unknownConstant : String → TCError
  | notASort : Term → TCError
  | notDefEq : Term → Term → TCError
  | wrongArgumentType : Term → Term → TypedTerm → TCError
  | notAFunction : Value → Value → TCError
  | notAFunction₂ : TypedTerm → Term → TCError
  | unTypedVariable : Nat → VarContext → TCError
  | cannotInfer : Term → TCError
  | wrongNumberOfUniverse : String → Nat → Nat → TCError
  | alreadyDefined : String → TCError
deriving Repr

instance : ToString TCError where
  toString
    | .unboundDeBruijnIndex n con => s!"unbound De Bruijn index {n} in context {con}"
    | .unknownConstant c => s!"unknown constant {c}"
    | .notASort t => s!"expected a sort, found {t}"
    | .notDefEq t₁ t₂ => s!"{t₁} and {t₂} are not definitionally equal"
    | .wrongArgumentType f exp (t,ty)=> s!"function {f} expects an argument of type {exp}, received argument {t} of type {ty}"
    | .cannotInfer t => s!"cannot infer type of term {t}"
    | .alreadyDefined s => s!"{s} is already defined"
    | .wrongNumberOfUniverse s n k => s!"wrong number of universes given, {s} expect {n} universes, received {k}"
    | .unTypedVariable v ctx => s!"unable to infer the type of variable {v} in context {ctx}"
    | .notAFunction f x => s!"{f} is not a function but was given an argument {x}"
    | .notAFunction₂ (f,ty) x => s!"{f} : {ty} is not a function but was given an argument {x}"
      
abbrev Result (A) := Except TCError A

abbrev TCEnv := ReaderT TCContext (Except TCError)

def EStateM.Result.get : EStateM.Result ε σ α → σ
  | .ok _ st
  | .error _ st => st

def add_trace (tr : String): TCEnv Unit := do
    if (← read).debug then dbg_trace tr

def with_add_const (name : String) (c : Const) (u : TCEnv α) : TCEnv α := do
    if let some _ := (← read).const_con.find? name then
      throw $  .alreadyDefined name
    withReader (λ con => {con with const_con := HashMap.insert con.const_con name c}) u

def with_add_decl (name : String) (d: Decl) (u : TCEnv α)  :  TCEnv α := 
    with_add_const name (.de d) u

def with_add_axiom (a : Axiom) (u : TCEnv α)  :  TCEnv α := do
    with_add_const a.name (.ax a) u

def with_add_axioms (a : List Axiom) (u : TCEnv α) : TCEnv α := do
  a.foldlM (fun u ax => with_add_axiom ax (pure u)) (← u)

instance (priority := high) : MonadExceptOf TCError TCEnv where
  throw err := do
    dbg_trace s!"{err}"
    throw err
  tryCatch := tryCatch

def withadd_var_to_context_no_shift (t : Option Term) : TCEnv α →TCEnv α  :=
    withReader λ con => {con with var_cont := con.var_cont.push t}

def reduce_decl (s : String) : TCEnv Term := do
  let res := (← read).const_con.find? s
  if let some $ .de d := res then
    return d.term
  else
    throw $ .unknownConstant s

class GetType (A: Type) where
  get_type : A → TCEnv Term

def get_const_type (s : String) (arr : Array Level): TCEnv Term := do
  let res := (← read).const_con.find? s
  if let some $ c := res then
    if c.n_of_univ != arr.size then
      throw $ .wrongNumberOfUniverse s c.n_of_univ arr.size
    return c.type
  else
    throw $ .unknownConstant s
instance : GetType $ String × Array Level := ⟨uncurry get_const_type⟩

def get_var_type (n:Nat) : TCEnv Term := do
  let ctx := (← read).var_cont
  let some optty := ctx.get? (ctx.size - n - 1) | unreachable!
  let some ty := optty | throw $ .unTypedVariable n ctx
  pure ty
instance : GetType $ Nat := ⟨get_var_type⟩

inductive Command : Type :=
  | def : String → Nat → Option Term → Term → Command
  | axiom : String → Nat → Term → Command
  | check : Term → Command
  | eval : Term → Command
deriving Repr

instance : ToString Command where
  toString 
    | .def s _ none t => s!"def {s} := {t}"
    | .def s _ (some ty) t => s!"def {s} : {ty} := {t}"
    | .axiom s _ ty => s!"axiom {s} : {ty}"
    | .check t => s!"check {t}"
    | .eval t => s!"eval {t}"

abbrev Commands := List Command
