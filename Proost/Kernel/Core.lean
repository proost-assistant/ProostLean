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
    | .var i => s!"{i}"
    | .sort l => s!"Sort {l}"
    | .app t1 t2 => s!"({t1.toString}) ({t2.toString})"
    | .abs (some t1) t2 => s!"λ {t1.toString} => {t2.toString}"
    | .abs _ t2 => s!"λ _ => {t2.toString}"
    | .prod t1 t2  => s!"Π ({t1.toString}). {t2.toString}"
    | .const s _ => s
    | .ann t ty => s!"({t.toString} : {ty.toString})"

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
  | fvar : Nat → Neutral
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
deriving Repr

inductive Const  : Type:=
  | ax : Axiom → Const
  | de : Decl  → Const
deriving Repr

def Const.type : Const → Term
  | .ax a | .de a => a.type

def Const.n_of_univ : Const → Nat
  | .ax a | .de a => a.n_of_univ

abbrev ConstContext := HashMap String Const
abbrev VarContext := Array $ Option Term

structure TCContext where
  const_ctx : ConstContext := default
  var_ctx : VarContext := default
  debug : List String := []
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
    | .notDefEq t₁ t₂ => s!"{repr t₁} and {repr t₂} are not definitionally equal"
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

def add_trace (ty : String) (tr : String): TCEnv Unit := do
    if ty ∈ (← read).debug || "all" ∈ (← read).debug then dbg_trace s!"\n{tr}"

def with_add_const (name : String) (c : Const) (u : TCEnv α) : TCEnv α := do
    add_trace "cmd" s!"adding const {name} to the env"
    if let some _ := (← read).const_ctx.find? name then
      throw $  .alreadyDefined name
    withReader 
      (λ con : TCContext => 
        let res : TCContext := {const_ctx := con.const_ctx.insert name c}
        --dbg_trace s!"{repr res.const_ctx.toArray}"
        res
      )
      u

def with_add_decl (name : String) (d: Decl) : TCEnv α → TCEnv α := 
    with_add_const name (.de d)

def with_add_axiom (a : Axiom) : TCEnv α →  TCEnv α := 
    with_add_const a.name (.ax a)

def with_add_axioms (a : List Axiom) : TCEnv α → TCEnv α :=
  a.foldl (fun u ax => with_add_axiom ax u)

instance (priority := high) : MonadExceptOf TCError TCEnv where
  throw err := do
    dbg_trace s!"{err}"
    throw err
  tryCatch := tryCatch

def withadd_var_to_context_no_shift (t : Option Term) : TCEnv α →TCEnv α  :=
    withReader λ con => {con with var_ctx := con.var_ctx.push t}

class GetType (A: Type) where
  get_type : A → TCEnv Term

partial def Term.substitute_univ (lvl : Array Level) : Term → Term
  | sort l => sort $ l.substitute lvl
  | var n => var n
  | app t₁ t₂ => app (t₁.substitute_univ lvl) (t₂.substitute_univ lvl)
  | abs ty body => abs (ty.map (substitute_univ lvl)) (body.substitute_univ lvl)
  | prod a b => prod (a.substitute_univ lvl) (b.substitute_univ lvl)
  | ann t ty => ann (t.substitute_univ lvl) (ty.substitute_univ lvl) 
  | const s arr => const s $ arr.map (Level.substitute · lvl)

def get_const_type (s : String) (arr : Array Level): TCEnv Term := do
  let res := (← read).const_ctx.find? s
  let some $ c := res | throw $ .unknownConstant s
  if c.n_of_univ != arr.size then
    throw $ .wrongNumberOfUniverse s c.n_of_univ arr.size
  return c.type.substitute_univ arr --todo substitute univ
    
instance : GetType $ String × Array Level := ⟨uncurry get_const_type⟩

def get_var_type (n:Nat) : TCEnv Term := do
  let ctx := (← read).var_ctx
  let some optty := ctx.get? (ctx.size - n) | unreachable!
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
