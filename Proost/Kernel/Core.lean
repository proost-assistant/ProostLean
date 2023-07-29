import Proost.Kernel.Level
import Std.Data.HashMap
import Proost.Util.Misc

open Std

abbrev Name := String

inductive Term : Type :=
  | var   : Nat → Term
  | sort  : Level → Term
  | app   : Term → Term → Term
  | abs   : Option Term → Term → Term
  | prod  : Term → Term → Term
  | const : Name → Array Level →  Term
  | ann   : Term → Term → Term
deriving Repr, Inhabited, BEq

namespace Term

def getAppFn : Term →  Term
  | .app f _ => f.getAppFn
  | t => t

def getAppArgs : Term → Array Term
  | .app f arg => f.getAppArgs.push arg
  | _ => #[]

def getAppFnArgs : Term →  Term × Array Term
  | .app f arg =>
    let ⟨f,args⟩ := f.getAppFnArgs
    ⟨f,args.push arg⟩
  | t => ⟨t,#[]⟩

def mkAppN : Term → Array Term → Term := fun hd arr =>
  arr.foldl (λ f x => app f x) hd

def n_of_univ : Term → Nat 
  | .var _ => 0
  | .abs t₁ t₂ => 
    let t₁_univ := match t₁ with | some t => t.n_of_univ | none => 0
    max t₁_univ t₂.n_of_univ
  | .app t₁ t₂ 
  | .ann t₁ t₂
  | .prod t₁ t₂ => max t₁.n_of_univ t₂.n_of_univ
  | .const _ arr => arr.foldl (fun acc l => max acc l.n_of_univ) 0
  | .sort l => l.n_of_univ

def prop : Term := .sort 0
def type (l : Level) : Term := .sort l.succ

def toString : Term → String
    | .var i => s!"{i}"
    | .sort l => s!"Sort {l}"
    | .app t1 t2 => s!"({t1.toString}) ({t2.toString})"
    | .abs (some t1) t2 => s!"λ {t1.toString} => {t2.toString}"
    | .abs _ t2 => s!"λ _ => {t2.toString}"
    | .prod t1 t2  => s!"Π ({t1.toString}). {t2.toString}"
    | .const s #[] => s
    | .const s arr => s ++ Array.toString₂ ".{" "," "}" arr
    | .ann t ty => s!"({t.toString} : {ty.toString})"

instance : ToString Term := ⟨Term.toString⟩

partial def substitute_univ (lvl : Array Level) : Term → Term
  | sort l => sort $ l.substitute lvl
  | var n => var n
  | app t₁ t₂ => app (t₁.substitute_univ lvl) (t₂.substitute_univ lvl)
  | abs ty body => abs (ty.map (substitute_univ lvl)) (body.substitute_univ lvl)
  | prod a b => prod (a.substitute_univ lvl) (b.substitute_univ lvl)
  | ann t ty => ann (t.substitute_univ lvl) (ty.substitute_univ lvl) 
  | const s arr => const s $ arr.map (Level.substitute · lvl)

end Term

structure ConstantVal where
  name : Name
  type : Term
  levelParamsNum : Nat := type.n_of_univ
deriving Repr, Inhabited

abbrev AxiomVal := ConstantVal

structure DefinitionVal extends ConstantVal where
  term : Term
deriving Repr

inductive Declaration where
  | axiomDecl       (val : AxiomVal)
  | defnDecl        (val : DefinitionVal)
  --| inductDecl      (lparams : List Name) (nparams : Nat) (types : List InductiveType) (isUnsafe : Bool)
deriving Inhabited, Repr

def Declaration.name : Declaration → Name
  | axiomDecl a => a.name
  | defnDecl d  => d.name

def Declaration.type : Declaration → Term
  | axiomDecl a => a.type
  | defnDecl d  => d.type

def Declaration.levelParamsNum : Declaration → Nat
  | axiomDecl a => a.levelParamsNum
  | defnDecl d  => d.levelParamsNum

/-
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

def Value.var (n : Nat) : Value := .neutral (.var n) [] -/

abbrev ConstContext := HashMap Name Declaration
abbrev VarContext := Array $ Option Term

structure TCContext where
  const_ctx : ConstContext := default
  var_ctx : VarContext := default
  debug : List String := []
deriving Inhabited

abbrev TypedTerm := Term × Term

inductive TCError : Type :=
  | unboundDeBruijnIndex : Nat → List Term → TCError
  | unknownConstant : Name → TCError
  | notASort : Term → TCError
  | notDefEq : Term → Term → TCError
  | wrongArgumentType : Term → Term → TypedTerm → TCError
  --| notAFunction : Value → Value → TCError
  | notAFunction₂ : TypedTerm → Term → TCError
  | unTypedVariable : Nat → VarContext → TCError
  | cannotInfer : Term → TCError
  | wrongNumberOfUniverse : Name → Nat → Nat → TCError
  | alreadyDefined : Name → TCError
deriving Repr

instance : ToString TCError where
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
      
abbrev Result (A) := Except TCError A

abbrev TCEnv := ReaderT TCContext (Except TCError)

def EStateM.Result.get : EStateM.Result ε σ α → σ
  | .ok _ st
  | .error _ st => st

def add_trace (ty : String) (tr : String): TCEnv Unit := do
    if ty ∈ (← read).debug || "all" ∈ (← read).debug then dbg_trace tr

def with_add_const (name : Name) (c : Declaration) (u : TCEnv α) : TCEnv α := do
    --add_trace "cmd" s!"adding const {name} to the env"
    if let some _ := (← read).const_ctx.find? name then
      throw $  .alreadyDefined name
    withReader 
      (λ con : TCContext => 
        let res : TCContext := {const_ctx := con.const_ctx.insert name c}
        --dbg_trace s!"{repr res.const_ctx.toArray}"
        res
      )
      u

def with_add_decl (d: DefinitionVal) : TCEnv α → TCEnv α := 
    with_add_const d.name (.defnDecl d)

def with_add_axiom (a : AxiomVal) : TCEnv α →  TCEnv α := 
    with_add_const a.name (.axiomDecl a)

def with_add_axioms (a : List AxiomVal) : TCEnv α → TCEnv α :=
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

def get_const_type (s : Name) (arr : Array Level): TCEnv Term := do
  let res := (← read).const_ctx.find? s
  let some c := res | throw $ .unknownConstant s
  if c.levelParamsNum != arr.size then
    throw $ .wrongNumberOfUniverse s c.levelParamsNum arr.size
  return c.type.substitute_univ arr --todo substitute univ
    
instance : GetType $ String × Array Level := ⟨uncurry get_const_type⟩

def get_var_type (n:Nat) : TCEnv Term := do
  let ctx := (← read).var_ctx
  let some optty := ctx.get? (ctx.size - n) | panic! s!"unknown free var {n}"
  let some ty := optty | throw $ .unTypedVariable n ctx
  pure ty
instance : GetType $ Nat := ⟨get_var_type⟩

inductive Command : Type :=
  | def : Name → Nat → Option Term → Term → Command
  | axiom : Name → Nat → Term → Command
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

@[extern "proost_whnf"] opaque whnf : Term → TCEnv Term
--@[extern "infer"]  opaque infer : Term → TCEnv Term
@[extern "isDefEq"] opaque isDefEq : Term → Term → TCEnv Unit