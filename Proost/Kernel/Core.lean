import Proost.Kernel.Level
import Std.Data.HashMap
import Proost.Util.Misc
import Proost.Kernel.Term
import Proost.Kernel.Error

open Std

structure ConstantVal where
  name : Name
  type : Term
  levelParamsNum : Nat := type.n_of_univ
deriving Repr, Inhabited

abbrev AxiomVal := ConstantVal

structure DefinitionVal extends ConstantVal where
  term : Term
deriving Repr


structure ConstructorVal extends ConstantVal where
  /-- Inductive type this constructor is a member of -/
  induct  : Name
  /-- Constructor index (i.e., Position in the inductive declaration) -/
  cidx    : Nat
  /-- Number of parameters in inductive datatype. -/
  numParams : Nat
  /-- Number of fields (i.e., arity - nparams) -/
  numFields : Nat
  deriving Inhabited


structure InductiveVal extends ConstantVal where
  /-- Number of parameters. A parameter is an argument to the defined type that is fixed over constructors.
  An example of this is the `α : Type` argument in the vector constructors
  `nil : Vector α 0` and `cons : α → Vector α n → Vector α (n+1)`.

  The intuition is that the inductive type must exhibit _parametric polymorphism_ over the inductive
  parameter, as opposed to _ad-hoc polymorphism_.
  -/
  numParams : Nat
  /-- Number of indices. An index is an argument that varies over constructors.

  An example of this is the `n : Nat` argument in the vector constructor `cons : α → Vector α n → Vector α (n+1)`.
  -/
  numIndices : Nat
  /-- List of all (including this one) inductive datatypes in the mutual declaration containing this one -/
  all : List Name
  /-- List of the names of the constructors for this inductive datatype. -/
  ctors : List Name
  /-- `true` when recursive (that is, the inductive type appears as an argument in a constructor). -/
  isRec : Bool
  /-- An inductive type is called reflexive if it has at least one constructor that takes as an argument a function returning the
  same type we are defining.-/
  isReflexive : Bool
  /-- An inductive definition `T` is nested when there is a constructor with an argument `x : F T`,
   where `F : Type → Type` is some suitably behaved (ie strictly positive) function (Eg `Array T`, `List T`, `T × T`, ...). -/
  isNested : Bool
  deriving Inhabited

/-- Information for reducing a recursor -/
structure RecursorRule where
  /-- Reduction rule for this Constructor -/
  ctor : Name
  /-- Number of fields (i.e., without counting inductive datatype parameters) -/
  nfields : Nat
  /-- Right hand side of the reduction rule -/
  rhs : Term
  deriving Inhabited


structure RecursorVal extends ConstantVal where
  /-- List of all inductive datatypes in the mutual declaration that generated this recursor -/
  all : List Name
  /-- Number of parameters -/
  numParams : Nat
  /-- Number of indices -/
  numIndices : Nat
  /-- Number of motives -/
  numMotives : Nat
  /-- Number of minor premises -/
  numMinors : Nat
  /-- A reduction for each Constructor -/
  rules : List RecursorRule
  /-- Supports singleton elimination ? -/
  k : Bool
  deriving Inhabited

namespace RecursorVal
 
def getMajorIdx (v : RecursorVal) : Nat :=
  v.numParams + v.numMotives + v.numMinors + v.numIndices

def getFirstIndexIdx (v : RecursorVal) : Nat :=
  v.numParams + v.numMotives + v.numMinors

def getFirstMinorIdx (v : RecursorVal) : Nat :=
  v.numParams + v.numMotives

def getInduct (v : RecursorVal) : Name :=
  v.all.head!

end RecursorVal


inductive Declaration where
  | axiomDecl       (val : AxiomVal)
  | defnDecl        (val : DefinitionVal)
  | ctorDecl        (val : ConstructorVal)
  | inductDecl      (var : InductiveVal)
  | recursorDecl    (val : RecursorVal)
deriving Inhabited

namespace Declaration 

def toConstantVal : Declaration → ConstantVal
  | axiomDecl    d => d
  | defnDecl     {toConstantVal := d, ..} => d
  | inductDecl   {toConstantVal := d, ..} => d
  | ctorDecl     {toConstantVal := d, ..} => d
  | recursorDecl {toConstantVal := d, ..} => d

def name : Declaration → Name := 
  ConstantVal.name ∘ Declaration.toConstantVal 

def type : Declaration → Term :=
  ConstantVal.type ∘ Declaration.toConstantVal

def levelParamsNum : Declaration → Nat :=
  ConstantVal.levelParamsNum ∘ Declaration.toConstantVal 

instance : Repr Declaration where
  reprPrec d := Repr.reprPrec d.name

instance : Coe AxiomVal Declaration := ⟨axiomDecl⟩ 
instance : Coe DefinitionVal Declaration := ⟨defnDecl⟩ 
instance : Coe InductiveVal Declaration := ⟨inductDecl⟩ 
instance : Coe ConstructorVal Declaration := ⟨ctorDecl⟩ 
instance : Coe RecursorVal Declaration := ⟨recursorDecl⟩ 

end Declaration

abbrev ConstContext := HashMap Name Declaration

structure TCContext where
  fvar_count : Nat := 0
  const_ctx : ConstContext := default
  var_ctx : VarContext := default
  debug : Array String := #[]
deriving Inhabited

abbrev TCEnv := ReaderT TCContext Result

open TCKind

def add_trace (ty : String) (tr : String): TCEnv Unit := do
    if (← read).debug.any (λ d => d = ty || d = "all") then 
      dbg_trace tr

def with_add_const (name : Name) (c : Declaration) (u : TCEnv α) : TCEnv α := do
    add_trace "cmd" s!"adding const {name} to the env"
    if let some _ := (← read).const_ctx.find? name then
      throw ↑(alreadyDefined name)
    withReader (λ con => {con with const_ctx := con.const_ctx.insert name c})
      u

def with_add_decl (d: Declaration) : TCEnv α → TCEnv α := 
    with_add_const d.name d

def with_add_def (d: DefinitionVal) : TCEnv α → TCEnv α := 
    with_add_const d.name d

def with_add_axiom (a : AxiomVal) : TCEnv α →  TCEnv α := 
    with_add_const a.name a

def with_add_axioms (a : List Declaration) : TCEnv α → TCEnv α :=
  a.foldl (fun u ax => with_add_decl ax u)

-- Overwrites the MonadExceptOf to print the errors
-- TODO have better error management
instance (priority := high) : MonadExceptOf TCError TCEnv where
  throw err := do
    dbg_trace s!"{err}"
    throw err
  tryCatch := tryCatch

def withadd_var_to_context_no_shift (t : Option Term) : TCEnv α →TCEnv α  :=
    withReader λ con => {con with var_ctx := con.var_ctx.push t}

class GetType (A: Type) where
  get_type : A → TCEnv Term

def get_const_decl? (s : Name) : TCEnv (Option Declaration) := do
  return (← read).const_ctx.find? s
  
def get_const_type (s : Name) (arr : Array Level): TCEnv Term := do
  let res := (← read).const_ctx.find? s
  let some c := res | throw $ ↑(unknownConstant s)
  if c.levelParamsNum != arr.size then
    throw ↑(wrongNumberOfUniverse s c.levelParamsNum arr.size)
  return c.type.substitute_univ arr
    
instance : GetType $ String × Array Level := ⟨uncurry get_const_type⟩

def get_var_type (n:Nat) : TCEnv Term := do
  let ctx := (← read).var_ctx
  let some optty := ctx.get? (ctx.size - n) | panic! s!"unknown free var {n}"
  let some ty := optty | throw ↑(unTypedVariable n ctx)
  pure ty
instance : GetType $ Nat := ⟨get_var_type⟩

@[inline] def matchConstAux {α} (e : Term) (failK : Unit → TCEnv α) (k : Declaration → Array Level → TCEnv α) : TCEnv α :=
  match e with
  | .const name lvls => do
    let (some cinfo) ← get_const_decl? name | failK ()
    k cinfo lvls
  | _ => failK ()


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
@[extern "infer"]  opaque infer : Term → TCEnv Term
@[extern "conversion"] opaque conversion : Term → Term → TCEnv Bool
@[extern "isDefEq"] opaque isDefEq : Term → Term → TCEnv Unit

instance : CoeFun Term (λ _ => Term → Term) where
  coe := Term.app
