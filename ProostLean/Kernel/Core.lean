import ProostLean.Kernel.Level
import Std.Data.HashMap
import ProostLean.Util.Misc

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
  n_of_univ : Nat
deriving BEq,Repr

structure AppClosure (Values : Type): Type where
  term : Term
  closure : List Values
deriving BEq,Repr

inductive Neutral : Type :=
  | var : Nat → Neutral
  | ax : Axiom → Array Level → Neutral
deriving BEq,Repr

inductive Value : Type :=
  | neutral : Neutral → List Value → Value
  | sort : Level → Value
  | abs : Option Value → AppClosure Value → Value
  | prod : Value → AppClosure Value → Value
deriving Inhabited, BEq,Repr

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

deriving instance Repr for Queue
structure TCContext where
  trace     : List String
  const_con : ConstContext
  var_cont : VarContext
deriving Inhabited


abbrev TypedTerm := Term × Term

inductive TCError : Type :=
  | unboundDeBruijnIndex : Nat → List Term → TCError
  | unknownConstant : String → TCError
  | notUniverse : Term → TCError
  | notDefEq : Term → Term → TCError
  | wrongArgumentType : Term → Term → TypedTerm → TCError
  | notAFunction : Value → Value → TCError
  | notAFunction₂ : TypedTerm → Term → TCError
  | typeMismatch : Term → Term → TCError
  | unTypedVariable : Nat → VarContext → TCError
  | cannotInfer : Term → TCError
  | wrongNumberOfUniverse : String → Nat → Nat → TCError
deriving Repr

instance : ToString TCError where
  toString
    | .unboundDeBruijnIndex n con => s!"unbound De Bruijn index {n} in context {con}"
    | .unknownConstant c => s!"unknown constant {c}"
    | .notUniverse t => s!"expected a sort, found {t}"
    | .notDefEq t₁ t₂ => s!"{t₁} and {t₂} are not definitionally equal"
    | .wrongArgumentType f exp (t,ty)=> s!"function {f} expects an argument of type {exp}, received argument {t} of type {ty}"
    | .cannotInfer t => s!"cannot infer type of term {t}"
    | _ => todo!

abbrev Result (A) := Except TCError A

abbrev TCEnv := EStateM TCError TCContext

def EStateM.Result.get : EStateM.Result ε σ α → σ
  | .ok _ st
  | .error _ st => st

def add_trace (tr : String): TCEnv Unit :=
    modify $ λ con => {con with trace := tr :: con.trace}

instance (priority := high) : MonadExceptOf TCError TCEnv where
  throw err := do
    add_trace $ toString err
    throw err
  tryCatch := tryCatch

def add_var_to_context_no_shift (t : Option Term) : TCEnv Unit :=
    modify $ λ con => {con with var_cont := con.var_cont.push t}

def reduce_decl (s : String) : TCEnv Term := do
  let res := (← get).const_con.find? s
  if let some $ .de d := res then
    return d.term
  else
    throw $ .unknownConstant s

class GetType (A: Type) where
  get_type : A → TCEnv Term

def get_const_type (s : String) (arr : Array Level): TCEnv Term := do
  let res := (← get).const_con.find? s
  if let some $ c := res then
    if c.n_of_univ != arr.size then
      throw $ .wrongNumberOfUniverse s c.n_of_univ arr.size
    return c.type
  else
    throw $ .unknownConstant s
instance : GetType $ String × Array Level := ⟨uncurry get_const_type⟩

def get_var_type (n:Nat) : TCEnv Term := do
  let some optty := (← get).var_cont.get? n | unreachable!
  let some ty := optty | throw $ .unTypedVariable n (← get).var_cont
  pure ty
instance : GetType $ Nat := ⟨get_var_type⟩

inductive Command : Type :=
  | def : String → Option Term → Term → Command
  | axiom : String → Term → Command
  | check : Term → Command
  | eval : Term → Command
