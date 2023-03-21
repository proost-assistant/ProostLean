import ProostLean.Kernel.Level
import Std.Data.HashMap

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
    | .abs (some t1) t2 => "λ" ++ t1.toString ++ " => " ++ t2.toString
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

abbrev ConstEnv := ReaderT ConstContext

abbrev TypedTerm := Term × Term
abbrev Context := List $ Option Term

inductive TCError : Type := 
  | unboundDeBruijnIndex : Nat → List Term → TCError 
  | unknownConstant : String → TCError
  | notUniverse : Term → TCError
  | notDefEq : Term → Term → TCError
  | wrongArgumentType : Term → Term → TypedTerm → TCError
  | notAFunction : Value → Value → TCError
  | notAFunction₂ : TypedTerm → Term → TCError
  | typeMismatch : Term → Term → TCError
  | unTypedVariable : Nat → Context → TCError
  | cannotInfer : Term → TCError
  | wrongNumberOfUniverse : String → Nat → Nat → TCError 
deriving Repr

abbrev Result (A) := Except TCError A

abbrev Traced := StateM (List String)
abbrev TCEnv :=  ConstEnv $ EStateM TCError (List String)  

def EStateM.Result.get : EStateM.Result ε σ α → σ 
  | .ok _ st
  | .error _ st => st

def add_trace (trace : String): TCEnv Unit := do 
    let st : List String ← get
    set $ trace::st

def reduce_decl (s : String) : TCEnv Term := do
  let res := (← read).find? s
  if let some $ .de d := res then
    return d.term
  else 
    throw $ .unknownConstant s

def get_type (s : String) (arr : Array Level): TCEnv Term := do
  let res := (← read).find? s
  if let some $ c := res then
    if c.n_of_univ != arr.size then
      throw $ .wrongNumberOfUniverse s c.n_of_univ arr.size
    return c.type
  else 
    throw $ .unknownConstant s

def Context.get_type (con : Context) (n:Nat) : TCEnv Term := do
  let some optty := con.get? n | unreachable!
  let some ty := optty | throw $ .unTypedVariable n con
  pure ty

inductive Command : Type :=
  | def : String → Option Term → Term → Command
  | axiom : String → Term → Command
  | check : Term → Command
  | eval : Term → Command
