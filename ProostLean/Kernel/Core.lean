import ProostLean.Kernel.Level
import Std.Data.HashMap

open Std

inductive Term : Type :=
  | var  : Nat → Term 
  | sort : Level → Term
  | app  : Term → Term → Term
  | abs  : Option Term → Term → Term
  | prod  : Term → Term → Term
  | const : String → Term 
deriving Repr, Inhabited, BEq


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
  | ax : Axiom → Neutral 
deriving BEq,Repr

inductive Value : Type :=
  | neutral : Neutral → List Value → Value
  | sort : Level → Value  
  | abs : Option Value → AppClosure Value → Value
  | prod : Value → AppClosure Value → Value
deriving Inhabited, BEq,Repr

def Value.var (n : Nat) : Value := .neutral (.var n) []

structure Decl where  
  type : Term
  n_of_univ : Nat
  term : Term

inductive Const :=
  | ax : Axiom → Const
  | de : Decl  → Const 

namespace Const
def type : Const → Term
  | .ax a | .de a => a.type
end Const

abbrev ConstContext := HashMap String Const

abbrev ConstEnv := ReaderT ConstContext

abbrev TypedTerm := Term × Term

inductive TCError : Type := 
  | unboundDeBruijnIndex : Nat → List Value → TCError 
  | unknownConstant : String → TCError
  | notUniverse : Term → TCError
  | notDefEq : Term → Term → TCError
  | wrongArgumentType : Term → Term → TypedTerm → TCError
  | notAFunction : Value → Value → TCError
  | typeMismatch : Term → Term → TCError
deriving Repr

abbrev Result (A) := Except TCError A

abbrev Traced := StateT (List String)
abbrev TCEnv :=  ConstEnv $ Traced Result 

def addTrace : String → TCEnv Unit :=
  fun trace => do 
    let st ← get
    set $ trace::st

def reduceDecl (s : String) : TCEnv Term := do
  let res := (← read).find? s
  if let some $ .de d := res then
    return d.term
  else 
    throw $ .unknownConstant s

def getType (s : String) : TCEnv Term := do
  let res := (← read).find? s
  if let some $ c := res then
    return c.type
  else 
    throw $ .unknownConstant s

def todo! {A : Type _} [Inhabited A] : A := panic! "todo"

syntax "return" term : term
macro_rules
  | `(term| "return" $t:term) => `(term | do return $t)
