import ProostLean.Kernel.Level
import ProostLean.Kernel.Reduce
import ProostLean.Kernel.Term

open Reduce

abbrev TypedTerm := Term × Term

inductive TCError : Type := 
  | notUniverse : Term → TCError
  | notDefEq : Term → Term → TCError
  | wrongArgumentType : Term → Term → TypedTerm → TCError
  | notAFunction : TypedTerm → Term → TCError
  | typeMismatch : Term → Term → TCError

abbrev Result (A : Type) := Except TCError A

namespace Term 

partial def conversion (lhs rhs : Term) : Bool := Id.run do
  if lhs = rhs then
    return true
  if !lhs.is_relevant then
    return true
  let lhs := reduce lhs
  let rhs := reduce rhs

  if lhs = rhs then
    return true

  match lhs,rhs with
    | sort l₁, sort l₂ => l₁ == l₂
    | var i, var j => i == j
    | abs _ t₁, abs _ t₂ => conversion t₁ t₂
    | prod t₁ u₁, prod t₂ u₂
    | app t₁ u₁, app t₂ u₂ => conversion t₁ t₂ && conversion u₁ u₂
    | _,_ => false

instance : BEq Term := ⟨conversion⟩

def is_def_eq (lhs rhs : Term) : Result Unit := do
  if lhs != rhs then 
    throw $ .notDefEq lhs rhs

def imax (lhs rhs : Term) : Result Term := do
  match lhs,rhs with
    | sort l₁, sort l₂ => return sort $ l₁.imax l₂
    | sort _,_ => throw $ .notUniverse rhs
    | _,_ => throw $ .notUniverse lhs
  
def infer : Term → Result Term
  | sort l => pure $ sort l.succ
  | var _ => panic "ah"
  | prod t u => do
    let univ_t := (← t.infer).whnf
    let univ_u := (← u.infer).whnf
    univ_t.imax univ_u

  | abs t u => do
    let type_t ← t.infer 
    if let sort _ := type_t then
      return t.prod $ ← u.infer
    else throw $ .notUniverse type_t

  | app t u => do
    let type_t := (← t.infer).whnf
     
    if let prod arg_type cls := type_t then
      let type_u ← u.infer 
      if type_u == arg_type then
        return cls.substitute u 1
      else 
        throw $ .wrongArgumentType t arg_type (u,type_u)
    else throw $ .notAFunction (t,type_t) u
   | const .. => panic "ah"

def check (t ty : Term) : Result Unit := do
  let tty ← t.infer 
  if ! tty.conversion ty then
    throw $ .typeMismatch ty tty

end Term