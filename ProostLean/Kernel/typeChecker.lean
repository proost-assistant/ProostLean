import ProostLean.Kernel.Level
import ProostLean.Kernel.Reduce
import ProostLean.Kernel.Term
import ProostLean.Kernel.Nbe


set_option autoImplicit false

open Reduce



partial def Value.is_prop_type (closure : List Value := []): Value → TCEnv Bool 
  | abs .. 
  | sort .. => pure false
  | prod _ cod => do (← Term.eval cod.closure cod.term).is_prop_type cod.closure
  | neutral (.ax a) _ => pure $ a.type == .sort 0
  | neutral (.var x) _ => closure.get! x |>.is_prop_type closure

mutual
  partial def Neutral.is_irrelevant (closure : List Value := []): Neutral → TCEnv Bool 
    | .ax a => a.type.eval closure >>= Value.is_prop_type closure
    | .var x => closure.get! x |>.is_irrelevant closure

  partial def Value.is_irrelevant (closure : List Value := []): Value → TCEnv Bool 
    | .neutral ne _ => ne.is_irrelevant closure
    | .abs _ body => do (← Term.eval body.closure body.term).is_irrelevant body.closure
    | _ => pure false
end

mutual

partial def Term.conversion (lhs rhs : Term) : TCEnv Bool := do
  if lhs == rhs then
    return true
  
  let lhs ← lhs.eval 
  let rhs ← rhs.eval

  lhs.conversion rhs


partial def Value.conversion (lhs rhs : Value) : TCEnv Bool := do
  if lhs == rhs || (← lhs.is_irrelevant) then
    return true
  
  match lhs,rhs with
    | .sort l₁, .sort l₂ => pure $ l₁ == l₂
    | .abs _ t₁, .abs _ t₂ => t₁.term.conversion  t₂.term
    | .prod t₁ u₁, .prod t₂ u₂ => pure $ (← t₁.conversion  t₂) && (← u₁.term.conversion  u₂.term)
    | _,_ => pure false

end

#eval Term.conversion (.abs none $ .var 0) (.app (.abs none $ .abs none $ .var 0) (.sort 0)) default []

namespace Term 


def is_def_eq (lhs rhs : Term) : TCEnv Unit := do
  if lhs != rhs then 
    throw $ .notDefEq lhs rhs

def imax (lhs rhs : Term) : TCEnv Term := do
  match lhs,rhs with
    | sort l₁, sort l₂ => return sort $ l₁.imax l₂
    | sort _,_ => throw $ .notUniverse rhs
    | _,_ => throw $ .notUniverse lhs
/-  
def infer : Term → TCEnv Term
  | sort l => pure $ sort l.succ
  | var _ => pure ty
  | prod t u => do
    let univ_t ← (← t.infer).whnf
    let univ_u ← (← u.infer).whnf
    univ_t.imax univ_u

  | abs t u => do
    let type_t ← t.infer 
    if let sort _ := type_t then
      return t.prod $ ← u.infer
    else throw $ .notUniverse type_t

  | app t u => do
    let type_t ← (← t.infer).whnf
     
    if let prod arg_type cls := type_t then
      let type_u ← u.infer 
      if type_u == arg_type then
        return cls.substitute u 1
      else 
        throw $ .wrongArgumentType t arg_type (u,type_u)
    else throw $ .notAFunction (t,type_t) u
   | const .. => panic "ah"

def check (t ty : Term) : TCEnv Unit := do
  let tty ← t.infer 
  if ! (← tty.conversion ty) then
    throw $ .typeMismatch ty tty
-/
end Term