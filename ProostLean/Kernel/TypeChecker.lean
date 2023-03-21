import ProostLean.Kernel.Level
import ProostLean.Kernel.Reduce
import ProostLean.Kernel.Term
import ProostLean.Kernel.Nbe
import ProostLean.Util.Misc


set_option autoImplicit false

open Reduce



partial def Value.is_prop_type (closure : List Value := []): Value → TCEnv Bool 
  | abs .. 
  | sort .. => pure false
  | prod _ cod => do (← Term.eval cod.closure cod.term).is_prop_type cod.closure
  | neutral (.ax a) _ => pure $ a.type == .sort 0
  | neutral (.var x) _ => 
      if let some b := closure.get? x |>.map (·.is_prop_type closure)
      then b else pure false

mutual
  partial def Neutral.is_irrelevant (closure : List Value := []): Neutral → TCEnv Bool 
    | .ax a => a.type.eval closure >>= Value.is_prop_type closure
    | .var x =>       if let some b := closure.get? x |>.map (·.is_prop_type closure)
      then b else pure false

  partial def Value.is_irrelevant (closure : List Value := []): Value → TCEnv Bool 
    | .neutral ne _ => ne.is_irrelevant closure
    | .abs _ body => do (← Term.eval body.closure body.term).is_irrelevant body.closure
    | _ => pure false
end

partial def Term.conversion (lhs rhs : Term) : TCEnv Bool := do
  if lhs == rhs then
    return true
  --if !lhs.is_relevant then
  --  return true
  let lhs ←  lhs.whnf
  let rhs ←  rhs.whnf

  if lhs == rhs then
    return true

  match lhs,rhs with
    | .sort l₁, .sort l₂ => pure $ l₁ == l₂
    | .var i, .var j => pure $ i == j
    | .abs _ t₁, .abs _ t₂ => conversion t₁ t₂
    | .prod t₁ u₁, .prod t₂ u₂
    | .app t₁ u₁, .app t₂ u₂ => return (←conversion t₁ t₂) && (← conversion u₁ u₂)
    | _,_ => pure false

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

mutual
def infer (con : Context): Term → TCEnv Term
  | sort l => pure $ sort l.succ
  | var n => con.get_type n
  | prod t u => do
    let univ_t ← (← t.infer con).whnf
    let con := (some univ_t)::con
    let univ_u ← (← u.infer con).whnf
    univ_t.imax univ_u
  | t@(abs none _) => throw $ .cannotInfer t
  | abs (some t) u => do
    let type_t ← t.infer con
    if let sort _ := type_t then
      let con := (some type_t)::con
      return t.prod $ ← u.infer con
    else throw $ .notUniverse type_t

  | app t u => do
    let type_t ← (← t.infer con).whnf
    
    if let prod arg_type cls := type_t then
      check con u arg_type
      pure $ cls.substitute u 1
    else throw $ .notAFunction₂ (t,type_t) u
   | const s => get_type s

def check (con : Context): Term → Term →  TCEnv Unit 
  | .abs none body, .prod a b => check ((some a)::con) body b
  | .abs (some ty) body, .prod a b => do
    is_def_eq a ty
    check ((some a)::con) body b
  | .app t u, ty => do
    let type_t ← infer con t
    let .prod a b := type_t | throw $ .notAFunction₂ (t,type_t) u
    check con u a
    let b := b.substitute u 1
    is_def_eq b ty
  | t, ty => do  
    let tty ← infer con t
    is_def_eq ty tty
end

#eval check [] (.app (.abs none $ .abs none $ .var 0) (.sort 0)) (.prod (.sort 0) $ .prod (.sort 0) (.sort 1)) default []


end Term