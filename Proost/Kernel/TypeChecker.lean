import Proost.Kernel.Level
import Proost.Kernel.Term
import Proost.Kernel.Nbe
import Proost.Util.Misc

set_option autoImplicit false
open GetType
--partial def Value.is_prop_type : Value → TCEnv Bool
--  | abs ..
--  | sort .. => pure false
--  | prod _ cod => do (← Term.eval cod.closure cod.term).is_prop_type cod.closure
--  | neutral (.ax a arr) _ => pure $ (a.type |>.substitute_univ arr) == .sort 0
--  | neutral (.var x) _ =>
--      if let some b := closure.get? x |>.map (·.is_prop_type closure)
--      then b else pure false
--
--mutual
--  partial def Neutral.is_irrelevant : Neutral → TCEnv Bool
--    | .ax a arr => (a.type |>.substitute_univ arr).eval closure >>= Value.is_prop_type closure
--    | .var x =>       if let some b := closure.get? x |>.map (·.is_prop_type closure)
--      then b else pure false
--
--  partial def Value.is_irrelevant : Value → TCEnv Bool
--    | .neutral ne _ => ne.is_irrelevant closure
--    | .abs _ body => do (← Term.eval body.closure body.term).is_irrelevant body.closure
--    | _ => pure false
--end

partial def Term.conversion (lhs rhs : Term) : TCEnv Bool := do
  add_trace s!"checking {lhs} = {rhs}"
  let lhs := lhs.noAnn
  let rhs := rhs.noAnn
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

#eval Term.conversion (.abs none $ .var 0) (.app (.abs none $ .abs none $ .var 0) (.sort 0)) default

namespace Term


def is_def_eq (lhs rhs : Term) : TCEnv Unit :=
  unless lhs == rhs do
  throw $ .notDefEq lhs rhs

def imax (lhs rhs : Term) : TCEnv Term := do
  match lhs,rhs with
    | sort l₁, sort l₂ => return sort $ l₁.imax l₂
    | sort _,_ => throw $ .notUniverse rhs
    | _,_ => throw $ .notUniverse lhs

mutual
partial def infer (t : Term): TCEnv Term := do
  add_trace s!"trying to infer the type of {t}"
  let res ← match t with
  | ann t ty => do
    check t ty
    return ty
  | sort l => pure $ sort l.succ
  | var n => get_type n
  | prod t u => do
    let univ_t ← (← t.infer).whnf
    add_var_to_context $ some univ_t
    let univ_u ← (← u.infer).whnf
    univ_t.imax univ_u
  | t@(abs none _) => throw $ .cannotInfer t
  | abs (some t) u => do
    let univ_t ← t.infer
    if let sort _ := univ_t then
      add_var_to_context $ some t
      return t.prod $ ← u.infer
    else throw $ .notUniverse univ_t

  | app t u => do
    let type_t ← (← t.infer).whnf

    if let prod arg_type cls := type_t then
      check u arg_type
      pure $ cls.substitute u 1
    else throw $ .notAFunction₂ (t,type_t) u
   | const s arr => get_type (s,arr)
   add_trace s!"inferred {t} : {res}"
   return res

partial def check (t ty : Term ):  TCEnv Unit := do
  add_trace s!"checking {t} : {ty}"
  match t,ty with
  | .abs none body, .prod a b => do
    add_var_to_context $ some a
    check  body b
  | .abs (some ty) body, .prod a b => do
    is_def_eq a ty
    add_var_to_context $ some a
    check body b
  | .app t u, ty => do
    let type_t ← infer t
    let .prod a b := type_t | throw $ .notAFunction₂ (t,type_t) u
    check u a
    let b := b.substitute u 1
    is_def_eq b ty
  | .const s arr,ty => do is_def_eq ty $ ← get_type (s,arr)
  | .ann t ty, tty => do
    is_def_eq ty tty
    check t ty
  | .sort l₁, .sort l₂ =>
    unless l₁ == l₂ do
      throw $ .notDefEq (.sort l₁) (.sort l₂)
  | .var n, ty => do
    is_def_eq ty $ ← get_type n
  | t,ty => do
    let tty ← infer t
    is_def_eq ty tty
end

#eval is_def_eq (.sort 1) (.sort 2) default
#eval check (.abs (some $ .sort 1) $ .abs (some $ .sort 2) $ .var 1) (.prod (.sort 1) $ .prod (.sort 1) (.sort 1)) default |>.get.trace
/-
["Π Sort 1.Sort 1 and Π Sort 1.Π Sort 1.Sort 1 are not definitionally equal", "checking Sort 0 : Sort 1",
 "inferred 0 : Sort 1", "trying to infer the type of 0", "inferred Sort 1 : Sort 2",
 "trying to infer the type of Sort 1", "trying to infer the type of λ Sort 1 => 0", "inferred Sort 1 : Sort 2",
 "trying to infer the type of Sort 1", "trying to infer the type of λ Sort 1 => λ Sort 1 => 0",
 "checking (λ Sort 1 => λ Sort 1 => 0) (Sort 0) : Π Sort 1.Π Sort 1.Sort 1"]

-/


end Term