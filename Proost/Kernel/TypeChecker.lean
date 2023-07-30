import Proost.Kernel.Level
import Proost.Kernel.Term
import Proost.Kernel.Whnf

--import Proost.Kernel.Nbe
import Proost.Util.Misc

set_option autoImplicit false
open GetType

def Term.is_prop_type :Term → TCEnv Bool
  | .var i => do
    let ty ← get_type i
    let ty ← ty.whnf
    return ty == Term.prop
  | .prod t₁ t₂ =>
    with_add_var_to_context (some t₁) $ do
      t₂.is_prop_type
  | .const s arr => do
    let ty ← get_type (s,arr)
    let ty ← ty.whnf
    return ty == Term.prop
  | _ => return false


inductive relevance :=
  | relevant
  | irrelevant
deriving DecidableEq

def Term.relevance :Term → TCEnv relevance
  | .abs t body => 
    with_add_var_to_context t $ do
      body.relevance
  | .var i => do
    let ty ← get_type i
    let is_prop ← ty.is_prop_type
    return if is_prop then .irrelevant else .relevant
  | .ann t _ => t.relevance -- ty.is_prop_type ?
  | .app f _ => f.relevance
  | _ => return .relevant


--assumption : `lhs` and `rhs` are well-typed and of the same type
@[export conversion]
partial def Term.conversion (lhs rhs : Term) : TCEnv Bool := do
  --dbg_trace s!"checking \n{lhs} = {rhs}\n"
  let lhs := lhs.noAnn
  let rhs := rhs.noAnn
  if lhs == rhs then
    return true
  let relevance ← lhs.relevance 
  if relevance == .irrelevant then
    return true
  let lhs ← lhs.whnf
  let rhs ← rhs.whnf

  if lhs == rhs then
    return true
  --dbg_trace s!"matching \n{lhs} , {rhs}\n"
  match lhs,rhs with
    | sort l₁, sort l₂ => return l₁.is_eq l₂
    | var i, var j => return i == j
    | abs _ t₁, abs _ t₂ => conversion t₁ t₂
    | prod t₁ u₁, prod t₂ u₂
    | app t₁ u₁, app t₂ u₂ => andM (conversion t₁ t₂) ( conversion u₁ u₂)
    | const s₁ _, const s₂ _ => return s₁ == s₂ 
    | _,_ => pure false

namespace Term
@[export isDefEq]
def isDefEq (lhs rhs : Term) : TCEnv Unit :=
  unless ← conversion lhs rhs do
  throw $ .notDefEq lhs rhs


def imax (lhs rhs : Term) : TCEnv Term := do
  match lhs,rhs with
    | sort l₁, sort l₂ => return sort $ l₁.imax l₂ |>.normalize 
    | sort _,_ => throw $ .notASort rhs
    | _,_ => throw $ .notASort lhs

mutual
@[export infer]
def infer (t : Term): TCEnv Term := do
  add_trace "tc" s!"trying to infer the type of \n{t}\n in var_env {(← read).var_ctx}\n"
  let res ← match t with
  | ann t ty => do
    check t ty
    return ty
  | sort l => pure $ sort l.succ
  | var n => get_type n
  | prod t u => do
    let univ_t ← (← t.infer).whnf
    with_add_var_to_context (some t) $ do
      let univ_u ← (← u.infer).whnf
      univ_t.imax univ_u
  | t@(abs none _) => throw $ .cannotInfer t
  | abs (some t) u => do
    let univ_t ← t.infer
    if let sort _ := univ_t then
      with_add_var_to_context (some t) $ do
      return t.prod $ ← u.infer
    else throw $ .notASort univ_t

  | app t u => do
    let type_t ← (← t.infer).whnf
    add_trace "tc" s!"{t} has type {type_t}"
    if let prod arg_type cls := type_t then
      check u arg_type
      pure $ cls.substitute u 1
    else throw $ .notAFunction₂ (t,type_t) u
   | const s arr => get_type (s,arr)
   add_trace "tc" s!"inferred \n{t} \n: {res}\n"
   return res



def check (t ty : Term):  TCEnv Unit := do
  add_trace "tc" s!"checking \n{t}\n : {ty}\n in var_env {(← read).var_ctx}\n"
  match t,ty with
  | .abs none body, .prod a b => do
    with_add_var_to_context (some a) $
    check body b
  | .abs (some ty) body, .prod a b => do
    isDefEq a ty
    with_add_var_to_context (some a) $
    check body b
  | .app t u, ty => do
    let type_t ← infer t
    let .prod a b := type_t | throw $ .notAFunction₂ (t,type_t) u
    check u a
    let b := b.substitute u 1
    isDefEq b ty
  | .const s arr,ty => do isDefEq ty $ ← get_type (s,arr)
  | .ann t ty, tty => do
    check t ty
    isDefEq ty tty
  | .sort l₁, .sort l₂ =>
    unless l₁+1 == l₂ do
      throw $ .notDefEq (.sort (l₁+1)) (.sort l₂)
  | .var n, ty => do
    isDefEq ty $ ← get_type n
  | t,ty => do
    let tty ← infer t
    isDefEq ty tty
end

def is_sort (t :Term): TCEnv Unit := do
  let .sort _ := t | throw $ .notASort t
  return

def is_type (t : Term): TCEnv Unit := do
  let ty ← infer t
  is_sort ty

end Term

--#eval {debug := ["nbe"]} |> do
--  let And : Term := 
--    .abs (some .prop) $ 
--    .abs (some .prop) $ 
--    .prod .prop $ 
--    .prod (.prod (.var 3) $ .prod (.var 3) $ .var 3) $
--    .var 2
--  let And_ty : Term := .prod .prop
--    $ .prod .prop
--    $ .prop
--
--  let And_intro : Term :=
--    .abs (some .prop) $ 
--    .abs (some .prop) $ 
--    .abs (some $ .var 2) $ 
--    .abs (some $ .var 2) $ 
--    .abs (some .prop) $ 
--    .abs (some $ .prod (.var 5) $ .prod (.var 5) $ .var 3) $
--    .app (.app (.var 1) (.var 4)) (.var 3)
--  let And_intro_ty : Term :=
--    .prod .prop $ 
--    .prod .prop $ 
--    .prod (.var 2) $ 
--    .prod (.var 2) $ 
--    .app (.app And (.var 4)) (.var 3)
--
--  let And_decl : Decl := ⟨And_ty,0,And⟩
--  with_add_def "And" And_decl $
--    Term.app (Term.app (.const "And" #[]) (.var 4)) (.var 3) |>.is_def_eq 
--      (.prod .prop $ 
--    .prod (.prod (.var 5) $ .prod (.var 5) $ .var 3) $
--    .var 2)
--