import Proost.Kernel.Level
import Proost.Kernel.Core
import Proost.Kernel.Axioms
import Std.Data.HashMap
import Proost.Util.Misc

open Std
namespace Term

def shift (offset depth : Nat) : Term → Term
  | var n => 
    let n := if n >= depth then n+offset else n
    var n
  | app t₁ t₂ => app (t₁.shift offset depth) (t₂.shift offset depth)
  | abs ty body =>
    let ty   := ty.attach.map (λ ⟨e,_⟩ => e.shift offset depth)
    let body := body.shift offset depth.succ
    abs ty body
  | prod ty body =>
    let ty := ty.shift offset depth
    let body := body.shift offset depth.succ
    prod ty body
  | ann t ty => ann (t.shift offset depth) (ty.shift offset depth)
  | const s l => const s l
  | sort l => sort l

def substitute (self sub : Term) (depth : Nat) : Term := match self with
  | var n => match compare n depth with
      | .eq => sub.shift depth.pred 1
      | .gt => var (n-1)
      | .lt => var n
  | app t₁ t₂ => app (t₁.substitute sub depth) (t₂.substitute sub depth)
  | abs ty body => 
    let ty := ty.attach.map (λ ⟨e,_⟩ => e.substitute sub depth)
    let body := body.substitute sub depth.succ
    abs ty body 
  | prod ty body => 
    let ty := ty.substitute sub depth
    let body := body.substitute sub depth.succ
    prod ty body
  | ann t ty => ann (t.substitute sub depth) (ty.substitute sub depth)
  | const s l => const s l
  | sort l => sort l

def with_add_var_to_context (t : Option Term) : TCEnv α → TCEnv α:= 
    withReader λ con => {con with var_ctx := con.var_ctx|>.push t |>.map (.map $ Term.shift 1 0) }

def noAnn : Term → Term
  | ann t _ => t
  | t => t

def reduce_decl : Term → TCEnv Term
  | t@(const s arr) => do
    let res := (← read).const_ctx.find? s
    if let some $ .defnDecl d := res then
      return d.term |>.substitute_univ arr
    else
      return t
  | t => pure t

def RedRecs := HashMap String (Term → TCEnv (Option Term))

def red_rec (m : RedRecs)(s : String) (t : Term): TCEnv Term := do
  let some rec := m.find? s | pure t
  let some t ← rec t | pure t
  pure t


@[export proost_whnf]
partial def whnf (t : Term) : TCEnv Term := do 
  let res ← do
    let t ← reduce_decl t
    match t with
      | app t₁ t₂ => do
        let t₁ ← whnf (← reduce_decl t₁)
        match t₁ with
          | abs _ body =>
            whnf $ body.substitute t₂ 1
          | const s _ => red_rec (all_recs ()) s (.app t₁ t₂)
          | _ => pure $ .app t₁ t₂
      | _ => pure t
  add_trace "whnf"  s!"{t}\n reduces to \n{res}"
  pure res

