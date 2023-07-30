import Proost.Kernel.Level
import Proost.Kernel.Core
import Proost.Kernel.Axioms
import Std.Data.HashMap
import Proost.Util.Misc

open Std
namespace Term

partial def shift (offset depth : Nat) : Term → Term
  | var n => 
    let n := if n >= depth then n+offset else n
    var n
  | app t₁ t₂ => app (t₁.shift offset depth) (t₂.shift offset depth)
  | abs ty body =>
    let ty   := ty.map (shift offset depth)
    let body := body.shift offset depth.succ
    abs ty body
  | prod ty body =>
    let ty := ty.shift offset depth
    let body := body.shift offset depth.succ
    prod ty body
  | ann t ty => ann (t.shift offset depth) (ty.shift offset depth)
  | const s l => const s l
  | sort l => sort l

partial def substitute (self sub : Term) (depth : Nat) : Term := match self with
  | var n => match compare n depth with
      | .eq => sub.shift depth.pred 1
      | .gt => var (n-1)
      | .lt => var n
  | app t₁ t₂ => app (t₁.substitute sub depth) (t₂.substitute sub depth)
  | abs ty body => 
    let ty := ty.map (substitute · sub depth)
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

def red_rec (m : RedRecs) (s : String) (t : Term): TCEnv (Option Term) := do
  let some rec := m.find? s | pure none
  rec t


@[export proost_whnf]
partial def whnf (t : Term) : TCEnv Term := do 
  let t ← reduce_decl t
  let mut ⟨hd,args⟩ := t.getAppFnArgs
  if !args.isEmpty then
    let hd₂ ← hd.whnf
    let (t₁,t₂) := hd₂.getAppFnArgs
    hd := t₁
    args := t₂.append args
    match hd with
      | abs _ body =>
        let mut t := body.substitute args[0]! 1
        for arg in args[1:] do
          t := app t arg
        Term.whnf t
      | const s _ => 
        let t := mkAppN hd args
        let some t ← red_rec all_recs s $ t | pure t
        t.whnf
      | _ => 
        let t := mkAppN hd args
        pure t
  else 
    pure t
