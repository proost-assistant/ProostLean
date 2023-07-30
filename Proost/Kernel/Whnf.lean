import Proost.Kernel.Level
import Proost.Kernel.Core
import Proost.Kernel.Term
import Proost.Kernel.Axioms
import Proost.Kernel.ReduceRec
import Std.Data.HashMap
import Proost.Util.Misc

open Std
namespace Term

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

@[export proost_whnf]
partial def whnf (t : Term) : TCEnv Term := do 
  let t ← reduce_decl t
  let mut ⟨hd,args⟩ := t.getAppFnArgs
  if !args.isEmpty then
    let hd₂ ← hd.whnf
    let (t₁,t₂) := hd₂.getAppFnArgs
    hd := t₁
    args := t₂.append args
    let finish := λ () => pure $ mkAppN hd args
    match hd with
      | abs _ body =>
        let mut t := body.substitute args[0]! 1
        for arg in args[1:] do
          t := app t arg
        Term.whnf t
      | const _ _ => 
        matchConstAux hd finish fun cinfo lvls =>
          match cinfo with
          | .recursorDecl rec => reduceRec rec lvls args finish Term.whnf
          | .inductDecl i => reduceEqCast i.name t 
          | _ => finish ()
      | _ => finish ()
  else 
    pure t
