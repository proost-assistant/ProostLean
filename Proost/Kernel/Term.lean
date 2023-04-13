import Proost.Kernel.Level
import Proost.Kernel.Core

namespace Term

-- Only partial because structural recursion on nested inductives is broken
partial def shift (offset depth : Nat) : Term → Term
  | var n => 
    let n := if n > depth then n+offset else n
    var n
  | app t₁ t₂ => app (t₁.shift offset depth) (t₂.shift offset depth)
  | abs ty body =>
    let ty   := ty.map (·.shift offset depth)
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
      | .eq => sub.shift depth.pred 0
      | .gt => var (n-1)
      | .lt => var n
  | app t₁ t₂ => app (t₁.substitute sub depth) (t₂.substitute sub depth)
  | abs ty body => 
    let ty := ty.map (·.substitute sub depth)
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
    withReader λ con => {con with var_cont := con.var_cont|>.push t |>.map (.map $ Term.shift 1 0) }

def noAnn : Term → Term
  | ann t _ => t
  | t => t

partial def substitute_univ (lvl : Array Level) : Term → Term
  | sort l => sort $ l.substitute lvl
  | var n => var n
  | app t₁ t₂ => app (t₁.substitute_univ lvl) (t₂.substitute_univ lvl)
  | abs ty body => abs (ty.map (substitute_univ lvl)) (body.substitute_univ lvl)
  | prod a b => prod (a.substitute_univ lvl) (b.substitute_univ lvl)
  | ann t ty => ann (t.substitute_univ lvl) (ty.substitute_univ lvl) 
  | const s arr => const s $ arr.map (Level.substitute · lvl)

--#eval Term.prod (.var 4) (.prod (.var 4) (.var 2)) |>.shift 1 0


/-
partial def whnf (t : Term) : TCEnv Term := match t with
  | app t₁ t₂ => do
    if let abs _ body := ← whnf t₁ then whnf $ body.substitute t₂ 1
    else pure t
  | const s => do
    try
      reduceDecl s
    catch
      | .unknownConstant _ => pure t
      | _ => unreachable!
  | _ => pure t


def is_relevant (closure : List Term): Term → TCEnv Bool 
  | var x => do
    if let some t := closure.get? x then 
      t.is_relevant closure
    else 
      throw $ .unboundDeBruijnIndex x closure
  | abs _ body => body.is_relevant closure
  | app t _ => t.is_relevant closure
  | const s => do return (← (← getType s).whnf) == sort 0
  | _ => pure false

end Term -/