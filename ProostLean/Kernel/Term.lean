import ProostLean.Kernel.Level
import ProostLean.Kernel.Core

/-namespace Term

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
  | self => self

partial def substitute (self sub : Term) (depth : Nat) : Term := match self with
  | var n => match compare n depth with
      | .eq => sub.shift depth.pred 0
      | .gt => var n.pred
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
  | t => t


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