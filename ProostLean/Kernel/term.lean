import ProostLean.Kernel.Level
import ProostLean.Kernel.Reduce


inductive Term : Type :=
  | var  : Nat → Term 
  | sort : Level → Term
  | app  : Term → Term → Term
  | abs  : Term → Term → Term
  | prod  : Term → Term → Term
  | const : String → Term 
deriving Repr, DecidableEq, Inhabited

namespace Term

def shift (offset depth : Nat) : Term → Term
  | var n => 
    let n := if n > depth then n+offset else n
    var n
  | app t₁ t₂ => app (t₁.shift offset depth) (t₂.shift offset depth)
  | abs ty body =>
    let ty := ty.shift offset depth
    let body := body.shift offset depth.succ
    abs ty body
  | prod ty body =>
    let ty := ty.shift offset depth
    let body := body.shift offset depth.succ
    prod ty body
  | self => self

def substitute (self sub : Term) (depth : Nat) : Term := match self with
  | var n => match compare n depth with
      | .eq => sub.shift depth.pred 0
      | .gt => var n.pred
      | .lt => var n
  | app t₁ t₂ => app (t₁.substitute sub depth) (t₂.substitute sub depth)
  | abs ty body => 
    let ty := ty.substitute sub depth
    let body := body.substitute sub depth.succ
    abs ty body 
  | prod ty body => 
    let ty := ty.substitute sub depth
    let body := body.substitute sub depth.succ
    prod ty body
  | t => t


partial def whnf (t : Term) : Term := match t with
  | app t₁ t₂ =>
    if let abs _ body := whnf t₁ then whnf $ body.substitute t₂ 1
    else t
  | _ => t

instance : Reduce Term := ⟨whnf⟩   

def is_relevant : Term → Bool 
  | var _ => panic "ah"
  | abs _ body => body.is_relevant
  | app t _ => t.is_relevant
  -- TODO | decl d => d.decl.term.is_relevant
  | _ => false

end Term