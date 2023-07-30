import Proost.Kernel.Level
import Proost.Kernel.Core
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

