import Proost.Kernel.Level
import Std.Data.HashMap
import Proost.Util.Misc

open Std

abbrev Name := String

inductive Term : Type :=
  | var   : Nat → Term
  | sort  : Level → Term
  | app   : Term → Term → Term
  | abs   : Option Term → Term → Term
  | prod  : Term → Term → Term
  | const : Name → Array Level →  Term
  | ann   : Term → Term → Term
deriving Repr, Inhabited, BEq

namespace Term

def getAppFn : Term →  Term
  | .app f _ => f.getAppFn
  | t => t

def getAppArgs : Term → Array Term
  | .app f arg => f.getAppArgs.push arg
  | _ => #[]

def getAppFnArgs : Term →  Term × Array Term
  | .app f arg =>
    let ⟨f,args⟩ := f.getAppFnArgs
    ⟨f,args.push arg⟩
  | t => ⟨t,#[]⟩

def mkAppN : Term → Array Term → Term := fun hd arr =>
  arr.foldl app hd

partial def mkAppRangeAux (n : Nat) (args : Array Term) (i : Nat) (e : Term) : Term :=
  if i < n then mkAppRangeAux n args (i+1) (app e (args.get! i)) else e

/-- `mkAppRange f i j #[a_1, ..., a_i, ..., a_j, ... ]` ==> the expression `f a_i ... a_{j-1}` -/
def mkAppRange (f : Term) (i j : Nat) (args : Array Term) : Term :=
  mkAppRangeAux j args i f

def n_of_univ : Term → Nat 
  | .var _ => 0
  | .abs t₁ t₂ => 
    let t₁_univ := match t₁ with | some t => t.n_of_univ | none => 0
    max t₁_univ t₂.n_of_univ
  | .app t₁ t₂ 
  | .ann t₁ t₂
  | .prod t₁ t₂ => max t₁.n_of_univ t₂.n_of_univ
  | .const _ arr => arr.foldl (fun acc l => max acc l.n_of_univ) 0
  | .sort l => l.n_of_univ

def prop : Term := .sort 0
def type (l : Level) : Term := .sort l.succ

def toString : Term → String
    | .var i => s!"{i}"
    | .sort l => s!"Sort {l}"
    | .app t1 t2 => s!"({t1.toString}) ({t2.toString})"
    | .abs (some t1) t2 => s!"λ {t1.toString} => {t2.toString}"
    | .abs _ t2 => s!"λ _ => {t2.toString}"
    | .prod t1 t2  => s!"Π ({t1.toString}). {t2.toString}"
    | .const s #[] => s
    | .const s arr => s ++ Array.toString₂ ".{" "," "}" arr
    | .ann t ty => s!"({t.toString} : {ty.toString})"

instance : ToString Term := ⟨Term.toString⟩

partial def substitute_univ (lvl : Array Level) : Term → Term
  | sort l => sort $ l.substitute lvl
  | var n => var n
  | app t₁ t₂ => app (t₁.substitute_univ lvl) (t₂.substitute_univ lvl)
  | abs ty body => abs (ty.map (substitute_univ lvl)) (body.substitute_univ lvl)
  | prod a b => prod (a.substitute_univ lvl) (b.substitute_univ lvl)
  | ann t ty => ann (t.substitute_univ lvl) (ty.substitute_univ lvl) 
  | const s arr => const s $ arr.map (Level.substitute · lvl)

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


def isConstOf : Term → Name → Bool
  | const n .., m => n == m
  | _,          _ => false
