import Proost.Kernel.Level
import Std.Data.HashMap
import Proost.Util.Misc
import Proost.Util.Attach

open Std

abbrev Name := String

inductive Term : Type :=
  | fvar   : Name → Term
  | bvar   : Nat → Term
  | sort  : Level → Term
  | app   : Term → Term → Term
  | abs   : Option Term → Term → Term
  | prod  : Term → Term → Term
  | const : Name → Array Level →  Term
deriving Repr, Inhabited, BEq

abbrev VarContext := Array $ Option Term
abbrev TypedTerm := Term × Term

open Term

def mkAppN : Term → Array Term → Term := fun hd arr =>
  arr.foldl app hd

partial def mkAppRangeAux (n : Nat) (args : Array Term) (i : Nat) (e : Term) : Term :=
  if i < n then mkAppRangeAux n args (i+1) (app e (args.get! i)) else e

/-- `mkAppRange f i j #[a_1, ..., a_i, ..., a_j, ... ]` ==> the expression `f a_i ... a_{j-1}` -/
def mkAppRange (f : Term) (i j : Nat) (args : Array Term) : Term :=
  mkAppRangeAux j args i f

namespace Term


partial def abstract (n : Name): Term → Term :=
  go 0
where
  go outer := fun
    | fvar fv =>
        if fv = n then
          bvar outer
        else 
          fvar fv
    | abs dom codom =>
        abs (dom.map $ go outer) (go (outer+1) codom)
    | prod dom codom =>
        prod (go outer dom) (go (outer+1) codom)
    | app f x => app (go outer f) (go outer x)
    | t@(bvar ..) 
    | t@(const ..)
    | t@(sort ..) => t

partial def instantiate1 (image : Term) : Term → Term :=
  go 0
where
  go outer := fun
    | bvar b =>
      if b = outer then 
        image
      else 
        bvar b
    | abs dom codom => 
        abs (dom.map $ go outer) (go (outer+1) codom)
    | prod dom codom => 
        prod (go outer dom) (go (outer+1) codom)
    | app f x => app (go outer f) (go outer x)
    | t@(fvar ..)
    | t@(const ..) 
    | t@(sort ..) => t


@[inline]
def substitute (image : Term) (name : Name) : Term → Term :=
  instantiate1 image ∘ abstract name

def getAppFn : Term →  Term
  | app f _ => f.getAppFn
  | t => t

def getAppArgs : Term → Array Term
  | app f arg => f.getAppArgs.push arg
  | _ => #[]

def getAppFnArgs : Term →  Term × Array Term
  | app f arg =>
    let ⟨f,args⟩ := f.getAppFnArgs
    ⟨f,args.push arg⟩
  | t => ⟨t,#[]⟩

def n_of_univ : Term → Nat 
  | bvar _ | fvar _ => 0
  | abs t₁ t₂ => 
    let t₁_univ := match t₁ with | some t => t.n_of_univ | none => 0
    max t₁_univ t₂.n_of_univ
  | app t₁ t₂ 
  | prod t₁ t₂ => max t₁.n_of_univ t₂.n_of_univ
  | const _ arr => arr.foldl (fun acc l => max acc l.n_of_univ) 0
  | sort l => l.n_of_univ

def prop : Term := .sort 0
def type (l : Level) : Term := .sort l.succ

def toString : Term → String
  | fvar n => n
  | bvar i => s!"{i}"
  | sort l => s!"Sort {l}"
  | app t1 t2 => s!"({t1.toString}) ({t2.toString})"
  | abs (some t1) t2 => s!"λ {t1.toString} => {t2.toString}"
  | abs _ t2 => s!"λ _ => {t2.toString}"
  | prod t1 t2  => s!"Π ({t1.toString}). {t2.toString}"
  | const s #[] => s
  | const s arr => s ++ Array.toString₂ ".{" "," "}" arr

instance : ToString Term := ⟨Term.toString⟩

def substitute_univ (lvl : Array Level) : Term → Term
  | sort l => sort $ l.substitute lvl
  | bvar n => bvar n
  | fvar fv => fvar fv
  | app t₁ t₂ => app (t₁.substitute_univ lvl) (t₂.substitute_univ lvl)
  | abs ty body => abs (ty.attach |>.map (λ ⟨e,_⟩ => substitute_univ lvl e)) (body.substitute_univ lvl)
  | prod a b => prod (a.substitute_univ lvl) (b.substitute_univ lvl)
  | const s arr => const s $ arr.map (Level.substitute · lvl)

def isConstOf : Term → Name → Bool
  | const n .., m => n == m
  | _,          _ => false
