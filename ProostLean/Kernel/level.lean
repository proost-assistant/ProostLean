import ProostLean.Kernel.Reduce
open Reduce
inductive Level : Type :=
  | zero : Level
  | succ : Level → Level 
  | max  : Level → Level → Level 
  | imax : Level → Level → Level 
  | var  : Nat   → Level 
deriving Repr, DecidableEq, Inhabited

def foo : Nat → Level 
  | 0 => .zero
  | n+1 => .succ $ foo n

instance : OfNat Level n := ⟨
  let rec foo : Nat → Level 
    | 0 => .zero
    | n+1 => .succ $ foo n
  foo n
⟩ 
@[matchPattern]
instance : HAdd Level Nat Level := ⟨
  let rec foo (l : Level): Nat → Level
    | 0 => l
    | n+1 => foo l.succ n
  foo
⟩ 

inductive State : Type :=
  | true
  | false
  | stuck : Nat → State
deriving Inhabited

def State.isTrue : State → Bool
  | .true => .true
  | _ => .false

namespace Level

partial def normalize (self: Level) : Level := match self with
  | imax u v => 
    if u = v then u else 
    match v with
      | zero => v
      | succ _ => normalize (u.max v)
      | imax _ vw => max (u.imax vw) v
      | max vv vw => max (u.imax vv) $ u.imax vw
      | _ => self
  | max u v => 
    if u = v then u else 
    match u,v with
      | 0, _ => v
      | _,0 => u
      | succ uu, succ vv => (uu.max vv).succ
      | _,_ => self
  | _ => self

instance : Reduce Level := ⟨normalize⟩

def substitute_single (l : Level) (n : Nat) (u : Level):  Level := match l with
  | zero => zero
  | succ l => succ $ l.substitute_single n u
  | max l₁ l₂ => l₁.substitute_single n u |>.max $ l₂.substitute_single n u  
  | imax l₁ l₂ => l₁.substitute_single n u |>.imax $ l₂.substitute_single n u 
  | var k => if k=n then u else l

def substitute (l : Level) (univs : Array Level):  Level := match l with
  | zero => zero
  | succ l => succ $ l.substitute univs
  | max l₁ l₂ => l₁.substitute univs |>.max $ l₂.substitute univs 
  | imax l₁ l₂ => l₁.substitute univs |>.imax $ l₂.substitute univs
  | var k => univs[k]!

partial def geq_no_subst (lhs rhs : Level) (n : Int) : State := Id.run do

  let lhs := reduce lhs
  let rhs := reduce rhs

  if let .zero := lhs then if n >= 0 then
    return .true
  if lhs=rhs && n>=0 then
    return .true
  if let .succ lhs := lhs then
    return lhs.geq_no_subst rhs (n-1)
  if let .succ rhs := rhs then
    return lhs.geq_no_subst rhs (n+1)
  
  --max split cases
  if let .max l₁ l₂ := rhs then
    if (lhs.geq_no_subst l₁ n |>.isTrue) || (lhs.geq_no_subst l₂ n |>.isTrue) then
      return .true
  if let .max l₁ l₂ := lhs then
    if (l₁.geq_no_subst rhs n |>.isTrue) && (l₂.geq_no_subst rhs n |>.isTrue) then
      return .true

  -- stuck cases where imaxes couldn't reduce
  if let .imax _ $ .var i := lhs then 
    return .stuck i
  if let .imax _ $ .var i := rhs then 
    return .stuck i
  
  return .false
  
partial def geq (lhs rhs : Level) (n : Int) : Bool :=
  match lhs.geq_no_subst rhs n with
    | .true => true
    | .false => false
    | .stuck i =>
      (lhs.substitute_single i zero |>.geq (rhs.substitute_single i zero) n) &&
      (lhs.substitute_single i (.succ $ .var i) |>.geq (rhs.substitute_single i (.succ $ .var i)) n)

def is_eq (lhs rhs : Level) : Bool := lhs.geq rhs 0

instance : BEq Level := ⟨is_eq⟩   
end Level


