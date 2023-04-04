import Proost.Util.AppSep

inductive Level : Type :=
  | zero : Level
  | plus : Level → Nat → Level
  | max  : Level → Level → Level
  | imax : Level → Level → Level
  | var  : Nat   → Level
deriving Repr, DecidableEq, Inhabited

def Level.succ : Level → Level := (·.plus 1) 

def Level.toNum? : Level → Option Nat
  | zero => some 0
  | plus l n => l.toNum?.map (· + n)
  | max l₁ l₂ => do pure $ Nat.max (← l₁.toNum?) (← l₂.toNum?)
  | imax l₁ l₂ =>
    if let some 0 := l₂.toNum? then some 0
    else do pure $ Nat.max (← l₁.toNum?) (← l₂.toNum?)
  | var .. => none

def Level.toString (l : Level): String :=
  if let some n := l.toNum? then s!"{n}"
  else match l with
  | zero => unreachable!
  | plus l n => l.toString ++ s!"+ {n}"
  | var i => "u" ++ ToString.toString i
  | max l1 l2 => "max (" ++ l1.toString ++ ") (" ++ l2.toString ++")"
  | imax l1 l2 => "imax (" ++ l1.toString ++ ") (" ++ l2.toString ++")"

instance : ToString Level := ⟨Level.toString⟩

instance : OfNat Level n := ⟨
  let rec foo : Nat → Level
    | 0 => .zero
    | n+1 => .succ $ foo n
  foo n
⟩

@[match_pattern]
instance : HAdd Level Nat Level := ⟨Level.plus⟩

inductive State : Type :=
  | true
  | false
  | stuck : Nat → State
deriving Inhabited, Repr

def State.isTrue : State → Bool
  | .true => .true
  | _ => .false

namespace Level

partial def normalize (self: Level) : Level := match self with
  | imax u v =>
    if u = v then u else
    match normalize v with
      | zero => v
      | plus _  (_+1) => normalize (u.max v)
      | imax _ vw => normalize $ max (u.imax vw) v
      | max vv vw => normalize $ max (u.imax vv) $ u.imax vw
      | _ => self
  | max u v =>
    if u = v then u else
    match u,v with
      | 0, _ => v
      | _,0 => u
      | plus uu n₁, plus vv n₂ => 
        let n := min n₁ n₂
        ((plus uu $ n₁-n).max (plus vv $ n₂-n)).plus n
      | _,_ => self
  | plus l 0 => normalize l
  | plus l₁ n₁ =>
    if let plus l₂ n₂ := normalize l₁ then
      plus l₂ (n₁+n₂)
    else self
  | _ => self

def n_of_univ : Level → Nat 
  | zero => 0
  | plus l _ => l.n_of_univ
  | max l₁ l₂
  | imax l₁ l₂ => Max.max l₁.n_of_univ l₂.n_of_univ
  | var k => k

def substitute_single (l : Level) (n : Nat) (u : Level):  Level := match l with
  | zero => zero
  | plus l n₂ => plus £ l.substitute_single n u £ n₂
  | max l₁ l₂ => l₁.substitute_single n u |>.max $ l₂.substitute_single n u
  | imax l₁ l₂ => l₁.substitute_single n u |>.imax $ l₂.substitute_single n u
  | var k => if k=n then u else l

def substitute (l : Level) (univs : Array Level):  Level := match l with
  | zero => zero
  | plus l n => plus £ l.substitute univs £ n
  | max l₁ l₂ => l₁.substitute univs |>.max $ l₂.substitute univs
  | imax l₁ l₂ => l₁.substitute univs |>.imax $ l₂.substitute univs
  | var k => univs[k]!

partial def geq_no_subst (lhs rhs : Level) (n : Int) : State := Id.run do

  let lhs := normalize lhs
  let rhs := normalize rhs

  if let .zero := lhs then if n >= 0 then
    return .true
  if lhs=rhs && n>=0 then
    return .true
  if let .plus lhs k := lhs then
    return lhs.geq_no_subst rhs (n-k)
  if let .plus rhs k := rhs then
    return lhs.geq_no_subst rhs (n+k)

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

def is_eq (lhs rhs : Level) : Bool := lhs.geq rhs 0 && rhs.geq lhs 0

instance : BEq Level := ⟨is_eq⟩

end Level


