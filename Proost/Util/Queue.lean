inductive Queue (α  : Type) := 
  | nil
  | unit : α → Queue α 
  | two : α → α → Queue α 
  | more : α → Queue α  → α → Queue α 
deriving Inhabited, DecidableEq, Repr

open Queue

namespace Queue

instance [Repr α] : ToString $ Queue α := ⟨fun x => reprStr x⟩

def length : Queue α → Nat
  | nil => 0
  | unit _ => 1
  | two .. => 2
  | more _ m _ => 2+ m.length


def head : Queue α → Option α
  | nil => none
  | unit a => a
  | two _ b => b
  | more _ _ b => b

def pop : Queue α →  Option (Queue α × α)
  | nil => none
  | unit a => pure (nil,a)
  | two a b => (unit a, b)
  | more a q₁ b => do 
    let (q₂, e) ← pop q₁
    (more a q₂ e,b)

def push (a : α) : Queue α → Queue α
  | nil => unit a
  | unit b => two a b
  | two b₁ b₂ => more a (unit b₁) b₂
  | more b₁ middle b₂ => more a (push b₁ middle) b₂

def push_all (q : Queue α) (arr : Array α) : Queue α := Id.run do
  let mut res := q
  for i in arr do
    res := res.push i
  res


def ofList : List α → Queue α
    | [] => nil
    | h::t => push h (ofList t)

instance : Coe (List α) (Queue α) where
  coe := ofList

def position [DecidableEq α] (x : α) : Queue α → Option Nat
  | nil => none
  | unit a => if x = a then some 0 else none
  | two a b =>
    if x = a then some 0 else
    if x = b then some 1 else
      none
  | more a middle b => do
    if x = a then
      some 0 
    else
    if let some res := position x middle then
      pure $ res + 1
    else
    if x = b then 
      some $ 1 + middle.length 
    else
      none

end Queue