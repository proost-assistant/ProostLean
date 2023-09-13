import Proost.Kernel.Core
import Proost.Kernel.Axioms.Logic
import Proost.Kernel.Axioms.Nat
import Proost.Kernel.Axioms.Exists
import Proost.Kernel.Term

open Term
@[match_pattern]
def eq_ (l : Level) := const "Eq" #[l]
def refl_ (l : Level) := const "Refl" #[l]
@[match_pattern]
def cast__ (l : Level) := const "cast" #[l]

def sort_u := sort $ .var 0

def eq : InductiveVal :=
  { name := "Eq"
    type := prod sort_u $ prod (bvar 1) $ prod (bvar 2) prop
    all := ["Eq"]
    numParams := 2
    numIndices := 1
    ctors := ["refl"]
    isRec := false
    isReflexive := false
    isNested := false
  }

def refl : ConstructorVal := 
  { name := "refl"
    induct := "Eq"
    type := 
      -- (A : Sort u) -> (x : A) -> Eq.{u} A x x
      prod sort_u $ prod (bvar 1) $ const "Eq" #[.var 0] (bvar 2) (bvar 1) (bvar 1)
    cidx := 1
    numParams := 2
    numFields := 1
  }

def cast_ : AxiomVal :=
  {
    name := "cast"
    type := 
      -- (A B : Sort u) -> Eq.{u+1} (Sort u) A B -> A -> B
        prod sort_u 
      $ prod sort_u 
      $ prod (const "Eq" #[.succ $ .var 0] (.sort (.var 0)) (bvar 2) (bvar 1)) 
      $ prod (bvar 3) 
      $ bvar 3
  }
  
def transport : AxiomVal :=
  {
    name := "transp"
    type :=
      -- (A : Type u) -> (t : A) -> (B : A -> Prop) -> B t -> (t' : A) → Eq.{u+1} A t t' -> B t'
        prod (type $ .var 0)
      $ prod (bvar 1)
      $ prod (prod (bvar 2) prop)
      $ prod ((bvar 1) (bvar 3))
      $ prod (bvar 4)
      $ prod (eq_ (.succ $ .succ $ .var 0) (bvar 5) (bvar 4) (bvar 1)) 
      $ (bvar 4) (bvar 2)
  }

def eq_axioms : List Declaration :=
  [eq,refl,cast_,transport]

--def eq_rec : AxiomVal := 
--  { name := "Eq_rec"
--    type := 
--      let sort_u := sort (.bvar 0)
--      let sort_v := sort (.bvar 1)
--      -- {α : Sort u_2} → {a : α} → {motive : (a_1 : α) → a = a_1 → Sort u_1} 
--      -- → motive a (_ : a = a) → {a_1 : α} → (t : a = a_1) → motive a_1 t
--      prod sort_u
--      $ prod (bvar 1)
--      $ prod (
--             prod (bvar 2)
--          $  prod (eq_ (.bvar 1)  (bvar 3) (bvar 2) (bvar 1))
--          $  sort_v
--         )
--    $  prod (
--          (bvar 1) (bvar 2) (refl_ (.bvar 1) (bvar 3) (bvar 2) (bvar 2))
--         )
--      $ prod (bvar 4)
--      $ prod (eq_ (.bvar 1) (bvar 5) (bvar 4) (bvar 1))
--      $ mkAppN (bvar 4) #[bvar 2, bvar 1]
--  }


def reduce_eq_prod (d₁ d₂ b₁ b₂ : Term) : TCEnv (Option Term) := do
  let s₁@(sort l₁) ← infer d₁ | unreachable!
  let s₂@(sort l₂) ← infer b₁ | unreachable!
  let rhs := 
      --(a' : d₂) ->  b₁ (cast d₂ d₁ e a')) = b2 a'
      prod d₂ 
    $ eq_ (l₂+1) s₂ (b₁ (cast__ l₁ d₂ d₁ (bvar 2) (bvar 1))) (b₂ (bvar 1))
  return some$ exists_ (eq_ (l₁+1) s₁ d₂ d₁) (abs none rhs)

--returns true if the heads are definitely different
def hd_different : Term → Term → TCEnv Bool
  | const s₁ _, const s₂ _ => pure $ s₁ = s₂
  | prod A _, prod B _ => conversion A B
  | sort _, sort _ => pure false
  | _,_ => pure true

def reduce_eq_type (A B : Term): TCEnv (Option Term) := do
  if ← conversion A B then
    return true_
  let A ← whnf A
  let B ← whnf B
  if ← hd_different A B then
    return false_
  match A, B with
    | prod d₁ b₁, prod d₂ b₂ =>  reduce_eq_prod d₁ d₂ b₁ b₂
    | _,_ => pure none

def reduce_eq_prop (A B : Term): TCEnv (Option Term) := 
  --Eq Prop A B => (A -> B ∧ B -> A)
  let res := exists_ (prod A B) (abs A (prod B A))
  return some res

def reduce_eq_sort (l : Level) : Term → Term → TCEnv (Option Term) := 
  if l.is_eq 0 then 
    reduce_eq_prop
  else 
    reduce_eq_type


/-- Reduces `Eq.{1} Nat self rhs` by checking the whnf of self and rhs as such: 
    match (self,rhs) with
      | 0,0 => True
      | S k, S n => Eq.{1} Nat k n
      | 0, S _ | S _, 0 => False-/
def reduce_eq_nat (t₁ t₂ : Term): TCEnv (Option Term) := do
  let no := pure none
  let t₁ ← whnf t₁
  let t₂ ← whnf t₂
  match t₁,t₂ with
    | zero_,zero_ => pure true_
    | .app hd₁ arg₁, .app hd₂ arg₂ => 
        let .const "succ" _succ_ ← whnf hd₁ | no
        let .const "succ" _succ_ ← whnf hd₂ | no
        whnf (eq_ 1 nat_ arg₁ arg₂)
    | zero_, app hd₁ _ | app hd₁ _,zero_ =>
        let .const "succ" _succ_ ← whnf hd₁ | no
        pure false_
    | _,_ => pure none

def reduce_eq_fun (A B t₁ t₂ : Term): TCEnv (Option Term) := do
  let sort l ← infer B | unreachable!
  let x := bvar 1
  let new_eq := eq_ l (B.substitute x 1) (app (t₁.shift 1 0) x) (app (t₂.shift 1 0) x) 
  return prod A new_eq

def reduce_eq (t: Term) : TCEnv (Option Term) := do
  let no := pure none
  let ⟨hd,arr⟩:= t.getAppFnArgs
  let (eq_ l) ← whnf hd    | no
  let some type := arr[0]? | no
  let some t₁   := arr[1]? | no
  let some t₂   := arr[2]? | no
  --equality over Prop terms always reduces to True
  if l.is_eq 0 then 
    return some true_
  let type ← whnf type
  let res ← 
    match type with
      | sort l => reduce_eq_sort l t₁ t₂
      | const "Nat" _ => reduce_eq_nat t₁ t₂
      | prod A B => reduce_eq_fun A B t₁ t₂ 
      | _ => pure none
  if let some t := res then
    return mkAppN t arr[3:]
  else pure none

def red_cast_nat (e n : Term) : TCEnv (Option Term) := do
  let no := pure none
  match ← whnf n with
    | zero_ => pure zero_
    | app s k =>
      let .const "succ" _ ← whnf s | no
      pure $ succ_ (cast__ 1 nat_ nat_ e k)
    | _ => no

def red_cast_prod (A A' B B' e f : Term) : TCEnv (Option Term) := do
  let s₁@(sort l₁) ← infer A | unreachable!
  let s₂@(sort l₂) ← infer A' | unreachable!
  let lhs_exists := (eq_ (l₁+1) s₁ A' A)
  --(e : A' = A) -> (a' : d₂) ->  b₁ (cast d₂ d₁ e a')) = b2 a'
  let rhs_exists := 
       prod lhs_exists
    $  prod A' 
    $ eq_ (l₂+1) s₂ (B  (cast__ l₁ A' A (bvar 2) (bvar 1))) (B' (bvar 1))
  let a' := bvar 1
  let a := cast__ (l₁+1) s₁ A' A (fst_ lhs_exists rhs_exists e) a'
  let res :=
    abs A' (cast__ (l₂+1) s₂ (B a) (B' a') (snd_ lhs_exists rhs_exists e a') (f a)) 
  pure res

def reduce_cast (t: Term) : TCEnv (Option Term) := do
  let no := pure none
  let ⟨hd,arr⟩:= t.getAppFnArgs
  let (cast__ _) ← whnf hd | no
  let some ty_origin := arr[0]? | no
  let some ty_target := arr[1]? | no
  let some e         := arr[2]? | no
  let some a         := arr[3]? | no
  let ty_origin ← whnf ty_origin
  let ty_target ← whnf ty_target
  let res ← 
    match ty_origin,ty_target with
      | nat_,nat_ => red_cast_nat e a
      | sort _, sort _ => pure a
      | prod d₁ b₁, prod d₂ b₂ => red_cast_prod d₁ d₂ b₁ b₂ e a
      | _,_ => pure none
  if let some t := res then
    return mkAppN t arr[4:]
  else pure none

--def eq_axioms : List AxiomVal :=
--  [eq,refl,eq_rec]
--
--
--partial def reduce_eq_rec (t: Term) : TCEnv (Option Term) := do
--  let no := pure none
--  let ⟨hd,arr⟩:= t.getAppFnArgs
--  let (.const "Eq_rec" _) ← whnf hd | no
--  let some _eq := arr[5]? | no
--  try
--    let () ← isDefEq arr[2]! arr[4]!
--    return some (arr[3]!)
--  catch e => throw e
--
--

def reduceEqCast (n : Name) (t : Term) : TCEnv Term := do
    if n = "Eq" then 
      let some t ← reduce_eq t | pure t
      pure t
    else if n = "cast" then
      let some t ← reduce_cast t | pure t
      pure t
    else pure t