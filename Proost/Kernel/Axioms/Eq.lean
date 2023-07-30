import Proost.Kernel.Core

open Term

def eq : AxiomVal :=
  { name := "Eq"
    type := prod (sort $ .var 0) $ prod (var 1) $ prod (var 2) prop
  }

def refl : AxiomVal := 
  { name := "Refl"
    type := 
      -- (A : Sort u) -> (x : A) -> Eq.{u} A x x
      prod (sort $ .var 0) $ prod (var 1) $ const "Eq" #[.var 0] |>.app (var 2) |>.app (var 1) |>.app (var 1)
  }

--def cast_ : AxiomVal :=
--  {
--    name := "cast"
--    type := 
--      -- (A B : Sort u) -> Eq.{u+1} A B -> A -> B
--        prod (sort $ .var 1) 
--      $ prod (sort $ .var 1) 
--      $ prod (const "Eq" #[.succ $ .var 1] |>.app (.sort (.var 1)) |>.app (var 2) |>.app (var 1)) 
--      $ prod (var 3) 
--      $ var 3
--  }
--  
--def transport : AxiomVal :=
--  {
--    name := "transp"
--    type :=
--      -- (A : Type u) -> (t t' : A) -> (B : A -> Prop) -> B t -> Eq.{u+1} t t' -> B t'
--        prod (type $ .var 1)
--      $ prod (var 1)
--      $ prod (var 2)
--      $ prod (prod (var 3) prop)
--      $ prod (app (var 1) (var 3))
--      $ prod (const "Eq" #[.succ $ .var 1] |>.app (var 4) |>.app (var 3)) 
--      $ (app (var 3) (var 4))
--  }
--
--def eq_axioms : List AxiomVal :=
--  [eq,refl,cast_,transport]

def eq_rec : AxiomVal := 
  { name := "Eq_rec"
    type := 
      let sort_u := sort (.var 0)
      let sort_v := sort (.var 1)
      -- {α : Sort u_2} → {a : α} → {motive : (a_1 : α) → a = a_1 → Sort u_1} 
      -- → motive a (_ : a = a) → {a_1 : α} → (t : a = a_1) → motive a_1 t
      prod sort_u
      $ prod (var 1)
      $ prod (
             prod (var 2)
          $  prod (mkAppN (const "Eq" #[.var 1]) #[var 3, var 2, var 1])
          $  sort_v
         )
    $  prod (
          mkAppN (var 1) #[var 2, mkAppN (const "Refl" #[.var 1]) #[var 3, var 2, var 2]]
         )
      $ prod (var 4)
      $ prod (mkAppN (const "Eq" #[.var 1]) #[var 5, var 4, var 1])
      $ mkAppN (var 4) #[var 2, var 1]
  }

def eq_axioms : List AxiomVal :=
  [eq,refl,eq_rec]


partial def reduce_eq_rec (t: Term) : TCEnv (Option Term) := do
  let no := pure none
  let ⟨hd,arr⟩:= t.getAppFnArgs
  let (.const "Eq_rec" _) ← whnf hd | no
  let some _eq := arr[5]? | no
  try
    let () ← isDefEq arr[2]! arr[4]!
    return some (arr[3]!)
  catch e => throw e

