import Proost.Kernel.Core

open Term

def eq : AxiomVal :=
  { name := "Eq"
    type := prod (sort $ .var 1) $ prod (var 1) $ prod (var 1) prop
  }

def refl : AxiomVal := 
  { name := "refl"
    type := 
      -- (A : Sort u) -> (x : A) -> Eq.{u} A x x
      prod (sort $ .var 1) $ prod (var 1) $ const "Eq" #[.var 1] |>.app (var 2) |>.app (var 1) |>.app (var 1)
  }

def cast_ : AxiomVal :=
  {
    name := "cast"
    type := 
      -- (A B : Sort u) -> Eq.{u+1} A B -> A -> B
        prod (sort $ .var 1) 
      $ prod (sort $ .var 1) 
      $ prod (const "Eq" #[.succ $ .var 1] |>.app (.sort (.var 1)) |>.app (var 2) |>.app (var 1)) 
      $ prod (var 3) 
      $ var 3
  }
  
def transport : AxiomVal :=
  {
    name := "transp"
    type :=
      -- (A : Type u) -> (t t' : A) -> (B : A -> Prop) -> B t -> Eq.{u+1} t t' -> B t'
        prod (type $ .var 1)
      $ prod (var 1)
      $ prod (var 2)
      $ prod (prod (var 3) prop)
      $ prod (app (var 1) (var 3))
      $ prod (const "Eq" #[.succ $ .var 1] |>.app (var 4) |>.app (var 3)) 
      $ (app (var 3) (var 4))
  }

def eq_axioms : List AxiomVal :=
  [eq,refl,cast_,transport]
