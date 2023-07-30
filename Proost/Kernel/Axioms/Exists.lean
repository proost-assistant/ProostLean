import Proost.Kernel.Core

open Term

def exists_ := const "Exists" #[]
def fst_ := const "fst" #[]
def snd_ := const "snd" #[]

def «exists» : AxiomVal :=
  { name := "Exists"
    type := 
        prod prop
      $ prod (prod (var 1) prop) 
      $ prop
  }

def exists_intro : AxiomVal :=
  { name := "Exists_intro"
    type := 
      -- (A : Prop) -> (B :A -> Prop) -> (x : A) -> (y : B x) -> Exists A B
        prod prop
      $ prod (prod (var 1) prop) 
      $ prod (var 2)
      $ prod (app (var 2) (var 1))
      $ mkAppN (const "Exists" #[]) #[var 4, var 3]
  }

-- We favor a negative presentation of the existential since it's easier to define
-- reduction over equality/cast that way
def fst: AxiomVal :=
  { name := "fst"
    type := 
      -- (A : Prop) -> (B :A -> Prop) -> Exists A B -> A
        prod prop
      $ prod (prod (var 1) prop) 
      $ prod (mkAppN (const "Exists" #[]) #[var 2, var 1])
      $ var (3)
  }

def snd: AxiomVal :=
  { name := "snd"
    type := 
      -- (A : Prop) -> (B :A -> Prop) -> Exists A B -> A
        prod prop
      $ prod (prod (var 1) prop) 
      $ prod (mkAppN (const "Exists" #[]) #[var 2, var 1])
      $ app (var 2) (mkAppN (const "fst" #[]) #[var 3, var 2, var 1])
  }