import Proost.Kernel.Core

open Term

def exists_ := const "Exists" #[]
def fst_ := const "fst" #[]
def snd_ := const "snd" #[]

def «exists» : AxiomVal :=
  { name := "Exists"
    type := 
        prod prop
      $ prod (prod (bvar 1) prop) 
      $ prop
  }

def exists_intro : AxiomVal :=
  { name := "Exists_intro"
    type := 
      -- (A : Prop) -> (B :A -> Prop) -> (x : A) -> (y : B x) -> Exists A B
        prod prop
      $ prod (prod (bvar 1) prop) 
      $ prod (bvar 2)
      $ prod (app (bvar 2) (bvar 1))
      $ mkAppN (const "Exists" #[]) #[bvar 4, bvar 3]
  }

-- We favor a negative presentation of the existential since it's easier to define
-- reduction over equality/cast that way
def fst: AxiomVal :=
  { name := "fst"
    type := 
      -- (A : Prop) -> (B :A -> Prop) -> Exists A B -> A
        prod prop
      $ prod (prod (bvar 1) prop) 
      $ prod (mkAppN (const "Exists" #[]) #[bvar 2, bvar 1])
      $ bvar (3)
  }

def snd: AxiomVal :=
  { name := "snd"
    type := 
      -- (A : Prop) -> (B :A -> Prop) -> Exists A B -> A
        prod prop
      $ prod (prod (bvar 1) prop) 
      $ prod (mkAppN (const "Exists" #[]) #[bvar 2, bvar 1])
      $ app (bvar 2) (mkAppN (const "fst" #[]) #[bvar 3, bvar 2, bvar 1])
  }