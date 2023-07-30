import Proost.Kernel.Core

open Term

def true_ := const "True" #[]
def false_ := const "False" #[]

def true : AxiomVal :=
  { name := "True"
    type := prop
  }

def tt : AxiomVal :=
  { name := "tt"
    type := const "True" #[]
  }

def false : AxiomVal :=
  { name := "False"
    type := prop
  }

def false_rec : AxiomVal :=
  { name := "False_rec"
    type := 
        prod (sort $ .var 0)
      $ prod (const "False" #[])
      $ var 2
  }

def logic_axioms : List AxiomVal :=
  [true,tt,false,false_rec]
