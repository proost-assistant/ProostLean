import Proost.Kernel.Core

open Term

def true_ : AxiomVal :=
  { name := "True"
    type := prop
  }

def tt : AxiomVal :=
  { name := "Tt"
    type := const "True" #[]
  }

def false_ : AxiomVal :=
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
  [true_,tt,false_,false_rec]
