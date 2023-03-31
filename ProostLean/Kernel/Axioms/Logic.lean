import ProostLean.Kernel.Core

open Term

def true_ : Axiom :=
  { name := "True"
    type := prop
  }

def tt : Axiom :=
  { name := "tt"
    type := const "True" #[]
  }

def false_ : Axiom :=
  { name := "False"
    type := prop
  }


def false_rec : Axiom :=
  { name := "False_rec"
    type := 
        prod (sort $ .var 1)
      $ prod (const "False" #[])
      $ var 2
  }

