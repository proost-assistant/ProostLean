import Proost.Kernel.Core

open Term

def true_ := const "True" #[]
def false_ := const "False" #[]

def true : InductiveVal :=
  { name := "True"
    type := prop
    numParams := 0
    numIndices := 0
    all := ["True"]
    ctors := ["tt"]
    isRec := false
    isReflexive := false
    isNested := false
  }

def tt : ConstructorVal :=
  { name := "tt"
    type := const "True" #[]
    induct := "True"
    cidx := 0
    numParams := 0
    numFields := 0
  }

def false : InductiveVal :=
  { name := "False"
    type := prop
    numParams := 0
    numIndices := 0
    all := ["false"]
    ctors := []
    isRec := Bool.false
    isReflexive := Bool.false
    isNested := Bool.false
  }

def false_rec : RecursorVal :=
  { name := "False_rec"
    type := 
        prod (sort $ .var 0)
      $ prod (const "False" #[])
      $ var 2
    all := ["False"]
    numParams := 0
    numIndices := 0
    numMotives := 1
    k := .true
    numMinors := 0
    rules := []
  }

def logic_axioms : List Declaration :=
  [true,tt,false,false_rec]
