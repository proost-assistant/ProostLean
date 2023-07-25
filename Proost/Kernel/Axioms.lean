import Proost.Kernel.Axioms.Eq
import Proost.Kernel.Axioms.Logic
import Proost.Kernel.Axioms.Nat
import Std.Data.HashMap
open Std

@[inline]
def axioms : List AxiomVal :=
  [ eq_axioms,
    logic_axioms,
    nat_axioms
  ] |>.join


@[inline]
partial def all_recs : Unit →  HashMap String (Term → TCEnv (Option Term)) := λ () =>
  HashMap.empty.insert "Nat_rec" reduce_nat_rec

@[inline]
def red_recs : List RedRec := []

def with_initialize_env_axioms : TCEnv α → TCEnv α := 
  with_add_axioms axioms

