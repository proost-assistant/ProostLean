import Proost.Kernel.Axioms.Eq
import Proost.Kernel.Axioms.Logic
import Proost.Kernel.Axioms.Nat


@[inline]
def axioms : List Axiom :=
  [ eq_axioms,
    logic_axioms,
    nat_axioms
  ] |>.join

@[inline]
def red_recs : List RedRec := []

def with_initialize_env_axioms : TCEnv α → TCEnv α := with_add_axioms axioms

