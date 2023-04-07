import Proost.Kernel.Axioms.Eq
import Proost.Kernel.Axioms.Logic
import Proost.Kernel.Axioms.Nat


@[inline]
def axioms : List Axiom :=
  [ eq_axioms,
    logic_axioms,
    nat_axioms
  ] |>.join


def initialize_env : TCEnv α →TCEnv α := with_add_axioms axioms