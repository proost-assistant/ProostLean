import ProostLean.Kernel.Axioms.Eq

@[inline]
def axioms : List Axiom :=
  [
    eq_axioms
    
  ] |>.join


def initialize_env : TCEnv Unit := add_axioms axioms