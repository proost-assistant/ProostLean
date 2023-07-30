import Proost.Kernel.Axioms.Eq
import Proost.Kernel.Axioms.Logic
import Proost.Kernel.Axioms.Nat
import Std.Data.HashMap
open Std

def axioms : List Declaration :=
  [ eq_axioms,
    logic_axioms,
    nat_axioms
  ] |>.join

def with_initialize_env_axioms : TCEnv α → TCEnv α := 
  with_add_axioms axioms