import Proost.Kernel.Axioms.Eq
import Proost.Kernel.Axioms.Logic
import Proost.Kernel.Axioms.Nat
import Std.Data.HashMap
open Std

def axioms : List AxiomVal :=
  [ eq_axioms,
    logic_axioms,
    nat_axioms
  ] |>.join

partial def all_recs : HashMap String (Term → TCEnv (Option Term)) := 
  HashMap.ofList [("Nat_rec",reduce_nat_rec)]

def red_recs : List RedRec := []

def with_initialize_env_axioms : TCEnv α → TCEnv α := 
  with_add_axioms axioms

