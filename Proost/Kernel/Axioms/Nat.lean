import Proost.Kernel.Core
import Proost.Kernel.Term

open Term

def nat : Axiom :=
  { name := "Nat"
    type := type 0
  }

def nat_ : Term := const "Nat" #[]

def zero : Axiom :=
  { name := "zero"
    type := nat_
  }

def succ : Axiom :=
  { name := "succ"
    type := prod nat_ nat_
  }

--Nat_rec : (P : Nat → Sort u) -> P 0 -> ((n : Nat) -> P n -> P (succ n)) -> () 
def nat_rec : Axiom :=
  { name := "Nat_rec"
    type := 
        prod (prod nat_ (sort $ .var 1))
      $ prod (app (var 1) (const "zero" #[]))
      $ prod (prod nat_ (app (var 2) (app (const "succ" #[]) (var 1))))
      $ prod nat_ 
      $ app (var 4) (var 1)
  }

/-def reduce_nat_rec : Value → Option Value 
  | .neutral (.ax nat_rec) l::[P,P_zero,P_succ,n] => 
    match n with
      | .neutral (.ax zero) []  => some P_zero
      | .neutral (.ax succ) [n] => -/


def nat_axioms : List Axiom :=
  [nat,zero,succ,nat_rec]
