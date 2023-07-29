import Proost.Kernel.Core

open Term

def nat : AxiomVal :=
  { name := "Nat"
    type := type 0
  }

def nat_ : Term := const "Nat" #[]

def zero : AxiomVal :=
  { name := "zero"
    type := nat_
  }

def succ : AxiomVal :=
  { name := "succ"
    type := prod nat_ nat_
  }
        -- ∀ _, 1 zero → (∀ _, 3 1 → 3 (succ 2)) → ∀ _, 4 1
--Nat_rec : (P : Nat → Sort u) -> P 0 -> ((n : Nat) -> P n -> P (succ n)) -> () 
def nat_rec : AxiomVal :=
  { name := "Nat_rec"
    type := 
        prod (prod nat_ (sort $ .var 0))
      $ prod (app (var 1) (const "zero" #[]))
      $ prod (prod nat_ (prod (app (var 3) (var 1)) (app (var 4) (app (const "succ" #[]) (var 2)))))
      $ prod nat_ 
      $ app (var 4) (var 1)
  }

/-def reduce_nat_rec : Value → Option Value 
  | .neutral (.ax nat_rec) l::[P,P_zero,P_succ,n] => 
    match n with
      | .neutral (.ax zero) []  => some P_zero
      | .neutral (.ax succ) [n] => -/
partial def reduce_nat_rec (t: Term) : TCEnv (Option Term) := do
  let no := pure none
  let ⟨hd,arr⟩:= t.getAppFnArgs
  let hd@(.const "Nat_rec" _) ← whnf hd | no
  let some n := arr[3]? | no
  match ← whnf n with
    | .const "zero" _ => pure arr[1]!
    | .app s k =>
        let .const "succ" _ ← whnf s | no
        let p_succ := arr[2]!
        let new_rec_args := arr.modify 3 (λ _ => k)
        return some $ .app (.app p_succ k) (hd.mkAppN new_rec_args)
    | _ => no



def nat_axioms : List AxiomVal :=
  [nat,zero,succ,nat_rec]
