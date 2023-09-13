import Proost.Kernel.Core

open Term

@[match_pattern]
def nat_  := const "Nat" #[]
@[match_pattern]
def zero_ := const "zero" #[]
@[match_pattern]
def succ_ := const "succ" #[]

@[match_pattern]
def nat_rec_ (l : Level) := const "Nat_rec" #[l]

def nat : InductiveVal :=
  { name := "Nat"
    type := type 0
    numParams := 0
    numIndices := 0
    all := ["Nat"]
    ctors := ["zero","succ"]
    isRec := true
    isReflexive := false
    isNested := False
  }


def zero : ConstructorVal :=
  { name := "zero"
    type := nat_
    induct := "Nat"
    cidx := 0
    numParams := 0
    numFields := 0
  }

def succ : ConstructorVal :=
  { name := "succ"
    type := prod nat_ nat_
    induct := "Nat"
    cidx := 1
    numParams := 0
    numFields := 1
  }
        -- ∀ _, 1 zero → (∀ _, 3 1 → 3 (succ 2)) → ∀ _, 4 1
--Nat_rec : (P : Nat → Sort u) -> P 0 -> ((n : Nat) -> P n -> P (succ n)) -> () 
def nat_rec : RecursorVal :=
  { name := "Nat_rec"
    type := 
        prod (prod nat_ (sort $ .var 0))
      $ prod (app (bvar 1) (const "zero" #[]))
      $ prod (prod nat_ (prod (app (bvar 3) (bvar 1)) (app (bvar 4) (app succ_ (bvar 2)))))
      $ prod nat_ 
      $ app (bvar 4) (bvar 1)
    all := ["Nat"]
    numParams := 0
    numIndices := 0
    numMotives := 1
    numMinors := 2
    k := false
    rules := [{
      ctor := "zero"
      nfields := 0
      rhs := 
          --λ motive zero succ n => zero
          .abs none 
        $ .abs none
        $ .abs none
        $ bvar 2
    },{
      ctor := "succ"
      nfields := 1
      rhs := 
          --λ motive p_zero p_succ n => p_succ n (Nat_rec.{u} motive p_zero p_succ n)
          .abs none 
        $ .abs none
        $ .abs none
        $ .abs none
        $ (bvar 2) (bvar 1) (nat_rec_ (.var 0) (bvar 4) (bvar 3) (bvar 2) (bvar 1))
    }
    ]
  }

/-def reduce_nat_rec : Value → Option Value 
  | .neutral (.ax nat_rec) l::[P,P_zero,P_succ,n] => 
    match n with
      | .neutral (.ax zero) []  => some P_zero
      | .neutral (.ax succ) [n] => -/
partial def reduce_nat_rec (t: Term) : TCEnv (Option Term) := do
  let no := pure none
  let ⟨hd,arr⟩:= t.getAppFnArgs
  let hd@(nat_rec_ _) ← whnf hd | no
  let some n := arr[3]? | no
  match ← whnf n with
    | zero_ => pure arr[1]!
    | .app s k =>
        let .const "succ" _ ← whnf s | no
        let p_succ := arr[2]!
        let new_rec_args := arr.modify 3 (λ _ => k)
        return some $ p_succ k (mkAppN hd new_rec_args)
    | _ => no


def nat_axioms : List Declaration :=
  [nat,zero,succ,nat_rec]
