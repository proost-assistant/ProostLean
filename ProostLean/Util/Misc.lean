@[specialize]
def List.allM₂ {m : Type → Type u} [Monad m] {α : Type v} {β : Type w} (f : α → β → m Bool) : List α → List β → m Bool
  | [],[]    => pure true
  | a::as,b::bs => do
    match (← f a b) with
    | true  => allM₂ f as bs
    | false => pure false
  | _,_ => pure false


def todo! {A : Type _} [Inhabited A] : A := panic! "todo"

syntax "return" term : term
macro_rules
  | `(term| "return" $t:term) => `(term | do return $t)
