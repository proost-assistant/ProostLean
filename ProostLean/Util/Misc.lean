@[specialize]
def List.allM₂ {m : Type → Type u} [Monad m] {α : Type v} {β : Type w} (f : α → β → m Bool) : List α → List β → m Bool
  | [],[]    => pure true
  | a::as,b::bs => do
    match (← f a b) with
    | true  => allM₂ f as bs
    | false => pure false
  | _,_ => pure false