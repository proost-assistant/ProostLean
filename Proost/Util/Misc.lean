--import Std.Data.Option.Basic

@[specialize]
def List.allM₂ {m : Type → Type u} [Monad m] {α : Type v} {β : Type w} (f : α → β → m Bool) : List α → List β → m Bool
  | [],[]    => pure true
  | a::as,b::bs => do
    match (← f a b) with
    | true  => allM₂ f as bs
    | false => pure false
  | _,_ => pure false

--def Option.attach {α : Type _} (l : Option α) : Option { x // x ∈ l } :=
--  pmap Subtype.mk l fun _ => id

def todo! {A : Type _} [Inhabited A] : A := panic! "todo"

syntax "return" term : term
macro_rules
  | `(term| "return" $t:term) => `(term | do return $t)

def uncurry {A B C}: (A → B → C) → (A × B) → C :=
  λ f => λ ⟨a,b⟩ => f a b  

def List.toString₂ [ToString α] (pre sep post : String) : List α → String
  | [] => s!"{pre}{post}"
  | [x] => s!"{pre}{x}{post}"
  | x::xs => xs.foldl (s!"{·}{sep} {·}") (s!"{pre}{x}") |> (· ++ post)

def Array.toString₂ [ToString α] (pre sep post : String) : Array α →  String := 
  List.toString₂ pre sep post ∘ Array.toList


