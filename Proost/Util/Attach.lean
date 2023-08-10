import Std
open Std

class PMap (T : Type _ → Type _) [∀ α, Membership α (T α)] where
  pmap {p : α → Prop} : (∀ a, p a → β) → ∀ l : T α, (∀ a : α, a ∈ l → p a) → T β

attribute [simp] PMap.pmap

/--TODO remove to make use of the general attach-/
def Option.attach {α : Type u_1} (l : Option α) : Option { x // x ∈ l } :=
  pmap Subtype.mk l fun _ => id

@[reducible]
def attach [∀ α, Membership α (T α)] [PMap T] {α : Type u_1} (l : T α) : T { x // x ∈ l } :=
  PMap.pmap Subtype.mk l fun _ => id

instance : PMap List where
  pmap := List.pmap

instance : PMap Option where  
  pmap := Option.pmap
