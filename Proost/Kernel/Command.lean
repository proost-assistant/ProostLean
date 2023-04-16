import Proost.Kernel.TypeChecker
import Proost.Kernel.Core


def evalCommand (c : Command) : TCEnv ConstContext := do
  match c with
  | .def s n_of_univ ty te => do
    let typ : Term ← 
      if let some ty := ty then
        te.check ty
        pure ty
      else te.infer 
    let decl : Decl := ⟨typ,n_of_univ,te⟩ 
    add_trace "cmd" s!"adding decl {s} to the env"
    return (← read).const_con.insert s (.de decl)
  | .axiom s n_of_univ ty => do
    ty.is_type 
     return (← read).const_con.insert s (.ax ⟨s,ty,n_of_univ⟩)
  | .check t => do
    let _ ← t.infer
    return (← read).const_con
  | _ => return (← read).const_con

def evalCommands (cs : Commands) : TCEnv ConstContext := do
  List.foldlM 
    (λ u c => do
      add_trace "cmd" s!"evaluating command {c} in env {repr u.toArray}"
      evalCommand c {const_con := u} ) 
    (← read).const_con
    cs