import Proost.Kernel.TypeChecker

def evalCommand (c : Command) (u : TCEnv α): TCEnv α := do
  match c with
  | .def s n_of_univ ty te => do
    let typ : Term ← 
      if let some ty := ty then
        te.check ty
        pure ty
      else te.infer 
    let decl : Decl := ⟨typ,n_of_univ,te⟩ 
    with_add_decl s decl u
  | .axiom s n_of_univ ty => do
    ty.is_type 
    with_add_axiom ⟨s,ty,n_of_univ⟩ u
  | .check t => do
    let _ ← t.infer
    u
  | _ => u

def evalCommands (cs : Commands) (u : TCEnv α): TCEnv α := do
  List.foldlM (λ u c => dbg_trace s!"evaluating command {c}";evalCommand c (pure u)) (← u) cs