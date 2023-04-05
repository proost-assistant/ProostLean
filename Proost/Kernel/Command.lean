import Proost.Kernel.TypeChecker

def evalCommand (c : Command): TCEnv Unit := do
  match c with
  | .def s n_of_univ ty te => do
    let typ : Term ← 
      if let some ty := ty then
        te.check ty
        pure ty
      else te.infer 
    let decl : Decl := ⟨typ,n_of_univ,te⟩ 
    add_decl s decl
  | .axiom s n_of_univ ty => do
    ty.is_type 
    add_axiom ⟨s,ty,n_of_univ⟩ 
  | .check t => do
    let _ ← t.infer
    return
  | _ => return

def evalCommands (cs : Commands): TCEnv Unit := do
  List.foldlM (λ () c => evalCommand c) () cs