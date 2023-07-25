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
    let decl : DefinitionVal := ⟨⟨s,typ,n_of_univ⟩,te⟩ 
    add_trace "cmd" s!"adding decl {s} to the env"
    return (← read).const_ctx.insert s (.defnDecl decl)
  | .axiom s n_of_univ ty => do
    ty.is_type 
     return (← read).const_ctx.insert s (.axiomDecl ⟨s,ty,n_of_univ⟩)
  | .check t => do
    let ty ← t.infer
    add_trace "print" s!"{t} : {ty}"
    return (← read).const_ctx
  | .eval t => 
    let t ← t.whnf
    add_trace "print"  s!"Evaluated term : {t}"
    return (← read).const_ctx

def evalCommands (cs : Commands) : TCEnv ConstContext := do
  List.foldlM 
    (λ u c => do
      add_trace "cmd" s!"evaluating command {c} in env {repr u.toArray}"
      evalCommand c {const_ctx := u} ) 
    (← read).const_ctx
    cs