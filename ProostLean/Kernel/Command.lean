import ProostLean.Kernel.TypeChecker

def evalCommand (con : Context): Command → TCEnv Unit
  | .def s ty te => do
    let typ : Term ← 
      if let some ty := ty then
        te.check con ty
        pure ty
      else te.infer con 
    return ()
  | _ => sorry
    
