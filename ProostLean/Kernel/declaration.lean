import ProostLean.Kernel.Level
import ProostLean.Kernel.Term


structure Declaration : Type where
  term : Term
  n_of_uvars : Nat

structure InstantiatedDeclaration : Type where
  decl : Declaration
  params : Array Level
  is_correct : params.size = n_of_uvars := by decide
