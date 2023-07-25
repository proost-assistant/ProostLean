import Lean

open Lean Meta Elab Term Command

#print Level

def genParentCoes (structName : Name) : MetaM Unit := do
  let env ← getEnv
  let parents := getParentStructures env structName
  for parent in parents do
    let instCoeStructParent := 
      mkApp (mkConst `Coe.mk  [.zero, .zero ]) $
        .forallE `x (mkConst structName)
          (mkApp (mkConst (structName.mkStr s!"to{parent.getString!}") ) 
            (.fvar ⟨`x⟩))
          default
    let instCoeType ← inferType instCoeStructParent
    let instName := s!"instCoe{structName}{parent}"
    addDecl $ .defnDecl {
      name := instName
      levelParams := [`u,`v]
      type := instCoeType
      value := instCoeStructParent
      hints := default
      safety := default
    }
    addInstance instName default default

elab "#instParentCoes" i:ident : term => do
  let structName := i.getId
  let _ ← genParentCoes structName
  elabTerm (← `(())) none
  
elab "#elabParentCoes" i:ident : command => do
  let stx ← `(example := #instParentCoes $i)
  elabCommand stx

structure Foo where 
  x : Nat

structure Bar extends Foo where
  y : x = x 

#elabParentCoes Bar
