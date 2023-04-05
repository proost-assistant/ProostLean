import Proost.Parser.Syntax
import Proost.Elab.Raw
import Lean

open Lean Elab Meta

partial def elabLevel (stx : TSyntax `proost_level) : MetaM Expr := do
  match stx with

  | `(proost_level| $n:num) => mkAppM `RawLevel.num #[mkNatLit n.getNat]
  
  | `(proost_level| $x:ident) => mkAppM `RawLevel.var #[mkStrLit x.getId.toString]

  | `(proost_level| $l + 0) => 
      elabLevel (←`(proost_level| $l))
  
  | `(proost_level| $l + $n) => 
        let l ← elabLevel l
        mkAppM `RawLevel.plus #[l, mkNatLit n.getNat]

  |`(proost_level| max $l₁ $l₂) =>
      let l₁ ← elabLevel l₁
      let l₂ ← elabLevel l₂
      mkAppM `RawLevel.max #[l₁,l₂]

  |`(proost_level| imax $l₁ $l₂) =>
      let l₁ ← elabLevel l₁
      let l₂ ← elabLevel l₂
      mkAppM `RawLevel.imax #[l₁,l₂]

  | _ => do println! stx; throwUnsupportedSyntax

elab "test_elab_level" e:proost_level : term => elabLevel e

partial def elabProost (stx : TSyntax `proost) : MetaM Expr := do
  match stx with

  | `(Prop) => pure $ mkConst `RawTerm.prop

  | `(proost| Type $l) => mkAppM `RawTerm.type #[← elabLevel l]

  | `(proost| Sort $l) => mkAppM `RawTerm.sort #[← elabLevel l]

  | `(proost| $x:ident $[.{ $l:proost_level ,* }]?  ) => 
      let arr ←  
        if let some stx := l then
            Array.mapM elabLevel stx
        else pure Array.empty
      mkAppM `RawTerm.varconst #[mkStrLit x.getId.toString, ← mkAppM `Array.mk #[← mkListLit (mkConst `RawLevel) $ arr.toList] ]
    

  | `(proost| ($t : $ty)) => do
      let t ← elabProost t
      let ty ← elabProost ty 
      mkAppM `RawTerm.ann #[t,ty]

  | `(proost| fun $x:ident $[: $A:proost]? => $B) => do
        let A ←  
            if let some A := A then
                mkAppM `Option.some #[ ← elabProost A]
            else mkAppOptM `Option.none #[some $ mkConst `RawTerm]
        let B ← elabProost B
        mkAppM `RawTerm.lam #[mkStrLit x.getId.toString, A, B]

  | `(proost| fun $x $y * $[: $A:proost]? => $B) => do
        elabProost $ ←`(proost| fun $x $[: $A]? => fun $y* $[: $A]? => $B)

  | `(proost| fun $x * $[: $A]?,  $[$y * : $B],* => $C) => do
      elabProost $ ←`(proost| fun $x * $[: $A]? => fun $[$y* : $B],* => $C)
      
  | `(proost| $A -> $B) => do
        let A ← elabProost A  
        let B ← elabProost B
        mkAppM `RawTerm.prod #[mkStrLit "_", A, B]

  | `(proost| ($x:ident : $A ) -> $B ) => do
        let A ← elabProost A  
        let B ← elabProost B
        mkAppM `RawTerm.prod #[mkStrLit x.getId.toString, A, B]

  | `(proost| ($x:ident $y * : $A ) -> $B) => do
        elabProost $ ←`(proost| ($x : $A) -> ($y * : $A) -> $B)
        
  | _ => do println! stx; throwUnsupportedSyntax

elab "test_elab" e:proost : term => elabProost e

#check test_elab fun x y : Foo, z : Bar => (x : Foo)