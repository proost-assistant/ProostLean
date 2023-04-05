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
        let A ← do
            let some A := A | mkAppOptM `Option.none #[some $ mkConst `RawTerm]
            mkAppM `Option.some #[ ← elabProost A]
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

partial def elabCommand (stx : TSyntax `proost_command) : MetaM Expr := do
  match stx with
  | `(proost_command| def $s $[.{ $l:ident ,* }]? $[: $ty]? := $t) =>
      let l ← do
        let some l := l | mkListLit (mkConst `String) .nil
        mkListLit (mkConst `String) $ l.getElems.toList.map (λ x => mkStrLit (TSyntax.getId x).toString)
      let ty ← do
        let some ty := ty | mkAppOptM `Option.none #[some $ mkConst `RawTerm]
        mkAppM `Option.some #[ ← elabProost ty]
      let t ← elabProost t
      mkAppM `RawCommand.def #[mkStrLit s.getId.toString, l, ty, t]

  | `(proost_command| axiom $s $[.{ $l:ident ,* }]? : $ty ) => 
      let l ← do
        let some l := l | mkListLit (mkConst `String) .nil
        mkListLit (mkConst `String) $ l.getElems.toList.map (λ x => mkStrLit (TSyntax.getId x).toString)
      let ty ← elabProost ty
      mkAppM `RawCommand.axiom #[mkStrLit s.getId.toString, l, ty]

  | `(proost_command| check $t) => 
      let t ← elabProost t 
      mkAppM `RawCommand.check #[t]

  | `(proost_command| eval $t) => 
      let t ← elabProost t 
      mkAppM `RawCommand.eval #[t]
  
  | _ => do println! stx; throwUnsupportedSyntax

elab "test_elab_cmd" e:proost_command : term => elabCommand e

#check test_elab_cmd def foo.{u} : Foo := Bar
