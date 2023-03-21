import ProostLean.Util.Queue
import ProostLean.Kernel.Core
import Lean

open Queue
open Lean Elab Meta

declare_syntax_cat proost
syntax ident : proost
syntax "(" proost ")" : proost
syntax "fun" (ident* (":" proost)?),* "=>" proost : proost 
syntax "(" ident* ":" proost ")" "->" proost : proost
syntax proost "->" proost : proost
syntax proost proost : proost
syntax "Prop" : proost
syntax "Type" num : proost
syntax "Sort" num : proost

partial def elabProost (pos : Queue Name) (stx : TSyntax `proost) : MetaM Expr := do
  match stx with

  | `(proost| Prop) => mkAppM `Term.sort #[mkNatLit 0]

  | `(proost| Type $n) => mkAppM `Term.sort #[mkNatLit n.getNat.succ]

  | `(proost| Sort $n) => mkAppM `Term.sort #[mkNatLit n.getNat]

  | `(proost| $x:ident ) => do 
      let some posx := pos.position x.getId | mkAppM `Term.const #[mkStrLit x.getId.toString]
      mkAppM `Term.var #[mkNatLit posx.pred]

  | `(proost| fun $x:ident $[: $A:proost]? => $B) => do
        let A ←  
            if let some A := A then
                mkAppM `Option.some #[ ← elabProost pos A]
            else mkAppOptM `Option.none #[some $ mkConst `Term]
        let B ← elabProost (pos.push x.getId) B
        mkAppM `Term.abs #[A, B]

  | `(proost| fun $x $y * $[: $A:proost]? => $B) => do
        elabProost pos $ ←`(proost| fun $x $[: $A]? => fun $y* $[: $A]? => $B)

  | `(proost| fun $x * $[: $A]?,  $[$y * : $B],* => $C) => do
      elabProost pos $ ←`(proost| fun $x * $[: $A]? =>fun $[$y* : $B],* => $C)
      

  | `(proost| $A -> $B) => do
        let A ← elabProost pos A  
        let B ← elabProost pos B
        mkAppM `Term.prod #[A, B]

  | `(proost| ($x:ident : $A ) -> $B ) => do
        let A ← elabProost pos A  
        let B ← elabProost (pos.push x.getId) B
        mkAppM `Term.prod #[A, B]

  | `(proost| ($x:ident $y * : $A ) -> $B) => do
        elabProost pos $ ←`(proost| ($x : $A) -> ($y * : $A) -> $B)
        
        
  | _ => do println! stx; throwUnsupportedSyntax

elab "test_elab " e:proost : term => elabProost default e

#check test_elab fun x y : Bar, z : Foo => x
--Term.Abs (Term.Const "Foo") (Term.Abs (Term.Const "Foo") (Term.Var 2))

declare_syntax_cat proost_command