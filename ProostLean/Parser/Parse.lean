import ProostLean.Util.Queue
import ProostLean.Elab
import Lean

open Queue
open Lean Elab Meta

declare_syntax_cat proost_level

syntax num : proost_level
syntax ident : proost_level
syntax proost_level "+" num : proost_level
syntax "max" proost_level (proost_level)+ : proost_level
syntax "imax" proost_level (proost_level)+ : proost_level


declare_syntax_cat constant
syntax ident (".{" (proost_level)+ "}")? : constant


declare_syntax_cat proost
syntax constant : proost
syntax "(" proost ")" : proost
syntax "(" proost ":" proost ")" : proost
syntax "fun" (ident* (":" proost)?),* "=>" proost : proost 
syntax "(" ident* ":" proost ")" "->" proost : proost
syntax proost "->" proost : proost
syntax proost proost : proost
syntax "Prop" : proost
syntax "Type" proost_level : proost
syntax "Sort" proost_level : proost

partial def elabProost (pos : Queue Name) (stx : TSyntax `proost) : MetaM Expr := do
  match stx with

  | `(proost| Prop) => mkAppM `Term.sort #[mkNatLit 0]

  | `(proost| Type $n) => mkAppM `Term.sort #[mkNatLit n.getNat.succ]

  | `(proost| Sort $n) => mkAppM `Term.sort #[mkNatLit n.getNat]

  | `(proost| $x:ident ) => do 
      let some posx := pos.position x.getId | mkAppM `Term.const #[mkStrLit x.getId.toString, ← mkAppOptM `Array.empty #[mkConst `Level]]
      mkAppM `Term.var #[mkNatLit posx.pred]

  | `(proost| ($t : $ty)) => do
      let t ← elabProost pos t
      let ty ← elabProost pos ty 
      mkAppM `Term.ann #[t,ty]

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
      elabProost pos $ ←`(proost| fun $x * $[: $A]? => fun $[$y* : $B],* => $C)
      
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

#check test_elab fun x y : Bar, z : Foo => (x : Foo)

declare_syntax_cat proost_command
syntax "def" ident (":" proost)? ":=" proost : proost_command

#check whnf