import ProostLean.Queue
import Lean

open Queue
open Lean Elab Meta


inductive Term : Type := 
  | Var : Nat → Term
  | Const : String → Term
  | Sort : Nat → Term
  | App : Term → Term → Term
  | Abs : Term → Term → Term
  | Prod : Term → Term → Term


declare_syntax_cat proost
syntax ident : proost
syntax "(" proost ")" : proost
syntax "fun" (ident* ":" proost),* "=>" proost : proost 
syntax "(" ident* ":" proost ")" "->" proost : proost
syntax proost proost : proost
syntax "Prop" : proost
syntax "Type" num : proost
syntax "Sort" num : proost

partial def elabProost (pos : Queue Name) (stx : TSyntax `proost) : MetaM Expr := do
  match stx with

  | `(proost| Prop) => mkAppM `Term.Sort #[mkNatLit 0]

  | `(proost| Type $n) => mkAppM `Term.Sort #[mkNatLit n.getNat.succ]

  | `(proost| Sort $n) => mkAppM `Term.Sort #[mkNatLit n.getNat]

  | `(proost| $x:ident ) => do 
      let some posx := pos.position x.getId | mkAppM `Term.Const #[mkStrLit x.getId.toString]
      mkAppM `Term.Var #[mkNatLit posx]

  | `(proost| fun $x:ident : $A:proost => $B) => do
        let A ← elabProost pos A
        let B ← elabProost (pos.push x.getId) B
        mkAppM `Term.Abs #[A, B]

  | `(proost| fun $x $y * : $A:proost => $B) => do
        let B ← elabProost (pos.push x.getId) $ ←`(proost| fun $y* : $A => $B)
        let A ← elabProost pos A
        mkAppM `Term.Abs #[A, B]

  | `(proost| fun $x * : $A,  $[$y * : $B],* => $C) => do
        let B ← elabProost (pos.push_all (x.map (·.getId))) $ ←`(proost| fun $[$y* : $B],* => $C)
        let A ← elabProost pos A
        mkAppM `Term.Abs #[A, B]  

  | `(proost| ($x:ident : $A ) -> $B ) => do
        let A ← elabProost pos A  
        let B ← elabProost (pos.push x.getId) B
        mkAppM `Term.Prod #[A, B]

  | `(proost| ($x:ident $y * : $A ) -> $B) => do
        let B ← elabProost (pos.push x.getId) $ ←`(proost| ($y * : $A) -> $B)
        let A ← elabProost pos A
        mkAppM `Term.Abs #[A, B]
        
  | _ => do println! stx; throwUnsupportedSyntax
    

elab "test_elab " e:proost : term => elabProost default e

#check test_elab fun x y : Foo => x
--Term.Abs (Term.Const "Foo") (Term.Abs (Term.Const "Foo") (Term.Var 2))
