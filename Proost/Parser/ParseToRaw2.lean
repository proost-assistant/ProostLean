import Proost.Parser.Syntax
import Proost.Elab.Raw
import Proost.Util.Misc
import Lean

open Lean Elab Meta

partial def elabLevel (stx : TSyntax `proost_level) : Except String RawLevel := do
  match stx with

  | `(proost_level| $n:num) => return .num n.getNat
  
  | `(proost_level| $x:ident) => return .var x.getId.toString

  | `(proost_level| $l + 0) => elabLevel l
  
  | `(proost_level| $l + $n) => 
        let l ← elabLevel l
        return .plus l n.getNat

  |`(proost_level| max $l₁ $l₂) =>
      let l₁ ← elabLevel l₁
      let l₂ ← elabLevel l₂
      return .max l₁ l₂

  |`(proost_level| imax $l₁ $l₂) =>
      let l₁ ← elabLevel l₁
      let l₂ ← elabLevel l₂
      return .imax l₁ l₂

  | _ => throw s!"unknown level syntax: {stx}"

partial def elabProost (stx : TSyntax `proost) : Except String RawTerm := do
  match stx with

  | `(proost| Prop) => return .prop

  | `(proost| Type) => return .type none

  | `(proost| Sort) => return .sort none

  | `(proost| Type $l) => return .type (← elabLevel l)

  | `(proost| Sort $l) =>  return .sort (← elabLevel l)

  | `(proost| ($t)) => elabProost t

  | `(proost| $x:ident $[.{ $l:proost_level ,* }]?  ) => 
      let arr ←  
        if let some stx := l then
            Array.mapM elabLevel stx
        else pure Array.empty
      return .varconst x.getId.toString arr
    
  | `(proost| ($t : $ty)) => do
      let t ← elabProost t
      let ty ← elabProost ty 
      return .ann t ty

  | `(proost| $t $ty) => do
      let t ← elabProost t
      let ty ← elabProost ty 
      return .app t ty

  | `(proost| fun $x:ident $[: $A:proost]? => $B) => do
        let A ← A.mapM elabProost
        let B ← elabProost B
        return .lam x.getId.toString A B

  | `(proost| fun $[$y * $[: $A]?],* => $B) => do
        let A ← A.mapM (Option.mapM elabProost)  
        let mut res ← elabProost B
        for i in [1:y.size+1] do
          let cur := y.size-i
          let ty := A[cur]!
          for j in [1:y[cur]!.size+1] do
            let sub := y[cur]!.size - j
            let x := y[cur]![sub]!.getId.toString
            res ← pure $ .lam x ty res
        return res
      
  | `(proost| $A -> $B) => do
        let A ← elabProost A  
        let B ← elabProost B
        return .pi "_" A B

  | `(proost| ($x:ident : $A ) -> $B ) => do
        let A ← elabProost A  
        let B ← elabProost B
        return .pi x.getId.toString A B

  | `(proost| ($y * : $A ) -> $B) => do
        let A ← elabProost A  
        let B ← elabProost B
        y.foldrM (λ x t => return .pi x.getId.toString A t) B
        
  | _ => throw s!"unknown term syntax: {stx}"

partial def elabCommand (stx : TSyntax `proost_command) : Except String RawCommand := do
  match stx with
  | `(proost_command| def $s $[.{ $l:ident ,* }]? $[($args * : $args_ty)]* $[: $ty]? := $t) =>
      let l := Id.run do
        let some l := l | []
        l.getElems.map (·.getId.toString) |>.toList
      let mut res_args := []
      for i in [:args.size] do
        let ty ← elabProost args_ty[i]!
        res_args := (args[i]!.map (·.getId.toString),ty)::res_args
      let ty ← ty.mapM elabProost
      let t ← elabProost t
      -- parse arguments
      return .def s.getId.toString l res_args ty t

  | `(proost_command| axiom $s $[.{ $l:ident ,* }]? : $ty ) => 
      let l := Id.run do
        let some l := l | []
        l.getElems.map (·.getId.toString) |>.toList
      let ty ← elabProost ty
      return .axiom s.getId.toString l ty

  | `(proost_command| check $t) => 
      let t ← elabProost t 
      return .check t

  | `(proost_command| eval $t) => 
      let t ← elabProost t 
      return .eval t
  
  | _ => throw s!"unknown command: {stx}"


partial def elabCommands (stx : TSyntax `proost_commands) : Except String RawCommands := do
   match stx with
  | `(proost_commands| $[$cl]* ) => 
      let cl := cl
      cl.mapM elabCommand |>.map Array.toList
  | _ => throw s!"unknown commands syntax: {stx}"


def parse (s: String) (env: Environment) : Except String RawCommands := do
  elabCommands ⟨(← Parser.runParserCategory env `proost_commands s)⟩ 