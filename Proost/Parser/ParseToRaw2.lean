import Proost.Parser.Syntax
import Proost.Elab.Raw
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

  | `(proost|Prop) => return .prop

  | `(proost|Type) => return .type none

  | `(proost|Sort) => return .sort none

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

  --| `(proost| fun $x $y * $[: $A:proost]? => $B) => do
  --      elabProost $ ←`(proost| fun $x $[: $A]? => fun $y* $[: $A]? => $B)
--
  --| `(proost| fun $x * $[: $A]?,  $[$y * : $B],* => $C) => do
  --    elabProost $ ←`(proost| fun $x * $[: $A]? => fun $[$y* : $B],* => $C)
      
  | `(proost| $A -> $B) => do
        let A ← elabProost A  
        let B ← elabProost B
        return .pi "_" A B

  | `(proost| ($x:ident : $A ) -> $B ) => do
        let A ← elabProost A  
        let B ← elabProost B
        return .pi x.getId.toString A B

  --| `(proost| ($x:ident $y * : $A ) -> $B) => do
  --      elabProost $ ←`(proost| ($x : $A) -> ($y * : $A) -> $B)
        
  | _ => throw s!"unknown term syntax: {stx}"


partial def elabCommand (stx : TSyntax `proost_command) : Except String RawCommand := do
  match stx with
  | `(proost_command| def $s $[.{ $l:ident ,* }]? $[: $ty]? := $t) =>
      let l := Id.run do
        let some l := l | []
        l.getElems.map (·.getId.toString) |>.toList
      let ty ← ty.mapM elabProost
      let t ← elabProost t
      return .def s.getId.toString l ty t

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