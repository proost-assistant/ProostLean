import Proost.Elab.Raw
import Proost.Kernel.Level
import Proost.Kernel.Core
import Proost.Util.AppSep
import Proost.Util.Queue

import Std.Data.HashMap
open Std (HashMap)

abbrev RawLevelEnv := ReaderT (HashMap String Nat) (Except RawError)

def RawLevel.toCore (l : RawLevel) : RawLevelEnv Level := do
  match l with
  | var s => 
    let index := (← read)
    if let some n := index.find? s
    then pure $ .var n
    else throw $ .unboundLevelVar s
  | num n => pure $ OfNat.ofNat n
  | plus l n => pure $ .plus (← toCore l) n
  | max l₁ l₂ => pure $ .max (← toCore l₁) (← toCore l₂)
  | imax l₁ l₂ => pure $ .imax (← toCore l₁) (← toCore l₂)

abbrev RawTermEnv := ReaderT (HashMap String Nat) $ EStateM RawError (Queue String)


partial def RawTerm.toCore (t : RawTerm) : RawTermEnv Term := do
  match t with
    | prop | sort none => 
      return .sort 0
    | type none => 
      return .sort 1
    | type (some l) => 
      let l ← liftExcept $ l.toCore (← read)
      return .sort (l+1)
    | sort (some l) => 
      let l ← liftExcept $ l.toCore (← read)
      return .sort l
    | ann t ty =>
      return .ann (← t.toCore) (← ty.toCore)
    | app f x => 
      return .app (← f.toCore) (← x.toCore)
    | pi x t ty =>
      let t ← t.toCore
      modify (·.push x)
      let ty ←  ty.toCore
      return .prod t ty
    | lam x ty t =>
      let ty ← do
        if let some ty := ty.map $ (RawTerm.toCore)
        then
          let ty ← ty
          pure $ some ty
        else pure none
      modify (·.push x)
      let t ← t.toCore
      return .abs ty t
    | varconst s none => 
      let some posx := (← get).position s | return .const s #[]
      return .var posx
    | varconst _ (some _) =>
      todo!
    | «let» x ty t body => 
      let ty ← do
        if let some ty := ty.map $ (RawTerm.toCore)
        then
          let ty ← ty
          pure $ some ty
        else pure none
      let t ← t.toCore
      modify (·.push x)
      let body ← body.toCore
      return .app (.abs ty body) t





    

