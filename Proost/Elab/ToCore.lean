import Proost.Elab.Raw
import Proost.Kernel.Level
import Proost.Kernel.Core
import Proost.Kernel.Command
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

instance :  MonadLiftT RawLevelEnv RawTermEnv where
  monadLift {α} (a : RawLevelEnv α) := do
    fun h => liftExcept (a h)

partial def RawTerm.toCore (t : RawTerm) : RawTermEnv Term := do
  --dbg_trace "elaborating :\n  {repr t} \nin env: \n  {repr (← get)}"
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
      if x != "_" then modify (·.push x)
      let ty ←  ty.toCore
      return .prod t ty
    | lam x ty t =>
      let ty ← ty.mapM RawTerm.toCore
      if x != "_" then modify (·.push x)
      let t ← t.toCore
      return .abs ty t
    | varconst s #[] => 
      let some posx := (← get).position s | return .const s #[]
      return .var posx.pred
    | varconst s arr =>
      let arr ← Array.mapM (liftM ∘ RawLevel.toCore) arr
      return .const s arr
    | «let» x ty t body => 
      let ty ← ty.mapM RawTerm.toCore
      let t ← t.toCore
      if x != "_" then modify (·.push x)
      let body ← body.toCore
      return .app (.abs ty body) t

abbrev RawCommandEnv := Except RawError

#reduce EStateM.Result RawError (Queue String) Term 

instance : Coe (EStateM.Result ε σ α) (Except ε α) where
  coe 
    | .ok x _ => .ok x
    | .error e _ => .error e

def map_univs : List String → EStateM RawError (HashMap String Nat) Unit
    | [] => return
    | h::t => do 
      if let some _ := (← get).find? h then
        throw $ .duplicateUniverseVar h
      else 
        modify (λ hm => HashMap.insert hm h hm.size.succ)
        map_univs t


def RawCommand.toCore (t : RawCommand) : RawCommandEnv Command := do
  match t with
    | .def s l _todo ty t =>
      let hm ← match map_univs l default with
        | .ok () hm => pure hm
        | .error e _ => throw e
      let ty ← Option.mapM (RawTerm.toCore · hm default) ty
      let t ← RawTerm.toCore t hm default
      return .def s hm.size ty t

    | .axiom s l ty =>       
      let hm ← match map_univs l default with
        | .ok () hm => pure hm
        | .error e _ => throw e
      let ty ← RawTerm.toCore ty hm default
      return .axiom s hm.size ty

    | .eval t => 
      let t ← RawTerm.toCore t default default
      return .eval t

    | .check t => 
      let t ← RawTerm.toCore t default default
      return .check t
  
def RawCommands.toCore (t : RawCommands) : RawCommandEnv Commands := 
  t.mapM RawCommand.toCore
