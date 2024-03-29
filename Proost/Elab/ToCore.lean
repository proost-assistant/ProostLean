import Proost.Elab.Raw
import Proost.Kernel.Level
import Proost.Kernel.Core
import Proost.Kernel.Command
import Proost.Util.AppSep
import Proost.Util.Queue
import Proost.Util.Misc
import Proost.Util.Attach

import Std.Data.HashMap

open Std (HashMap)
open PMap
open RawError

abbrev RawLevelEnv := ReaderT (HashMap String Nat) $ Except $ WithTrace RawError

def RawLevel.toCore (l : RawLevel) : RawLevelEnv Level := do
  match l with
  | var s => 
    let index := (← read)
    let some n := index.find? s | throw ↑(unboundLevelVar s)
    return .var n
  | num n => pure $ OfNat.ofNat n
  | plus l n => pure $ .plus (← toCore l) n
  | max l₁ l₂ => pure $ .max (← toCore l₁) (← toCore l₂)
  | imax l₁ l₂ => pure $ .imax (← toCore l₁) (← toCore l₂)

structure RawTermCtx where
  univs : HashMap String Nat
  vars : Queue String
deriving Inhabited

abbrev RawTermEnv := ReaderT RawTermCtx $ Except $ WithTrace RawError

instance :  MonadLiftT RawLevelEnv RawTermEnv where
  monadLift {α} (a : RawLevelEnv α) := do
    fun h => liftExcept (a h.univs)

def RawTerm.toCore (t : RawTerm) : RawTermEnv Term := do
  --dbg_trace "elaborating :\n  {repr t} \nin env: \n  {repr (← get)}"
  match t with
    | prop | sort none => 
      return .sort 0
    | type none => 
      return .sort 1
    | type (some l) => 
      let l ← liftExcept $ l.toCore (← read).univs
      return .sort (l+1)
    | sort (some l) => 
      let l ← liftExcept $ l.toCore (← read).univs
      return .sort l
    | ann t ty =>
      return .ann (← t.toCore) (← ty.toCore)
    | app f x => 
      return .app (← f.toCore) (← x.toCore)
    | pi x t ty =>
      let t ← t.toCore
      let ty ← withReader 
        (λ ctx =>  {ctx with vars := ctx.vars.push x}) 
        ty.toCore
      return .prod t ty
    | lam x ty t =>
      let ty ← ty.attach |>.mapM (λ ⟨e,_⟩ => RawTerm.toCore e)
      let t ← withReader 
        (λ ctx =>  {ctx with vars := ctx.vars.push x}) 
        t.toCore
      return .abs ty t
    | varconst s #[] => 
      let some posx := (← read).vars.position s | return .const s #[]
      --dbg_trace s!"looking for DB var of {s} in {(← read).vars}, found {posx}"
      return .var posx.succ
    | varconst s arr =>
      let arr ← Array.mapM (liftM ∘ RawLevel.toCore) arr
      return .const s arr
    | «let» x ty t body => 
      let ty ← ty.attach |>.mapM (λ ⟨e,_⟩ => RawTerm.toCore e)
      let t ← t.toCore
      let body ← withReader 
        (λ ctx =>  {ctx with vars := ctx.vars.push x}) 
        body.toCore
      return .app (.abs ty body) t

abbrev RawCommandEnv := Except $ WithTrace RawError

def map_univs (arr : Array String) : Except RawError (HashMap String Nat) := do 
    let mut map := HashMap.empty
    for h in [0:arr.size] do
      if let some _ := map.find? arr[h]! then
        throw $ .duplicateUniverseVar arr[h]!
      else 
        map := HashMap.insert map arr[h]! h
    return map


def RawCommand.toCore (t : RawCommand) : RawCommandEnv Command := do
  match t with
    | .def s l args ty t =>
      let hm ← match map_univs l with
        | .ok hm => pure hm
        | .error e => throw ↑e
      let (t,ty) := args.foldl
        (λ (t,ty) (idents,ity) => 
          idents.foldr 
            (λ x (t,ty) => 
              (RawTerm.lam x (some ity) t, 
               Option.map (RawTerm.pi x ity ·) ty)) 
            (t,ty)
        ) (t,ty)
      
      let ty ← Option.mapM (RawTerm.toCore · ⟨hm,default⟩ ) ty
      let t ← RawTerm.toCore t ⟨hm,default⟩
      return .def s hm.size ty t

    | .axiom s l ty =>       
      let hm ← match map_univs l  with
        | .ok hm => pure hm
        | .error e => throw ↑e
      let ty ← RawTerm.toCore ty ⟨hm,default⟩
      return .axiom s hm.size ty

    | .eval t => 
      let t ← RawTerm.toCore t default
      return .eval t

    | .check t => 
      let t ← RawTerm.toCore t default
      return .check t
  
def RawCommands.toCore (t : RawCommands) : RawCommandEnv Commands := 
  t.mapM RawCommand.toCore
