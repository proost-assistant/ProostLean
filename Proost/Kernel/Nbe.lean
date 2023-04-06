import Proost.Kernel.Core
import Proost.Kernel.Term
import Proost.Kernel.Axioms

mutual

  partial def AppClosure.app (closure : AppClosure Value) (arg : Value) : TCEnv Value :=
    closure.term.eval (arg::closure.closure)

  partial def Term.eval (closure : List Value := []) (x : Term): TCEnv Value := do
    add_trace s!"evaluating {x} in closure {closure}"
    match x with
    | .ann t _ => t.eval closure
    | .sort l => return .sort l
    | .app fn arg => do
        let fn ← fn.eval closure
        let arg ← arg.eval closure
        match fn with
          | .abs _ closure => closure.app arg
          | .neutral ne arr => pure (.neutral ne $ arg::arr)
          | _ => throw $ .notAFunction fn arg
    | .abs ty body => do
        let ty ←
          if let some ty := ty.map $ (·.eval closure)
          then
            let ty ← ty
            pure $ some ty
          else pure none
        let body := AppClosure.mk body closure
        return .abs ty body
    | .prod ty body => do
        let ty ← ty.eval closure
        let body := AppClosure.mk body closure
        return .prod ty body
    | .var x => do
        if let some val := closure.get? x
          then return val
        else
          dbg_trace s!"unbound index {x} with closure {closure}"
          return .neutral (.var x) []
    | .const s arr => do
        let res := (← get).const_con.find? s
        match res with
          | some (.ax a) => pure $ .neutral (.ax a arr) []
          | some (.de d) => d.term |>.substitute_univ arr |>.eval closure
          | none => throw $ .unknownConstant s
end

partial def read_back (size : Nat) : Value → TCEnv Term
  | .sort l => pure $ .sort l
  | .neutral ne spine =>
    let ne : Term := match ne with
      | .ax a arr => .const a.name arr
      | .var x => .var x
    List.foldlM (λ acc x => do return .app acc $ (← read_back size x))
      ne spine
  | .abs ty closure => do
    let ty ← ty.mapM (read_back size)
    let body ← closure.app (.var size) >>= read_back (size+1)
    pure $ .abs ty body
  | .prod ty closure => do
    let ty ← read_back size ty
    let body ← closure.app (.var size) >>= read_back (size+1)
    pure $ .prod ty body


def Term.whnf (t : Term): TCEnv Term := do
  let v ← t.eval []
  read_back 0 v
