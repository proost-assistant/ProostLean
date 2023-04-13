import Proost.Kernel.Core
import Proost.Kernel.Term
import Proost.Kernel.Axioms


mutual

  partial def AppClosure.app (closure : AppClosure Value) (arg : Value) : TCEnv Value :=
    closure.term.eval (arg::closure.closure)

  partial def Term.eval (closure : List Value := []) (x : Term): TCEnv Value := do
    add_trace s!"Evaluating \n  {x}\n in closure \n  {closure}"
    let res ← match x with
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
        if let some val := closure.get? (closure.length - x)
          then return val
        else
          add_trace s!"Unbound index {x} with closure {closure}"
          return .neutral (.var x) []
    | .const s arr => do
        let res := (← read).const_con.find? s
        match res with
          | some (.ax a) => pure $ .neutral (.ax a arr) []
          | some (.de d) => d.term |>.substitute_univ arr |>.eval closure
          | none => throw $ .unknownConstant s
    add_trace s!" {x}\nevaluates to\n {res}"
    return res
end

partial def read_back (size : Nat) (x : Value): TCEnv Term := do
    add_trace s!"Reading back \n  {x}\nsize: {size}"
    let res ← match x with
    | .sort l => pure $ .sort l
    | .neutral ne spine =>
      let ne : Term := match ne with
        | .ax a arr => .const a.name arr
        | .var x => .var (x+1) --FIX IS PROB HERE
      List.foldrM (λ x acc => do return .app acc $ (← read_back size x))
        ne spine
    | .abs ty closure => do
      let ty ← ty.mapM (read_back size)
      let body ← closure.app (.var size) >>= read_back (size+1)
      pure $ .abs ty body
    | .prod ty closure => do
      let ty ← read_back size ty
      let body ← closure.app (.var size) >>= read_back (size+1)
      pure $ .prod ty body
    add_trace s!"{x}\n reads back to\n {res}"
    return res

def Term.whnf (t : Term): TCEnv Term := do
  let v ← t.eval []
  read_back 0 v
