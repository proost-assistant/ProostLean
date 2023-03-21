import ProostLean.Kernel.Core

mutual

  partial def AppClosure.app (closure : AppClosure Value) (arg : Value) : TCEnv Value :=
    closure.term.eval (arg::closure.closure) 

  partial def Term.eval (closure : List Value := []): Term → TCEnv Value :=
    fun x => do
    addTrace "foo"
    match x with
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
        else throw $ .unboundDeBruijnIndex x closure
    | .const s => do
        let res := (← read).find? s
        match res with
          | some (.ax a) => pure $ .neutral (.ax a) []
          | some (.de d) => d.term.eval closure 
          | none => throw $ .unknownConstant s
end

#eval Term.eval [] (.app (.abs none $ .abs none $ .var 0) (.sort 0)) default []

#check Except.ok (Value.abs none { term := Term.var 0, closure := [Value.sort (Level.zero)] }, ["foo", "foo", "foo", "foo"])

partial def read_back (size : Nat) : Value → TCEnv Term 
  | .sort l => pure $ .sort l
  | .neutral ne spine => 
    let ne : Term := match ne with
      | .ax a => .const a.name
      | .var x => .var x
    List.foldl (λ acc x => do return .app (← acc) $ (← read_back size x)) 
      (pure ne) spine
  | .abs ty closure => do
    let ty ← 
      if let some ty := ty.map (read_back size)
      then 
        let ty ← ty 
        pure $ some ty 
      else pure none
    let body ← closure.app (.var size) >>= read_back (size+1)
    pure $ .abs ty body
  | .prod ty closure => do
    let ty ← read_back size ty
    let body ← closure.app (.var size) >>= read_back (size+1)
    pure $ .prod ty body


