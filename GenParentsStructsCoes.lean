import Lean

open Lean Meta Elab Term Command

deriving instance Repr for RecursorRule

elab "rules" n:ident : term => do
  let some (.inductInfo r) ← getConst? n.getId | unreachable!
  dbg_trace repr r.isRec
  throwAbortTerm

elab "#rules" n:ident : command => do
  let stx ← `(example : True := rules $n)
  elabCommand stx

#rules Eq