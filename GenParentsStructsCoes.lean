import Lean

open Lean Meta Elab Term Command

elab "numOfMinors" n:ident : term => do
  let some (.recInfo r) ← getConst? n.getId | unreachable!
  dbg_trace r.numMinors
  throwAbortTerm

elab "#numOfMinors" n:ident : command => do
  let stx ← `(example : True := numOfMinors $n)
  elabCommand stx

#numOfMinors Nat.rec