import Proost.Kernel.Core


--The following code is shamelessly stolen from Lean 4 repository, because I seriously don't feel like doing recursor reduction myself :)

/-- Information for reducing a recursor -/
structure RecursorRule where
  /-- Reduction rule for this Constructor -/
  ctor : Name
  /-- Number of fields (i.e., without counting inductive datatype parameters) -/
  nfields : Nat
  /-- Right hand side of the reduction rule -/
  rhs : Term
  deriving Inhabited


structure RecursorVal extends ConstantVal where
  /-- List of all inductive datatypes in the mutual declaration that generated this recursor -/
  all : List Name
  /-- Number of parameters -/
  numParams : Nat
  /-- Number of indices -/
  numIndices : Nat
  /-- Number of motives -/
  numMotives : Nat
  /-- Number of minor premises -/
  numMinors : Nat
  /-- A reduction for each Constructor -/
  rules : List RecursorRule
  /-- It supports K-like reduction.
  A recursor is said to support K-like reduction if one can assume it behaves
  like `Eq` under axiom `K` --- that is, it has one constructor, the constructor has 0 arguments,
  and it is an inductive predicate (ie, it lives in Prop).

  Examples of inductives with K-like reduction is `Eq`, `Acc`, and `And.intro`.
  Non-examples are `exists` (where the constructor has arguments) and
    `Or.intro` (which has multiple constructors).
  -/
  k : Bool
  isUnsafe : Bool
  deriving Inhabited

def RecursorVal.getMajorIdx (v : RecursorVal) : Nat :=
  v.numParams + v.numMotives + v.numMinors + v.numIndices

private def toCtorWhenK (recVal : RecursorVal) (major : Term) : TCEnv Term := do
  let majorType ← inferType major
  let majorType ←  whnf majorType
  let majorTypeI := majorType.getAppFn
  if !majorTypeI.isConstOf recVal.getInduct then
    return major
  else do
    let (some newCtorApp) ← mkNullaryCtor majorType recVal.numParams | pure major
    let newType ← inferType newCtorApp
    if ← isDefEq majorType newType then
      return newCtorApp
    else
      return major

-- Helper predicate that returns `true` for inductive predicates used to define functions by well-founded recursion.
private def isWFRec (declName : Name) : Bool :=
  declName == "Acc_rec" || declName == "WellFounded_rec"

/-- Auxiliary function for reducing recursor applications. -/
private def reduceRec (recVal : RecursorVal) (recLvls : List Level) (recArgs : Array Term) (failK : Unit → TCEnv α) (successK : Term → TCEnv α) : TCEnv α :=
  let majorIdx := recVal.getMajorIdx
  if h : majorIdx < recArgs.size then do
    let major := recArgs.get ⟨majorIdx, h⟩
    let mut major ← whnf major
    if recVal.k then
      major ← toCtorWhenK recVal major
    major := major.toCtorIfLit
    major ← toCtorWhenStructure recVal.getInduct major
    match getRecRuleFor recVal major with
    | some rule =>
      let majorArgs := major.getAppArgs
      if recLvls.length != recVal.levelParams.length then
        failK ()
      else
        let rhs := rule.rhs.instantiateLevelParams recVal.levelParams recLvls
        -- Apply parameters, motives and minor premises from recursor application.
        let rhs := mkAppRange rhs 0 (recVal.numParams+recVal.numMotives+recVal.numMinors) recArgs
        /- The number of parameters in the constructor is not necessarily
           equal to the number of parameters in the recursor when we have
           nested inductive types. -/
        let nparams := majorArgs.size - rule.nfields
        let rhs := mkAppRange rhs nparams majorArgs.size majorArgs
        let rhs := mkAppRange rhs (majorIdx + 1) recArgs.size recArgs
        successK rhs
    | none => failK ()
  else
    failK ()