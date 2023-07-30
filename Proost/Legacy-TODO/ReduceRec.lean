import Proost.Kernel.Core

--The following code is shamelessly stolen from Lean 4 repository, 
--because I seriously don't feel like doing recursor reduction myself :)


private def getRecRuleFor (recVal : RecursorVal) (major : Term) : Option RecursorRule :=
  match major.getAppFn with
  | .const fn _ => recVal.rules.find? fun r => r.ctor == fn
  | _               => none


private def toCtorWhenK (recVal : RecursorVal) (major : Term) : TCEnv Term := do
  let majorType ← infer major
  let majorType ←  whnf majorType
  let majorTypeI := majorType.getAppFn
  if !majorTypeI.isConstOf recVal.getInduct then
    return major
  else do
    let (some newCtorApp) ← mkNullaryCtor majorType recVal.numParams | pure major
    let newType ← infer newCtorApp
    if ← conversion majorType newType then
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
      if recLvls.length != recVal.levelParamsNum then
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