import Proost.Kernel.Core
import Proost.Kernel.Term

--The following code is shamelessly stolen from Lean 4 repository, 
--because I seriously don't feel like doing recursor reduction myself :)

private def getFirstCtor (d : Name) : TCEnv (Option Name) := do
  let some (.inductDecl { ctors := ctor::_, ..}) ← get_const_decl? d | pure none
  return some ctor

private def mkNullaryCtor (type : Term) (nparams : Nat) : TCEnv (Option Term) := do
  match type.getAppFn with
  | .const d lvls =>
    let (some ctor) ← getFirstCtor d | pure none
    return mkAppN (.const ctor lvls) (type.getAppArgs.shrink nparams)
  | _ =>
    return none


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
def reduceRec (recVal : RecursorVal) (recLvls : Array Level) (recArgs : Array Term) (failK : Unit → TCEnv α) (successK : Term → TCEnv α) : TCEnv α :=
  dbg_trace s!"trying to reduce {recVal.name} {recArgs}"
  let majorIdx := recVal.getMajorIdx
  if h : majorIdx < recArgs.size then do
    let major := recArgs.get ⟨majorIdx, h⟩
    let mut major ← whnf major
    if recVal.k then
      major ← toCtorWhenK recVal major
    --major ← toCtorWhenStructure recVal.getInduct major
    match getRecRuleFor recVal major with
    | some rule =>
      let majorArgs := major.getAppArgs
      if recLvls.size != recVal.levelParamsNum then
        dbg_trace s!"different number of universes (this shouldn't happend)"; failK ()
      else
        let rhs := rule.rhs.substitute_univ recLvls
        -- Apply parameters, motives and minor premises from recursor application.
        let rhs := mkAppRange rhs 0 (recVal.numParams+recVal.numMotives+recVal.numMinors) recArgs
        /- The number of parameters in the constructor is not necessarily
           equal to the number of parameters in the recursor when we have
           nested inductive types. -/
        let nparams := majorArgs.size - rule.nfields
        let rhs := mkAppRange rhs nparams majorArgs.size majorArgs
        let rhs := mkAppRange rhs (majorIdx + 1) recArgs.size recArgs
        dbg_trace s!"success ;D {rhs}"
        successK rhs
    | none => dbg_trace s!"no rule for {major}" ;failK ()
  else
    failK ()