import Proost.Kernel.Level
import Proost.Kernel.Core
import Std.Data.HashMap

open Std
namespace Term

-- Only partial because structural recursion on nested inductives is broken
partial def shift (offset depth : Nat) : Term → Term
  | var n => 
    let n := if n >= depth then n+offset else n
    var n
  | app t₁ t₂ => app (t₁.shift offset depth) (t₂.shift offset depth)
  | abs ty body =>
    let ty   := ty.map (·.shift offset depth)
    let body := body.shift offset depth.succ
    abs ty body
  | prod ty body =>
    let ty := ty.shift offset depth
    let body := body.shift offset depth.succ
    prod ty body
  | ann t ty => ann (t.shift offset depth) (ty.shift offset depth)
  | const s l => const s l
  | sort l => sort l

partial def substitute (self sub : Term) (depth : Nat) : Term := match self with
  | var n => match compare n depth with
      | .eq => sub.shift depth.pred 1
      | .gt => var (n-1)
      | .lt => var n
  | app t₁ t₂ => app (t₁.substitute sub depth) (t₂.substitute sub depth)
  | abs ty body => 
    let ty := ty.map (·.substitute sub depth)
    let body := body.substitute sub depth.succ
    abs ty body 
  | prod ty body => 
    let ty := ty.substitute sub depth
    let body := body.substitute sub depth.succ
    prod ty body
  | ann t ty => ann (t.substitute sub depth) (ty.substitute sub depth)
  | const s l => const s l
  | sort l => sort l

def with_add_var_to_context (t : Option Term) : TCEnv α → TCEnv α:= 
    withReader λ con => {con with var_ctx := con.var_ctx|>.push t |>.map (.map $ Term.shift 1 0) }

def noAnn : Term → Term
  | ann t _ => t
  | t => t

def reduce_decl : Term → TCEnv Term
  | t@(const s arr) => do
    let res := (← read).const_ctx.find? s
    if let some $ .de d := res then
      return d.term |>.substitute_univ arr
    else
      return t
  | t => pure t

def sep_fn_args : Term →  Term × Array Term
  | .app f arg =>
    let ⟨f,args⟩ := f.sep_fn_args
    ⟨f,args.push arg⟩
  | t => ⟨t,#[]⟩

def appN : Term → Array Term → Term := fun hd arr =>
  arr.foldr (λ f x => app f x) hd

def RedRecs := HashMap String (Term → TCEnv (Option Term))

def red_rec (m : RedRecs)(s : String) (t : Term): TCEnv Term := do
  let some rec := m.find? s | pure t
  let some t ← rec t | pure t
  pure t

mutual

partial def whnf (t : Term) : TCEnv Term := do 
  let res ← do
    let t ← reduce_decl t
    match t with
      | app t₁ t₂ => do
        let t₁ ← whnf (← reduce_decl t₁)
        match t₁ with
          | abs _ body =>
            whnf $ body.substitute t₂ 1
          | const s _ => red_rec (all_recs ()) s (.app t₁ t₂)
          | _ => pure $ .app t₁ t₂
      | _ => pure t
  dbg_trace s!"{t}\n reduces to \n{res}"
  pure res



--temporary, very ugly solution to having recursors reduce 
--before having a general induction/recursion setting.
@[inline]
partial def all_recs : Unit →  HashMap String (Term → TCEnv (Option Term)) := λ () =>
  HashMap.empty.insert "Nat_rec" reduce_nat_rec

partial def reduce_nat_rec (t: Term) : TCEnv (Option Term) := do
  let no := pure none
  let ⟨hd,arr⟩:= t.sep_fn_args
  let hd@(.const "Nat_rec" _) ← whnf hd | no
  let some n := arr[3]? | no
  dbg_trace arr.size
  match ← whnf n with
    | .const "zero" _ => pure arr[1]!
    | .app s k =>
        let .const "succ" _ ← whnf s | no
        let p_succ := arr[2]! 
        let new_rec_args := arr[0:arr.size-1]
        let new_rec_args := new_rec_args.as.push k
        return some $ .app (.app p_succ k) (hd.appN new_rec_args)
    | _ => no

end