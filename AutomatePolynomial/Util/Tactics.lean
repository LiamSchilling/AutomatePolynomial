import Lean

open Lean Meta Elab Tactic

namespace Lean

namespace Expr

-- unfold constant to its definition
def unwrapConst (e : Expr) : MetaM Expr := do
  match e with
  | const n _ => return (← getConstInfo n).value!
  | e => return e

-- replace instance binders with default binders until a non-binder is reached
def dissolveInstBinders (e : Expr) : Expr :=
  match e with
  | lam n t e BinderInfo.instImplicit =>
    lam n t e.dissolveInstBinders BinderInfo.default
  | lam n t e b =>
    lam n t e.dissolveInstBinders b
  | forallE n t e BinderInfo.instImplicit =>
    forallE n t e.dissolveInstBinders BinderInfo.default
  | forallE n t e b =>
    forallE n t e.dissolveInstBinders b
  | e => e

end Expr

namespace MVarId

-- apply theorem to goal without attempting to synthesize instances
def applyNoInst (goal : MVarId) (e : Expr) : MetaM (List MVarId) := do
  goal.apply (← e.unwrapConst).dissolveInstBinders

-- recursively synthesize type class instances,
-- admitting those matching pattern and setting them as new goals
def synthInstanceSupposing (goal : MVarId) (patterns : List Expr) (d : Nat := 8) :
    MetaM (List MVarId) := do
  match d with
  | 0 => throwError "maximum recursion depth reached"
  | d + 1 =>
  try
    goal.assign (← synthInstance (← goal.getType))
    return []
  catch _ =>
    if ← patterns.anyM (fun p => do isDefEq (← goal.getType) p) then
      return [goal]
    else
      for inst in ← SynthInstance.getInstances (← goal.getType) do
        let state ← saveState
        try
          let subgoals ← goal.applyNoInst inst.val
          let subgoals ← subgoals.mapM (
            fun subgoal => subgoal.synthInstanceSupposing patterns d )
          return subgoals.flatten
        catch _ =>
          restoreState state
      throwError "failed to synthesize instance"

-- recursively synthesize type class instances,
-- trying a provided tactic to resolve those that fail
def synthInstanceTrying (goal : MVarId) (tactic : Syntax) (d : Nat := 8) :
    MetaM Unit := do
  match d with
  | 0 => throwError "maximum recursion depth reached"
  | d + 1 =>
  try
    goal.assign (← synthInstance (← goal.getType))
  catch _ =>
    let state ← saveState
    try
      let (subgoals, _) ← runTactic goal tactic
      match subgoals with
      | [] => return
      | _ => throwError "tactic failed to resolve subgoals"
    catch _ =>
      restoreState state
      for inst in ← SynthInstance.getInstances (← goal.getType) do
        let state ← saveState
        try
          let subgoals := (← goal.applyNoInst inst.val).reverse
          let _ ← subgoals.mapM (
            fun subgoal => subgoal.synthInstanceTrying tactic d )
          return
        catch _ =>
          restoreState state
      throwError "failed to synthesize instance"

end MVarId

end Lean

-- recursively synthesize type class instances,
-- admitting those matching pattern and setting them as new goals
elab "infer_instance_supposing" "[" ts:term,* "]" : tactic => do
  let ts := ts.getElems
  let mut ps := []
  for t in ts do ps := (← elabTerm t none) :: ps
  setGoals (← (← getMainGoal).synthInstanceSupposing ps)

-- recursively synthesize type class instances,
-- trying a provided tactic to resolve those that fail
elab "infer_instance_trying" "<:>" t:tactic : tactic => do
  (← getMainGoal).synthInstanceTrying t
