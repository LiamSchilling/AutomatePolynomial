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
def synthInstanceSupposing (goal : MVarId) (pattern : Expr) (d : Nat := 8) :
    MetaM (List MVarId) := do
  match d with
  | 0 => throwError "maximum recursion depth reached"
  | d + 1 =>
  let target ← goal.getType
  try
    goal.assign (← synthInstance target)
    return []
  catch _ =>
    if ← isDefEq target pattern then
      return [goal]
    else
      for inst in ← SynthInstance.getInstances target do
        let state ← saveState
        try
          let subgoals ← goal.applyNoInst inst.val
          let subgoals ← subgoals.mapM (
            fun subgoal => subgoal.synthInstanceSupposing pattern d )
          return subgoals.flatten
        catch _ =>
          restoreState state
      throwError "failed to synthesize instance"

end MVarId

end Lean

-- recursively synthesize type class instances,
-- admitting those matching pattern and setting them as new goals
elab "infer_instance_supposing" p:term : tactic => do
  setGoals (← (← getMainGoal).synthInstanceSupposing (← elabTerm p none))
