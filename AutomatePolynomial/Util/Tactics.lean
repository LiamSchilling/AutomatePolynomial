import Lean

open Lean Meta Elab Tactic

namespace Lean

namespace MVarId

-- recursively synthesize type class instances,
-- admitting those matching pattern and setting them as new goals
def synthInstanceSupposing (goal : MVarId) (patterns : List Expr) (d : Nat := 8) :
    MetaM (List MVarId) := do
  match d with
  | 0 => throwError "maximum recursion depth reached"
  | d + 1 =>
  if ← patterns.anyM (fun p => do isDefEq (← goal.getType) p) then
    return [goal]
  else
    for inst in ← SynthInstance.getInstances (← goal.getType) do
      let state ← saveState
      try
        let subgoals ← goal.apply inst.val { allowSynthFailures := true }
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
        let subgoals ← goal.apply inst.val { allowSynthFailures := true }
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

-- intended for combination with infer_instance_trying
-- tries some regular tactics
syntax "try_reg" : tactic
macro_rules
  | `(tactic| try_reg) =>
    `(tactic| (try simp) <;> (try constructor) <;> (try simp) )

-- recursively synthesize type class instances
-- slightly stronger than normal inferInstance
syntax "infer_instance_trying" : tactic
macro_rules
  | `(tactic| infer_instance_trying) =>
    `(tactic| infer_instance_trying <:> ( try_reg ))
