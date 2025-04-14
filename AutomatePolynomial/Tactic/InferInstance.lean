import Lean

/-!
# Infer Instance

More powerful search tactics for instance inference.

 -/

open Lean Meta Elab Tactic

namespace Lean.MVarId

/-- Depth-first search of instances for inference,
trying a given tactic to resolve the current subgoal at any step where
Lean's automatic inference fails  -/
def synthInstanceTrying (goal : MVarId) (tactic : Syntax) (d : Nat := 8) :
    MetaM Unit := do
  -- terminate at max depth
  match d with
  | 0 => throwError "maximum recursion depth reached"
  | d' + 1 =>
  -- try to resolve goal using tactic
  let state ← saveState
  try
    let (subgoals, _) ← runTactic goal tactic
    match subgoals with
    | [] => return
    | _ => throwError "tactic failed to resolve subgoals"
  catch _ =>
    restoreState state
    -- iterate through applicable instances
    for inst in (← SynthInstance.getInstances (← goal.getType)).reverse do
      -- try to apply the instance and recursively resolve resulting subgoals
      let state ← saveState
      try
        let subgoals ← goal.apply inst.val { allowSynthFailures := true }
        let _ ← subgoals.reverse.mapM (synthInstanceTrying . tactic d')
        return
      catch _ =>
        restoreState state
    throwError "failed to synthesize instance"

end Lean.MVarId

/-- Depth-first search of instances for inference of the main goal,
trying a given tactic to resolve the current subgoal at any step where
Lean's automatic inference fails  -/
elab "infer_instance_trying" "<:>" t:tactic : tactic => do
  (← getMainGoal).synthInstanceTrying t
