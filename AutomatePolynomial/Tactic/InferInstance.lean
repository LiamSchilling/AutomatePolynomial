import Lean

open Lean Meta Elab Tactic

namespace Lean.MVarId

-- recursively synthesize type class instances,
-- trying a provided tactic to resolve those that fail
def synthInstanceTrying (goal : MVarId) (tactic : Syntax) (d : Nat := 8) :
    MetaM Unit := do
  -- terminate at max depth
  match d with
  | 0 => throwError "maximum recursion depth reached"
  | d + 1 =>
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
        let _ ← subgoals.reverse.mapM (synthInstanceTrying . tactic d)
        return
      catch _ =>
        restoreState state
    throwError "failed to synthesize instance"

end Lean.MVarId

-- recursively synthesize type class instances,
-- trying a provided tactic to resolve those that fail
elab "infer_instance_trying" "<:>" t:tactic : tactic => do
  (← getMainGoal).synthInstanceTrying t

-- intended for combination with infer_instance_trying
-- tries some regular tactics
syntax "try_reg" : tactic
macro_rules
  | `(tactic| try_reg) =>
    `(tactic|
      (try simp) <;>
      (try trivial) <;>
      (try constructor) <;>
      (try simp) <;>
      (try trivial) )

-- recursively synthesize type class instances
-- slightly stronger than normal inferInstance
syntax "infer_instance_trying" : tactic
macro_rules
  | `(tactic| infer_instance_trying) =>
    `(tactic| infer_instance_trying <:> ( try_reg ))
