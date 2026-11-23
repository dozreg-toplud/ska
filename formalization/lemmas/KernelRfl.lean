module

public import Lean
/-!
`kernel_rfl` closes `a = b` with `Eq.refl a` and leaves the comparison to the
kernel, which evaluates both sides when the theorem is added.  The elaborator
would run the same computation in its own, much slower evaluator first.
-/

@[expose] public section

open Lean Elab Tactic Meta

elab "kernel_rfl" : tactic => do
  let goal ← getMainGoal
  let type ← instantiateMVars (← goal.getType)
  let some (_, lhs, _) := type.eq? | throwError "kernel_rfl: the goal is not an equation"
  goal.assign (← mkEqRefl lhs)

end
