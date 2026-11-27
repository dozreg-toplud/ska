import lemmas.Compiler.CompSccLoopShapeLoop
import lemmas.Ska.SccLoopShapeCheck

/-! The axioms of the `%must` / `%may` steps (README Gaps 21.18).  Apart from `AuditSccLoop.lean`:
`Ska/RunShape.lean` (track A) and `Ska/SccLoopSoft.lean` both define `SkaModel.Comp.liftS`, so the
two cannot be imported together. -/

#print axioms Formalization.SkaModel.SccLoop.compReal_sweep
#print axioms Formalization.SkaModel.SccLoop.lazeReal_eq
#print axioms Formalization.Compiler.mem_entryX
#print axioms Formalization.Compiler.mem_afterX
#print axioms Formalization.Compiler.fin_placeholder
#print axioms Formalization.Compiler.mem_prod_newX
#print axioms Formalization.Compiler.mem_prod_oldX
#print axioms Formalization.Compiler.mem_gate_sweep_R
#print axioms Formalization.Compiler.memChgTN_loob
#print axioms Formalization.Compiler.topH_nil
#print axioms Formalization.Compiler.topH_of_topN
#print axioms Formalization.Compiler.mem_sweep_step
#print axioms Formalization.Compiler.memGate_sweep_real
#print axioms Formalization.Compiler.memGate_may_K
#print axioms Formalization.Compiler.memGate_must_K
#print axioms Formalization.Compiler.csi_gate_ranked_shape
