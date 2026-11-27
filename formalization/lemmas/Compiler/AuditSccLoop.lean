import lemmas.Ska.SccLoopCheck
import lemmas.Ska.SccLoopCycle
import lemmas.Ska.SccLoopTotal

/-! The axioms of the theorems of `Ska/SccLoop.lean`, `Ska/SccLoopMsg.lean` and `Ska/SccLoopCycle.lean`
(README Gaps 21): each must print
`[propext, Classical.choice, Quot.sound]` or a subset. -/

open Formalization.SkaModel.SccLoop

#print axioms member_view
#print axioms sweepStep_inv
#print axioms foldl_noany
#print axioms loop_end
#print axioms loop_inv
#print axioms loop_reads
#print axioms loop_left
#print axioms final_member
#print axioms final_keeps
#print axioms cyc_hyp
#print axioms cyc_never
#print axioms Formalization.SkaModel.Comp.msgOrd_abs
#print axioms Formalization.SkaModel.Comp.msgOrd_abs'
#print axioms Formalization.SkaModel.Comp.msgOrd_comm
#print axioms Formalization.SkaModel.Comp.msgNone_idem
#print axioms Formalization.SkaModel.Comp.msgOrd_none_self
#print axioms Formalization.SkaModel.Comp.msgOrd_cycle
#print axioms Formalization.SkaModel.Comp.msgOrd_not_assoc
#print axioms loop_total
#print axioms compileSccIn_total
#print axioms quiet_clean
#print axioms sweepStep_psi
#print axioms cyc_not_ranked
