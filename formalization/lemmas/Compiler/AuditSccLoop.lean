import lemmas.Ska.SccLoopCheck
import lemmas.Ska.SccLoopCycle
import lemmas.Ska.SccLoopTotal
import lemmas.Compiler.CompSccLoopGate
import lemmas.Compiler.CompSccLoopUse

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
#print axioms Formalization.Compiler.csiFix_cut
#print axioms Formalization.Compiler.csf_fix
#print axioms Formalization.Compiler.csf_trap
#print axioms Formalization.Compiler.csf_trap_end
#print axioms Formalization.Compiler.csf_trap_rec
#print axioms Formalization.Compiler.tickMap_get
#print axioms Formalization.Compiler.tickMap_put
#print axioms Formalization.Compiler.stN_st0
#print axioms Formalization.Compiler.sw_dirty
#print axioms Formalization.Compiler.sw_keep
#print axioms Formalization.Compiler.sw_mem
#print axioms Formalization.Compiler.sw_st
#print axioms Formalization.Compiler.sw_gate
#print axioms Formalization.Compiler.sw_fold
#print axioms Formalization.Compiler.sw_roll
#print axioms Formalization.Compiler.fin_fold
#print axioms Formalization.Compiler.fin_scc_gate
#print axioms Formalization.Compiler.may_map_bunt
#print axioms Formalization.Compiler.may_roll
#print axioms Formalization.Compiler.top_gate
#print axioms Formalization.Compiler.csf_rec
#print axioms Formalization.Compiler.csf_fin
#print axioms Formalization.Compiler.final_congr
#print axioms Formalization.Compiler.trap_loop
#print axioms Formalization.Compiler.csf_fix_loop
#print axioms Formalization.Compiler.csi_to_fix
#print axioms Formalization.Compiler.csi_gate_loop
#print axioms Formalization.Compiler.hcsi_of_loop
#print axioms Formalization.Compiler.csiNeeds_of_loop
#print axioms Formalization.Compiler.csiSures_of_loop
#print axioms Formalization.Compiler.sureHolds_uni
