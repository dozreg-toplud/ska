import lemmas.Ska.SccLoopCheck
import lemmas.Ska.SccLoopCycle
import lemmas.Ska.SccLoopTotal
import lemmas.Compiler.CompSccLoopGate
import lemmas.Compiler.CompSccLoopUse
import lemmas.Compiler.CompSccLoopClose
import lemmas.Compiler.CompSccLoopPrint
import lemmas.Compiler.CompSccLoopMemDone
import lemmas.Compiler.CompSccLoopMemShape
import lemmas.Ska.SccLoopReal
import lemmas.Compiler.CompSccLoopMemStep
import lemmas.Compiler.CompSccLoopSoft
import lemmas.Ska.SccLoopSoftCheck
import lemmas.Ska.SccLoopSoftFinCheck
import lemmas.Compiler.CompSccLoopSoftDone
import lemmas.Compiler.CompSccLoopStrDec
import lemmas.Compiler.CompSccLoopSoftEmit

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
#print axioms Formalization.Compiler.csSw_gate
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
#print axioms Formalization.SkaModel.SccLoop.dfsF_total
#print axioms Formalization.SkaModel.SccLoop.dfsOrder_sub
#print axioms Formalization.SkaModel.SccLoop.dfsOrder_cover
#print axioms Formalization.Compiler.ord_trap
#print axioms Formalization.Compiler.csf_order
#print axioms Formalization.Compiler.rep_gate_kinv
#print axioms Formalization.Compiler.csi_kids
#print axioms Formalization.Compiler.csi_done_false
#print axioms Formalization.Compiler.kids_self
#print axioms Formalization.SkaModel.SccLoop.compileSccIn_ml_some
#print axioms Formalization.SkaModel.SccLoop.compileSccIn_ml_out
#print axioms Formalization.Compiler.csi_levy_miss
#print axioms Formalization.Compiler.top_of_exact
#print axioms Formalization.Compiler.kids_facts
#print axioms Formalization.Compiler.csi_gate_loop_d
#print axioms Formalization.Compiler.csi_gate_ranked
#print axioms Formalization.Compiler.csiNeeds_of_loopR
#print axioms Formalization.Compiler.ccc_csi_open
#print axioms Formalization.Compiler.cccMiss_of_loop

-- Gaps 21.14 (the print, the member gate on `%done` for a real SCC)
#print axioms Formalization.Compiler.printId_pill
#print axioms Formalization.Compiler.csi_gate_loop_np
#print axioms Formalization.Compiler.csi_gate_loop_d_np
#print axioms Formalization.Compiler.csi_gate_ranked_np
#print axioms Formalization.Compiler.hcsi_of_loop_np
#print axioms Formalization.Compiler.mem_to_finish_R
#print axioms Formalization.Compiler.mem_prod_newM
#print axioms Formalization.Compiler.mem_prod_oldM
#print axioms Formalization.Compiler.mem_gate_done_R
#print axioms Formalization.SkaModel.SccLoop.compReal_done
#print axioms Formalization.SkaModel.SccLoop.toStraightF_need
#print axioms Formalization.SkaModel.SccLoop.finishLFC_need
#print axioms Formalization.Compiler.memMovedN_was
#print axioms Formalization.Compiler.memChgN_loob
#print axioms Formalization.Compiler.memChgO_loob
#print axioms Formalization.Compiler.csMlExact_put
#print axioms Formalization.Compiler.csSureHolds_put
#print axioms Formalization.Compiler.csAgreeIP_put
#print axioms Formalization.Compiler.csExt_put
#print axioms Formalization.Compiler.csQK_put
#print axioms Formalization.Compiler.rK_sure
#print axioms Formalization.Compiler.memDoneM_eq
#print axioms Formalization.Compiler.mem_done_step
#print axioms Formalization.Compiler.memGate_done_real
#print axioms Formalization.Compiler.sure_miss_of_agree
#print axioms Formalization.Compiler.memGate_done_K
#print axioms Formalization.SkaModel.Comp.simS_bind
#print axioms Formalization.SkaModel.Comp.kernS_sim
#print axioms Formalization.SkaModel.Comp.lazyShutS_sim
#print axioms Formalization.SkaModel.Comp.kerfS_sim
#print axioms Formalization.SkaModel.Comp.sixNextLCS_sim
#print axioms Formalization.SkaModel.Comp.callLS_sim
#print axioms Formalization.SkaModel.Comp.runLCS_sim
#print axioms Formalization.SkaModel.Comp.runLCS_eq
#print axioms Formalization.SkaModel.SccLoop.memDoneMS_eq
#print axioms Formalization.SkaModel.SccLoop.compRealS_done
#print axioms Formalization.SkaModel.SccLoop.compRealS_eq
#print axioms Formalization.SkaModel.SccLoop.cfgRealS_eq
#print axioms Formalization.SkaModel.SccLoop.doneRetS_iff
#print axioms Formalization.Compiler.crxts_of_xt
#print axioms Formalization.Compiler.sdArm_eq
#print axioms Formalization.Compiler.sd_trap
#print axioms Formalization.Compiler.sd_tree
#print axioms Formalization.Compiler.mlStr_put
#print axioms Formalization.Compiler.loopRS_reset
#print axioms Formalization.Compiler.loopRS_put
#print axioms Formalization.Compiler.ml_decode
#print axioms Formalization.Compiler.mem_done_stepStr
#print axioms Formalization.Compiler.memGate_done_realStr
#print axioms Formalization.Compiler.memGate_done_KStr
#print axioms Formalization.Compiler.csi_gate_loop_dStr
#print axioms Formalization.Compiler.csi_gate_rankedStr
#print axioms Formalization.Compiler.csi_gate_ranked_dec
#print axioms Formalization.Compiler.uni_decode
#print axioms Formalization.Compiler.se_at
#print axioms Formalization.Compiler.se_slam
#print axioms Formalization.Compiler.se_nil
#print axioms Formalization.Compiler.se_end
#print axioms Formalization.Compiler.csiDec_of_loop
