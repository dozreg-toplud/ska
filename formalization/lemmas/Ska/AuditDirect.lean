import lemmas.Ska.CompDirect
import lemmas.Ska.CompDirectMTop
import lemmas.Ska.CompDirectMGo
import lemmas.Ska.CompDirectMTailEx
import lemmas.Ska.CompDirectMTailP
import lemmas.Ska.CompDirectMMerge
import lemmas.Ska.CompDirectMCal
import lemmas.Ska.CompDirectMCalFour
import lemmas.Ska.CompDirectMTreeEx
import lemmas.Ska.CompDirectMCloseEx

/-! The axioms of the theorems of track J (direct calls, `Ska/CompDirect.lean`,
README Gaps 18).  `lake build` prints them; each should be `propext`,
`Classical.choice` and `Quot.sound` at most. -/

open Formalization.SkaModel.Comp

#print axioms tailStep_bwd
#print axioms callStep_bwd
#print axioms needOrdAllocRegs_clean
#print axioms runLC_n2_direct
#print axioms fits_of_split
#print axioms split_of_holds
#print axioms runLCM_eq
#print axioms runLCM_false
#print axioms runLCM_true
#print axioms finishLUCM_eq
#print axioms finishLFC_eq_M
#print axioms finishLUCM_bellContractCallTree7
#print axioms finishLUCM_bellContractCallTreeA
#print axioms finishLUCM_bellContractTopTree
#print axioms finishLUCM_contractNC
#print axioms monoTryLoop_mono
#print axioms holdsN_frame
#print axioms monoTry_go
#print axioms monoTryLoop_ok
#print axioms runLCM_tail
#print axioms copyL_reg_bunt
#print axioms minkF_tail
#print axioms mink_tail_bwd
#print axioms tail_done
#print axioms finishLUCM_contractGB
#print axioms finishLUCM_contractTail
#print axioms finishLUCM_bellContractTail
#print axioms callR_bellContract
#print axioms RunOKLB.copyBunt
#print axioms monoTryLoop_root
#print axioms minkC7_direct
#print axioms treeX_run
#print axioms tailP_done
#print axioms finishLUCM_contractTailP
#print axioms finishLUCM_bellContractTailP
#print axioms consTail_contract
#print axioms goJ_hop_par
#print axioms optStep_fwd
#print axioms optStep_bwd
#print axioms pesStep_fwd
#print axioms pesStep_bwd
#print axioms CondFresh.lower
#print axioms kerfLBM
#print axioms runOKGB_sevenLW
#print axioms monoTry_goW
#print axioms callOut_goal
#print axioms treeN_run
#print axioms runLCM_cal
#print axioms callLBM_run
#print axioms LOKS.toM
#print axioms lokSM_direct
#print axioms four_doneBM
#print axioms finishLUCM_contractFourDirect
#print axioms fourCallR_bellContract
#print axioms lokS_consHM
#print axioms lokS_consFM
#print axioms lokS_consSM
#print axioms lokS_indirectFM
#print axioms lokS_sevenFM
#print axioms lokS_fiveM
#print axioms five_doneBM
#print axioms done_of_lokSFM
#print axioms callLBM_runM
#print axioms lokSM_directF
#print axioms tailP_doneM
#print axioms jNewLSM_direct
#print axioms lokSM_callTreeD
#print axioms callTreeD_done
#print axioms finishLUCM_contractCallTreeD
#print axioms finishLUCM_bellContractCallTreeD
#print axioms dt_contract
#print axioms dc_contract
#print axioms dk_contract
#print axioms dn_contract
#print axioms Formalization.SkaModel.table_fwd
#print axioms Formalization.SkaModel.table_bwd
#print axioms Formalization.SkaModel.table_closed
#print axioms Formalization.SkaModel.table_closed_zero
#print axioms closed_callTreeD
#print axioms tableOK_slot
#print axioms closed_slotCall
#print axioms closed_slotCallFour
