import lemmas.Ska.Statements
import lemmas.Ska.CapeFacts
import lemmas.Ska.ContractExamples
import lemmas.Ska.BugWitness
import lemmas.Ska.NommSem
import lemmas.Ska.NommAgree
import lemmas.Ska.FolLoopSound
import lemmas.Ska.CallGraph
import lemmas.Ska.Prov
import lemmas.Ska.ProvFacts
import lemmas.Ska.WantMono
import lemmas.Ska.AppPath
import lemmas.Ska.Stat
import lemmas.Ska.AppMask
import lemmas.Ska.FolLoopRel
import lemmas.Ska.Converge
import lemmas.Ska.ConvergeProd
import lemmas.Ska.CompSim

/-! The axioms of the main theorems of `lemmas/Ska`.  `lake build` prints
them; each should be `propext`, `Classical.choice` and `Quot.sound` at most. -/

open Formalization.SkaModel

#print axioms interp_fwd
#print axioms interp_bwd
#print axioms meek
#print axioms weak
#print axioms converse
#print axioms meek_cell_tag
#print axioms meek_reach
#print axioms weak_reach
#print axioms converse_reach
#print axioms knit_fits
#print axioms pull_fits
#print axioms darn_fits
#print axioms purr_fits_left
#print axioms purr_fits_right
#print axioms huge_sound
#print axioms app_fits
#print axioms all_fits
#print axioms jibeMk_of_fits
#print axioms int_has
#print axioms uni_has
#print axioms patLoop_has
#print axioms lotLoop_has
#print axioms minkF_trace
#print axioms tail_fwd
#print axioms tail_bwd
#print axioms nok_fwd
#print axioms nok_bwd
#print axioms inline_drop
#print axioms default_crash
#print axioms dif_has
#print axioms lack_has
#print axioms bare_loops
#print axioms eval_bare
#print axioms bare_runs
#print axioms EvalA.toEvalH
#print axioms toneRel_mink_self
#print axioms nomm_fwd
#print axioms nomm_bwd
#print axioms nomm_agree
#print axioms doubleInt_fits_left
#print axioms doubleInt_fits_right
#print axioms pull_yes
#print axioms shape_other_crashes
#print axioms Annot.mono
#print axioms folLoop_good
#print axioms folLoop_prod
#print axioms folLoop_annot
#print axioms safeFolFol_inline
#print axioms saf_memo
#print axioms folLoop_agree
#print axioms msgSock_fits_left
#print axioms mergeProd_fits
#print axioms answers_tabOK
#print axioms entry_agree
#print axioms codeOK_of_entries
#print axioms entry_ok_of_run
#print axioms pull_blank_of_none
#print axioms patchProd_sound
#print axioms hit_prod
#print axioms pull_eq_sockAt
#print axioms springAt_slot
#print axioms provO_slot
#print axioms provO_knit
#print axioms provO_doubleInt_left
#print axioms provO_doubleInt_right
#print axioms provO_darn
#print axioms provO_compose
#print axioms distribute_has
#print axioms folLoopF_want_mono
#print axioms fitsOpt_app_part
#print axioms known_formula
#print axioms GenLe.toPosLe
#print axioms GenLe.appFits
#print axioms statOK_slot
#print axioms statOK_knit
#print axioms statOK_doubleInt_left
#print axioms statOK_doubleInt_right
#print axioms statOK_darn
#print axioms statOK_compose
#print axioms statOK_patchProd
#print axioms fitsOpt_app_mask
#print axioms call_sub_fits
#print axioms known_at
#print axioms folLoop_rgood
#print axioms folLoop_wantSound
#print axioms folLoop_relProd
#print axioms app_cape_fits
#print axioms huge_app_fits
#print axioms provO_patchProd
#print axioms msgSock_genLe
#print axioms rtab_of_answers
#print axioms codeOK_of_converged
#print axioms converged_agree
#print axioms prodRel_of_rtab
#print axioms minkF_inv_n2
#print axioms folLoop_rprod
#print axioms folLoop_relProdN
#print axioms prodRelN_of_converged
#print axioms prodRel_of_converged
#print axioms codeOK_at_convergence
#print axioms agree_at_convergence
#print axioms nommF_pure
#print axioms nommF_pure_total
#print axioms mink_pure
#print axioms bellContract_of_compDone
#print axioms compDone_of_compRel
#print axioms compRel_done_of_next
#print axioms const_contract
#print axioms slot1_contract
#print axioms bomb_contract
#print axioms Holds.agree
#print axioms GoalRel.transfer
#print axioms compRel_n7
#print axioms compRel_n6
