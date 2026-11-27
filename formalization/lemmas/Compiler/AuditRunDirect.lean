import lemmas.Compiler.CompRunDirect
import lemmas.Compiler.CompRunDirectC
import lemmas.Compiler.CompRunDirectP
import lemmas.Compiler.CompRunDirectS
import lemmas.Compiler.CompRunDirectMono
import lemmas.Compiler.CompRunDirectMonoL
import lemmas.Compiler.CompRunDirectMonoB
import lemmas.Compiler.CompRunDirectMonoP

/-! The axioms of the link of the direct call of `%2` (README Gaps 19). -/

open Formalization.Compiler

#print axioms crd_eq
#print axioms crd_pure
#print axioms crd_test
#print axioms crd_drop
#print axioms comp_run_n2_drop
#print axioms res_n2_drop
#print axioms made_gate
#print axioms crdk_eq
#print axioms crd_ctail
#print axioms crd_blk_done
#print axioms crd_blk_next
#print axioms crd_from7
#print axioms crd_head6
#print axioms crd_test_all
#print axioms crd_model_call
#print axioms crd_call_body
#print axioms comp_run_n2_call
#print axioms km_crdBlockM
#print axioms linv_need
#print axioms crd_goals
#print axioms crd_hpq
#print axioms res_n2_call
#print axioms comp_run_n2_callM
#print axioms csu_bat
#print axioms sureNoun_of_map
#print axioms csu_gate
#print axioms ccc_bat
#print axioms ccc_nary
#print axioms cne_bat
#print axioms cne_read
#print axioms callNoun_of_r
#print axioms comp_run_n2_callR
#print axioms mtc_gb
#print axioms mtc_at
#print axioms mtc_none
#print axioms mtc_this
#print axioms mtc_loop_eq
#print axioms mtcPA_0
#print axioms mtcPA_1
#print axioms mtcPA_2
#print axioms mtcPA_2n
#print axioms mtcPA_3
#print axioms mtcPA_3n
#print axioms mtcPA_4
#print axioms mtcPA_L
#print axioms mtcBO_0
#print axioms mtcBO_1
#print axioms mtcBO_2
#print axioms mtcBO_2n
#print axioms mtcBO_3
#print axioms mtcBO_3n
#print axioms mtcBO_4
#print axioms mtcBO_L
#print axioms mtc_disp_pair
#print axioms mtc_disp_both
#print axioms mtc_pair
#print axioms mtc_both
#print axioms mtc_loop
#print axioms mtc_gate
#print axioms monoBlocks_eq
#print axioms crd_blkM_done
#print axioms crNM_eq
#print axioms crNM_0
#print axioms crNM_1
#print axioms crNM_2
#print axioms crNM_3
#print axioms crNM_4
#print axioms crNM_5
#print axioms crNM_6
#print axioms crNM_L
#print axioms crd7_nm
#print axioms crd_blkM_next
#print axioms mtc_arm
#print axioms crd_7to9M
#print axioms crd_cnfR
#print axioms crd_ctailR
#print axioms crd_from7M
#print axioms crd_head6M
#print axioms crd_model_callM
#print axioms crd_callM
#print axioms callLM_true_direct
#print axioms km_monoTryLoop
#print axioms km_crdBlockMM
#print axioms km_monoBlocks
#print axioms crdBlockMM_sub
#print axioms monoBlocks_sub
#print axioms ginv_noar
#print axioms crd_goalsM
#print axioms runLCM_n2_direct
#print axioms crd_model_n2M
#print axioms comp_run_n2_callMono
#print axioms crd_fq_resR
#print axioms crd_hpqM
#print axioms res_n2_callMono
#print axioms comp_run_n2_callMM
#print axioms crd_nfR
#print axioms crd_dropR
#print axioms crd_model_dropM
#print axioms comp_run_n2_dropMono
#print axioms res_n2_dropMono
#print axioms comp_run_n2_directMM
#print axioms res_n2_directMono
#print axioms noDirect_of_nd
#print axioms partLM_of_partL
#print axioms comp_run_n2_directML
#print axioms res_n2_directML
