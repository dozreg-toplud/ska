import lemmas.Compiler.CompRunShapeLeaf
import lemmas.Compiler.CompRunShapeThree
import lemmas.Compiler.CompRunShapePast
import lemmas.Ska.RunShapeAgree
import lemmas.Compiler.CompRunShapeTen
import lemmas.Compiler.CompRunShapeTwo
import lemmas.Compiler.CompRunShapeTwoI
import lemmas.Compiler.CompRunShapeSix
import lemmas.Compiler.CompRunShapeECases
import lemmas.Compiler.CompRunShapeAll
import lemmas.Compiler.CompRunShapeAll6
import lemmas.Compiler.CompRunShapeMember
import lemmas.Compiler.CompRunShapeColl
import lemmas.Compiler.CompRunShapeMay
import lemmas.Compiler.CompRunShapeBno
import lemmas.Compiler.CompRunShapeLeaps
import lemmas.Compiler.CompRunShapeThisOnly
import lemmas.Compiler.CompRunShapeWhole
import lemmas.Compiler.CompRunShapeSoftFork
import lemmas.Compiler.CompRunShapeBranch
import lemmas.Compiler.CompRunShapeSixN
import lemmas.Compiler.CompRunShapeTwelve
import lemmas.Compiler.CompRunShapePastIf
import lemmas.Compiler.CompRunShapeEleven
import lemmas.Compiler.CompRunShapeMean

/-! The axioms of the main theorems of track A's `+run-shape` link (2026-11-27). -/

#print axioms Formalization.Compiler.rs_arm_at
#print axioms Formalization.Compiler.rs_push
#print axioms Formalization.Compiler.rs_n1
#print axioms Formalization.Compiler.rs_n0
#print axioms Formalization.Compiler.rs_n7
#print axioms Formalization.Compiler.rs_n4
#print axioms Formalization.Compiler.rs_cls
#print axioms Formalization.Compiler.lf_at
#print axioms Formalization.Compiler.lf_all
#print axioms Formalization.Compiler.lazeFromAtW_door
#print axioms Formalization.Compiler.rs_n0W
#print axioms Formalization.Compiler.rs_n7W
#print axioms Formalization.Compiler.runShape_nz
#print axioms Formalization.Compiler.rs_clsW
#print axioms Formalization.Compiler.lzp_at
#print axioms Formalization.Compiler.lzp_gate
#print axioms Formalization.Compiler.lzp_door
#print axioms Formalization.Compiler.lne_at
#print axioms Formalization.Compiler.lne_all
#print axioms Formalization.Compiler.lne_door
#print axioms Formalization.Compiler.rs_n3W
#print axioms Formalization.Compiler.rs_cls5
#print axioms Formalization.Compiler.rs_done5
#print axioms Formalization.Compiler.lc_at
#print axioms Formalization.Compiler.lc_all
#print axioms Formalization.Compiler.lc_door
#print axioms Formalization.Compiler.lazeCopy_nz
#print axioms Formalization.Compiler.lsp_at
#print axioms Formalization.Compiler.lsp_all
#print axioms Formalization.Compiler.lsp_door
#print axioms Formalization.Compiler.lazeSplit_nz
#print axioms Formalization.Compiler.lazeSplit_some
#print axioms Formalization.Compiler.lpr_gate
#print axioms Formalization.Compiler.lem_gate
#print axioms Formalization.Compiler.lmu_gate
#print axioms Formalization.Compiler.lzi_at
#print axioms Formalization.Compiler.lzi_all
#print axioms Formalization.Compiler.lzi_door
#print axioms Formalization.Compiler.lazeInto_nz
#print axioms Formalization.Compiler.lazePast_nz
#print axioms Formalization.Compiler.rs_consN
#print axioms Formalization.Compiler.rs_consP
#print axioms Formalization.Compiler.rs_consD
#print axioms Formalization.Compiler.rs_consW
#print axioms Formalization.Compiler.rs_n5W
#print axioms Formalization.Compiler.consNext_nz
#print axioms Formalization.Compiler.runShape_nz7
#print axioms Formalization.Compiler.rs_cls7
#print axioms Formalization.Compiler.rs_done7
#print axioms Formalization.Compiler.rs_n10W
#print axioms Formalization.Compiler.tenNz
#print axioms Formalization.Compiler.runShape_nz8
#print axioms Formalization.Compiler.rs_cls8
#print axioms Formalization.Compiler.rs_done8
#print axioms Formalization.Compiler.rsd_at
#print axioms Formalization.Compiler.rs_n2dW
#print axioms Formalization.Compiler.twoNz
#print axioms Formalization.Compiler.lzs_gate
#print axioms Formalization.Compiler.lpf_gate
#print axioms Formalization.Compiler.lbg_gate
#print axioms Formalization.Compiler.rs6_at
#print axioms Formalization.Compiler.rs_n6DP
#print axioms Formalization.Compiler.runShape_n6DP_nz
#print axioms Formalization.Compiler.rs_n2iW

/-! 2026-11-28: the induction on `RsAtE`, `%6` under `%next`, `%12`, `%11`, the helper arms, the sweeps' branch. -/

#print axioms Formalization.Compiler.rs_n3E
#print axioms Formalization.Compiler.rs_n7E
#print axioms Formalization.Compiler.rs_consE
#print axioms Formalization.Compiler.rs_n10E
#print axioms Formalization.Compiler.rs_n5E
#print axioms Formalization.Compiler.rs_n2iE
#print axioms Formalization.Compiler.rs_n6DPE
#print axioms Formalization.Compiler.runShape_nzE
#print axioms Formalization.Compiler.runShape_nzT
#print axioms Formalization.Compiler.rs_clsE
#print axioms Formalization.Compiler.rs_tailE
#print axioms Formalization.Compiler.rs_doneE
#print axioms Formalization.Compiler.memY_gen
#print axioms Formalization.Compiler.ms_run
#print axioms Formalization.Compiler.memShape_branchA
#print axioms Formalization.Compiler.memShape_branchA6
#print axioms Formalization.Compiler.lzt_gate
#print axioms Formalization.Compiler.lco_gate
#print axioms Formalization.Compiler.lco_call
#print axioms Formalization.Compiler.lmy_gate
#print axioms Formalization.Compiler.lmy_call
#print axioms Formalization.Compiler.bno_gate
#print axioms Formalization.Compiler.bno_loop
#print axioms Formalization.Compiler.bno_call
#print axioms Formalization.Compiler.nf_gate_ord
#print axioms Formalization.Compiler.llp_all
#print axioms Formalization.Compiler.lls_all
#print axioms Formalization.Compiler.lazeLeaps_nz
#print axioms Formalization.Compiler.noc_gate
#print axioms Formalization.Compiler.nof_gate
#print axioms Formalization.Compiler.lto_all
#print axioms Formalization.Compiler.whl_gate
#print axioms Formalization.Compiler.whl_both
#print axioms Formalization.Compiler.lsf_all
#print axioms Formalization.Compiler.lienO_gate
#print axioms Formalization.Compiler.lbr_all
#print axioms Formalization.Compiler.lbr_call
#print axioms Formalization.Compiler.lazeBranch_nz
#print axioms Formalization.Compiler.six_fuel
#print axioms Formalization.Compiler.rs_n6NE
#print axioms Formalization.Compiler.sixShape_nz
#print axioms Formalization.Compiler.sixDeep_of_idem
#print axioms Formalization.Compiler.runShape_nzE6
#print axioms Formalization.Compiler.rs_clsE6
#print axioms Formalization.Compiler.rs_doneE6
#print axioms Formalization.Compiler.rs_n12E
#print axioms Formalization.Compiler.twelveNz
#print axioms Formalization.Compiler.lpi_gate
#print axioms Formalization.Compiler.lazePastIf_nz
#print axioms Formalization.Compiler.rs_n11sE
#print axioms Formalization.Compiler.rs_n11dE
#print axioms Formalization.Compiler.elevenSNz
#print axioms Formalization.Compiler.elevenDNz
#print axioms Formalization.Compiler.rmk_gate
#print axioms Formalization.Compiler.meanNz
