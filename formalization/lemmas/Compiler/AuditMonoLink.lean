import lemmas.Compiler.CompMonoLinkMiss
import lemmas.Compiler.CompRunTNClass
import lemmas.Compiler.CompSccOfAny
import lemmas.Compiler.CompSccOfAnyK
import lemmas.Compiler.CompSccOfHeightEnv
import lemmas.Compiler.CompMonoLinkDec
import lemmas.Compiler.CompSccOfRank
import lemmas.Compiler.CompMonoLinkStr

/-! The axioms of the link of `+compiled-mono` and of the run at `mono` `|` (README Gaps 19 (g)).
`CompSccOfAny`, `PokeLinkGood` and track I's `CompSccLoop*` import together since the renames of
`swG` and `sw_gate` (`csSwG`, `csSw_gate`); this file stays apart from `AuditRunDirect.lean` to keep
that one's imports light. -/

#print axioms Formalization.Compiler.monoArm_eq
#print axioms Formalization.Compiler.cuArm_at
#print axioms Formalization.Compiler.monoRaw_hit
#print axioms Formalization.Compiler.monoLinkAt_of
#print axioms Formalization.Compiler.compileUnaryP_gate
#print axioms Formalization.Compiler.mono_slam
#print axioms Formalization.Compiler.mono_tail
#print axioms Formalization.Compiler.mono_get
#print axioms Formalization.Compiler.monoRaw_miss
#print axioms Formalization.Compiler.monoMissAt_of
#print axioms Formalization.Compiler.unaryImageAt_of_gate
#print axioms Formalization.Compiler.monoLinkGood_of_image
#print axioms Formalization.Compiler.cu_gate_dir_scc
#print axioms Formalization.Compiler.comp_run_n2_directNTT
#print axioms Formalization.Compiler.res_n2_directN
#print axioms Formalization.Compiler.comp_run_dirTN
#print axioms Formalization.Compiler.comp_run_n6_allRTN
#print axioms Formalization.Compiler.callOkTN_of_read
#print axioms Formalization.Compiler.callOkTN_of_E
#print axioms Formalization.Compiler.mem_runN
#print axioms Formalization.Compiler.calleeCompiled_sccA
#print axioms Formalization.Compiler.eM_step
#print axioms Formalization.Compiler.eM_start
#print axioms Formalization.Compiler.callOkTN_of_IP
#print axioms Formalization.Compiler.needRead_member
#print axioms Formalization.Compiler.sureNoun_done
#print axioms Formalization.Compiler.callOkTN_member
#print axioms Formalization.Compiler.callOkTN_out
#print axioms Formalization.Compiler.memDoneCall_of
#print axioms Formalization.Compiler.memDoneCall_of_rest
#print axioms Formalization.Compiler.sccLoopAtA_real
#print axioms Formalization.Compiler.callAt_anyA
#print axioms Formalization.Compiler.cu_gate_dir_sccA
#print axioms Formalization.Compiler.calleeCompiled_oneKP
#print axioms Formalization.Compiler.sccCalleeA_of_real
#print axioms Formalization.Compiler.calleeCompiled_stepH
#print axioms Formalization.Compiler.calleeCompiled_heights
#print axioms Formalization.Compiler.calleeCompiled_heights0
#print axioms Formalization.Compiler.above_memS
#print axioms Formalization.Compiler.dirCallsTN_of
#print axioms Formalization.Compiler.memCallOk_of
#print axioms Formalization.Compiler.callOkTN_outW
#print axioms Formalization.Compiler.callOkTN_memOk
#print axioms Formalization.Compiler.memDoneRest_of_S
#print axioms Formalization.Compiler.sccLoopData_of_S
#print axioms Formalization.Compiler.calleeH_of_S
#print axioms Formalization.Compiler.cu_gate_dir_sccH
#print axioms Formalization.Compiler.envIt_low
#print axioms Formalization.Compiler.envLim_agree
#print axioms Formalization.Compiler.envFrom_envIt
#print axioms Formalization.Compiler.calleeCompiled_oneKA
#print axioms Formalization.Compiler.FinMap.uniBy_toNoun
#print axioms Formalization.Compiler.cacheDec_put
#print axioms Formalization.Compiler.cacheDec_uni
#print axioms Formalization.Compiler.rKD_sure
#print axioms Formalization.Compiler.calleeCompiled_sccD
#print axioms Formalization.Compiler.eMD_step
#print axioms Formalization.Compiler.eMD_start
#print axioms Formalization.Compiler.sccLoopAtD_real
#print axioms Formalization.Compiler.calleeCompiled_oneKD
#print axioms Formalization.Compiler.calleeCompiled_heightsD
#print axioms Formalization.Compiler.calleeCompiled_heights0D
#print axioms Formalization.Compiler.callOkTN_memOkD
#print axioms Formalization.Compiler.calleeH_of_SD
#print axioms Formalization.Compiler.cu_gate_dir_sccD
#print axioms Formalization.Compiler.cacheNoun_of_dec
#print axioms Formalization.Compiler.unaryImageAt_of_gateD
#print axioms Formalization.Compiler.monoLinkGood3_of_gate
#print axioms Formalization.Compiler.memCall_side
#print axioms Formalization.Compiler.memCallOk_of_rank
#print axioms Formalization.Compiler.calleeCompiled_sccDStr
#print axioms Formalization.Compiler.sccLoopAtD_realStr
#print axioms Formalization.Compiler.calleeCompiled_heights0DStr
#print axioms Formalization.Compiler.calleeH_of_SDStr
#print axioms Formalization.Compiler.nmDec_of_top
#print axioms Formalization.Compiler.cu_gate_dir_sccDStr
#print axioms Formalization.Compiler.unaryImageAt_of_gateDStr
#print axioms Formalization.Compiler.monoLinkGood3_of_gateStr
