import lemmas.Compiler.CompMonoLinkMiss
import lemmas.Compiler.CompRunTNClass
import lemmas.Compiler.CompSccOfAny
import lemmas.Compiler.CompSccOfAnyK

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
