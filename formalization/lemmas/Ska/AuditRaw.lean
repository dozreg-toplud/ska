import lemmas.Ska.RawInvTop
import lemmas.Ska.RawInvCheck
import lemmas.Ska.RawInvSix
import lemmas.Ska.RawInvTopX
import lemmas.Ska.RawInvFragX
import lemmas.Ska.RawInvIHX
import lemmas.Ska.RawInvIHXBin
import lemmas.Ska.RawInvIHXSix
import lemmas.Ska.RawInvFinishX
import lemmas.Ska.RawInvEApart
import lemmas.Ska.RawInvWholeX
import lemmas.Ska.RawInvStX
import lemmas.Ska.RawInvATX
import lemmas.Ska.RawInvCAT
import lemmas.Ska.RawInvCLSpec
import lemmas.Ska.RawInvCLIJ
import lemmas.Ska.RawInvCLCollapse
import lemmas.Ska.RawInvCLRun
import lemmas.Ska.RawInvCLPast
import lemmas.Ska.RawInvCLFrameRun
import lemmas.Ska.RawInvCLCopyIL
import lemmas.Ska.RawInvCLRunL

/-!
# Axioms of the main theorems of track D (README Gaps 14)

Only `propext`, `Classical.choice` and `Quot.sound` are allowed.
-/

open Formalization SkaModel Raw

#print axioms defOnceR_of_defUniq
#print axioms defFirst_of_live
#print axioms trimBr_of_noTr
#print axioms defUniq_of
#print axioms passOK_of
#print axioms downPar_of_args
#print axioms run_raw
#print axioms raw_cons
#print axioms raw_n5
#print axioms raw_n10
#print axioms raw_collapse
#print axioms raw_copy
#print axioms raw_split
#print axioms raw_mede
#print axioms raw_into
#print axioms kernLoop_raw
#print axioms raw_sureLoop
#print axioms chase_raw
#print axioms optIn_toStraight
#print axioms optIn_finish
#print axioms optIn_finishLF
#print axioms optIn_finishLU
#print axioms dInvR_finishLF
#print axioms dInvR_finishLU
#print axioms rawDInv_finishLF
#print axioms rawDInv_finishLU
#print axioms optimize_keeps_finishLF
#print axioms optimize_keeps_finishLU
#print axioms run_closed
#print axioms live_cut
#print axioms liveAv_region
#print axioms raw_coerce
#print axioms optIn_finishLF6
#print axioms optIn_finishLF_frag6
#print axioms rawDInv_finishLF_frag6
#print axioms optimize_keeps_finishLF_frag6
#print axioms live_prep
#print axioms live_entry_of_prep
#print axioms liveK_prep
#print axioms acyclic_of_jdownR
#print axioms passOK_ofR
#print axioms downPar_of_argsR
#print axioms chase_rawR
#print axioms chaseFin_rawR
#print axioms optIn_toStraightR
#print axioms optIn_toStraight_prep
#print axioms coerceLazyL_prep
#print axioms run_rawP
#print axioms run_rawU
#print axioms live_prependRk
#print axioms run_rawPK
#print axioms run_rawUK
#print axioms sip_reRank
#print axioms rawX_tail
#print axioms rawX_frag
#print axioms rawX_sevenFrom
#print axioms rawX_seven
#print axioms rawX_four
#print axioms rawX_three
#print axioms rawX_binTail
#print axioms rawX_cons
#print axioms rawX_five
#print axioms rawX_ten
#print axioms rawX_sixTail
#print axioms rawX_sixP
#print axioms sip_forkSure
#print axioms rawX_sixN
#print axioms rawX_six
#print axioms runX_rawIHX
#print axioms argsAboveR_upRk_of_xup
#print axioms runX_rawIHX_up
#print axioms raw_coerceP
#print axioms coI_step
#print axioms coerceLazyL_prepI
#print axioms optIn_finishLFX_of
#print axioms optimize_keeps_finishLFX_of
#print axioms runX_eap
#print axioms lazOK_run
#print axioms optIn_finishLFX
#print axioms optimize_keeps_finishLFX
#print axioms optIn_finishLFX_consSix
#print axioms optimize_keeps_consSix
#print axioms optIn_finishLFX_sixSix
#print axioms optimize_keeps_sixSix
#print axioms optIn_renOutR
#print axioms optIn_prepN
#print axioms walkLazy_flat
#print axioms kernStep
#print axioms kernList_prep
#print axioms opsRF_ren_back
#print axioms liveK_frame
#print axioms optIn_finishLUX
#print axioms optimize_keeps_finishLUX
#print axioms optIn_finishLUX_consSix
#print axioms optimize_keeps_consSixU
#print axioms optIn_finishLUX_sixSix
#print axioms optimize_keeps_sixSixU
#print axioms stOut_ren
#print axioms chase_nil
#print axioms chaseFin_two
#print axioms readsIn_of_live
#print axioms stIn_toStraight_prep
#print axioms stIn_prepN
#print axioms stIn_finishLFX_of
#print axioms stIn_finishLUX
#print axioms optInput_finishLFX_of
#print axioms optInput_finishLUX_of
#print axioms Formalization.Compiler.opt_total_finishLFX
#print axioms Formalization.Compiler.opt_total_finishLUX
#print axioms run_at
#print axioms runX_at
#print axioms runAT_fragX
#print axioms stIn_finishLFX_at
#print axioms stIn_finishLUX_at
#print axioms optInput_finishLFX_at
#print axioms optInput_finishLUX_at
#print axioms Formalization.Compiler.opt_total_finishLFX_at
#print axioms Formalization.Compiler.opt_total_finishLUX_at
#print axioms Formalization.SkaModel.Comp.qm_kern
#print axioms Formalization.SkaModel.Comp.qm_copyLazyL
#print axioms ht_callL
#print axioms ht_runLC
#print axioms runATC_plain
#print axioms runDownC_plain
#print axioms LiveC.trans
#print axioms liveRun_seven
#print axioms liveC_fromL
#print axioms liveK_prepK
#print axioms unpM_prep
#print axioms liveK_hop_root
#print axioms liveK_old
#print axioms liveC_simpleNextL_done
#print axioms walkLazy_prepG
#print axioms unpM_prepG
#print axioms medeL_walk
#print axioms liveC_medeL
#print axioms liveC_bombL
#print axioms liveC_simpleNextL_pick
#print axioms liveC_n0
#print axioms liveC_n1
#print axioms il_emitGoal
#print axioms il_fromL
#print axioms il_medeL
#print axioms liveRun_n0
#print axioms liveRun_n1
#print axioms liveRun_n7
#print axioms walkLazy_inv
#print axioms walkLazy_prepD
#print axioms collapseGate_step
#print axioms collapseWalk_prep
#print axioms liveK_walkR
#print axioms liveC_emitG
#print axioms liveRun_n4_done
#print axioms liveRun_n4_pick
#print axioms liveRun_n4
#print axioms liveRun_clq
#print axioms doneBlocks_spec
#print axioms liveRun_n3
#print axioms liveRun_plainOf
#print axioms il_gen0
#print axioms liveRun_plain_topOf
#print axioms forlSpecL
#print axioms collapseGate_cw
#print axioms collapseSpecL
#print axioms pastL_spec
#print axioms pastL_frame
#print axioms il_lazyReg_after
#print axioms frame_copyL
#print axioms frame_chain
#print axioms frame_splitL
#print axioms frame_intoL
#print axioms frame_kerf
#print axioms frame_collapseL
#print axioms frame_medeL
#print axioms frameRun_n2
#print axioms frameRun_cons
#print axioms frameRun_n10
#print axioms frameRun_n5
#print axioms frameRun_plain
#print axioms copyNeed_dist
#print axioms copyNeed_mv
#print axioms mr_copyLazyL
#print axioms copyL_live
#print axioms cr_copyLazyL
#print axioms copyL_il
#print axioms copyL_spec
#print axioms labUniq_mk
#print axioms lu_copyLazyL
#print axioms lab_copyL
#print axioms lab_pastL
#print axioms lab_splitL
#print axioms lab_intoL
#print axioms lab_fromL
#print axioms labRun_plainOf
#print axioms labRun_plain
#print axioms liveRun_n5
#print axioms armsL_n5
#print axioms five_tail
#print axioms il_glue
#print axioms kerfSpecL
#print axioms liveRun_n2
#print axioms armsL_n2
#print axioms cons_tail
#print axioms liveRun_consL
#print axioms ten_tail
#print axioms liveRun_n10L
#print axioms armsL_n10L
#print axioms liveRun_plainOfL
#print axioms liveRun_plain_topOfL
#print axioms armsLL_of
#print axioms liveRun_plain_of_specs
