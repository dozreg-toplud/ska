import lemmas.Ska.CompFinal
import lemmas.Ska.CompLazyFinal
import lemmas.Ska.CompSix
import lemmas.Ska.CompFinishF
import lemmas.Ska.CompCopyFresh
import lemmas.Ska.CompNestFinalP
import lemmas.Ska.CompSixNext
import lemmas.Ska.CompSixNextCond
import lemmas.Ska.CompSixNextOK
import lemmas.Ska.CompSevenN
import lemmas.Ska.CompFragM
import lemmas.Ska.CompFragX
import lemmas.Ska.CompUnproxy
import lemmas.Ska.CompUnproxyEntry
import lemmas.Ska.CompUnproxyRegs
import lemmas.Ska.CompUnproxyFill
import lemmas.Ska.CompUnproxyTop
import lemmas.Ska.CompUnproxyBelow
import lemmas.Ska.CompBelowX
import lemmas.Ska.CompEntryGoal
import lemmas.Ska.CompLazyGoal
import lemmas.Ska.CompFromRun
import lemmas.Ska.CompEntryRun
import lemmas.Ska.CompSevenOne
import lemmas.Ska.ExecPath
import lemmas.Ska.CompFootRun
import lemmas.Ska.CompFrame
import lemmas.Ska.CompFootCons
import lemmas.Ska.CompFootTen
import lemmas.Ska.CompFootX
import lemmas.Ska.CompLeafKeep
import lemmas.Ska.CompLeafRel
import lemmas.Ska.CompRelSix
import lemmas.Ska.CompRelCopy
import lemmas.Ska.CompRelBinary
import lemmas.Ska.CompRelUnary
import lemmas.Ska.CompRelCons
import lemmas.Ska.CompRelTen
import lemmas.Ska.CompRelX
import lemmas.Ska.CompEntryRel
import lemmas.Ska.CompWalkU
import lemmas.Ska.CompCollapseGate
import lemmas.Ska.CompCollapseRun
import lemmas.Ska.CompCollapsePre
import lemmas.Ska.CompCollapseThree
import lemmas.Ska.CompAboveRun
import lemmas.Ska.CompAboveX
import lemmas.Ska.CompSevenSame
import lemmas.Ska.CompThreeNone
import lemmas.Ska.CompFragU
import lemmas.Ska.CompConsNV
import lemmas.Ska.CompConsV
import lemmas.Ska.CompSectSkip
import lemmas.Ska.CompTagKeep
import lemmas.Ska.CompDropKeep
import lemmas.Ska.CompTagX
import lemmas.Ska.CompTagU
import lemmas.Ska.CompSixNextV
import lemmas.Ska.CompFragUJGen
import lemmas.Ska.CompSevenV
import lemmas.Ska.CompFiveV
import lemmas.Ska.CompFourV
import lemmas.Ska.CompTenV
import lemmas.Ska.CompFragUJ
import lemmas.Ska.CompRunLCEq
import lemmas.Ska.CompCallSem
import lemmas.Ska.CompCallStep
import lemmas.Ska.CompWholeTop
import lemmas.Ska.CompHypOf
import lemmas.Ska.CompIndirect
import lemmas.Ska.CompIndirectFwd
import lemmas.Ska.CompIndirectBwd
import lemmas.Ska.CompIndirectWrap
import lemmas.Ska.CompIndirectGen
import lemmas.Ska.CompIndirectWrapTop
import lemmas.Ska.CompHypOfCall
import lemmas.Ska.CompIndirectNext
import lemmas.Ska.CompIndirectOut
import lemmas.Ska.CompConsCallTop
import lemmas.Ska.CompIndirectOutB
import lemmas.Ska.CompConsCallB
import lemmas.Ska.CompConsCallWrap
import lemmas.Ska.CompHypOfCons
import lemmas.Ska.CompConsCallTopB
import lemmas.Ska.CompHypOfUOKC
import lemmas.Ska.CompRunOKLCSeven
import lemmas.Ska.CompCallC
import lemmas.Ska.CompHypOfFragD
import lemmas.Ska.CompHypOfFragF
import lemmas.Ska.CompNCInd
import lemmas.Ska.CompNCExamples
import lemmas.Ska.CompRunOKLB
import lemmas.Ska.CompSimBodyLift
import lemmas.Ska.CompLBDone
import lemmas.Ska.CompLBFour
import lemmas.Ska.CompNCBond
import lemmas.Ska.CompFrontS
import lemmas.Ska.CompFlatCopy
import lemmas.Ska.CompPairLS
import lemmas.Ska.CompConsLS
import lemmas.Ska.CompConsLSRun
import lemmas.Ska.CompPastLS
import lemmas.Ska.CompConsLSCall
import lemmas.Ska.CompIndirectLS
import lemmas.Ska.CompCallTreeTop
import lemmas.Ska.CompSevenLS
import lemmas.Ska.CompFourLS
import lemmas.Ska.CompConsLSF
import lemmas.Ska.CompFourTop

/-!
# Axioms of the theorems about the model of `+comp`

Each should depend on `propext`, `Classical.choice` and `Quot.sound` only.
-/

open Formalization.SkaModel.Comp

#print axioms run_ok
#print axioms run_n0_ok
#print axioms run_n1_done_ok
#print axioms run_n1_pick_ok
#print axioms run_n1_next_ok
#print axioms run_n7_ok
#print axioms run_n4_done_ok
#print axioms run_n4_pick_ok
#print axioms run_n3_pick_ok
#print axioms unary_ok
#print axioms fromSure_spec
#print axioms sureRequireLook_spec
#print axioms medeLoop_spec
#print axioms finish_bellContract
#print axioms finish_compDone
#print axioms bellContract_of_compDoneOn
#print axioms toStraight_entry
#print axioms sim_block
#print axioms execPole_ren
#print axioms renameBlocks_spec
#print axioms holds_of_split
#print axioms needOrdAllocRegs_spec
#print axioms capeAxes_of_fits
#print axioms run_down
#print axioms runDown
#print axioms kernBoth_spec
#print axioms kernLoop_spec
#print axioms sureLoop_spec
#print axioms coerceSpec
#print axioms finish_compDone'
#print axioms finish_bellContract'
#print axioms flatten_needOrdAllocRegs
#print axioms isRun_needOrdAllocRegs
#print axioms doneBlocks_ok
#print axioms run_n3_done_ok
#print axioms collapse_ok
#print axioms run_n4_next_ok
#print axioms forl_ok
#print axioms runOK_n3_of_none
#print axioms run_n3_next_ok
#print axioms run_clean
#print axioms clean_copyNeed
#print axioms copyNeed_spec
#print axioms copy_ok
#print axioms binary_ok
#print axioms run_n5_ok
#print axioms splitLok_looks
#print axioms must_spec
#print axioms splitNeed_spec
#print axioms split_ok
#print axioms cons_next_ok
#print axioms run_cons_ok
#print axioms gep_some
#print axioms gep_none
#print axioms slot_edit_off
#print axioms intoLok_looks
#print axioms intoLoop_rec
#print axioms intoRec_ok
#print axioms intoNeed_rec
#print axioms into_ok
#print axioms clean_into
#print axioms into_down
#print axioms run_n10_down
#print axioms run_n10_ok
#print axioms past_some
#print axioms hinted_pure
#print axioms past_pure
#print axioms n10_next_ok
#print axioms Lazy.toNoun_ofSure
#print axioms Lazy.noneEquivalentL_ofSure
#print axioms Lazy.lazyBig_ofSure
#print axioms Lazy.softLess_noSoft
#print axioms Lazy.pastFork_pure
#print axioms Lazy.walkLazy_ofSure
#print axioms Lazy.fromL_ofSure
#print axioms Lazy.splitLoop_ofSure
#print axioms Lazy.intoLoopL_ofSure
#print axioms Lazy.copyLazyL_ofSure
#print axioms simpleNextL_toL
#print axioms splitL_toL
#print axioms intoL_toL
#print axioms copyL_toL
#print axioms pastL_pure
#print axioms medeL_toL
#print axioms collapseLazyAtomL_toL
#print axioms runL_toL
#print axioms frag_pure_noSix
#print axioms runL_ok
#print axioms coerceLazyL_ofSure
#print axioms finishL_eq
#print axioms finishL_bellContract
#print axioms keep_mono
#print axioms runL_six_done
#print axioms finishL_six_parts
#print axioms finishL_six_compDone
#print axioms finishL_six_bellContract
#print axioms finishL_bellContract6
#print axioms six_crash_iff
#print axioms six_example
#print axioms toStraightF_eq
#print axioms kc_run
#print axioms kc_coerceLazyL
#print axioms finishLF_eq
#print axioms runL_cond_frag6
#print axioms finishLF_bellContract6
#print axioms six_crash_iffF
#print axioms get_index_none
#print axioms seen_false
#print axioms mergeForks_fresh
#print axioms mergeBonds_fresh
#print axioms copyLazyL_apart
#print axioms mapBlocks_stateless
#print axioms toStraightF_run
#print axioms coerceLazyL_flat
#print axioms coerceSpecK
#print axioms coerceLazyL_spec
#print axioms lazySizeGo_eq
#print axioms lazyBig_entries
#print axioms runL_six_doneL
#print axioms sixBody_apart
#print axioms copyL_six_apart
#print axioms runP_ok
#print axioms finishLF_compDoneP
#print axioms finishLF_bellContractP
#print axioms crash_iffP
#print axioms finishLF_bellContract6'
#print axioms runL_n6_next
#print axioms sixNextSimple_apart
#print axioms sixNextL_ofSure
#print axioms keys_difM_self
#print axioms sect_apart
#print axioms sect_cond
#print axioms kc_forkSure
#print axioms kc_copyL
#print axioms sixNextSimple_cond
#print axioms forkNeedGo_spec
#print axioms evalPassLoop_copy
#print axioms forkSure_spec
#print axioms goJ_fork
#print axioms sectThread_same
#print axioms runOKN_frag
#print axioms sect_spec
#print axioms lazyBlkN
#print axioms sixNext_okN
#print axioms runN_ok
#print axioms GrowU.trans
#print axioms Grow.toU
#print axioms GrowU.up
#print axioms downRk_of_growU
#print axioms downRk_gen0
#print axioms growU_forkSure
#print axioms finishLF_compDoneR
#print axioms finishLF_bellContractR
#print axioms crash_iffR
#print axioms runOKP_n7
#print axioms runT_ok
#print axioms finishLF_bellContractT
#print axioms crash_iffT
#print axioms unaryP_ok
#print axioms runOKP_n4
#print axioms runOKP_n3
#print axioms sixP_ok
#print axioms unaryN_ok
#print axioms runOKN_n4
#print axioms runOKN_n3
#print axioms runOKN_n7
#print axioms runM_ok
#print axioms finishLF_bellContractM
#print axioms crash_iffM
#print axioms unaryG_ok
#print axioms runOKP_n4p
#print axioms runOKP_n3p
#print axioms runOKP_n7g
#print axioms fragM_pure
#print axioms fragM_of_fragT
#print axioms copyL_apart_some
#print axioms RunOKG.toN
#print axioms RunOKG.toP
#print axioms binaryN_ok
#print axioms runOKN_cons
#print axioms runOKP_consD
#print axioms runOKP_consP
#print axioms clean_copyL
#print axioms runX_clean
#print axioms runX_ok
#print axioms fragX_of_fragM
#print axioms finishLF_bellContractX
#print axioms crash_iffX
#print axioms runL_n5_toL
#print axioms n5Pre_ok
#print axioms runOKG_n5
#print axioms runL_n10_body
#print axioms n10N_body
#print axioms runOKN_n10
#print axioms runOKP_n10D
#print axioms runOKP_n10P
#print axioms clean_n10Body
#print axioms fromSure_fits
#print axioms fillSem_from
#print axioms fromL_ent
#print axioms RunOKP.toG
#print axioms RunOKN.toG
#print axioms runOKG_from
#print axioms runL_seven_from
#print axioms runOKE_n0
#print axioms runOKG_sevenE
#print axioms runOKG_from'
#print axioms walkLazy_ok
#print axioms medeGate_ok
#print axioms runOKE_n1
#print axioms runOKP_seven1
#print axioms finishLF_bellContract71
#print axioms crash_iff71
#print axioms Formalization.SkaModel.Path.step_run
#print axioms Formalization.SkaModel.Path.run_iff_path
#print axioms Formalization.SkaModel.Path.step_det
#print axioms Formalization.SkaModel.Path.execEntry_iff_path
#print axioms Formalization.SkaModel.Path.run_poison
#print axioms Formalization.SkaModel.Path.steps_reads
#print axioms Formalization.SkaModel.Path.guarded_reads
#print axioms Formalization.SkaModel.Path.steps_det
#print axioms unproxyBlob_empty
#print axioms proxy_condFresh
#print axioms CondFresh.trans
#print axioms unproxy_condFresh
#print axioms agreeU_empty
#print axioms rankDown_start
#print axioms chase_ren
#print axioms chaseFin_ren
#print axioms keepBlock_ren
#print axioms renameBlocks_ren
#print axioms proxRen_eq
#print axioms toStraightF_entryU
#print axioms FillSem.pair
#print axioms renPole_fix
#print axioms unproxy_ops
#print axioms kernBoth_regs
#print axioms kernLoop_regs
#print axioms sureLoop_regs
#print axioms Front.uniq
#print axioms coerceLazy_regs
#print axioms coerceList_regs
#print axioms coerceLazyL_regs
#print axioms get_mapVals
#print axioms RunOKP.toU
#print axioms finishLF_compDoneU
#print axioms finishLF_bellContractU
#print axioms finishLF_bellContractR_U
#print axioms finishLF_bellContractXU
#print axioms finishLF_bellContract71U
#print axioms agreeU_transfer
#print axioms RunOKU.semW
#print axioms RunOKU.semF
#print axioms BelowIn.ext
#print axioms BelowIn.front
#print axioms belowIn_addOps
#print axioms belowIn_proxy
#print axioms belowIn_emit
#print axioms run_keeps
#print axioms run_below
#print axioms keepX_sixP
#print axioms keepX_sixN
#print axioms keepX_cons
#print axioms runX_keeps
#print axioms runX_below
#print axioms runX_okU
#print axioms WroteIn.trans
#print axioms wr_splitNeed
#print axioms wr_medeLoop
#print axioms wr_mede
#print axioms wr_forl
#print axioms wr_copyNeed
#print axioms wr_collapseLazyAtom
#print axioms foot_tail
#print axioms foot_n0
#print axioms foot_n1
#print axioms foot_n7
#print axioms foot_n4
#print axioms foot_n3
#print axioms run_foot_of
#print axioms evalPass_frame
#print axioms execPole_frame
#print axioms step_frame
#print axioms steps_frame
#print axioms steps_frame_all
#print axioms run_frame
#print axioms execEntry_frame
#print axioms steps_reads_frame
#print axioms copyNeed_dist
#print axioms wr_splitNeedS
#print axioms foot_copyTail
#print axioms foot_cons
#print axioms foot_n5
#print axioms intoRec_wr
#print axioms intoNeed_wr
#print axioms into_wr
#print axioms foot_n10
#print axioms run_foot
#print axioms footR_toL
#print axioms FootR.pre
#print axioms footX_frag
#print axioms footX_seven
#print axioms footX_sevenFrom
#print axioms footX_tail
#print axioms footX_four
#print axioms footX_three
#print axioms foot_copy
#print axioms footX_binary
#print axioms footX_consBody
#print axioms footX_cons
#print axioms footX_five
#print axioms footX_ten
#print axioms runX_foot_of
#print axioms wroteIn_sixGenL
#print axioms footX_sixP
#print axioms wroteIn_forkSure
#print axioms wroteIn_sameBlocks
#print axioms footX_sixN
#print axioms runX_foot
#print axioms clear_gen0
#print axioms Clear.grow
#print axioms Clear.growU
#print axioms clear_new
#print axioms clear_newU
#print axioms steps_transfer
#print axioms steps_exit
#print axioms get_putFrom
#print axioms regionProg_in
#print axioms regionProg_z
#print axioms regionProg_out
#print axioms run_jump
#print axioms execBlob_args
#print axioms leaf_exit
#print axioms holdsN_pointwise
#print axioms leaf_sem
#print axioms leaf_keep
#print axioms runOKP_frag_semR
#print axioms runOKN_frag_semR
#print axioms leaf_keepK
#print axioms SemPR.strict
#print axioms SemGR.strict
#print axioms sixP_semR
#print axioms runP_semR
#print axioms lazyBlkNR
#print axioms sixNext_semR
#print axioms runN_semR
#print axioms holdsN_some
#print axioms execOps_don_zero
#print axioms runs_read
#print axioms copy_okR
#print axioms binaryN_semR
#print axioms n5Pre_okK
#print axioms SemGR.toP
#print axioms runOKG_n5_semR
#print axioms split_okK
#print axioms consN_semR
#print axioms unaryN_semR
#print axioms runOKN_n7_semR
#print axioms runOKP_n7g_semR
#print axioms unaryG_semR
#print axioms runOKN_n4_semR
#print axioms semN_n3_of_none
#print axioms runOKN_n3_semR
#print axioms runOKP_n4_semR
#print axioms runOKP_n3_semR
#print axioms runOKP_n4p_semR
#print axioms runOKP_n3p_semR
#print axioms consN_semRK
#print axioms runOKP_consD_semR
#print axioms runOKP_consP_semR
#print axioms semGR_from
#print axioms semPR_from
#print axioms into_okK
#print axioms n10N_semR
#print axioms runOKN_n10_semR
#print axioms runOKP_n10D_semR
#print axioms runOKP_n10P_semR
#print axioms runX_semR
#print axioms runX_semR_gen0
#print axioms semE_n0
#print axioms FrontSemR.strict
#print axioms frontK_n0
#print axioms runOKE_n1K
#print axioms frontER_n0
#print axioms runOKE_n1R
#print axioms semGR_sevenE
#print axioms semPR_seven1
#print axioms walkLazy_okC
#print axioms proxy_proxyFor
#print axioms walkLazy_okP
#print axioms walkLazy_okD
#print axioms collapseGate_ok
#print axioms walkLazy_okColl
#print axioms collP_fillSem
#print axioms collapseL_this
#print axioms collapsePre_spec
#print axioms keeps_walkColl
#print axioms collRun_n4
#print axioms runOKU_seven4
#print axioms aboveX_n0
#print axioms finishLF_bellContract74U
#print axioms aboveX_n1
#print axioms aboveX_n4
#print axioms finishLF_bellContract_target
#print axioms forl_above
#print axioms aboveX_n01
#print axioms aboveX_n3
#print axioms collRun_n3
#print axioms runOKU_seven3
#print axioms finishLF_bellContract73U
#print axioms runL_n01_done_ne
#print axioms finishLF_bellContract_three
#print axioms fromSure_lok_ne0
#print axioms splitLok_ne0
#print axioms run_keepsA
#print axioms run_above
#print axioms run_above_le
#print axioms runX_keepsA
#print axioms runX_above
#print axioms runX_above_le
#print axioms aboveX_of_fragX
#print axioms finishLF_bellContract74X
#print axioms finishLF_bellContract73X
#print axioms runL_n7_assoc
#print axioms runL_n7_n4
#print axioms runL_n7_n3
#print axioms sameL_assoc
#print axioms sameL_n7_n4
#print axioms sameL_n7_n3
#print axioms SameL.n7
#print axioms SameL.n4
#print axioms SameL.n3
#print axioms RunOKU.congr
#print axioms finishLF_bellContractSame
#print axioms finishLF_bellContract74S
#print axioms finishLF_bellContract73S
#print axioms finishLF_bellContract_slotTarget
#print axioms pureEval_const_of_noneEq
#print axioms runOKU_seven3F
#print axioms finishLF_bellContract73F
#print axioms finishLF_bellContract_threeNone
#print axioms RunOKV.toU
#print axioms RunOKP.toV
#print axioms okV_fragX
#print axioms runOKV_seven4
#print axioms sixP_okV
#print axioms runU_ok
#print axioms finishLF_bellContractFU
#print axioms finishLF_bellContract_sixProxy
#print axioms runOKNV_seven4
#print axioms runOKNV_seven4_le
#print axioms RunOKN.toNV
#print axioms okNV_fragX
#print axioms okNV_seven4
#print axioms AgreeU.part
#print axioms binaryNV_ok
#print axioms consNV_body
#print axioms okNV_cons
#print axioms runOKV_seven4P
#print axioms fragU_pure
#print axioms clean_n4L
#print axioms cleanA_seven4
#print axioms unaryGV_ok
#print axioms runOKV_consD
#print axioms RunOKGV.toNV
#print axioms RunOKGV.toV
#print axioms binaryGV_ok
#print axioms runOKV_consP
#print axioms sectStep_skip
#print axioms foldlM_sectStep_skip
#print axioms sectThread_skip
#print axioms sect_specV
#print axioms kt_run
#print axioms kt_copyL
#print axioms kd_run
#print axioms runX_tags
#print axioms tag_copyL
#print axioms tagX_sixN
#print axioms tagX_sixP
#print axioms collapseL_tag
#print axioms condTag_fragX
#print axioms condTag_seven4
#print axioms sect_h0
#print axioms sect_h1
#print axioms unproxyBlob_fix
#print axioms lazyBlkNV
#print axioms sixNext_okNV
#print axioms cleanA_six
#print axioms cleanA_cons
#print axioms sixNext_tagNV
#print axioms sixP_tagV
#print axioms cons_tagNV
#print axioms cons_tagP
#print axioms uok_x
#print axioms uok_seven4
#print axioms uok_six
#print axioms uok_cons
#print axioms runU_uok
#print axioms runU_okNV
#print axioms finishLF_bellContract_consProxy
#print axioms runOKV_n7g
#print axioms runOKNV_n7
#print axioms seven_tagV
#print axioms seven_tagNV
#print axioms cleanA_seven
#print axioms uok_seven
#print axioms finishLF_bellContract_sixNextProxy
#print axioms runOKGV_n5
#print axioms five_tagG
#print axioms cleanA_five
#print axioms uok_five
#print axioms fix_of_keeps
#print axioms unaryNV_ok
#print axioms runOKV_n4D
#print axioms runOKV_n4P
#print axioms runOKNV_n4
#print axioms four_tagNV
#print axioms four_tagP
#print axioms cleanA_four
#print axioms runOKV_n3D
#print axioms runOKV_n3P
#print axioms runOKNV_n3_of_none
#print axioms runOKNV_n3
#print axioms three_tagNV
#print axioms three_tagP
#print axioms cleanA_three
#print axioms uok_four
#print axioms uok_three
#print axioms runU_uok
#print axioms finishLF_bellContractFU
#print axioms finishLF_bellContract_fourProxy
#print axioms n10NV_body
#print axioms n10NV_tagBody
#print axioms runOKNV_n10
#print axioms ten_tagNV
#print axioms runOKV_n10D
#print axioms ten_tagD
#print axioms runOKV_n10P
#print axioms ten_tagP
#print axioms cleanA_ten
#print axioms uok_ten
#print axioms finishLF_bellContract_tenProxy
#print axioms hinted_noCall
#print axioms sixNextLC_eq
#print axioms runLC_eq
#print axioms finishLFC_eq
#print axioms goJ_cal
#print axioms callBlockSem
#print axioms goJ_jmp
#print axioms goJ_nok
#print axioms allocSplit
#print axioms argsFor_of_alloc
#print axioms holds_mapM
#print axioms frames_mono
#print axioms oracle_call_alloc
#print axioms callStep_fwd
#print axioms tailStep_fwd
#print axioms toneRel_toneOf
#print axioms goalSemC_of_goalSem
#print axioms finishLUC_eq
#print axioms kernLoop_head
#print axioms kernLoop_lt
#print axioms kernLoop_ren
#print axioms kernP_mono
#print axioms kernGate_ok
#print axioms walkLazy_okDI
#print axioms kern_spec
#print axioms upBelow_of_growU
#print axioms finishLU_compDone
#print axioms toStraightF_nargs
#print axioms finishLU_nargs
#print axioms finishLU_bellContractV
#print axioms finishLU_bellContractFU
#print axioms finishLU_fullCode
#print axioms Formalization.SkaModel.PokeM.toStraightF_this
#print axioms Formalization.SkaModel.PokeM.finishLUC_this
#print axioms Formalization.SkaModel.PokeM.bellContract_of_keeps
#print axioms Formalization.SkaModel.PokeM.CompRest.keeps
#print axioms Formalization.SkaModel.PokeM.contract_of_pieces
#print axioms Formalization.SkaModel.PokeM.compHyp_of_pieces
#print axioms Formalization.SkaModel.PokeM.rawMono_fragU
#print axioms Formalization.SkaModel.PokeM.rawNary_fragU
#print axioms Formalization.SkaModel.PokeM.compHyp_of_frag
#print axioms runLC_n2_none
#print axioms indirect_mid
#print axioms finishTop_gen
#print axioms indirect_prefix
#print axioms minkF_n2_pure
#print axioms indirect_sem
#print axioms indirectTop_fwd
#print axioms mink_n2_of
#print axioms mink_n2_crash1
#print axioms mink_n2_crash2
#print axioms indirectTop_gen
#print axioms indirect_semB
#print axioms indirect_necB
#print axioms indirectTop_bwd
#print axioms indirectTop_contract
#print axioms minkN2_indirect
#print axioms mink_call1
#print axioms mink_memo_of
#print axioms minkN2_memo
#print axioms mink_six_of
#print axioms minkN2_six
#print axioms minkN2_of_annot
#print axioms indirect_semM
#print axioms indirect_semBM
#print axioms indirect_necM
#print axioms indirect_necBM
#print axioms indirectTop_fwdM
#print axioms indirectTop_bwdM
#print axioms indirectTop_contractM
#print axioms indirectTop_contractA
#print axioms Formalization.SkaModel.PokeM.rawMono_or
#print axioms Formalization.SkaModel.PokeM.rawMono_indU
#print axioms Formalization.SkaModel.PokeM.rawMono_fragUC
#print axioms Formalization.SkaModel.PokeM.compHyp_of_fragC
#print axioms indirect_semN
#print axioms returnsC_step
#print axioms goesC_step
#print axioms goalSemCM_step
#print axioms goalSemCM_ret
#print axioms indirect_semG
#print axioms runs_keep
#print axioms kernLoop_kop
#print axioms outGoal_next_of_fill
#print axioms kerf_ofSure
#print axioms outGoal_kerf
#print axioms indirect_prefixN
#print axioms indirect_runN
#print axioms outGoal_done
#print axioms outGoal_pick
#print axioms indirect_runS
#print axioms indirect_runD
#print axioms indirect_runP
#print axioms pastL_hinted
#print axioms tailNV_past
#print axioms minkF_consC
#print axioms consNC_ok
#print axioms indirect_clean
#print axioms consCH_runN
#print axioms finishTop_genA
#print axioms returnsC_done
#print axioms finishLUC_fwdC
#print axioms consCH_runD
#print axioms consCHTop_fwd
#print axioms consCHTop_fwdA
#print axioms consCH_example
#print axioms indirect_semGB
#print axioms indirect_runSB
#print axioms indirect_runNB
#print axioms indirect_runDB
#print axioms indirect_runPB
#print axioms finishLUC_bwdC
#print axioms indirectTop_bwdC
#print axioms indirectTop_bwd'
#print axioms mink_consC_bwd
#print axioms mink_consC_crash
#print axioms consNC_bwd
#print axioms consCH_runNB
#print axioms consCH_runDB
#print axioms consCHTop_bwd
#print axioms consCHTop_contract
#print axioms consCHTop_contractA
#print axioms consCH_exampleC
#print axioms wrapRel_six
#print axioms wrapRel_memo
#print axioms contract_wrap
#print axioms consCH_contractP
#print axioms consCH_contract_of_annot
#print axioms Formalization.SkaModel.PokeM.rawMono_consU
#print axioms Formalization.SkaModel.PokeM.rawMono_fragUCC
#print axioms Formalization.SkaModel.PokeM.compHyp_of_fragCC
#print axioms uokc_of_uok
#print axioms okc_indirect
#print axioms uokc_indirect
#print axioms UOKC.wrap
#print axioms finishLUC_contractG
#print axioms consNC_okF
#print axioms necC_consH
#print axioms consGH_runN
#print axioms consGH_runD
#print axioms uokc_consH
#print axioms uokc_of_fragC
#print axioms uokc_of_fragUC
#print axioms finishLUC_contractUC
#print axioms uokc_example2
#print axioms Formalization.SkaModel.PokeM.rawMono_fragUCG
#print axioms Formalization.SkaModel.PokeM.fragUCCM_sub
#print axioms Formalization.SkaModel.PokeM.compHyp_of_fragUCG
#print axioms RunOKL.toNV
#print axioms RunOKNV.toL
#print axioms runOKL_n0
#print axioms runOKL_n0_run
#print axioms runOKL_n4
#print axioms runOKL_n4_none
#print axioms runOKL_seven
#print axioms minkF_consT
#print axioms mink_consT_bwd
#print axioms consNT_ok
#print axioms runOKL_n01
#print axioms bondOK_n0
#print axioms bondOK_n4
#print axioms entNew_indirect
#print axioms consT_runN
#print axioms consT_cleanN
#print axioms consT_runD
#print axioms uokc_consT
#print axioms uokc_consTA
#print axioms consT_example1
#print axioms consT_example4
#print axioms copyL_th
#print axioms entNew_consH
#print axioms entNew_consT
#print axioms uokc_entNew_of_fragC
#print axioms consT_example5
#print axioms RunOKL.toLC
#print axioms RunOKGC.toLC
#print axioms RunOKLC.toGC
#print axioms minkF_sevenC
#print axioms mink_sevenC_bwd
#print axioms frontLC_seven
#print axioms runOKLC_seven
#print axioms TailGC.ofRun
#print axioms tailGC_past
#print axioms totalC_of_minkEq
#print axioms pairLC_ok
#print axioms minkC2_indirect
#print axioms nokStep_fwd
#print axioms nokStep_bwd
#print axioms indirectC_runS
#print axioms indirectC_runN
#print axioms indirectC_runB
#print axioms okc_indirectC
#print axioms uokc_indirectC
#print axioms entNew_indirectC
#print axioms bondOKC_of_bondOK
#print axioms minkF_consG
#print axioms mink_consG_bwd
#print axioms consLC_runN
#print axioms consLC_cleanN
#print axioms consLC_runD
#print axioms uokc_consLC
#print axioms entNew_consLC
#print axioms fragC_fragD
#print axioms uokc_indDA
#print axioms uokc_consDA
#print axioms uokc_entNew_of_fragD
#print axioms finishLUC_contractUD
#print axioms indC_example1
#print axioms indC_example2
#print axioms indC_example3
#print axioms Formalization.SkaModel.PokeM.rawMono_fragUDG
#print axioms Formalization.SkaModel.PokeM.fragUCG_sub
#print axioms Formalization.SkaModel.PokeM.compHyp_of_fragUDG
#print axioms kern_specW
#print axioms kernPW_fill
#print axioms indirectC_inner
#print axioms kerf_specL
#print axioms kerfLC
#print axioms RunOKLC.wrap
#print axioms bondOKC_indirectC
#print axioms bondOKC_indA
#print axioms uokc_consEA
#print axioms uokc_entNew_of_fragE
#print axioms finishLUC_contractUE
#print axioms consCC_example
#print axioms Formalization.SkaModel.PokeM.rawMono_fragUEG
#print axioms Formalization.SkaModel.PokeM.fragUDG_subE
#print axioms Formalization.SkaModel.PokeM.compHyp_of_fragUEG
#print axioms minkC7_seven
#print axioms runOKGC_sevenG
#print axioms noEnt_pure
#print axioms noEnt_sevenC
#print axioms okc_sevenC
#print axioms uokc_sevenC
#print axioms jNew_n0
#print axioms jNew_n1
#print axioms entNew_sevenC
#print axioms minkC7_inline
#print axioms minkC7_eight
#print axioms minkC7_eightAtom
#print axioms minkC7_eightL
#print axioms minkC7_nine
#print axioms UOKC.mono
#print axioms annot_atom
#print axioms annot_slot1_pure
#print axioms uokc_atomPair
#print axioms uokc_sevenM
#print axioms uokc_sevenA
#print axioms entries_copyL
#print axioms noEnt_ind
#print axioms noEnt_of_noEntF
#print axioms jNew_of_jNewQ
#print axioms fragI_hinted
#print axioms uokc_entNew_of_fragI
#print axioms finishLUC_contractUF
#print axioms seven_exampleA
#print axioms seven_exampleB
#print axioms eight_exampleA
#print axioms eight_exampleB
#print axioms nine_exampleA
#print axioms nine_exampleB
#print axioms seven_exampleN
#print axioms seven_exampleT
#print axioms Formalization.SkaModel.PokeM.rawMono_fragUFG
#print axioms Formalization.SkaModel.PokeM.fragUEG_subF
#print axioms Formalization.SkaModel.PokeM.compHyp_of_fragUFG
#print axioms runOKGC_sevenL
#print axioms lokc_n0
#print axioms lokc_indirectC
#print axioms LOKC.wrap
#print axioms lokc_indA
#print axioms okc_sevenL
#print axioms uokc_sevenL
#print axioms entNew_sevenL
#print axioms uokc_sevenLA
#print axioms lokc_n0A
#print axioms sevenL_exampleF
#print axioms sevenL_exampleG
#print axioms runOKLC_sevenM
#print axioms bondOKC_sevenC
#print axioms bondOKC_sevenA
#print axioms lokc_headP
#print axioms bondOKC_headQ
#print axioms uokc_headQ
#print axioms uokc_head7
#print axioms bondOKC_head7
#print axioms consS7_exampleC
#print axioms consS7_exampleH
#print axioms gate_example
#print axioms LOKC.toS
#print axioms LOKCS.toBond
#print axioms LOKCS.wrap
#print axioms NCOK.weak
#print axioms hinted_noDirect
#print axioms lokc_seven_core
#print axioms lokc_sevenC
#print axioms lokcs_sevenC
#print axioms lokcLv_sevenA
#print axioms jNew_sevenC
#print axioms jNew_sevenL
#print axioms runOKL_n00
#print axioms lokc_n00
#print axioms lokc_n0all
#print axioms lokc_indAU
#print axioms entNew_consAny
#print axioms annot_atomLeaf
#print axioms annot_slot1Leaf
#print axioms entNew_consLeaf
#print axioms jump_sevenNA
#print axioms jump_sevenEA
#print axioms hinted_nc
#print axioms fragU_of_nc
#print axioms nc_lv2_shape
#print axioms ncOK
#print axioms uokc_of_nc
#print axioms lokc_of_nc
#print axioms bondOKC_of_nc
#print axioms entNew_of_nc
#print axioms finishLUC_contractNC
#print axioms lokcs_n4X
#print axioms lokcs_n4XA
#print axioms pure_false_of_hinted
#print axioms nc_of_fragB
#print axioms nc_of_fragC
#print axioms nc_of_fragD
#print axioms nc_of_fragE
#print axioms nc_of_fragI
#print axioms Formalization.SkaModel.PokeM.rawMono_NCG
#print axioms Formalization.SkaModel.PokeM.fragUFG_subNC
#print axioms Formalization.SkaModel.PokeM.compHyp_of_NCG
#print axioms nc_c8tTail
#print axioms c8t_example
#print axioms minkC4_four
#print axioms goalSemCM_of_returnsC
#print axioms unaryGC_ok
#print axioms four_runD
#print axioms four_runN
#print axioms runLC_n4_last
#print axioms okc_fourC
#print axioms uokc_fourC
#print axioms uokc_fourA
#print axioms four_example
#print axioms minkC3_three
#print axioms unaryGT_ok
#print axioms wutTone_keep
#print axioms three_runD
#print axioms three_of_none
#print axioms three_runN
#print axioms runLC_n3_last
#print axioms okc_threeC
#print axioms uokc_threeC
#print axioms uokc_threeA
#print axioms three_example
#print axioms AgreeLB.toL
#print axioms AgreeL.toB
#print axioms frontLB_of_frontLC
#print axioms FrontLB.up
#print axioms FrontLB.toLC
#print axioms RunOKLC.toB
#print axioms RunOKLB.up
#print axioms RunOKLB.toLC
#print axioms RunOKLB.wrap
#print axioms SimM.getDrop
#print axioms simM_splitLoop
#print axioms simM_intoLoopL
#print axioms simM_copyLazyL
#print axioms simM_collapseLazyAtomL
#print axioms simM_kern
#print axioms simM_medeL
#print axioms simM_callL
#print axioms simM_runLC
#print axioms SimB.growU
#print axioms RunOKLB.ofSim
#print axioms get_stripBl
#print axioms simB_strip
#print axioms LOKC.toB
#print axioms LOKB.up
#print axioms LOKB.wrap
#print axioms FillSem.conv
#print axioms frontLB_seven
#print axioms frontLB_seven_bunt
#print axioms runOKLB_seven
#print axioms AgreeUB.toU
#print axioms RunOKGC.toB
#print axioms runOKGB_sevenL
#print axioms finishTop_genB
#print axioms finishLUC_contractGB
#print axioms holdsN_atom_mem
#print axioms runOKLB_n4
#print axioms lokb_n4X
#print axioms collLC
#print axioms four_runBond
#print axioms bondOKC_fourC
#print axioms bondOKC_fourA
#print axioms h4c_example
#print axioms FrontS.toLB
#print axioms frontS_false
#print axioms frontS_empty
#print axioms frontS_pair
#print axioms FrontsS.toFront
#print axioms entries_flat
#print axioms splitSure_ok
#print axioms splitBonds_flat
#print axioms SplitBs.spec
#print axioms splitLoop_flat
#print axioms get_index_mem
#print axioms copyLazy_ok
#print axioms mergeBonds_flat
#print axioms MergeBs.spec
#print axioms copyLazyL_flat
#print axioms copyL_flat
#print axioms eq_of_label
#print axioms mem_pairRes_bond
#print axioms goalSemCMD_of_CM
#print axioms goalSemCMD_bad
#print axioms pairLS_ok
#print axioms clean_copyLazy
#print axioms fromBonds_flat
#print axioms fromL_flat
#print axioms lokS_n0
#print axioms splitL_flat
#print axioms copyL_flat'
#print axioms splitAt_of_splitBs
#print axioms lokS_consP_run
#print axioms clean_splitLoop
#print axioms clean_copyLazyL
#print axioms lokS_consP
#print axioms pairLS_core
#print axioms pairLS_sem
#print axioms pairLS_semB
#print axioms pairLS_fronts
#print axioms RunOKLS.past
#print axioms lokS_cons_run
#print axioms lokS_cons
#print axioms lokS_n00
#print axioms JNewL.toS
#print axioms lokS_consS
#print axioms jNewLS_cons
#print axioms nokLB
#print axioms kerfLB
#print axioms lokS_indirect_run
#print axioms lokS_indirect
#print axioms jNewLS_indirect
#print axioms CallTree.kind
#print axioms lokS_callTree
#print axioms RunOKLB.toGB
#print axioms runOKGB_of_next
#print axioms runOKGB_done
#print axioms runLC_done_next
#print axioms lokS_done
#print axioms CallTree.sixCount
#print axioms callTree_done
#print axioms topTree_done
#print axioms finishLUC_contractTopTree
#print axioms finishLUC_bellContractTopTree
#print axioms cc2_contract
#print axioms consInd_contract
#print axioms bc1_contract
#print axioms frontS_seven
#print axioms frontS_seven_bunt
#print axioms frontsS_seven
#print axioms runOKLS_seven
#print axioms lokS_seven
#print axioms jNewLS_seven
#print axioms CallTree7.kind
#print axioms lokS_callTree7
#print axioms done_of_lokS
#print axioms callTree7_done
#print axioms finishLUC_contractCallTree7
#print axioms finishLUC_bellContractCallTree7
#print axioms TopTree.to7
#print axioms sevenIn_contract
#print axioms incLB
#print axioms collLS
#print axioms RunOKLS.unflag
#print axioms LOKS.toF
#print axioms JNewLS.toF
#print axioms lokS_four_run
#print axioms lokS_four
#print axioms jNewLS_four
#print axioms split_none
#print axioms lokS_cons_runF
#print axioms lokS_consF
#print axioms jNewLSF_cons
#print axioms lokS_indirect_runF
#print axioms lokS_indirectF
#print axioms jNewLS_indirectF
#print axioms lokS_sevenF
#print axioms jNewLSF_seven
#print axioms unaryGB_ok
#print axioms four_doneB
#print axioms lokS_doneF
#print axioms done_of_lokSF
#print axioms CallTreeA.annot
#print axioms CallTreeA.kind
#print axioms lokS_callTreeA
#print axioms callTreeA_done
#print axioms finishLUC_contractCallTreeA
#print axioms finishLUC_bellContractCallTreeA
#print axioms CallTree7.toA
#print axioms fourInd_contract
#print axioms fourCons_contract
