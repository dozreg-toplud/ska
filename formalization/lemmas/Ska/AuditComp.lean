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
