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
