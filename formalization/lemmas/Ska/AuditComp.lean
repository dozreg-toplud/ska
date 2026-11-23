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
