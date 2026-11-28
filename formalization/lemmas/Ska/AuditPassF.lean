import lemmas.Ska.PassMeasureK
import lemmas.Ska.PassMeasureS
import lemmas.Ska.PassMeasureE
import lemmas.Ska.PassMeasureP
import lemmas.Ska.PassMeasureW
import lemmas.Ska.PassMeasureF
import lemmas.Ska.PassMeasureB
import lemmas.Ska.PassStab
import lemmas.Ska.PassStabM
import lemmas.Ska.PassFreeze
import lemmas.Ska.PassMoves
import lemmas.Ska.PassIdents
import lemmas.Ska.PassQuiet
import lemmas.Ska.PassGrow
import lemmas.Ska.PassStack
import lemmas.Ska.PassDepth
import lemmas.Ska.PassClosure

/-! The axioms of the theorems of track F (`Ska/PassMeasure.lean`,
`Ska/PassMeasureK.lean`, `Ska/PassMeasureT.lean`, `Ska/PassMeasureS.lean`, `Ska/PassMeasureA.lean`,
`Ska/PassMeasureI.lean`, `Ska/PassMeasureE.lean`, README Gaps 16), and checks of the measure of
`PassMeasureK.lean` on the runs that broke the first guess of it.  `lake build` prints them; each should be `propext`,
`Classical.choice` and `Quot.sound` at most. -/

open Formalization.SkaModel

#print axioms capeLe_refl
#print axioms capeLe_no_inv
#print axioms capeLe_uni_right
#print axioms uni_denorm_example
#print axioms doubleInt_dunno_old
#print axioms msgAnno_dunno_old
#print axioms mergeProd_dunno_old
#print axioms runDatum_dunno_prod
#print axioms genZ_k
#print axioms app_mono
#print axioms app_idem
#print axioms less_genZ
#print axioms mergeProd_genZ
#print axioms runDatum_prod_step
#print axioms runDatum_less_step
#print axioms less_untidy_example
#print axioms doubleInt_map
#print axioms msgAnno_map
#print axioms runDatum_map_step
#print axioms capeLe_msgCa
#print axioms runDatum_indi_seek
#print axioms runDatum_measure
#print axioms tidy_pull
#print axioms tidy_darn
#print axioms tidy_msgSock
#print axioms annoTP_doubleInt
#print axioms annoTP_msgAnno
#print axioms annoTP_patchProd
#print axioms folStep_tp
#print axioms folTopR_tp
#print axioms runDatum_tp
#print axioms GStepT.tp
#print axioms graphTP_stepsT
#print axioms runDatum_measure_graph
#print axioms msgCa_lex
#print axioms runDatum_seek_lex
#print axioms lack_idem
#print axioms runDatum_indi_lack
#print axioms Ana.bridge_stepQ
#print axioms Ana.run_folTopRQ
#print axioms Ana.allPT
#print axioms Ana.skaCallgraph_tp
#print axioms Ana.run_entry
#print axioms lack_mono
#print axioms normCape_msgCa_right
#print axioms wB_step
#print axioms wB_mono_B
#print axioms indi_merge_step
#print axioms mergeProd_old_void
#print axioms runW_runDatum
#print axioms runDatum_entry_step
#print axioms entry_finite
#print axioms Ana.run_entry_step

open Formalization.Nock

/- The six runs where `less-code` went from `[[& &] |]` to `[& |]` over the
same nouns: the weight rises. -/
#guard kS (Sock.mk (Cape.cell (Cape.cell Cape.yes Cape.yes) Cape.no) (C (C (A 1) (A 2)) (A 0))) <
  kS (Sock.mk (Cape.cell Cape.yes Cape.no) (C (C (A 1) (A 2)) (A 0)))

/- The 51 map-only runs with a product that knows a cell: provenance lost
under a `|` leaf (`1` to `[2 0]`, `[2 [6 7]]` to `[2 [0 7]]`) lowers `mapL`;
the map spelled out along the cells (`1` to `[2 [6 7]]`) keeps `mapL` and
lowers `mapA`. -/
#guard mapL (Cape.cell Cape.yes Cape.no) (C (A 2) (A 0)) < mapL (Cape.cell Cape.yes Cape.no) (A 1)
#guard mapL (Cape.cell Cape.yes (Cape.cell Cape.no Cape.yes)) (C (A 2) (C (A 0) (A 7))) <
  mapL (Cape.cell Cape.yes (Cape.cell Cape.no Cape.yes)) (C (A 2) (C (A 6) (A 7)))
#guard mapL (Cape.cell Cape.yes (Cape.cell Cape.yes Cape.yes)) (C (A 2) (C (A 6) (A 7))) =
  mapL (Cape.cell Cape.yes (Cape.cell Cape.yes Cape.yes)) (A 1)
#guard mapA (Cape.cell Cape.yes (Cape.cell Cape.yes Cape.yes)) (C (A 2) (C (A 6) (A 7))) <
  mapA (Cape.cell Cape.yes (Cape.cell Cape.yes Cape.yes)) (A 1)

/- And `+double-int` makes that last move itself: the same product with the
maps `[2 [6 7]]` (new) and `1` (old) keeps the product and spells the map
out. -/
#guard
  let T := Sock.mk (Cape.cell Cape.yes (Cape.cell Cape.yes Cape.yes)) (C (A 5) (C (A 6) (A 7)))
  doubleInt ⟨T, C (A 2) (C (A 6) (A 7))⟩ ⟨T, A 1⟩ == ⟨T, C (A 2) (C (A 6) (A 7))⟩

-- the pass loop (`Ska/PassMeasureN.lean`, `Ska/PassMeasureP.lean`)
#print axioms Ana.allN
#print axioms ev_const
#print axioms fam_finite
#print axioms runDatum_changed
#print axioms Ana.memberLoop_le
#print axioms Ana.passLoop_of_on
#print axioms Ana.passOn_inv
#print axioms Ana.passOn_wf

-- the stack invariant (`Ska/PassMeasureW.lean`)
#print axioms normCape_distribute
#print axioms folR_ni
#print axioms msgSock_ne_void
#print axioms Ana.cull_winv
#print axioms Ana.allPW
#print axioms Ana.run_winv
#print axioms Ana.passOn_wf_W
#print axioms Ana.skaCallgraph_w

-- the fuel of the pass loop (`Ska/PassMeasureF.lean`)
#print axioms Ana.acc_of_no_chain
#print axioms Ana.passOn_mono
#print axioms Ana.passNext_acc
#print axioms Ana.passLoop_returns

-- the bound on `next` restated: finitely many pushes per chain (`Ska/PassMeasureB.lean`)
#print axioms Ana.finPushes_of_bound
#print axioms Ana.passOn_wf_fin
#print axioms Ana.passNext_acc_fin
#print axioms Ana.passLoop_returns_fin

-- what holds whatever the measure, and the fuel of `+sweep` and `+cull` (`Ska/PassStab.lean`)
#print axioms Ana.valE_run_ext
#print axioms Ana.memberLoop_old
#print axioms Ana.passOn_old
#print axioms Ana.chain_root_mem
#print axioms Ana.chain_present_const
#print axioms Ana.chain_root_const
#print axioms Ana.liveLoop_ends
#print axioms Ana.sweepLoop_ends
#print axioms Ana.sweep_ends
#print axioms Ana.cull_ends
-- the candidates (`Ska/PassStabM.lean`)
#print axioms Ana.svLt_of_olt
#print axioms Ana.stabLt_of_A
-- the freezing argument (`Ska/PassFreeze.lean`)
#print axioms Ana.memberLoop_clean
#print axioms Ana.passOn_dirty
#print axioms Ana.cull_keeps_kid
#print axioms Ana.cull_reach
-- C on the model (`Ska/PassMoves.lean`)
#print axioms Ana.sweep_nodup
#print axioms Ana.resolve_new
#print axioms Ana.run_new
#print axioms Ana.memberLoop_new
-- (i) from finite branching, Kruskal and König (`Ska/PassIdents.lean`)
#print axioms Ana.konig
#print axioms Ana.finIdents_of_tree
#print axioms Ana.noPath_of_kruskal
#print axioms Ana.finIdents_of_kruskal
#print axioms Ana.pstart_mem
#print axioms Ana.passLoop_of_quiet
#print axioms Ana.passQuiet_step
#print axioms Ana.passQuiet_inv
#print axioms Ana.fam_finite_q
#print axioms Ana.passMixed_wf
#print axioms Ana.passLoop_returns_q
#print axioms Ana.memberLoop_returns
#print axioms Ana.passStep_parts
#print axioms Ana.passLoop_returns_runs
#print axioms Ana.passGoOn_next
#print axioms Ana.finPushesQ_of_grow
#print axioms Ana.cull_gg
#print axioms Ana.pop_gg
#print axioms Ana.allG
#print axioms Ana.passGoOn_grow
#print axioms Ana.passLoop_returns_g
#print axioms Ana.finIdentsG_of_tree
#print axioms Ana.finIdentsG_of_kruskal
#print axioms Ana.passLoop_returns_k
#print axioms Ana.recLoop_none
#print axioms Ana.recursiveCall_none
#print axioms Ana.resolveStep_new
#print axioms Ana.push_guard
#print axioms Ana.noStackSeq_of_kruskal
#print axioms Ana.heSock_of_btEmb
#print axioms Ana.btEmb_of_map
#print axioms Ana.noStackSeq_heSock
#print axioms Ana.stkGood_sub
#print axioms Ana.stkGood_push
#print axioms Ana.noGoodChain
#print axioms Ana.goodUp_acc
#print axioms Ana.stack_fin
#print axioms Ana.passChain_stack_fin
#print axioms Ana.finIdentsG_of_width
#print axioms Ana.passLoop_returns_w
#print axioms Ana.allS
#print axioms Ana.chainStk_of
#print axioms Ana.passLoop_returns_ws
#print axioms Ana.mem_nounsUpTo
#print axioms Ana.okId_of_good
#print axioms Ana.safV_bound
#print axioms Ana.callStep_saf
#print axioms Ana.folStep_saf
#print axioms Ana.folLoop_saf
#print axioms Ana.sockG_knit
#print axioms Ana.sockG_pull
#print axioms Ana.sockG_darn
#print axioms Ana.formG_of
#print axioms Ana.formG_op8
#print axioms Ana.formG_op9
#print axioms Ana.formG_bare
#print axioms Ana.formG_memo
#print axioms Ana.formG_op11c
#print axioms Ana.formG_two_slot
