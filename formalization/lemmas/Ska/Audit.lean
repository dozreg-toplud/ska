import lemmas.Ska.Statements
import lemmas.Ska.KnowMeets
import lemmas.Ska.LessProvides
import lemmas.Ska.SiteCover
import lemmas.Ska.AnaInv
import lemmas.Ska.StaleWitness
import lemmas.Ska.CapeFacts
import lemmas.Ska.ContractExamples
import lemmas.Ska.BugWitness
import lemmas.Ska.NommSem
import lemmas.Ska.NommAgree
import lemmas.Ska.FolLoopSound
import lemmas.Ska.CallGraph
import lemmas.Ska.Prov
import lemmas.Ska.ProvFacts
import lemmas.Ska.WantMono
import lemmas.Ska.AppPath
import lemmas.Ska.Stat
import lemmas.Ska.AppMask
import lemmas.Ska.FolLoopRel
import lemmas.Ska.Converge
import lemmas.Ska.ConvergeProd
import lemmas.Ska.CompSim
import lemmas.Ska.ConvergeGraph
import lemmas.Ska.CompSimOps
import lemmas.Ska.Bridge
import lemmas.Ska.MemoPoke
import lemmas.Ska.SockNorm
import lemmas.Ska.ConvAna
import lemmas.Ska.PokeConv
import lemmas.Ska.FolNorm
import lemmas.Ska.Bake
import lemmas.Ska.Know
import lemmas.Ska.KnowSound
import lemmas.Ska.BakeGraph
import lemmas.Ska.PokeBake
import lemmas.Ska.PokeModel
import lemmas.Ska.PokeAna
import lemmas.Ska.PokeHalt
import lemmas.Ska.PokeJets
import lemmas.Ska.BakeMeasure
import lemmas.Ska.SitesMeet
import lemmas.Ska.KnowMonoFalse
import lemmas.Ska.SitesMeetNF
import lemmas.Ska.AnaFuel

/-! The axioms of the main theorems of `lemmas/Ska`.  `lake build` prints
them; each should be `propext`, `Classical.choice` and `Quot.sound` at most. -/

open Formalization.SkaModel

#print axioms interp_fwd
#print axioms interp_bwd
#print axioms meek
#print axioms weak
#print axioms converse
#print axioms meek_cell_tag
#print axioms meek_reach
#print axioms weak_reach
#print axioms converse_reach
#print axioms knit_fits
#print axioms pull_fits
#print axioms darn_fits
#print axioms purr_fits_left
#print axioms purr_fits_right
#print axioms huge_sound
#print axioms app_fits
#print axioms all_fits
#print axioms jibeMk_of_fits
#print axioms int_has
#print axioms uni_has
#print axioms patLoop_has
#print axioms lotLoop_has
#print axioms minkF_trace
#print axioms tail_fwd
#print axioms tail_bwd
#print axioms nok_fwd
#print axioms nok_bwd
#print axioms inline_drop
#print axioms default_crash
#print axioms dif_has
#print axioms lack_has
#print axioms bare_loops
#print axioms eval_bare
#print axioms bare_runs
#print axioms EvalA.toEvalH
#print axioms toneRel_mink_self
#print axioms nomm_fwd
#print axioms nomm_bwd
#print axioms nomm_agree
#print axioms doubleInt_fits_left
#print axioms doubleInt_fits_right
#print axioms pull_yes
#print axioms shape_other_crashes
#print axioms Annot.mono
#print axioms folLoop_good
#print axioms folLoop_prod
#print axioms folLoop_annot
#print axioms safeFolFol_inline
#print axioms saf_memo
#print axioms folLoop_agree
#print axioms msgSock_fits_left
#print axioms mergeProd_fits
#print axioms answers_tabOK
#print axioms entry_agree
#print axioms codeOK_of_entries
#print axioms entry_ok_of_run
#print axioms pull_blank_of_none
#print axioms patchProd_sound
#print axioms hit_prod
#print axioms pull_eq_sockAt
#print axioms springAt_slot
#print axioms provO_slot
#print axioms provO_knit
#print axioms provO_doubleInt_left
#print axioms provO_doubleInt_right
#print axioms provO_darn
#print axioms provO_compose
#print axioms distribute_has
#print axioms folLoopF_want_mono
#print axioms fitsOpt_app_part
#print axioms known_formula
#print axioms GenLe.toPosLe
#print axioms GenLe.appFits
#print axioms statOK_slot
#print axioms statOK_knit
#print axioms statOK_doubleInt_left
#print axioms statOK_doubleInt_right
#print axioms statOK_darn
#print axioms statOK_compose
#print axioms statOK_patchProd
#print axioms fitsOpt_app_mask
#print axioms call_sub_fits
#print axioms known_at
#print axioms folLoop_rgood
#print axioms folLoop_wantSound
#print axioms folLoop_relProd
#print axioms app_cape_fits
#print axioms huge_app_fits
#print axioms provO_patchProd
#print axioms msgSock_genLe
#print axioms rtab_of_answers
#print axioms codeOK_of_converged
#print axioms converged_agree
#print axioms prodRel_of_rtab
#print axioms minkF_inv_n2
#print axioms folLoop_rprod
#print axioms folLoop_relProdN
#print axioms prodRelN_of_converged
#print axioms prodRel_of_converged
#print axioms codeOK_at_convergence
#print axioms agree_at_convergence
#print axioms provO_msgAnno_left
#print axioms statOK_msgAnno_left
#print axioms mergeProd_rel
#print axioms merge_no_fixed_point
#print axioms folLoopTop_wf
#print axioms wf_darn
#print axioms wf_msgSock
#print axioms wf_patchProd
#print axioms runDatum_entryM
#print axioms GStep.wf
#print axioms graphWF_steps
#print axioms answersS_wf
#print axioms codeOf_is
#print axioms codeOf_has
#print axioms agree_converged_graph
#print axioms agree_poke
#print axioms compRel_cons_next
#print axioms compRel_done_of_con
#print axioms compRel_n4_done
#print axioms compRel_n3_pick
#print axioms compRel_n5_pick
#print axioms compRel_done_of_pick
#print axioms compRel_n3_done
#print axioms compRel_n5_done
#print axioms nommF_pure
#print axioms nommF_pure_total
#print axioms mink_pure
#print axioms bellContract_of_compDone
#print axioms compDone_of_compRel
#print axioms compRel_done_of_next
#print axioms const_contract
#print axioms slot1_contract
#print axioms bomb_contract
#print axioms Holds.agree
#print axioms GoalRel.transfer
#print axioms compRel_n7
#print axioms compRel_n6
#print axioms folLoopF_folR
#print axioms folR_mono
#print axioms folR_wf
#print axioms folR_rgood
#print axioms folR_rprod
#print axioms ConvergedGraph.toR
#print axioms GStepR.wf
#print axioms agree_converged_graphR
#print axioms agree_pokeR
#print axioms agree_poke_of_fixed
#print axioms Ana.bridge_step
#print axioms Ana.folLoop_goOK
#print axioms Ana.run_folTopR
#print axioms Annot.mono_code
#print axioms agree_converged_graphM
#print axioms memoEntryOK_final
#print axioms memoInv_poke
#print axioms agree_pokeM
#print axioms mergeProd_void
#print axioms Ana.resolveStep_ok
#print axioms Ana.runStep_ok
#print axioms Ana.passStep_ok
#print axioms Ana.analyzeStep_ok
#print axioms Ana.allP
#print axioms Ana.skaCallgraph_steps
#print axioms Ana.run_ok
#print axioms RunEntryR.pop
#print axioms Ana.runEnd_gStepR
#print axioms normCape_con
#print axioms normCape_uni
#print axioms normCape_int
#print axioms normCape_lack
#print axioms normCape_dif
#print axioms normCape_pat
#print axioms normCape_msgCa
#print axioms normSock_knit
#print axioms normSock_pull
#print axioms normSock_darn
#print axioms normSock_purr
#print axioms normSock_app
#print axioms normSock_doubleInt
#print axioms normSock_msgAnno
#print axioms normSock_msgSock
#print axioms normSock_patchProd
#print axioms runDatum_norm
#print axioms Ana.bridge_stepD
#print axioms Ana.run_folTopRD
#print axioms Ana.pop_frozen
#print axioms Ana.runStep_ok2
#print axioms Ana.resolveStep_ok2
#print axioms Ana.cull_ok2
#print axioms Ana.sweep_reach
#print axioms Ana.memberStep_ok2
#print axioms Ana.passStep_ok2
#print axioms Ana.analyzeStep_ok2
#print axioms Ana.allP2
#print axioms Ana.skaCallgraph_frozen
#print axioms Ana.memoHit_hitEntry
#print axioms Ana.skaCallgraph_convergedM
#print axioms Ana.pruneCallgraph_spec
#print axioms Ana.pokeMemo_spec
#print axioms Ana.skaCallgraph_prunedM
#print axioms Ana.skaPoke_sound
#print axioms Ana.PokeInv.agree
#print axioms folR_norm
#print axioms Bake.uniSock_fits
#print axioms Bake.normSockH_fits
#print axioms Bake.bakeOf_fits
#print axioms Bake.rebake_fits
#print axioms Bake.uniSock_drops_less_fits
#print axioms Bake.annot_safe_total
#print axioms Bake.annot_lit
#print axioms Bake.knowGo_sound
#print axioms Bake.know_annot
#print axioms Bake.know_annot_of_implies
#print axioms Bake.datOK_of_prov
#print axioms Bake.bakeLoop_sound
#print axioms Bake.knowGo_idc
#print axioms Bake.pick_spec
#print axioms Bake.bakeRes_ok
#print axioms Bake.variant_annot
#print axioms Bake.uniSock_left
#print axioms Bake.purr_sub
#print axioms Bake.normSockH_rev
#print axioms Bake.bakeOf_ok
#print axioms Bake.rebakeG_ok
#print axioms Bake.addCode_get
#print axioms Bake.finalFold_spec
#print axioms Bake.skaPoke_dats
#print axioms Bake.pokeDat_ok
#print axioms Bake.skaPokeB_sound
#print axioms Bake.InvB.agree
#print axioms Bake.bakeLoop_pred
#print axioms Bake.bakes_ok_of_meet
#print axioms Bake.bakes_norm
#print axioms Bake.bakesImply_of_meet
#print axioms PokeM.compileStep_spec
#print axioms PokeM.needOf_eq
#print axioms PokeM.pokeS_sound
#print axioms PokeM.pokeS_invKept
#print axioms PokeM.invS_init
#print axioms PokeM.sound_lift
#print axioms PokeM.gap_of
#print axioms Bake.skaPoke_root_fits
#print axioms PokeM.anaHyp_of_bakes
#print axioms PokeM.anaHyp_of_meet
#print axioms PokeM.pokeS_sound_of_meet
#print axioms PokeM.pokeS_invKept_of_meet
#print axioms PokeM.gap_of_meet
#print axioms Bake.bakeLoop_mono
#print axioms Bake.rebakeG_grows
#print axioms Bake.bakeLoop_grows
#print axioms PokeM.anaArm_some
#print axioms PokeM.fullAnswers_of
#print axioms Bake.knowGo_res
#print axioms Bake.finalPass_some
#print axioms PokeM.finalEnds_always
#print axioms PokeM.fullAnswers_of_loops
#print axioms Jets.reverseGraph_has
#print axioms Jets.hotStale_closed
#print axioms Jets.delBells_get
#print axioms Bake.normSockH_canon
#print axioms Bake.kap_sub
#print axioms Bake.kapS_lt
#print axioms Bake.canon_ext
#print axioms Bake.rebakeG_canon
#print axioms Bake.normCD_of_canon
#print axioms Bake.noLoss_lessc
#print axioms Bake.bakes_canon
#print axioms Bake.sitesMeet_at_less
#print axioms Bake.sitesMeet_of_parts
#print axioms PokeM.pokeSites_of_parts
#print axioms Bake.knit_mono
#print axioms Bake.knowMono_false
#print axioms Bake.sitesMeet_of_nf
#print axioms Bake.meets_knit
#print axioms Bake.meets_doubleInt
#print axioms Bake.meets_doubleInt_left
#print axioms Bake.meets_pull
#print axioms Bake.meets_of_bakeOK
#print axioms Bake.meets_patchProd
#print axioms Bake.darn_fits_force
#print axioms Bake.meets_darn
#print axioms Bake.darn_some
#print axioms Bake.knowGo_lit
#print axioms Bake.knowGo_nf_some
#print axioms Bake.knowGo_meets
#print axioms Bake.knowMeetsNF_of
#print axioms Bake.sitesMeet_of_lessNF
#print axioms Bake.prodMeet_of_same
#print axioms PokeM.pokeSites_of_nf
#print axioms Ana.folLoop_noAx0
#print axioms wf_inhab
#print axioms patchProd_inhab
#print axioms Ana.skaCallgraph_dat
#print axioms Ana.skaPoke_dat
#print axioms Ana.skaPoke_sound
#print axioms PokeM.poke_datFacts
#print axioms PokeM.pokeNF_of_lessNF
#print axioms PokeM.pokeSites_of_lessNF
#print axioms Bake.sub_app_cape
#print axioms Bake.sub_of_cover
#print axioms Bake.lessProvidesNF_of_cover
#print axioms PokeM.pokeLessNF_of_cover
#print axioms PokeM.pokeSites_of_cover
#print axioms Bake.knowT_datTab
#print axioms Bake.know_sites_knowT
#print axioms Bake.siteCover_of
#print axioms Bake.lessProvidesNF_of_replay
#print axioms Bake.prodSame_of_M
#print axioms Ana.fuelStep
#print axioms Ana.folLoop_fuel_le
#print axioms Ana.resolve_fuel_le
#print axioms Ana.analyze_fuel_le
#print axioms Ana.run_fuel_le
#print axioms Ana.passLoop_fuel_le
#print axioms Ana.memberLoop_fuel_le
#print axioms Ana.skaPoke_fuel_le
#print axioms GenLe.fits_and
#print axioms HeChain.lift
#print axioms HeChain.genLe
#print axioms Ana.ansW_hitGen
#print axioms answers_less
#print axioms answers_rel
#print axioms answers_relN
