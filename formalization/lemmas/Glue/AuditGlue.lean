import lemmas.Assembly
import lemmas.Glue.RawOptIn
import lemmas.Ska.SccLoop
import lemmas.Compiler.CompShapeColSur
import lemmas.Ska.CompLeapTwice
import lemmas.Compiler.CompRunRClass
import lemmas.Compiler.CompRunAllSix
import lemmas.Ska.PassStab
import lemmas.Ska.PassMeasureB
import lemmas.Ska.OptAliasOnce
import lemmas.Compiler.CompStraightMapSix
import lemmas.Ska.CompDirectMCloseEx
import lemmas.Glue.GuardCallsD
import lemmas.Ska.CompDirectMTailP
import lemmas.Ska.CompDirectMTree
import lemmas.Ska.RawInvCAT
import lemmas.Compiler.RegisterFastShape
import lemmas.Compiler.SkaJointConv
import lemmas.Compiler.FolLoopConv
import lemmas.Compiler.RoadPure
import lemmas.Ska.CompDirectMTop
import lemmas.Ska.OptAliasWitness
import lemmas.Glue.MonoCalls
import lemmas.Glue.InvMemo
import lemmas.Glue.LibPill
import lemmas.Glue.EntryFragX
import lemmas.Compiler.CompSofArms
import lemmas.Compiler.CompSofPush
import lemmas.Compiler.CompShapeColLoop
import lemmas.Compiler.CompShapeColOrig
import lemmas.Compiler.CompShapeColI12
import lemmas.Compiler.CompCoerceLazyGen
import lemmas.Ska.CompNaryTopRecEx
import lemmas.Ska.CompNaryTopClose
import lemmas.Ska.RawInvCLIJ
import lemmas.Ska.PassFreeze
import lemmas.Ska.PassMoves
import lemmas.Ska.PassIdents
import lemmas.Ska.CompTenLS
import lemmas.Ska.CompSixLSRCall
import lemmas.Compiler.CompShapeColRet
import lemmas.Glue.InvMemoP
import lemmas.Glue.GuardRun
import lemmas.Glue.GuardTop
import lemmas.Glue.GuardFinalTop
import lemmas.Compiler.PokeLinkGood
import lemmas.Compiler.PokeLinkRestCut
import lemmas.Compiler.PokeLinkRest
import lemmas.Ska.ShapeColAlgFix
import lemmas.Compiler.CompRunAllNorm
import lemmas.Compiler.CompShapeColNorm
import lemmas.Compiler.CompStraightRun
import lemmas.Compiler.CompUnaryDirE
import lemmas.Compiler.CompSccOfOne
import lemmas.Compiler.CompSccOfOneGate
import lemmas.Compiler.CompSccLoopSt
import lemmas.Compiler.SkaCallgraph
import lemmas.Ska.CompHintTree
import lemmas.Ska.CompHintTreeU
import lemmas.Ska.CompHintKeep
import lemmas.Ska.CompSixNxTag
import lemmas.Ska.CompSixNxClass
import lemmas.Compiler.CompRunHintKS
import lemmas.Compiler.CompRunHintKD
import lemmas.Compiler.CompRunHintPI
import lemmas.Compiler.CompRunHintClass
import lemmas.Ska.SccLoopTotal
import lemmas.Compiler.CompShapeColFuel
import lemmas.Compiler.PokeLink
import lemmas.Ska.PokeEnc
import lemmas.Ska.SccLoopMsg
import lemmas.Ska.SccLoopCycle
import lemmas.Compiler.CompSccLoopInd
import lemmas.Compiler.CompSccLoopClose
import lemmas.Compiler.CompSccLoopPrint
import lemmas.Compiler.CompSccOfAny
import lemmas.Compiler.CompMonoLink
import lemmas.Compiler.CompSccLoopMemDone
import lemmas.Ska.CompGen
import lemmas.Glue.InlineAnnot
import lemmas.Glue.InlineCheck
import lemmas.Glue.GuardCallsMono
import lemmas.Glue.GuardCallsTop

/-!
# Audit of `formalization/LEDGER.md`

Every declaration the ledger names, checked to exist, and the axioms of the
theorems of `lemmas/Glue/`.  Track P's route (`Ska/PokeEnc.lean`,
`Compiler/PokeLink.lean`, `Glue/InvMemoP.lean`) and track I's
`Ska/SccLoopMsg.lean` are checked here too since the renames
`unitNoun_id_injP` and `ordIsLeaf` (M15 closed; `AuditGlueP.lean` folded in).  Run:
`systemd-run --user --scope -q -p MemoryMax=3500M -p MemorySwapMax=0 -- lake env lean lemmas/Glue/AuditGlue.lean`.
-/

namespace Formalization

/-! ## `Gap` and the assembly -/
#check @Assembly.Gap
#check @Assembly.full_of
#check @Assembly.PokeModel
#check @Assembly.Contract
#check @Assembly.Halting
#check @Assembly.InvStart
#check @Assembly.InvKept
#check @Assembly.LibSlam
#check @Assembly.LibFormat
#check @Assembly.MookFormat
#check @Assembly.cueRoot
#check @Assembly.ovumMold
#check @Assembly.pokeValid
#check @Assembly.reach_model
#check @Compiler.pokeFrame_corIn
#check @Compiler.pokeIs_of_frame
#check @Compiler.pokeN_validates
#check @Compiler.pokeDireBad
#check @Compiler.listMoldIs
#check @Compiler.mookOtherTwo_of
#check @Compiler.rendBaseIs_layer4
#check @Compiler.mock_pill_iff
#check @Compiler.eval_mook_le
#check @Compiler.SlamIsNock
#check @Compiler.RendLeafIs
#check @Compiler.HandIs
#check @Compiler.RendRestIs
#check @Compiler.SoftTankIs
#check @Compiler.SkipMsgIs
#check @Compiler.EvalMookMsgIs
#check @Compiler.CorIn
#check @Compiler.PokeReach

/-! ## Contract, InvKept, InvStart: the model side -/
#check @SkaModel.Sound
#check @SkaModel.FullAnswers
#check @SkaModel.PokeM.liftPoke
#check @SkaModel.PokeM.liftInv
#check @SkaModel.PokeM.gap_of
#check @SkaModel.PokeM.gap_of_comp
#check @SkaModel.PokeM.anaHyp_of_arm
#check @SkaModel.PokeM.pokeBakes
#check @SkaModel.PokeM.CompHyp
#check @SkaModel.PokeM.InvS
#check @SkaModel.PokeM.CompRest
#check @SkaModel.PokeM.CompPieces
#check @SkaModel.PokeM.compHyp_of_pieces
#check @SkaModel.PokeM.contract_of_pieces
#check @SkaModel.PokeM.CompRest.keeps
#check @SkaModel.PokeM.RawMono
#check @SkaModel.PokeM.RawNary
#check @SkaModel.PokeM.rawMono_fragU
#check @SkaModel.PokeM.rawNary_fragU
#check @SkaModel.PokeM.compHyp_of_frag
#check @SkaModel.PokeM.rawMono_NCG
#check @SkaModel.PokeM.compHyp_of_NCG
#check @SkaModel.PokeM.rawMono_fragUFG
#check @SkaModel.PokeM.compHyp_of_fragUFG
#check @SkaModel.PokeM.rawMono_fragUCG
#check @SkaModel.PokeM.rawMono_fragUDG
#check @SkaModel.PokeM.rawMono_fragUEG
#check @SkaModel.Bake.InvB
#check @SkaModel.Bake.InvB.init
#check @SkaModel.PokeM.invS_init

/-! ## The raw side and the optimizer -/
#check @SkaModel.Comp.FragX
#check @SkaModel.Comp.FragU
#check @SkaModel.Comp.fragX_pure
#check @SkaModel.Comp.finishLUC_eq
#check @SkaModel.Comp.finishLFC_eq
#check @SkaModel.Comp.finishLUCM_eq
#check @SkaModel.Comp.runLCM_eq
#check @SkaModel.Comp.finishLF_bellContractX
#check @SkaModel.Comp.finishLUC_contractNC
#check @SkaModel.Raw.optIn_finishLUX
#check @SkaModel.Raw.optIn_finishLFX
#check @SkaModel.Raw.optIn_finishLFX_of
#check @SkaModel.Raw.optimize_keeps_finishLFX
#check @SkaModel.Raw.optimize_keeps_finishLUX
#check @SkaModel.Raw.runAT_fragX
#check @SkaModel.Raw.runATC_plain
#check @SkaModel.Opt.OptIn
#check @SkaModel.Opt.DInvS
#check @SkaModel.Opt.DInvR
#check @SkaModel.Opt.optimize_keeps_optIn
#check @SkaModel.Opt.optimize_keeps_ssaR
#check @SkaModel.Opt.AliasOnceB
#check @Compiler.gateTotalN
#check @Compiler.aliasReadsN
#check @Compiler.optimize_total_finishLFX
#check @Compiler.optimize_total_finishLUX

/-! ## The pill link of `+comp` -/
#check @Compiler.cu_gate_scc_one_six_ts
#check @Compiler.cu_gate_six_ts
#check @Compiler.tsMapAt_holds
#check @Compiler.FinSure
#check @Compiler.NoSelfCall
#check @Compiler.shapeCol_sccSur
#check @Compiler.shapeCol_finSure
#check @Compiler.comp_run_all_l6
#check @Compiler.res_all6
#check @Compiler.comp_run_dir
#check @Compiler.res_dir
#check @SkaModel.Comp.leap_twice

/-! ## Direct calls and the SCC loop -/
#check @SkaModel.Comp.finishLUCM_bellContractCallTreeD
#check @SkaModel.Comp.finishLUCM_contractTailP
#check @SkaModel.Comp.closed_slotCall
#check @SkaModel.Comp.dt_closed_of_table
#check @SkaModel.SccLoop.final_member
#check @SkaModel.SccLoop.final_keeps
#check @SkaModel.SccLoop.loop_end

/-! ## Halting -/
#check @SkaModel.PokeM.fullAnswers_of
#check @SkaModel.PokeM.fullAnswers_of_loops
#check @SkaModel.PokeM.finalEnds_always
#check @SkaModel.PokeM.fullAnswers_lift
#check @SkaModel.PokeM.CgHalts
#check @SkaModel.PokeM.anaHalts_of_cgHalts
#check @SkaModel.PokeM.anaEndsN_of_halts
#check @SkaModel.PokeM.anaEnds_of_N
#check @SkaModel.PokeM.AnaEnds
#check @SkaModel.PokeM.BakeEnds
#check @SkaModel.PokeM.RootAnswers
#check @SkaModel.Ana.memoNoCallees_skaPoke
#check @SkaModel.Ana.passLoop_returns_fin
#check @SkaModel.Ana.FinPushes
#check @SkaModel.Ana.passOn_old

/-! ## Further names of the ledger -/
#check @SkaModel.Comp.noDirect_of_fragX
#check @SkaModel.Ana.skaPoke_fuel_le
#check @SkaModel.Ana.memoNoCallees_empty
#check @SkaModel.Bake.bakeLoop_mono
#check @SkaModel.Bake.bakeLoop_grows
#check @Compiler.ska_poke_iff
#check @Compiler.ska_poke_ana_iff_pill
#check @Compiler.analyze_iff
#check @Compiler.fol_loop_iff
#check @Compiler.resolve_iff
#check @Compiler.opt_gate
#check @Compiler.cu_gate_scc_one_six_fol_ts
#check @SkaModel.Opt.not_aliasOnceB
#check @SkaModel.Opt.w_opt
#check @SkaModel.PokeM.finishLUC_this
#check @SkaModel.Opt.EntryOK

/-! ## The glue theorems -/
#print axioms SkaModel.Glue.keeps_of_optIn
#print axioms SkaModel.Glue.contract_of_piecesO
#print axioms SkaModel.Glue.compHyp_of_piecesO
#print axioms SkaModel.Glue.rawMono_fragX
#print axioms SkaModel.Glue.rawNary_fragX
#print axioms SkaModel.Glue.rawOptIn_fragX
#print axioms SkaModel.Glue.compHyp_of_fragX
#print axioms SkaModel.Glue.optRef_fragX
#print axioms SkaModel.Glue.fullAnswers_of_cg
#print axioms SkaModel.Glue.rawMonoM_of
#print axioms SkaModel.Glue.rawMonoM_fragX

/-! ## Names of the ledger after 2026-11-27 (second pass) -/
#check @SkaModel.Comp.NC.noDirect
#check @SkaModel.PokeM.fragUFG_subNC
#check @SkaModel.Comp.CallTreeD
#check @SkaModel.Comp.QDirect
#check @SkaModel.Comp.CallTreeDN
#check @SkaModel.Comp.finishLFC_bellContractCallTreeDN
#check @SkaModel.Comp.finishLUCM_bellContractCallTreeA
#check @SkaModel.Comp.finishLUCM_bellContractTopTree
#check @SkaModel.Comp.finishLFC_bellContractCallTreeA
#check @SkaModel.Comp.finishLFC_contractTailN
#check @SkaModel.Comp.Six0
#check @SkaModel.Comp.finishLUC_contractSix0
#check @SkaModel.Comp.NeedsRead
#check @SkaModel.Comp.tableOK_classes
#check @SkaModel.Comp.closed_entry
#check @SkaModel.Comp.closed_selfCall
#check @SkaModel.Comp.closed_selfWalk
#check @SkaModel.Comp.closed_pairWalk
#check @SkaModel.Comp.tableOK_callTreeA
#check @SkaModel.Comp.closed_treeNary
#check @SkaModel.Raw.LiveC
#check @SkaModel.Raw.LiveRun
#check @SkaModel.Raw.liveC_n0
#check @SkaModel.Opt.optIn_iff
#check @SkaModel.Opt.optimize_keeps_optIn
#check @Compiler.cu_gate_dir_csi
#check @Compiler.cu_gate_dir_arms
#check @Compiler.cu_gate_dir_this
#check @Compiler.CsiNeeds
#check @Compiler.CsiSures
#check @Compiler.sof_push
#check @Compiler.comp_coerce_lazy_all
#check @Compiler.fx_gate
#check @Compiler.i12_gate
#check @Compiler.fr_gate
#check @Compiler.oi_gate
#check @Compiler.ic_gate
#check @Compiler.blob_toNoun_inj
#check @SkaModel.Annot.inline
#check @SkaModel.Opt.ReadsOK
#check @SkaModel.Opt.ArgsOK
#check @SkaModel.Opt.LocalOK
#check @SkaModel.Opt.Keeps
#check @SkaModel.Opt.optimize_keeps_plain_pickR
#check @SkaModel.PokeM.bellContract_of_keeps
#check @SkaModel.PokeM.sound_lift
#check @SkaModel.PokeM.invKept_lift
#check @SkaModel.Comp.finishLFC_eq_M
#check @SkaModel.Ana.FinIdents
#check @SkaModel.Ana.PassMoves
#check @SkaModel.Ana.freeze_no_chain
#check @SkaModel.Ana.KruskalBT
#check @SkaModel.Ana.passMoves_chain
#check @SkaModel.Ana.finPushes_of_freezeC
#check @SkaModel.Ana.finIdents_of_kruskal
#check @SkaModel.Comp.lokSE_tenR
#check @SkaModel.Comp.finishLFC_contractGBN
#check @SkaModel.Comp.finishLFC_contractRT
#check @Compiler.cu_gate_scc_one_six_fix
#check @Compiler.FixRet
#check @Compiler.scOrd
#check @SkaModel.Ana.finPushes_of_freeze
#check @SkaModel.Ana.EvFrozen

/-! ## The glue theorems of the second pass -/
#print axioms SkaModel.Glue.rawMonoD_calls
#print axioms SkaModel.Glue.rawNaryD_calls
#print axioms SkaModel.Glue.noDirect_NCG
#print axioms SkaModel.Glue.noDirect_fragUFG
#print axioms SkaModel.Glue.six0_noDirect
#print axioms SkaModel.Glue.contract_of_piecesM
#print axioms SkaModel.Glue.compHyp_of_piecesM
#print axioms SkaModel.Glue.compRestM_of_O
#print axioms SkaModel.Glue.rawOptIn_of
#print axioms SkaModel.Glue.optInMono_fragX
#print axioms SkaModel.Glue.optInNary_fragX
#print axioms SkaModel.Glue.compHyp_of_calls
#print axioms SkaModel.Glue.rawEntry_of
#print axioms SkaModel.Glue.optRef_fragX'
#print axioms SkaModel.Glue.optTotalMono_fragX
#print axioms SkaModel.Glue.optTotalNary_fragX
#print axioms SkaModel.Glue.optRef_of_total
#print axioms SkaModel.Glue.invSM_init
#print axioms SkaModel.Glue.sound_and
#print axioms SkaModel.Glue.pokeS_memo
#print axioms SkaModel.Glue.gap_of_compM
#print axioms SkaModel.Glue.fullAnswers_of_cgM
#print axioms SkaModel.Glue.libP_slam
#print axioms SkaModel.Glue.libP_rendLeaf
#print axioms SkaModel.Glue.libP_hand
#print axioms SkaModel.Glue.libP_format
#print axioms SkaModel.Glue.libP_evalMook
#print axioms Compiler.straight_toNoun_inj

-- rawEntry (LEDGER 2.c): the generic lemma and FragX
#check @SkaModel.Glue.NoPoison
#check @SkaModel.Glue.CelGuard
#check @SkaModel.Glue.EInv
#check @SkaModel.Glue.einv_step
#check @SkaModel.Glue.GuardMonoX
#check @SkaModel.Glue.GuardNaryX
#check @SkaModel.Glue.CompRestOE
#check @SkaModel.Glue.BlocksOK
#check @SkaModel.Glue.guardedBody_append
#check @SkaModel.Glue.noPoison_of_blocksOK
#check @SkaModel.Glue.celGuard_of_blocksOK
#check @SkaModel.Opt.EntryOK
#check @SkaModel.Raw.optInput_finishLUX_at
#check @SkaModel.Raw.optInput_finishLFX_at
#check @SkaModel.Raw.optIn_finishLFX
#check @Compiler.cu_gate_dir_code
#print axioms SkaModel.Glue.entryOK_of
#print axioms SkaModel.Glue.entry_finishLUX
#print axioms SkaModel.Glue.entry_finishLFX
#print axioms SkaModel.Glue.entryMono_fragX
#print axioms SkaModel.Glue.entryNary_fragX
#print axioms SkaModel.Glue.rawEntry_fragX
#print axioms SkaModel.Glue.compHyp_of_fragX'

-- GuardMonoX / GuardNaryX (LEDGER 2.c, fourth pass): the +kern-need guard, the block steps
#check @SkaModel.Glue.GuardedPre
#check @SkaModel.Glue.BlockOK
#check @SkaModel.Raw.KR
#check @SkaModel.Raw.kernLoop_raw
#check @SkaModel.Raw.raw_sureLoop
#check @SkaModel.Raw.stOut_ren
#check @SkaModel.Raw.runX_at
#check @SkaModel.Comp.sect_spec
#check @SkaModel.Annot.mono
#print axioms SkaModel.Glue.guardedBody_cel
#print axioms SkaModel.Glue.guardedPre_append
#print axioms SkaModel.Glue.kernBoth_guard
#print axioms SkaModel.Glue.kernLoop_guarded
#print axioms SkaModel.Glue.kernNeed_guarded
#print axioms SkaModel.Glue.blocksOK_emitted
#print axioms SkaModel.Glue.addOps_ok
#print axioms SkaModel.Glue.blocksOK_insertHop
#print axioms SkaModel.Glue.sureLoop_guard

-- GuardMonoX / GuardNaryX (LEDGER 2.c, fifth pass): KP, the run-level induction on FragX, the final passes stated
#check @SkaModel.Glue.KP
#check @SkaModel.Glue.Inv
#check @SkaModel.Glue.RKX
#check @SkaModel.Glue.GuardFinalU
#check @SkaModel.Glue.GuardFinalF
#print axioms SkaModel.Glue.guardedBody_of_noSplit
#print axioms SkaModel.Glue.kp_copyNeed
#print axioms SkaModel.Glue.kp_copyLazyL
#print axioms SkaModel.Glue.kp_forkSure
#print axioms SkaModel.Glue.run_kp
#print axioms SkaModel.Glue.rkx_sixN
#print axioms SkaModel.Glue.rkx_sixP
#print axioms SkaModel.Glue.runX_kp
#print axioms SkaModel.Glue.runX_blocksOK
#print axioms SkaModel.Glue.guardMonoX_of
#print axioms SkaModel.Glue.guardNaryX_of
#print axioms SkaModel.Glue.compHyp_of_fragX''

-- track P's route and track I's SccLoopMsg (was AuditGlueP.lean; M15)
#check @Compiler.straight_toNoun_inj
#check @Compiler.enc
#check @Compiler.enc_inj
#check @Compiler.cor_enc
#check @Compiler.cor_enc_gap
#check @Compiler.emptySt
#check @Compiler.Flags
#check @Compiler.anaArmP
#check @Compiler.anaHyp_of_armP
#check @Compiler.gap_of_armP
#check @Compiler.invStart_cor
#check @Compiler.FuelOK
#check @Compiler.fuelOK_anaFuel
#check @Compiler.pokeN_full_of
#check @Compiler.FullBranchIs
#check @Compiler.SkaLink
#check @Compiler.JetRootLink
#check @Compiler.SccLink
#check @Compiler.MonoLink
#check @Compiler.OptLink
#check @SkaModel.Comp.msgOrd_abs
#check @SkaModel.SccLoop.cyc_never
#print axioms SkaModel.Glue.anaArmP_memo
#print axioms SkaModel.Glue.pokeS_memoP
#print axioms SkaModel.Glue.fullAnswers_of_cgMP
#print axioms SkaModel.Glue.gap_of_armPM
#print axioms SkaModel.Glue.halting_of_cgMP

#print axioms SkaModel.Glue.blocksOK_rename
#print axioms SkaModel.Glue.kernListG
#print axioms SkaModel.Glue.coerceLazyLG
#print axioms SkaModel.Glue.guardFinalU
#print axioms SkaModel.Glue.guardFinalF
#print axioms SkaModel.Glue.guardMonoX
#print axioms SkaModel.Glue.guardNaryX
#print axioms SkaModel.Glue.compHyp_of_fragX₃

/-! ## LEDGER sixth pass: names from digest [256] to [269] -/
#check @Compiler.pokeReachGood
#check @Compiler.pokeModel_fullReach
#check @Compiler.pokeModel_fullReachP
#check @Compiler.good_empty
#check @Compiler.good_full_step
#check @Compiler.spRest_cut
#check @Compiler.spRest_of_parts
#check @SkaModel.Comp.fixRet_bound
#check @Compiler.normRun_six
#check @Compiler.cu_gate_scc_one_six_cl
#check @Compiler.cu_gate_scc_one_six_bake_cl
#check @Compiler.cu_gate_scc_one_six_fol_cl
#check @Compiler.cu_gate_scc_one_six_bake_fol_cl
#check @Compiler.tsr_rer
#check @Compiler.tsr_par
#check @Compiler.tsr_args
#check @Compiler.cu_gate_dirE
#check @Compiler.ccc_scc_hit
#check @Compiler.calleeCompiled_one
#check @Compiler.cu_gate_dir_one
-- M15' closed (372dcb9: track I's `sw_gate` is `csSw_gate`, `swG` is `csSwG`): the loop files import here
#check @Compiler.csi_gate_loop
#check @Compiler.csi_gate_ranked
#check @Compiler.cccMiss_of_loop
#check @Compiler.PrintId
#check @Compiler.cg_print
#check @SkaModel.Comp.lokSH_callTreeH
#check @SkaModel.Comp.finishLUCH_contractCallTreeHU
#check @SkaModel.Comp.n11sKept_done
#check @SkaModel.Comp.finishLUCH_contractN11sKept
#check @SkaModel.Comp.tagLSP_callTreeA
#check @SkaModel.Comp.finishLUC_contractSix1
#check @Compiler.comp_run_n11s_kept
#check @Compiler.comp_run_n11d_kept
#check @Compiler.comp_past_if
#check @Compiler.comp_run_hint
#check @Compiler.HintSound
#check @SkaModel.Ana.EvFrozen
#check @SkaModel.Comp.CallTreeH
#check @SkaModel.Comp.CallTreeHU
#check @SkaModel.Comp.Six1
#check @Compiler.HintOk
#check @Compiler.MemGate
#check @SkaModel.SccLoop.Ranked
#check @Compiler.NormRun

/-! ## LEDGER seventh pass: digest [270] to [272], and `inlAnnot` (track G) -/
-- track I [271]: `PrintId` proved (M18 closed), the loop theorems without it
#check @Compiler.printId_pill
#check @Compiler.csi_gate_loop_np
#check @Compiler.csi_gate_loop_d_np
#check @Compiler.csi_gate_ranked_np
#check @Compiler.mem_gate_done_R
-- track K [271]: callees in SCCs of any size; the member invariant `QK`
#check @Compiler.cu_gate_dir_scc
#check @Compiler.calleeCompiled_scc
#check @Compiler.envP
#check @Compiler.envP_agree
#check @Compiler.QK
#check @Compiler.AnyCallee
#check @Compiler.monoRaw_hit
#check @Compiler.monoLinkAt_of
#check @Compiler.compileUnaryP_gate
#check @Compiler.PGoodK
-- track C [270]: `RunOKGen` adopted, phase F open
#check @SkaModel.Comp.RunOKGen
#check @SkaModel.Comp.FrameG
#check @SkaModel.Comp.SemCoreG
#check @SkaModel.Comp.RunOKLS.toGen
#check @SkaModel.Comp.FillSemL.cons
#check @SkaModel.Comp.AgreeG.toLB
-- track G: the model of `+inlined` and the model half of `inlAnnot` (2.e)
#check @SkaModel.Glue.inlinedM
#check @SkaModel.Glue.inlWalk
#check @SkaModel.Glue.nommSize
#check @SkaModel.Glue.inlFailing
#check @SkaModel.Glue.AnnotS
#check @SkaModel.Glue.CodeOKS
#check @SkaModel.Glue.InlPill
#check @SkaModel.Glue.InvBS
#print axioms SkaModel.Glue.AnnotS.toAnnot
#print axioms SkaModel.Glue.inlWalk_annot
#print axioms SkaModel.Glue.inlinedM_annot
#print axioms SkaModel.Glue.inlAnnot_of

-- eighth pass, track G: `rawEntry` with calls (2.c)
#check @SkaModel.Glue.ClqYes
#check @SkaModel.Glue.EntryCell
#check @SkaModel.Glue.CelGuardP
#check @SkaModel.Glue.CellOut
#check @SkaModel.Glue.CelAnn
#check @SkaModel.Glue.GuardMonoC
#check @SkaModel.Glue.GuardNaryC
#check @SkaModel.Glue.ReadsInMono
#check @SkaModel.Glue.ReadsInNary
#check @SkaModel.Glue.BlocksOKA
#check @SkaModel.Glue.InvA
#print axioms SkaModel.Glue.einvP_step
#print axioms SkaModel.Glue.entryOK_ofP
#print axioms SkaModel.Glue.entryOK_of'
#print axioms SkaModel.Glue.einvK_step
#print axioms SkaModel.Glue.entryOK_ofK
#print axioms SkaModel.Glue.celAnn_of_P
#print axioms SkaModel.Glue.entryMono_of
#print axioms SkaModel.Glue.entryNary_of
#print axioms SkaModel.Glue.celAnn_of_blocksOKA
#print axioms SkaModel.Glue.guardMonoC_fragX
#print axioms SkaModel.Glue.emitA
#print axioms SkaModel.Glue.mtl_tail
#print axioms SkaModel.Glue.mtl_kpa

-- ninth pass, track G: `KPA` over `InvA` (2.c)
#check @SkaModel.Glue.FL
#check @SkaModel.Glue.XB
#check @SkaModel.Glue.LzL
#check @SkaModel.Glue.GFL
#check @SkaModel.Glue.KPA
#check @SkaModel.Glue.KerfA
#check @SkaModel.Glue.RunA
#check @SkaModel.Glue.RN
#print axioms SkaModel.Glue.KPA.bind'
#print axioms SkaModel.Glue.KPA.emit'
#print axioms SkaModel.Glue.KPA.addOps'
#print axioms SkaModel.Glue.KPA.mtc
#print axioms SkaModel.Glue.kpa_simpleNextL
#print axioms SkaModel.Glue.kpa_monoBlocks
#print axioms SkaModel.Glue.kpa_copyNeed
#print axioms SkaModel.Glue.kpa_copyLazyL
#print axioms SkaModel.Glue.kpa_copyL
#print axioms SkaModel.Glue.kpa_pastL
#print axioms SkaModel.Glue.kpa_needOrd
#print axioms SkaModel.Glue.kpa_callTail
#print axioms SkaModel.Glue.kpa_callDM

-- tenth pass, track G: `RunG`, `kerfG`, `GuardMonoC` on `NoSixM` (2.c)
#check @SkaModel.Glue.NoSixM
#check @SkaModel.Glue.KIMid
#check @SkaModel.Glue.StraightA
#check @SkaModel.Glue.RunG
#print axioms SkaModel.Glue.kerfG
#print axioms SkaModel.Glue.kpa_callDMG
#print axioms SkaModel.Glue.kpa_callLI
#print axioms SkaModel.Glue.kpa_splitL
#print axioms SkaModel.Glue.kpa_intoL
#print axioms SkaModel.Glue.kpa_medeL
#print axioms SkaModel.Glue.kpa_collapseLazyAtomL
#print axioms SkaModel.Glue.runG_lcm
#print axioms SkaModel.Glue.guardMonoC_noSix
#print axioms SkaModel.Glue.entryMono_noSix

end Formalization
