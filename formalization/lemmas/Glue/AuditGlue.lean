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

/-!
# Audit of `formalization/LEDGER.md`

Every declaration the ledger names, checked to exist, and the axioms of the
theorems of `lemmas/Glue/`.  Run:
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
#print axioms SkaModel.Glue.straight_toNoun_inj

-- rawEntry (LEDGER 2.c): the generic lemma and FragX
#check @SkaModel.Glue.NoPoison
#check @SkaModel.Glue.CelGuard
#check @SkaModel.Glue.EInv
#check @SkaModel.Glue.einv_step
#check @SkaModel.Glue.GuardMonoX
#check @SkaModel.Glue.GuardNaryX
#check @SkaModel.Glue.CompRestOE
#print axioms SkaModel.Glue.entryOK_of
#print axioms SkaModel.Glue.entry_finishLUX
#print axioms SkaModel.Glue.entry_finishLFX
#print axioms SkaModel.Glue.entryMono_fragX
#print axioms SkaModel.Glue.entryNary_fragX
#print axioms SkaModel.Glue.rawEntry_fragX
#print axioms SkaModel.Glue.compHyp_of_fragX'

end Formalization
