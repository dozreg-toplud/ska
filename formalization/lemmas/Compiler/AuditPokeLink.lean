import lemmas.Compiler.PokeLinkColeUpd
import lemmas.Compiler.PokeLinkGood8
import lemmas.Compiler.PokeLinkHotTop
import lemmas.Compiler.PokeLinkTailEnd
import lemmas.Compiler.PokeLinkTailJets
import lemmas.Compiler.PokeLinkTailCores
import lemmas.Compiler.PokeLinkGood7
import lemmas.Compiler.PokeLinkJetsCole
import lemmas.Compiler.PokeLinkJetsP
import lemmas.Compiler.PokeLink
import lemmas.Compiler.PokeLinkFull
import lemmas.Compiler.PokeLinkScc
import lemmas.Compiler.PokeLinkSka
import lemmas.Compiler.PokeLinkGood
import lemmas.Compiler.PokeLinkSccHit
import lemmas.Compiler.PokeLinkRest
import lemmas.Compiler.PokeLinkRestTail
import lemmas.Compiler.PokeLinkGood2
import lemmas.Compiler.PokeLinkGoodK
import lemmas.Ska.PokeFlagsOf
import lemmas.Compiler.PokeLinkLoop
import lemmas.Compiler.PokeLinkLoopRun
import lemmas.Compiler.PokeLinkGood4
import lemmas.Compiler.PokeLinkTop5
import lemmas.Compiler.PokeLinkEvalFin
import lemmas.Compiler.PokeLinkCole
import lemmas.Compiler.PokeLinkGlue

/-! # Audit of track P: `enc` and the `%full` branch of `+poke` -/

open Formalization Formalization.Compiler

#check @enc
#check @enc_inj
#check @cor_enc
#check @cor_enc_gap
#check @straight_toNoun_inj
#check @nomm_toNoun_inj
#check @memoNoun_inj
#check @PokeReachEnc
#check @anaArmP
#check @FullBranchIs
#check @SkaLink

#print axioms enc_inj
#print axioms cor_enc
#print axioms straight_toNoun_inj
#print axioms anaHyp_of_armP
#print axioms gap_of_armP
#print axioms invStart_cor
#print axioms pokeN_full_of
#print axioms fuelOK_anaFuel
#check @fullBranchIs
#check @pokeN_full
#check @pokeModel_full
#check @pokeModel_full_corIn
#check @JetRootLinkR
#print axioms vovum_full
#print axioms mold_full_cell
#print axioms mold_full_atom
#print axioms ipokeR_eq
#print axioms full_run
#print axioms fullBranchIs
#print axioms pokeN_full_atom
#print axioms jetRootLink_false
#print axioms pokeN_full
#print axioms pokeModel_full
#print axioms pokeModel_full_corIn

-- 2026-11-27, second session: the links restated so that they are true
#check @OptLinkOn
#check @OptTotal
#check @optimizeP
#check @OptInAt
#check @SccImage
#check @sccOfP
#check @JetsGood
#check @jetRootP
#check @JetRootLinkG
#check @SkaLinkU
#check @SkaFlags
#check @SpRestAt
#check @SkaLinkAt
#print axioms optP_eq
#print axioms optLinkOn_optimizeP
#print axioms optimizeP_ref
#print axioms optP_hpill
#print axioms optTotal_of_inv
#print axioms optTotal_finishLUX
#print axioms pokeN_fullO
#print axioms pokeModel_fullO
#print axioms pokeModel_fullP
#print axioms sccs_raw_enc
#print axioms enc_edit958
#print axioms sccLink_of
#print axioms jrP_enc
#print axioms jetRootLinkG_of
#print axioms jetRootLinkR_of_good
#print axioms pokeN_fullAt
#print axioms pokeModel_fullG
#print axioms enc_flags_congr
#print axioms skaLink_of_flags
#print axioms full_step_enc
#print axioms full_step_enc_flags
#print axioms skaRaw_eq
#print axioms skaRaw_iff
#print axioms skaLinkAt_of
#print axioms pokeN_fullAt2
#print axioms keyRaw_enc
#print axioms good_empty
#print axioms skaKeeps_of_armP
#print axioms compiledMono_good
#print axioms good_full_step
#print axioms optInAt_of_good
#print axioms skaLinkAt_good
#print axioms pokeN_fullAt3
#print axioms pokeModel_fullGood
#print axioms full_step_good
#print axioms pokeReachGood
#print axioms pokeModel_fullReach
#print axioms pokeModel_fullReachP
#print axioms sccG_eq
#print axioms sccBat_run
#print axioms sccG_hit
#print axioms sccImage_of_miss
#print axioms spRest_cut
#print axioms pokeDat_eq
#print axioms spRest_three
#print axioms srK3_run
#print axioms srK7_run
#print axioms srK8_run
#print axioms spRest_of_parts
#check @DatLinkAt
#check @JetLinkAt
#check @BakeLinkAt
#check @NewCodeLinkAt
#check @LoopLinkAt
#check @TailLinkAt
#print axioms newCodeLinkAt
#print axioms datLinkAt
#print axioms tailBunt_run
#print axioms srSeek_run
#print axioms srCalls_run
#print axioms srK10_run
#print axioms tailLinkAt_of
#print axioms good2_empty
#check @TailEndAt
#check @PGood2
#print axioms knowGo_infos
#print axioms bakeGraph_closed
#print axioms bakeGraph_vars
#print axioms addCode_closed
#print axioms skaCodeKeeps_of_armP
#print axioms good3_empty
#print axioms good3_full_step
#print axioms pokeN_fullAt4
#print axioms pokeModel_fullReachP3
#print axioms pgoodK_state_of
#print axioms flagsOf_eq
#check @pokeModel_fullReachP3
#check @FlagSol
#check @TarjanSpecN
#print axioms efGo_congr
#print axioms flagSol_uniq
#print axioms flagsOf_sol
#print axioms sccStep_spec
#print axioms sccLoop_sol
#print axioms flagsOf_loop
#print axioms addsTo_addCode
#print axioms bakeGraph_infoCalls
#print axioms infoCalls_addCode
#print axioms flagsOf_poke
#print axioms loopLinkAt_flagsOf
#check @SccsLeafAt
#check @LoopRunAt
#check @LoopTotal
#print axioms srLoop_cut
#print axioms FinMap.jabF_toNoun
#print axioms lp_g1
#print axioms lp_g2
#print axioms lp_loc1
#print axioms lp_loc2
#print axioms lp_trap
#print axioms lp_run
#print axioms acc_loop
#print axioms acc_final
#print axioms loopRunAtT
#print axioms loopLinkAt_flagsOfT
#print axioms good4_empty
#print axioms flags_poke
#check @EvalFinAt
#check @LoopRunAtT
#print axioms annot_noAx0
#print axioms efGo_some
#print axioms sccLoop_some
#print axioms loopTotal_of
#print axioms loopTotal_poke
#print axioms htRank_of
#print axioms good5_empty
#print axioms good5_full_step
#print axioms good5_mid
#print axioms heights_good5
#print axioms loopLinkAt_good5
#print axioms noAx0_poke
#print axioms monoLinkGood5_of_gate
#print axioms pokeModel_fullGood5
#print axioms pokeReachGood5
#print axioms pokeModel_fullReachP5
#print axioms ef_htrap
#print axioms ef_loop_all
#print axioms evalFinAt
#print axioms loopLinkAt_good5E
#print axioms coleCohM_put
#print axioms coleCohM_put_bad
#print axioms coleCohM_fold
#print axioms good6_full_step
#print axioms anaArmP_root
#print axioms coleCoh_toNoun
#print axioms coleDom_toNoun
#print axioms loopLinkAt_good6
#print axioms pokeModel_fullReachP6
#print axioms spRestAt_of_leaves
#print axioms spRestGood6_of_leaves
#print axioms pokeModel_fullReachP6L
#print axioms pokeModel_fullReachP7
#print axioms gateGot_of_key
#print axioms gateCole_of_good
#print axioms jetsOfGood_P
#print axioms pokeModel_fullReachP8
#print axioms jetsOfCole6_P
#print axioms pokeModel_fullReachP9
#print axioms uniR_det
#print axioms jetsOfSets_P
#print axioms good7_full_step
#print axioms good7_mid
#print axioms pokeReachGood7
#print axioms pokeModel_fullReachG7
#print axioms spRestGood7_of_leaves
#print axioms pokeModel_fullReachP10
#print axioms srCores_run
#print axioms rep_gateP
#print axioms ujStep_run
#print axioms uniJu_run
#print axioms srJetsF_run
#print axioms uniJuO_some
#print axioms tailEndAt_of_end
#print axioms spLeavesGood7_of_8
#print axioms spRestGood7_of_leaves8
#print axioms pokeModel_fullReachP11
#print axioms invK_empty
#print axioms good8_empty
#print axioms pokeS_full_long
#print axioms invK_armP
#print axioms good8_full_step
#print axioms otherKeeps7_of_8
#print axioms otherGood8
#print axioms pokeReachGood8
#print axioms pokeModel_fullReachP12
#print axioms reach_invK
#print axioms juPutF_sets_some
#print axioms cputBat_run
#print axioms coleStepO_pair
#print axioms couCm_run
#print axioms couStep_run
#print axioms couBunt_run
#print axioms couSam_run
#print axioms couBat_run
#print axioms srEnd_run
#print axioms srEnd_ts
#print axioms srEndAt_of
#print axioms good9_full_step
#print axioms pokeReachGood9
#print axioms pokeModel_fullReachP13
#print axioms reach_hotEmpty
#print axioms reach_ringVals
#print axioms mold_jets_nil
#print axioms pokeN_jets_idle
#print axioms jetsIdle_keeps
#print axioms otherKeeps9_of
#print axioms spRestGood9_of_leaves9
#print axioms pokeModel_fullGood9
#print axioms pokeReachGood9R
#print axioms pokeModel_fullReachP14
#print axioms keyRaw_hot0
