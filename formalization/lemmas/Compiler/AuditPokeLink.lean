import lemmas.Compiler.PokeLink
import lemmas.Compiler.PokeLinkFull
import lemmas.Compiler.PokeLinkScc
import lemmas.Compiler.PokeLinkSka
import lemmas.Compiler.PokeLinkGood
import lemmas.Compiler.PokeLinkSccHit

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
