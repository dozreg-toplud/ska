import lemmas.Compiler.PokeLink
import lemmas.Compiler.PokeLinkFull

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
