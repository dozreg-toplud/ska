import lemmas.Compiler.PokeLink

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
