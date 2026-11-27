import lemmas.Ska.TarjanSound
import lemmas.Compiler.CompTarjanLink
import lemmas.Compiler.CompTarjanBunt
import lemmas.Compiler.CompSccOfMissEnc
import lemmas.Compiler.CompTarjanLeaf
import lemmas.Compiler.CompSccOfMissSem
import lemmas.Ska.TarjanSccOfSem

/-! The axioms of track Q's `+tarjan` theorems: the model (`Ska/Tarjan*.lean`)
and the pill link of `+tarjan` and of the miss of `+scc-of`. -/

open Formalization.Tarjan Formalization.Compiler

#print axioms tarjanM_total
#print axioms tarjanM_count
#print axioms tarjanM_spec
#print axioms tjSpec_flop
#print axioms tj_bat
#print axioms tarjanLinkAt_jug
#print axioms sccG_missJ
#print axioms sccG_miss_enc
#print axioms srSccs_empty
#print axioms srSccs_tarjan
#print axioms finMap_rap_nodup
#print axioms tjReach_jug
#print axioms tarjanSpec_of_tj
#print axioms tarjanSpecN_of
#print axioms tarjanSpecN_empty
#print axioms tarjanExists
#print axioms sccsLeafAt_of_tarjan
#print axioms preorder_keys_nodup
#print axioms scoSub_total
#print axioms scoMiss_total
#print axioms scoMiss_spec
#print axioms scoReach_fresh
#print axioms scoMiss_keeps
#print axioms sccG_miss_eq
#print axioms sccsNoun_rbSccs
#print axioms sccImageMiss
#print axioms sccImage
#print axioms sccOfP_hit
#print axioms sccOfP_miss
#print axioms sccOfKeeps_of
#print axioms scoKids_enc
#print axioms scoReach_key
#print axioms reach_sco
#print axioms scoScc_iff
#print axioms scoScc_set
#print axioms scoReach_blocked
#print axioms sccOfIs_needs_key
#print axioms sccOfIs_needs_good
#print axioms sccOfP_is
#print axioms sccOfIsK_of
#print axioms singleScc_of_sccOf
