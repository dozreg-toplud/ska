import lemmas.Ska.AnnotS
import lemmas.Ska.AnnotSDet
import lemmas.Ska.AnnotSCheck
import lemmas.Ska.AnnotSInv

/-! Axioms of track F's `InvBS` file (`Ska/AnnotS.lean`). -/

open Formalization.SkaModel.AnnotSF

#print axioms annot_sff_returns
#print axioms sockHas_axisIn
#print axioms rgood_direct_ret
#print axioms witCode_codeOK
#print axioms witCode_not_codeOKS
#print axioms witLong_invB
#print axioms invBS_false
#print axioms inlAnnot_of_inv
#print axioms DetK.mono
#print axioms sffOn_of_detK
#print axioms ret_of_detK

/-! Track Q, `InvBSR` (README Gaps 27.6). -/

#print axioms detKB_sound
#print axioms kcB_iff
#print axioms AnnotK.toAnnotS
#print axioms KC.not_safe
#print axioms doubleInt_yes
#print axioms folR_rgoodK
#print axioms folTopR_annotK
#print axioms Formalization.SkaModel.annotK_of_graphM
#print axioms Formalization.SkaModel.memoInvK_poke
#print axioms Formalization.SkaModel.Ana.skaPoke_soundK
#print axioms Formalization.SkaModel.Bake.knowGo_kc
#print axioms Formalization.SkaModel.Bake.knowGo_detK_safe
#print axioms Formalization.SkaModel.Bake.knowGo_soundK
#print axioms Formalization.SkaModel.Bake.know_annot_of_impliesK
#print axioms Formalization.SkaModel.Bake.variant_annotK
#print axioms Formalization.SkaModel.Bake.skaPokeB_soundK
#print axioms folTopK
#print axioms invBSR_skaPokeB
#print axioms inlAnnot_of_invK
