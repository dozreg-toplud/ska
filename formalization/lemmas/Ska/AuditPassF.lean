import lemmas.Ska.PassMeasure

/-! The axioms of the theorems of track F (`Ska/PassMeasure.lean`, README
Gaps 16).  `lake build` prints them; each should be `propext`,
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
