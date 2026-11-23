import lemmas.Ska.Statements
import lemmas.Ska.CapeFacts

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
