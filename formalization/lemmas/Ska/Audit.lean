import lemmas.Ska.Statements

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
