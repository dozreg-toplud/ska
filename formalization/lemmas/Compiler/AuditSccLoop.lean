import lemmas.Ska.SccLoopCheck

/-! The axioms of the theorems of `Ska/SccLoop.lean` (README Gaps 21): each must print
`[propext, Classical.choice, Quot.sound]` or a subset. -/

open Formalization.SkaModel.SccLoop

#print axioms member_view
#print axioms sweepStep_inv
#print axioms foldl_noany
#print axioms loop_end
#print axioms loop_inv
#print axioms loop_reads
#print axioms loop_left
#print axioms final_member
#print axioms final_keeps
