import lemmas.Compiler.OptLinkAlWalkGate

/-! `#print axioms` of the main theorems of phases 15 and 16 of `+alias`.
`al_body_link` (`OptLinkAlWalkBody.lean`) cannot be imported beside these
(`alRnArm` and `alBat_rn` are declared in both `OptLinkAlBody.lean` and
`OptLinkAlFin.lean`); its axioms are those of `al_body_gen`. -/

open Formalization Compiler

#print axioms al_tail
#print axioms store_put
#print axioms al_reach_comp
#print axioms al_walk_step
#print axioms al_turn
#print axioms al_walk
#print axioms al_gate
#print axioms al_link
#print axioms opt_gate_alias
