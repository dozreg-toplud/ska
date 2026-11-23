import lemmas.Ska.CompFinal

/-!
# Axioms of the theorems about the model of `+comp`

Each should depend on `propext`, `Classical.choice` and `Quot.sound` only.
-/

open Formalization.SkaModel.Comp

#print axioms run_ok
#print axioms run_n0_ok
#print axioms run_n1_done_ok
#print axioms run_n1_pick_ok
#print axioms run_n1_next_ok
#print axioms run_n7_ok
#print axioms run_n4_done_ok
#print axioms run_n4_pick_ok
#print axioms run_n3_pick_ok
#print axioms unary_ok
#print axioms fromSure_spec
#print axioms sureRequireLook_spec
#print axioms medeLoop_spec
#print axioms finish_bellContract
#print axioms finish_compDone
#print axioms bellContract_of_compDoneOn
#print axioms toStraight_entry
#print axioms sim_block
#print axioms execPole_ren
#print axioms renameBlocks_spec
#print axioms holds_of_split
#print axioms needOrdAllocRegs_spec
#print axioms capeAxes_of_fits
#print axioms run_down
#print axioms runDown
#print axioms kernBoth_spec
#print axioms kernLoop_spec
#print axioms sureLoop_spec
#print axioms coerceSpec
#print axioms finish_compDone'
#print axioms finish_bellContract'
#print axioms flatten_needOrdAllocRegs
#print axioms isRun_needOrdAllocRegs
#print axioms doneBlocks_ok
#print axioms run_n3_done_ok
#print axioms collapse_ok
#print axioms run_n4_next_ok
#print axioms forl_ok
#print axioms runOK_n3_of_none
#print axioms run_n3_next_ok
#print axioms run_clean
#print axioms clean_copyNeed
#print axioms copyNeed_spec
#print axioms copy_ok
#print axioms binary_ok
#print axioms run_n5_ok
#print axioms splitLok_looks
#print axioms must_spec
#print axioms splitNeed_spec
#print axioms split_ok
#print axioms cons_next_ok
#print axioms run_cons_ok
