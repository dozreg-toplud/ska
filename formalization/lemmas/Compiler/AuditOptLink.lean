import lemmas.Compiler.OptLinkRub
import lemmas.Compiler.OptLinkDead

/-!
# Axioms of the pill link of the optimizer

Every main theorem of `Compiler/OptLink*.lean` depends on `propext`,
`Classical.choice` and `Quot.sound` only.
-/

open Formalization Compiler

#print axioms rap_keys_nodup
#print axioms blob_toNoun_inj
#print axioms termin_toNoun_inj
#print axioms gj_gate
#print axioms gj_gate_lti
#print axioms jr_gate
#print axioms gr_gate_pole
#print axioms gr_gate_fin
#print axioms gr_gate_lti
#print axioms gs_gate
#print axioms rub_sw
#print axioms rub_step
#print axioms rub_gate
#print axioms blocks_got
#print axioms rdc_inner
#print axioms rdc_trap
#print axioms rdc_gate
