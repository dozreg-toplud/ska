import lemmas.Run
import lemmas.CueExample
import lemmas.Hoon.PutBy

/-! The axioms behind the main statements.  Run with `lake env lean lemmas/Audit.lean`. -/

open Formalization

#print axioms Nock.evalFuel_sound
#print axioms Nock.nock_eq_some_iff
#print axioms CueExample.cue_words
#print axioms Pill.core_evalFuel
#print axioms Pill.core_layer2
#print axioms Hoon.dec_gate_eval
#print axioms Hoon.lth_gate
#print axioms Hoon.dor_gate
#print axioms Hoon.gor_gate
#print axioms Hoon.mor_gate
#print axioms Hoon.put_by
