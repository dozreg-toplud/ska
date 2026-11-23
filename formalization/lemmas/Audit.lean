import lemmas.Run
import lemmas.CueExample
import lemmas.Hoon.PutBy
import lemmas.Hoon.Lists
import lemmas.Hoon.Sets
import lemmas.Hoon.Bits
import lemmas.Hoon.Layer2
import lemmas.Hoon.Axis
import lemmas.Hoon.Apt
import lemmas.Hoon.TapIn
import lemmas.Hoon.DelBy
import lemmas.Hoon.GasBy
import lemmas.Hoon.RepBy
import lemmas.Hoon.JabBy
import lemmas.Hoon.Ju
import lemmas.Hoon.MapFolds
import lemmas.Hoon.SetFolds
import lemmas.Hoon.ListsMore
import lemmas.Compiler.Ca
import lemmas.Compiler.So

/-! The axioms behind the main statements.  Run with `lake env lean lemmas/Audit.lean`. -/

open Formalization

#print axioms Nock.evalFuel_sound
#print axioms Nock.nock_eq_some_iff
#print axioms CueExample.cue_words
#print axioms Pill.core_evalFuel
#print axioms Pill.core_layer2
#print axioms Hoon.dec_gate_eval
#print axioms Hoon.dec_gate_zero_eval
#print axioms Hoon.add_gate
#print axioms Hoon.sub_gate
#print axioms Hoon.sub_gate_lt
#print axioms Hoon.mul_gate
#print axioms Hoon.lth_gate
#print axioms Hoon.lte_gate
#print axioms Hoon.gte_gate
#print axioms Hoon.gth_gate
#print axioms Hoon.max_gate
#print axioms Hoon.min_gate
#print axioms Hoon.dvr_gate
#print axioms Hoon.div_gate
#print axioms Hoon.mod_gate
#print axioms Hoon.div_gate_zero
#print axioms Hoon.mod_gate_zero
#print axioms Hoon.arith_layer1
#print axioms Hoon.dor_gate
#print axioms Hoon.gor_gate
#print axioms Hoon.mor_gate
#print axioms Hoon.put_by
#print axioms Hoon.lent_gate
#print axioms Hoon.weld_gate
#print axioms Hoon.flop_gate
#print axioms Hoon.snag_gate
#print axioms Hoon.snag_gate_none
#print axioms Hoon.scag_gate
#print axioms Hoon.slag_gate
#print axioms Hoon.turn_gate
#print axioms Hoon.roll_gate
#print axioms Hoon.levy_gate
#print axioms Hoon.lien_gate
#print axioms Hoon.get_by
#print axioms Hoon.has_by
#print axioms Hoon.put_in
#print axioms Hoon.has_in
#print axioms Hoon.bex_gate
#print axioms Hoon.lsh_gate
#print axioms Hoon.rsh_gate
#print axioms Hoon.end_gate
#print axioms Hoon.met_gate
#print axioms Hoon.cut_gate
#print axioms Hoon.cat_gate
#print axioms Hoon.mix_gate
#print axioms Hoon.dis_gate
#print axioms Hoon.con_gate
#print axioms Hoon.can_gate
#print axioms Hoon.sit_gate
#print axioms Hoon.sum_gate
#print axioms Hoon.rol_gate
#print axioms Hoon.muk_gate
#print axioms Hoon.mug_spec
#print axioms Hoon.mug_layer2
#print axioms Hoon.gor_pill
#print axioms Hoon.mor_pill
#print axioms Hoon.put_by_pill
#print axioms Hoon.get_by_pill
#print axioms Hoon.has_by_pill
#print axioms Hoon.put_in_pill
#print axioms Hoon.has_in_pill
#print axioms Hoon.need_gate
#print axioms Hoon.got_by
#print axioms Hoon.gut_by
#print axioms Hoon.cap_gate
#print axioms Hoon.mas_gate
#print axioms Hoon.peg_gate
#print axioms Hoon.slot_pegF
#print axioms Hoon.slot_cap_mas
#print axioms Hoon.apt_loop
#print axioms Hoon.apt_by
#print axioms Hoon.tap_by
#print axioms Hoon.tap_in
#print axioms Hoon.del_by
#print axioms Hoon.gas_by
#print axioms Hoon.rep_tree
#print axioms Hoon.jab_by
#print axioms Hoon.ju_get
#print axioms Hoon.ju_put
#print axioms Hoon.ju_has_gate
#print axioms Hoon.ja_add_gate
#print axioms Hoon.ju_gas_loop
#print axioms Hoon.key_by
#print axioms Hoon.run_by
#print axioms Hoon.any_by_loop
#print axioms Hoon.anyByF_spec
#print axioms Hoon.gas_in
#print axioms Hoon.any_in_loop
#print axioms Hoon.anyInF_spec
#print axioms Hoon.run_in_loop
#print axioms Hoon.runInF_spec
#print axioms Hoon.del_in
#print axioms Hoon.ju_del_gate
#print axioms Hoon.skim_gate
#print axioms Hoon.skip_gate
#print axioms Hoon.murn_gate
#print axioms Hoon.rear_gate
#print axioms Hoon.snip_gate
#print axioms Compiler.ca_hed_gate
#print axioms Compiler.ca_tel_gate
#print axioms Compiler.ca_con_gate
#print axioms Compiler.ca_all_gate
#print axioms Compiler.ca_int_gate
#print axioms Compiler.ca_uni_gate
#print axioms Compiler.ca_lack_gate
#print axioms Compiler.so_hed_gate
#print axioms Compiler.so_tel_gate
#print axioms Compiler.so_jibe_gate
