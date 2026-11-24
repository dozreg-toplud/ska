import lemmas.Compiler.OptLinkRub
import lemmas.Compiler.OptLinkDead
import lemmas.Compiler.OptLinkRev
import lemmas.Compiler.OptLinkTopo
import lemmas.Compiler.OptLinkHops
import lemmas.Compiler.OptLinkMiddle
import lemmas.Compiler.OptLinkMiddleGate
import lemmas.Compiler.OptLinkMiddleRd
import lemmas.Compiler.OptLinkNoLti
import lemmas.Compiler.OptLinkSy
import lemmas.Compiler.OptLinkOnce
import lemmas.Compiler.OptLinkOnceGate
import lemmas.Compiler.OptLinkOpt
import lemmas.Hoon.UnoBy

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
#print axioms jar_add
#print axioms jar_get
#print axioms roll_gate_list
#print axioms rev_rgate
#print axioms rev_step
#print axioms rev_gate
#print axioms roll_gate_rel
#print axioms saw_put
#print axioms bb_trap
#print axioms bb_gate
#print axioms rh_segt
#print axioms rh_done
#print axioms rh_trap
#print axioms rh_step
#print axioms rh_gate
#print axioms pole_bunt
#print axioms rj_gate
#print axioms saw_del
#print axioms rem_subt
#print axioms rem_pass
#print axioms rem_levyg
#print axioms rhop_gate
#print axioms rep_gate_fwd
#print axioms rem_sw
#print axioms rem_rest
#print axioms rem_step
#print axioms rem_gate_of
#print axioms rep_gate_rel
#print axioms jug_put
#print axioms rd_step
#print axioms rd_rep
#print axioms any_gate_tr
#print axioms rd_readers
#print axioms rem_gate
#print axioms noLti_rub
#print axioms noLti_mid
#print axioms noLti_dead
#print axioms noLti_hops
#print axioms sy_arm
#print axioms si_gate
#print axioms oo_loop
#print axioms structLoop_noLti
#print axioms skim_has
#print axioms ooAfter_cut
#print axioms skim_arm
#print axioms oo_s0
#print axioms oo_alias
#print axioms oo_skimrev
#print axioms oo_trimdead
#print axioms oo_hops
#print axioms oo_rub
#print axioms oo_rem
#print axioms oo_fin
#print axioms oo_pre
#print axioms oo_gate
#print axioms optimizeOnce_noLti
#print axioms opt_at
#print axioms sw_at
#print axioms opt_loop
#print axioms opt_gate
#print axioms Hoon.uno_at
#print axioms Hoon.uno_loop
#print axioms Hoon.look_get
#print axioms Hoon.unoByP_of_maps
#print axioms Hoon.uno_by
