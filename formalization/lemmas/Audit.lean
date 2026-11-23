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
import lemmas.Hoon.ListsSort
import lemmas.Hoon.Rip
import lemmas.Compiler.Ca
import lemmas.Compiler.So
import lemmas.Compiler.Axes
import lemmas.Compiler.Lib
import lemmas.Compiler.MinkPill
import lemmas.Compiler.MockPill
import lemmas.Compiler.PiEdit
import lemmas.Compiler.Inlineable
import lemmas.Compiler.Safe
import lemmas.Compiler.Anno
import lemmas.Compiler.Regs
import lemmas.Compiler.EvalPass
import lemmas.Compiler.EvalPole
import lemmas.Compiler.TreapList
import lemmas.Compiler.EvalCall
import lemmas.Compiler.EvalConv
import lemmas.Compiler.EvalRend
import lemmas.Compiler.Connect
import lemmas.Compiler.PokeFrame
import lemmas.Assembly

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
#print axioms Hoon.welp_gate
#print axioms Hoon.zing_gate
#print axioms Hoon.snoc_gate
#print axioms Hoon.skid_gate
#print axioms Hoon.sort_gate
#print axioms Hoon.qsort_perm
#print axioms Hoon.spin_gate
#print axioms Hoon.biff_gate_nil
#print axioms Hoon.biff_gate_some
#print axioms Hoon.wyt_by
#print axioms Hoon.wyt_in
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
#print axioms Compiler.so_knit_gate
#print axioms Compiler.so_purr_gate
#print axioms Compiler.ca_app_gate
#print axioms Compiler.so_pull_gate
#print axioms Compiler.ca_pat_gate
#print axioms Compiler.ca_lot_gate
#print axioms Compiler.ca_yea_gate
#print axioms Compiler.so_darn_gate
#print axioms Compiler.capF_eq_cap
#print axioms Compiler.masF_eq_mas
#print axioms Compiler.ca_dif_gate
#print axioms Compiler.so_huge_gate
#print axioms Compiler.caIn_pill
#print axioms Compiler.soIn_pill
#print axioms Compiler.ca_int_pill
#print axioms Compiler.ca_uni_pill
#print axioms Compiler.ca_lack_pill
#print axioms Compiler.ca_dif_pill
#print axioms Compiler.ca_app_pill
#print axioms Compiler.ca_pat_pill
#print axioms Compiler.ca_lot_pill
#print axioms Compiler.ca_yea_pill
#print axioms Compiler.so_knit_pill
#print axioms Compiler.so_purr_pill
#print axioms Compiler.so_pull_pill
#print axioms Compiler.so_darn_pill
#print axioms Nock.nock_eq_nockW
#print axioms Nock.iterN_sound
#print axioms Nock.iterN_complete
#print axioms Hoon.mink_frag_gate
#print axioms Hoon.mink_edit_gate
#print axioms Compiler.mink_loop_unfold
#print axioms Compiler.nstep_exact
#print axioms Compiler.mink_gate_iff
#print axioms Compiler.mink_gate_of_model
#print axioms Compiler.mink_gate_to_model
#print axioms Compiler.mink_pill_iff
#print axioms Compiler.mink_pill_call
#print axioms Compiler.monk_gate_iff
#print axioms Compiler.mack_gate_iff
#print axioms Compiler.monk_pill_iff
#print axioms Compiler.mack_pill_iff
#print axioms Hoon.turn_gate_mapM
#print axioms Compiler.mook_skip
#print axioms Compiler.rend_mean
#print axioms Compiler.rend_frame_iff
#print axioms Compiler.mook_gate_iff
#print axioms Compiler.mock_gate_iff
#print axioms Compiler.mook_pill_iff
#print axioms Compiler.mock_pill_iff
#print axioms Hoon.rip_gate
#print axioms Compiler.rend_leaf
#print axioms Compiler.rend_hand
#print axioms Compiler.rendBaseIs_of
#print axioms Compiler.rendBaseIs_layer4
#print axioms Compiler.pi_cons_gate
#print axioms Compiler.pi_hed_gate
#print axioms Compiler.pi_tel_gate
#print axioms Compiler.pi_slot_gate
#print axioms Compiler.pi_hed_pill
#print axioms Compiler.pi_tel_pill
#print axioms Compiler.pi_slot_pill
#print axioms Compiler.pegF_eq_peg
#print axioms Compiler.pi_compose_gate
#print axioms Compiler.pi_compose_pill
#print axioms Compiler.pi_edit_up
#print axioms Compiler.pi_edit_down
#print axioms Compiler.pi_edit_gate
#print axioms Compiler.distribute_gate
#print axioms Compiler.pi_prune_gate
#print axioms Compiler.double_int_gate'
#print axioms Compiler.pi_edit_pill
#print axioms Compiler.pi_prune_pill
#print axioms Compiler.distribute_pill
#print axioms Compiler.double_int_pill
#print axioms Compiler.inlineable_gate'
#print axioms Compiler.safe_nomm_gate
#print axioms Compiler.safe_fol_fol_gate
#print axioms Compiler.safe_nomm_pill
#print axioms Compiler.safe_fol_fol_pill
#print axioms Compiler.knit_anno_gate
#print axioms Compiler.patch_prod_gate
#print axioms Compiler.msg_sock_gate
#print axioms Compiler.msg_anno_gate'
#print axioms Compiler.knit_anno_pill
#print axioms Compiler.patch_prod_pill
#print axioms Compiler.msg_sock_pill
#print axioms Compiler.msg_anno_pill
#print axioms Compiler.TreapMap.get_put
#print axioms Compiler.TreapMap.get_del
#print axioms Compiler.read_pill
#print axioms Compiler.store_pill
#print axioms Compiler.move_pill
#print axioms Compiler.eval_pass_pill
#print axioms Compiler.eval_pole_local
#print axioms Compiler.eval_pole_local_pill
#print axioms Hoon.isMap_ext
#print axioms Hoon.isSet_ext
#print axioms Hoon.tapList_pairwise
#print axioms Hoon.tapList_unique
#print axioms Hoon.preorder_ext
#print axioms Compiler.TreapMap.ext
#print axioms Compiler.TreapMap.mem_tap
#print axioms Compiler.TreapMap.mem_rap
#print axioms Compiler.TreapMap.tap_pairwise
#print axioms Compiler.eval_pole_gate
#print axioms Compiler.eval_pole_le
#print axioms Compiler.eval_blob_jmp_le
#print axioms Compiler.eval_blob_jsp_le
#print axioms Compiler.eval_blob_le
#print axioms Compiler.eval_top_le
#print axioms Compiler.interp_le
#print axioms Compiler.eval_top_of_model
#print axioms Compiler.interp_ge
#print axioms Compiler.eval_top_to_model
#print axioms Compiler.eval_top_iff
#print axioms Compiler.bell_ofNoun_toNoun
#print axioms Compiler.eval_rend_le
#print axioms Compiler.eval_rend_ge
#print axioms Compiler.eval_mook_le
#print axioms Compiler.eval_mook_ge
#print axioms Compiler.eval_mook_iff
#print axioms Compiler.axes_agree
#print axioms Compiler.core_layer4
#print axioms Compiler.core_shape
#print axioms Compiler.top_iff
#print axioms Compiler.mook_iff
#print axioms Compiler.run_iff
#print axioms Compiler.mock_iff
#print axioms Compiler.corIn_of_tail
#print axioms Compiler.pokeIs_of_frame
#print axioms Assembly.poke_iff
#print axioms Assembly.reach_model
#print axioms Assembly.meek_of
#print axioms Assembly.weak_of
#print axioms Assembly.converse_of
#print axioms Assembly.halts_of
#print axioms Assembly.full_of
#print axioms Frame.absNock_sound
#print axioms Compiler.poke_frame
#print axioms Compiler.pokeReach_frame
#print axioms Compiler.pokeFrame_corIn
#print axioms Compiler.listMoldIs
#print axioms Compiler.pokeDireBad
