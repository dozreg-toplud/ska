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
import lemmas.Hoon.DifIn
import lemmas.Hoon.ListsMore
import lemmas.Hoon.ListsSort
import lemmas.Hoon.Rip
import lemmas.Hoon.CellCrash
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
import lemmas.Compiler.TreapKey
import lemmas.Compiler.Mi
import lemmas.Compiler.GitMi
import lemmas.Compiler.HeSock
import lemmas.Compiler.RecCall
import lemmas.Compiler.FolLoopLink
import lemmas.Compiler.FolLoopCall
import lemmas.Compiler.SoftSpot
import lemmas.Compiler.FolLoopStep
import lemmas.Compiler.FolLoopMono
import lemmas.Compiler.ResolveLoop
import lemmas.Compiler.FolLoopConv
import lemmas.Compiler.SkaCore
import lemmas.Compiler.SkaArms
import lemmas.Compiler.SkaCull
import lemmas.Compiler.MsgCa
import lemmas.Compiler.SkaRun
import lemmas.Compiler.SkaPass
import lemmas.Compiler.SkaPassLoop
import lemmas.Compiler.SkaAnalyze
import lemmas.Compiler.SkaJointConv
import lemmas.Compiler.SkaCallgraph
import lemmas.Compiler.RegisterFast

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
#print axioms Pill.Cue.cue_pill
#print axioms Assembly.cueRoot
#print axioms Assembly.ovumMold
#print axioms Compiler.eval_mook_not2
#print axioms Assembly.mookOther_of
#print axioms Hoon.dec_gate_cell
#print axioms Hoon.rip_gate_cell
#print axioms Hoon.lent_gate_bad
#print axioms Compiler.eval_rend_cell_tag
#print axioms Compiler.loopN_indep
#print axioms Compiler.loopN_some
#print axioms Compiler.mookOtherTwo_of
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
#print axioms Compiler.FinMap.isMap_toNoun
#print axioms Compiler.FinMap.get_toNoun
#print axioms Compiler.FinMap.mem_tap
#print axioms Compiler.FinMap.mem_rap
#print axioms Compiler.FinMap.putF_toNoun
#print axioms Compiler.FinMap.delF_toNoun
#print axioms Compiler.FinMap.getF_toNoun
#print axioms Compiler.instTreapFinMap
#print axioms Compiler.FinMap.tapList_toNoun
#print axioms Compiler.FinMap.preorder_toNoun
#print axioms Compiler.cape_size_gate
#print axioms Compiler.cape_size_cape
#print axioms Compiler.cape_size_pill
#print axioms Compiler.git_g_gate
#print axioms Compiler.git_g_pill
#print axioms Compiler.mi_gut_gate
#print axioms Compiler.mi_put_gate
#print axioms Compiler.mi_gut_pill
#print axioms Compiler.mi_put_pill
#print axioms Compiler.mi_git_loop
#print axioms Compiler.mi_git_gate
#print axioms Compiler.mi_git_pill
#print axioms Compiler.he_sock_gate
#print axioms Compiler.he_sock_pill
#print axioms Compiler.rc_loop
#print axioms Compiler.recursive_call_gate
#print axioms Compiler.recursive_call_pill
#print axioms Compiler.fol_loop_op1
#print axioms Compiler.fol_loop_op3
#print axioms Compiler.fol_loop_op4
#print axioms Compiler.fol_loop_op7
#print axioms Compiler.fol_loop_op5
#print axioms Compiler.fol_loop_op12
#print axioms Compiler.fol_loop_op8
#print axioms Compiler.fol_loop_op9
#print axioms Compiler.fol_loop_cons
#print axioms Compiler.fol_loop_op0
#print axioms Compiler.fol_loop_op6
#print axioms Compiler.fol_loop_op10
#print axioms Compiler.fol_loop_other
#print axioms Compiler.fol_loop_op11s
#print axioms Compiler.fol_loop_soft
#print axioms Compiler.fol_loop_op11d_plain
#print axioms Compiler.fol_loop_op11d_memo
#print axioms Compiler.fol_loop_op11d_fast
#print axioms Compiler.fol_loop_op11d_spot
#print axioms Compiler.fol_loop_op11d_mean
#print axioms Compiler.fol_loop_op11d
#print axioms Compiler.fol_loop_step
#print axioms Compiler.fol_loop_direct
#print axioms Compiler.fol_loop_op2
#print axioms Compiler.fol_loop_step_all
#print axioms Pill.inlineable.arm_at_ana
#print axioms Compiler.soft_spot_loop
#print axioms Compiler.soft_spot_gate
#print axioms Compiler.softSpotIs_of
#print axioms Compiler.FinMap.putInF_setNoun
#print axioms Compiler.calleePutIs
#print axioms Compiler.fol_loop_step_all'
#print axioms Compiler.folStep_mono
#print axioms Compiler.goIs_patch
#print axioms Compiler.fol_loop_le
#print axioms Compiler.resolve_step
#print axioms Compiler.resolve_le
#print axioms Compiler.resLe_resolveH
#print axioms Compiler.fol_loop_step_allW'
#print axioms Compiler.dirIsW_of
#print axioms Compiler.resolve_stepW
#print axioms Compiler.iterN_le_ev
#print axioms Compiler.ev_complete
#print axioms Compiler.resolveStepH_mono
#print axioms Compiler.anaE_is
#print axioms Compiler.resE_is
#print axioms Compiler.folE_is
#print axioms Compiler.resE_le
#print axioms Compiler.folE_le
#print axioms Compiler.resolve_ge
#print axioms Compiler.fol_loop_ge
#print axioms Compiler.folDecodes
#print axioms Compiler.resolve_below_H
#print axioms Compiler.resInf_below
#print axioms Compiler.resIs_inf
#print axioms Compiler.resolve_iff
#print axioms Compiler.fol_loop_le'
#print axioms Compiler.fol_loop_iff
#print axioms Compiler.stepBridge
#print axioms Compiler.runRest_ana
#print axioms Compiler.runRest_K
#print axioms Compiler.runRest_Ka
#print axioms Compiler.kc_bat_at
#print axioms Compiler.kc_analyze_at
#print axioms Compiler.kc_run_at
#print axioms Compiler.runRest_kc
#print axioms Compiler.above_gate
#print axioms Compiler.pop_gate
#print axioms Compiler.pop_gate'
#print axioms Compiler.dirty_gate
#print axioms Compiler.kids_gate
#print axioms Compiler.sweep_stepW
#print axioms Compiler.sweep_loop_iff
#print axioms Compiler.sweep_gate
#print axioms Compiler.live_stepW
#print axioms Compiler.live_loop_iff
#print axioms Compiler.registerFastIs_of
#print axioms Compiler.resolveStepH_eq
#print axioms Hoon.bif_arm_at
#print axioms Hoon.bif_gate
#print axioms Hoon.dif_in_gate
#print axioms Hoon.bifInF_spec
#print axioms Hoon.difInF_spec
#print axioms Hoon.dif_in
#print axioms Compiler.silt_arm_at
#print axioms Compiler.silt_gate
#print axioms Compiler.silt_setNoun
#print axioms Compiler.dif_setNoun
#print axioms Compiler.setNoun_nil_iff
#print axioms Compiler.preorder_setNoun
#print axioms Compiler.wyt_setNoun
#print axioms Compiler.mold_bunt
#print axioms Compiler.ana_tail
#print axioms Compiler.cull_rep_gate
#print axioms Compiler.cull_rep
#print axioms Compiler.cull_skip
#print axioms Compiler.cull_run
#print axioms Compiler.cull_run_none
#print axioms Compiler.cull_gate
#print axioms Compiler.msg_ca_body_at
#print axioms Compiler.msg_ca_arm_at
#print axioms Compiler.msg_ca_gate
#print axioms Compiler.ska_run_battery_eq
#print axioms Compiler.runEnd_eq
#print axioms Compiler.run_datum
#print axioms Compiler.run_stepW
#print axioms Compiler.run_step
#print axioms Compiler.runTrapRest_ana
#print axioms Compiler.member_stepW
#print axioms Compiler.pass_stepW
#print axioms Compiler.passStepH_eq
#print axioms Compiler.analyze_stepW
#print axioms Compiler.analyzeStepH_eq
#print axioms Compiler.sweep_batteryW
#print axioms Compiler.cull_runW
#print axioms Compiler.kc_dirty_at
#print axioms Compiler.mold_arm_at
#print axioms Compiler.mold_bat_bunt
#print axioms Compiler.bunt_W
#print axioms Compiler.E_far
#print axioms Compiler.E_le_nock
#print axioms Compiler.E_complete
#print axioms Compiler.cull_run_noneW
#print axioms Compiler.cull_E
#print axioms Compiler.lvIs
#print axioms Compiler.analyzeStepH_le
#print axioms Compiler.passStepH_le
#print axioms Compiler.lv_below
#print axioms Compiler.lv_above
#print axioms Compiler.nock_iff_levels
#print axioms Compiler.analyze_iff
#print axioms Compiler.ska_run_iff
#print axioms Compiler.pass_loop_iff
#print axioms Compiler.member_loop_iff
#print axioms Compiler.fol_loop_iff_full
#print axioms Compiler.resolve_iff_full
#print axioms Compiler.cg_battery_eq
#print axioms Compiler.cg_run
#print axioms Compiler.cg_print
#print axioms Compiler.ska_callgraph_iff
