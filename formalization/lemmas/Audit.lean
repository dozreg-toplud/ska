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
import lemmas.Hoon.UniIn
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
import lemmas.Compiler.SkaPrune
import lemmas.Compiler.SkaPoke
import lemmas.Compiler.RoadPure
import lemmas.Compiler.RegisterFast
import lemmas.Compiler.FrameCall
import lemmas.Compiler.RegisterFastShape
import lemmas.Compiler.CompGen
import lemmas.Compiler.CompDoor
import lemmas.Compiler.CompSet
import lemmas.Compiler.CompFrom
import lemmas.Compiler.CompSplit
import lemmas.Compiler.CompInto
import lemmas.Compiler.CompForlLink
import lemmas.Compiler.CompCopyLink
import lemmas.Compiler.CompMedeLink
import lemmas.Compiler.CompCtx
import lemmas.Compiler.CompClaLink
import lemmas.Compiler.CompRunLink
import lemmas.Compiler.CompPastLink
import lemmas.Compiler.CompRunInv
import lemmas.Compiler.CompRunCases
import lemmas.Compiler.CompRunCons
import lemmas.Compiler.CompRunAll
import lemmas.Compiler.CompUnary
import lemmas.Compiler.CompKernLink
import lemmas.Compiler.CompKernNeed
import lemmas.Compiler.CompKerfLink
import lemmas.Compiler.CompUnaryEnd
import lemmas.Compiler.CompUnaryTop
import lemmas.Compiler.CompStraightPre
import lemmas.Compiler.CompStraightCore
import lemmas.Compiler.CompMapRegs
import lemmas.Compiler.CompChase
import lemmas.Compiler.CompChaseFin
import lemmas.Compiler.CompStraightStep
import lemmas.Compiler.CompLift
import lemmas.Compiler.CompUnaryTrap
import lemmas.Compiler.CompSccIn
import lemmas.Compiler.CompStraightN
import lemmas.Compiler.CompCoerceLazy
import lemmas.Compiler.CompBakeNeed
import lemmas.Compiler.CompFinish
import lemmas.Compiler.CompSureOf
import lemmas.Compiler.CompMember
import lemmas.Compiler.CompMemberGate
import lemmas.Compiler.CompSccGate
import lemmas.Hoon.RollUni
import lemmas.Compiler.CompInlined
import lemmas.Compiler.CompShapeCol
import lemmas.Hoon.IntIn
import lemmas.Hoon.UniBy
import lemmas.Compiler.CompSccOne
import lemmas.Compiler.CompMemOld
import lemmas.Compiler.CompNoNN
import lemmas.Compiler.CompRunCall
import lemmas.Compiler.CompSccCall
import lemmas.Compiler.CompSccCallGate
import lemmas.Compiler.CompPruneLink
import lemmas.Compiler.CompCopyGen
import lemmas.Compiler.CompSplitGen
import lemmas.Compiler.CompIntoGen
import lemmas.Compiler.CompFromGen
import lemmas.Compiler.CompClaGen
import lemmas.Compiler.CompRunInvL
import lemmas.Compiler.CompCopyAll
import lemmas.Compiler.CompRunAllL
import lemmas.Compiler.CompRunTags
import lemmas.Compiler.CompCoerceLazyGen

/-! The axioms behind the main statements.  Run with `lake env lean lemmas/Audit.lean`. -/

open Formalization

#print axioms Nock.evalFuel_sound
#print axioms Nock.nock_eq_some_iff
#print axioms Nock.evalFuel_soundA
#print axioms Nock.EvalA.toEval
#print axioms Nock.Eval.deterministic
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
#print axioms Hoon.uni_in_gate
#print axioms Hoon.uni_in
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
#print axioms Compiler.prune_loop_iff
#print axioms Compiler.prune_gate_iff
#print axioms Compiler.mfe_gate
#print axioms Compiler.pj_gate
#print axioms Compiler.pj_rep
#print axioms Compiler.pj_trap
#print axioms Compiler.sp_chain
#print axioms Compiler.ska_poke_ana_iff
#print axioms Compiler.sp_bat_run
#print axioms Compiler.rp_mean_none
#print axioms Compiler.rp_mock_cases
#print axioms Compiler.rp_mute_cases
#print axioms Compiler.rp_mule_cases
#print axioms Compiler.rp_run_iff
#print axioms Compiler.ska_poke_gate_iff
#print axioms Compiler.sp_trap_evalH
#print axioms Compiler.ska_poke_iff
#print axioms Compiler.evalH_of_minkF_nil
#print axioms Compiler.ska_poke_iff_evalH
#print axioms FrameCall.absNockS_sound
#print axioms Compiler.rf_summ_ok
#print axioms Compiler.rf_main_ok
#print axioms Compiler.registerFastShape
#print axioms Compiler.registerFastIs_pill
#print axioms Compiler.ska_poke_ana_iff_pill
#print axioms Compiler.re_noun
#print axioms Compiler.oo_noun
#print axioms Compiler.id_noun
#print axioms Compiler.comp_re
#print axioms Compiler.comp_oo
#print axioms Compiler.comp_id
#print axioms Compiler.comp_dropping
#print axioms Compiler.comp_emir
#print axioms Compiler.comp_set_tag
#print axioms Compiler.comp_add_ops
#print axioms Compiler.comp_emit
#print axioms Compiler.comp_bomb
#print axioms Compiler.comp_must
#print axioms Compiler.comp_split_need
#print axioms Compiler.comp_copy_tag
#print axioms Compiler.comp_drop_at
#print axioms Compiler.csHoonSet
#print axioms Compiler.cs_preorder
#print axioms Compiler.cs_runInF
#print axioms Compiler.cs_run_in_gate_on
#print axioms Compiler.comp_from_sure
#print axioms Compiler.comp_from
#print axioms Compiler.ss_gate
#print axioms Compiler.ss_splitLok
#print axioms Compiler.comp_split_sure
#print axioms Compiler.csp_loop
#print axioms Compiler.comp_split
#print axioms Compiler.gep_gate
#print axioms Compiler.cn_gate
#print axioms Compiler.inn_loop
#print axioms Compiler.comp_into_need
#print axioms Compiler.is_gate
#print axioms Compiler.comp_into_sure
#print axioms Compiler.cit_loop
#print axioms Compiler.comp_into
#print axioms Compiler.comp_forl
#print axioms Compiler.comp_flatten_need
#print axioms Compiler.cnm_seg
#print axioms Compiler.comp_copy_need
#print axioms Compiler.cs_uni_is
#print axioms Compiler.comp_copy_lazy
#print axioms Compiler.comp_copy
#print axioms Compiler.comp_crash_need
#print axioms Compiler.comp_walk_lazy
#print axioms Compiler.md_loop
#print axioms Compiler.md_gate
#print axioms Compiler.comp_mede
#print axioms Compiler.comp_proxy
#print axioms Compiler.comp_lazy_bound
#print axioms Compiler.srl_loop
#print axioms Compiler.srl_gate
#print axioms Compiler.comp_sure_require_look
#print axioms Compiler.comp_insert_hop
#print axioms Compiler.comp_ctx_pill
#print axioms Compiler.comp_ctx_cor
#print axioms Compiler.cs_small_cases
#print axioms Compiler.ne_gate
#print axioms Compiler.cla_gate
#print axioms Compiler.comp_collapse_lazy_atom
#print axioms Compiler.comp_run_at
#print axioms Compiler.comp_simple_next
#print axioms Compiler.comp_run_n0
#print axioms Compiler.comp_run_n7
#print axioms Compiler.comp_run_n1
#print axioms Compiler.hd_gate
#print axioms Compiler.compK_hd
#print axioms Compiler.comp_past_at
#print axioms Compiler.pa_test
#print axioms Compiler.comp_past
#print axioms Compiler.ct_lfr_gate
#print axioms Compiler.comp_run_n4
#print axioms Compiler.ct_lfn_gate
#print axioms Compiler.comp_run_n3
#print axioms Compiler.cr5_eq
#print axioms Compiler.cr5_tail
#print axioms Compiler.cr5_br
#print axioms Compiler.comp_run_n5
#print axioms Compiler.cr10_eq
#print axioms Compiler.cr10_tail
#print axioms Compiler.comp_run_n10
#print axioms Compiler.crc_eq
#print axioms Compiler.cr_split_at
#print axioms Compiler.crc_ntail
#print axioms Compiler.crc_pick
#print axioms Compiler.crc_next
#print axioms Compiler.crc_done_step
#print axioms Compiler.crc_split_lok
#print axioms Compiler.comp_run_cons
#print axioms Compiler.cra_copy_lok
#print axioms Compiler.cra_into_lok
#print axioms Compiler.cra_run_lok
#print axioms Compiler.comp_run_all'
#print axioms Compiler.comp_run_entry
#print axioms Compiler.cri_copy
#print axioms Compiler.cri_split
#print axioms Compiler.cri_into
#print axioms Compiler.cr5_br_keeps
#print axioms Compiler.cu_entry_noun
#print axioms Compiler.cu_entry_step
#print axioms Compiler.cu_entry_run
#print axioms Compiler.cu_bunt_at
#print axioms Compiler.comp_kn_at
#print axioms Compiler.kernLoop_suf
#print axioms Compiler.kn_at
#print axioms Compiler.kn_both
#print axioms Compiler.comp_kern_need
#print axioms Compiler.kern_gate
#print axioms Compiler.comp_kern
#print axioms Compiler.comp_kerf
#print axioms Compiler.cu_rp_iff
#print axioms Compiler.cu_run_kerf
#print axioms Compiler.comp_ts_at
#print axioms Compiler.cu_kern_cond
#print axioms Compiler.cu_cond_empty
#print axioms Compiler.cu_finish
#print axioms Compiler.ts_pre
#print axioms Compiler.ts_at_of_core
#print axioms Compiler.cu_finish_core
#print axioms Compiler.ts_ren
#print axioms Compiler.ts_rer
#print axioms Compiler.ts_dol
#print axioms Compiler.ts_ri_model
#print axioms Compiler.mr_slam
#print axioms Compiler.ts_rename
#print axioms Compiler.rep_gate_list
#print axioms Compiler.renameBlocks_rap
#print axioms Compiler.ts_core_at
#print axioms Compiler.ts_at_of_step
#print axioms Compiler.cu_finish_step
#print axioms Compiler.ts_byp
#print axioms Compiler.kn_suf_eq
#print axioms Compiler.mr_inner_eq
#print axioms Compiler.mr_turn_ren
#print axioms Compiler.mr_op
#print axioms Compiler.mr_turn_ops
#print axioms Compiler.mr_inner_bom
#print axioms Compiler.ts_byp_gen
#print axioms Compiler.ts_chase_at
#print axioms Compiler.ch_stepW
#print axioms Compiler.ch_loop_of_chase
#print axioms Compiler.ch_chase_of_loop
#print axioms Compiler.ch_nock
#print axioms Compiler.ts_cf_at
#print axioms Compiler.ch_gate
#print axioms Compiler.cf_chase_cell
#print axioms Compiler.cf_gate
#print axioms Compiler.ts_st_cf
#print axioms Compiler.ts_step
#print axioms Compiler.ts_step_at
#print axioms Compiler.cu_finish_rj
#print axioms Compiler.lf_bind
#print axioms Compiler.lf_inner
#print axioms Compiler.lf_turn
#print axioms Compiler.lf_rj
#print axioms Compiler.lf_mr_rj
#print axioms Compiler.lf_ts_rj
#print axioms Compiler.cu_finish_all
#print axioms Compiler.cu_trap_entry
#print axioms Compiler.cu_trap_run
#print axioms Compiler.cu_trap_kerf
#print axioms Compiler.cu_trap_end
#print axioms Compiler.cu_trap
#print axioms Compiler.cu_gate_rp
#print axioms Compiler.cu_gate
#print axioms Compiler.cu_ref_mono
#print axioms Compiler.cu_gate_some
#print axioms Compiler.sd_empty
#print axioms Compiler.sd_drop
#print axioms Compiler.nta_gate
#print axioms Compiler.noar_gate
#print axioms Compiler.cs_gate
#print axioms Compiler.mr_inner
#print axioms Compiler.mr_inner_ren
#print axioms Compiler.tsn_run
#print axioms Compiler.tsn_pre
#print axioms Compiler.tsn_ren
#print axioms Compiler.tsn_ri_trap
#print axioms Compiler.tsn_dol
#print axioms Compiler.ca_gate
#print axioms Compiler.tsn_step_gen
#print axioms Compiler.tsn_core
#print axioms Compiler.tsn_at
#print axioms Compiler.aic_gate
#print axioms Compiler.ain_gate
#print axioms Compiler.cz_gate_step
#print axioms Compiler.cz_lok
#print axioms Compiler.cz_srl
#print axioms Compiler.cz_loop
#print axioms Compiler.cz_gate
#print axioms Compiler.cz_gate_L
#print axioms Compiler.needNorm_noar
#print axioms Compiler.bn_test
#print axioms Compiler.bn_loop
#print axioms Compiler.bn_gate
#print axioms Compiler.finishLF_tail
#print axioms Compiler.fin_gate
#print axioms Compiler.fin_gate_finishLF
#print axioms Compiler.fin_bak
#print axioms Compiler.fin_after_cs
#print axioms Compiler.cn_gate_ord
#print axioms Compiler.i2_trap
#print axioms Compiler.i2_gate_step
#print axioms Compiler.i2_rep
#print axioms Compiler.i2_gate
#print axioms Compiler.so_gate
#print axioms Compiler.mem_at
#print axioms Compiler.mem_entry
#print axioms Compiler.mem_r3
#print axioms Compiler.mem_res
#print axioms Compiler.mem_run_call
#print axioms Compiler.mem_cs_call
#print axioms Compiler.mem_bak_call
#print axioms Compiler.mem_sur_call
#print axioms Compiler.mem_tuple_call
#print axioms Compiler.mem_final
#print axioms Compiler.mem_after
#print axioms Compiler.mem_prod_new
#print axioms Compiler.mem_mode_noop
#print axioms Compiler.mem_to_finish
#print axioms Compiler.mem_rest_slots
#print axioms Compiler.mem_cond_frag
#print axioms Compiler.mem_laz_frag
#print axioms Compiler.mem_gate
#print axioms Hoon.roll_loop_M
#print axioms Hoon.roll_gate_M
#print axioms Hoon.roll_gate_one
#print axioms Hoon.uni_by_arm
#print axioms Compiler.csi_at
#print axioms Compiler.bell_bunt
#print axioms Compiler.juIn_layer2
#print axioms Compiler.csi_to_final
#print axioms Compiler.csi_final_one
#print axioms Compiler.csi_gate_one
#print axioms Compiler.csi_arm
#print axioms Compiler.cu_csi_eq
#print axioms Compiler.cu_gate_scc_one
#print axioms Compiler.inl_body_at
#print axioms Compiler.inlBody_eq
#print axioms Compiler.inline_off_at
#print axioms Compiler.inl_trap_pure
#print axioms Compiler.inl_gate_miss
#print axioms Compiler.inl_gate_hit
#print axioms Compiler.inl_gate
#print axioms Compiler.uno_at
#print axioms Compiler.l2i_at
#print axioms Compiler.fr_at
#print axioms Compiler.oi_at
#print axioms Compiler.ic_at
#print axioms Compiler.scBody_eq
#print axioms Compiler.i2n_bunt
#print axioms Compiler.fr_bunt_at
#print axioms Compiler.fr_bunt2_at
#print axioms Compiler.uno_none
#print axioms Compiler.l2i_gate_sure
#print axioms Compiler.roll_gate_nil
#print axioms Compiler.fr_gate_nofork
#print axioms Compiler.oi_gate_nofork
#print axioms Compiler.ic_gate_nofork
#print axioms Compiler.sc_gate_sure
#print axioms Compiler.hsc_of_sure
#print axioms Hoon.int_in_arm
#print axioms Hoon.int_loop_nil
#print axioms Hoon.int_in_nil
#print axioms Hoon.rep_loop_nil
#print axioms Hoon.rep_gate_one
#print axioms Hoon.uni_by_loop
#print axioms Hoon.uni_by_gate
#print axioms Hoon.uniSpec_kin
#print axioms Hoon.uniBy_same
#print axioms Hoon.uniBy_domA
#print axioms Hoon.uniBy_domB
#print axioms Hoon.uniBy_step
#print axioms Hoon.uniByP_of_maps
#print axioms Hoon.uni_by
#print axioms Hoon.uni_by_one
#print axioms Compiler.csi_kids_nocalls
#print axioms Compiler.ju_has_kids
#print axioms Compiler.csi_final_one_none
#print axioms Compiler.cu_gate_none
#print axioms Compiler.getF_of_putF
#print axioms Compiler.sureOf_some
#print axioms Compiler.scc_sur_frag
#print axioms Compiler.csi_gate_scc_one_m
#print axioms Compiler.cu_gate_scc_one_m
#print axioms Compiler.mem_final_run_none
#print axioms Compiler.mem_final_cs_none
#print axioms Compiler.mem_gate_none
#print axioms Compiler.csi_gate_scc_one_f
#print axioms Compiler.cu_gate_scc_one_f
#print axioms Compiler.csiHit_gate
#print axioms Compiler.csi_hit_gate
#print axioms Compiler.csi_hit
#print axioms Compiler.csi_hit_one
#print axioms Compiler.cu_gate_hit
#print axioms Compiler.msg_at
#print axioms Compiler.msg_arm
#print axioms Compiler.msg_eq
#print axioms Compiler.mem_prod_old
#print axioms Compiler.mem_gate_old
#print axioms Hoon.uni_in_arm
#print axioms Hoon.int_loop
#print axioms Hoon.int_in_gate
#print axioms Hoon.int_uni
#print axioms Hoon.intP_mor
#print axioms Hoon.intP_step
#print axioms Hoon.intP_of_sets
#print axioms Hoon.int_in
#print axioms Compiler.noSelfCall_of_noCalls
#print axioms Compiler.isSet_setOne
#print axioms Compiler.csi_kids_noself
#print axioms Compiler.crx_copy_args
#print axioms Compiler.crx_bomb_args
#print axioms Compiler.crx_sn_args
#print axioms Compiler.crx_run_args
#print axioms Compiler.args_frag
#print axioms Compiler.nn_consNeed
#print axioms Compiler.needToOrd_none
#print axioms Compiler.nno_needToOrd
#print axioms Compiler.nno_consOrd
#print axioms Compiler.nno_halves
#print axioms Compiler.nno_rebuild
#print axioms Compiler.nno_sureLook
#print axioms Compiler.nno_sureOf
#print axioms Compiler.noar_nno
#print axioms Compiler.nn_fromPath
#print axioms Compiler.nn_must
#print axioms Compiler.nn_splitNeed
#print axioms Compiler.nn_copyNeed
#print axioms Compiler.nn_rollTack
#print axioms Compiler.nn_intoLoop
#print axioms Compiler.nn_into
#print axioms Compiler.nn_split
#print axioms Compiler.nn_copy
#print axioms Compiler.nn_bomb
#print axioms Compiler.nn_sn
#print axioms Compiler.nn_from
#print axioms Compiler.nn_run
#print axioms Compiler.noar_frag
#print axioms Compiler.noBake_no
#print axioms Compiler.cu_gate_scc_one_no
#print axioms Compiler.crc_of_pure
#print axioms Compiler.crr_pure
#print axioms Compiler.crf_copy_ok
#print axioms Compiler.crf_copy_out
#print axioms Compiler.cr2_eq
#print axioms Compiler.cr2_ind
#print axioms Compiler.cr2_tail
#print axioms Compiler.cr2_kf
#print axioms Compiler.comp_run_n2
#print axioms Compiler.comp_run_n4C
#print axioms Compiler.comp_run_n3C
#print axioms Compiler.comp_run_n7C
#print axioms Compiler.indOk_of_pure
#print axioms Compiler.crf_run
#print axioms Compiler.comp_run_all_c
#print axioms Compiler.comp_run_entry_c
#print axioms Compiler.cr5_tailC
#print axioms Compiler.cr5_modelC
#print axioms Compiler.comp_run_n5C
#print axioms Compiler.crx_run
#print axioms Compiler.cfr_run
#print axioms Compiler.mem_cond_frag_c
#print axioms Compiler.mem_laz_frag_c
#print axioms Compiler.args_frag_c
#print axioms Compiler.scc_sur_frag_c
#print axioms Compiler.noar_frag_c
#print axioms Compiler.indPure_of_indOk
#print axioms Compiler.inl_trap_ind
#print axioms Compiler.inl_gate_miss_ind
#print axioms Compiler.inl_gate_ind
#print axioms Compiler.cu_trap_c
#print axioms Compiler.cu_gate_c
#print axioms Compiler.finishLFC_tail
#print axioms Compiler.fin_gate_finishLF_c
#print axioms Compiler.mem_to_finish_c
#print axioms Compiler.mem_gate_c
#print axioms Compiler.csi_gate_one_c
#print axioms Compiler.csi_gate_scc_one_m_c
#print axioms Compiler.mem_gate_none_c
#print axioms Compiler.csi_gate_scc_one_f_c
#print axioms Compiler.cu_gate_scc_one_f_c
#print axioms Compiler.noBakeOneC_no
#print axioms Compiler.comp_walk_lazy_all
#print axioms Compiler.le_gate
#print axioms Compiler.comp_lazy_prune
#print axioms Compiler.comp_copy_lazy_nm
#print axioms Compiler.comp_copy_nm
#print axioms Compiler.spsp_gate
#print axioms Compiler.csp_all
#print axioms Compiler.comp_split_all
#print axioms Compiler.cit_all
#print axioms Compiler.comp_into_all
#print axioms Compiler.turn_gate_mapT
#print axioms Compiler.cfr_all
#print axioms Compiler.comp_mede_all
#print axioms Compiler.kern_gate_all
#print axioms Compiler.comp_kern_all
#print axioms Compiler.comp_kerf_all
#print axioms Compiler.levy_gate_map
#print axioms Compiler.ne_all
#print axioms Compiler.comp_collapse_lazy_atom_all
#print axioms Compiler.walk_mdP
#print axioms Compiler.split_lnb
#print axioms Compiler.into_lnb
#print axioms Compiler.from_lnb
#print axioms Compiler.past_lnb
#print axioms Compiler.crInvL_of_crInv
#print axioms Compiler.crInvL_lok
#print axioms Compiler.crInvL_mdP
#print axioms Compiler.crInvL_split
#print axioms Compiler.crInvL_into
#print axioms Compiler.crInvL_from
#print axioms Compiler.malt_gate
#print axioms Compiler.spin_gate_T
#print axioms Compiler.spin_gate_TI
#print axioms Compiler.malt_index
#print axioms Compiler.seen_set
#print axioms Compiler.copyLazyL_le
#print axioms Compiler.cl_fgate
#print axioms Compiler.cl_bgate
#print axioms Compiler.cl_fpart
#print axioms Compiler.cl_bpart
#print axioms Compiler.copy_all
#print axioms Compiler.comp_copy_lazy_all
#print axioms Compiler.comp_copy_all
#print axioms Compiler.copy_lnb
#print axioms Compiler.crInvL_copy
#print axioms Compiler.copy_regs
#print axioms Compiler.split_halves
#print axioms Compiler.into_halves
#print axioms Compiler.from_regs
#print axioms Compiler.past_regs
#print axioms Compiler.copyH_of_regs
#print axioms Compiler.splitL_inv
#print axioms Compiler.intoL_inv
#print axioms Compiler.copyL_inv
#print axioms Compiler.tail_copyH
#print axioms Compiler.tail_res
#print axioms Compiler.res_all
#print axioms Compiler.runResL
#print axioms Compiler.comp_run_n0L
#print axioms Compiler.comp_run_n1L
#print axioms Compiler.comp_run_n3L
#print axioms Compiler.comp_run_n4L
#print axioms Compiler.comp_run_consL
#print axioms Compiler.comp_run_n5L
#print axioms Compiler.comp_run_n2L
#print axioms Compiler.comp_run_n10L
#print axioms Compiler.comp_run_all_l
#print axioms Compiler.runLinkL
#print axioms Compiler.comp_run_entry_l
#print axioms Compiler.plainOk_of_indOk
#print axioms Compiler.km_runLC
#print axioms Compiler.past_tags
#print axioms Compiler.tail_tags
#print axioms Compiler.tag_all
#print axioms Compiler.tag_done
#print axioms Compiler.proxy_tagged
#print axioms Compiler.cz_x
#print axioms Compiler.cz_step
#print axioms Compiler.cz_all
#print axioms Compiler.comp_coerce_lazy_all
