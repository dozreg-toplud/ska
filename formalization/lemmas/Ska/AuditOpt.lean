import lemmas.Ska.OptDriver
import lemmas.Ska.OptHopsSim
import lemmas.Ska.OptDriverFields
import lemmas.Ska.OptMiddleSim
import lemmas.Ska.OptArgs
import lemmas.Ska.OptDriverTopo
import lemmas.Ska.OptDeadSim
import lemmas.Ska.OptSwitch
import lemmas.Ska.OptSwitchTree
import lemmas.Ska.OptSwitchSim
import lemmas.Ska.OptSwitchTag
import lemmas.Ska.OptSwitchShape
import lemmas.Ska.OptSwitchHyp
import lemmas.Ska.OptTrim
import lemmas.Ska.OptTrimWalk
import lemmas.Ska.OptTrimSim
import lemmas.Ska.OptTrimBr
import lemmas.Ska.OptSwitchWalk
import lemmas.Ska.OptSwitchMulti
import lemmas.Ska.OptAlias
import lemmas.Ska.OptAliasModel
import lemmas.Ska.OptAliasField
import lemmas.Ska.OptAliasSSA
import lemmas.Ska.OptAliasSSAKeep
import lemmas.Ska.OptAliasSSARub
import lemmas.Ska.OptAliasSSAMid
import lemmas.Ska.OptAliasSSADead
import lemmas.Ska.OptAliasSSADriver
import lemmas.Ska.OptAliasSSAHops
import lemmas.Ska.OptAliasFacts
import lemmas.Ska.OptSwitchPlainHyp
import lemmas.Ska.OptSwitchGen
import lemmas.Ska.OptSwitchWalkAll
import lemmas.Ska.OptDriverSwitch
import lemmas.Ska.OptSwitchSimG
import lemmas.Ska.OptSwitchPlain
import lemmas.Ska.OptAliasSSAOnce
import lemmas.Ska.OptAliasSound
import lemmas.Ska.OptAliasBody
import lemmas.Ska.OptAliasBodySSA
import lemmas.Ska.OptAliasRev
import lemmas.Ska.OptAliasWalk
import lemmas.Ska.OptAliasStart
import lemmas.Ska.OptAliasFin
import lemmas.Ska.OptAliasEdge
import lemmas.Ska.OptAliasFrame
import lemmas.Ska.OptAliasLti

/-! Axioms of the theorems about `+optimize`. -/

open Formalization.SkaModel.Opt

#print axioms keeps_trans
#print axioms rub_keeps
#print axioms rub_keepsB
#print axioms optimize_keeps
#print axioms hops_keeps
#print axioms hopsKeeps
#print axioms hops_parNodup
#print axioms hops_passOK
#print axioms hops_keeps_of
#print axioms mid_blocks
#print axioms mid_parNodup
#print axioms rub_parNodup
#print axioms rub_passOK
#print axioms hops_field
#print axioms rub_field
#print axioms middle_blkInv
#print axioms topoInv_revCfg
#print axioms execPole_agr
#print axioms passLoop_agr
#print axioms pass_sub
#print axioms byp_owner
#print axioms jump_walk
#print axioms hop_walk
#print axioms taken_mid
#print axioms mid_fwd_step
#print axioms mid_bwd_step
#print axioms mid_endOf
#print axioms middle_keeps_of
#print axioms middleKeeps
#print axioms rub_argsOK
#print axioms hops_argsOK_of
#print axioms keeps_of_R
#print axioms rub_keepsR
#print axioms hops_keepsR_of
#print axioms middle_keeps
#print axioms middle_field
#print axioms dfs_spec
#print axioms bbTopo_ok
#print axioms rub_acyclic
#print axioms hops_acyclic
#print axioms mid_acyclic
#print axioms rub_topoInv
#print axioms hops_topoInv
#print axioms mid_topoInv
#print axioms hops_same
#print axioms mid_same
#print axioms dead_shape
#print axioms dead_inv
#print axioms topo_field
#print axioms hops_fieldD
#print axioms rub_fieldD
#print axioms middle_fieldD
#print axioms driverHyp_of
#print axioms optimize_keeps_rest
#print axioms downPar_passOK
#print axioms rub_downPar
#print axioms hops_downPar
#print axioms mid_downPar
#print axioms mid_passOK_of
#print axioms rewriteHop_safe
#print axioms rub_localOK
#print axioms hops_localOK_of
#print axioms middle_localOK
#print axioms deadBody_rev
#print axioms dead_walk
#print axioms safe_frame
#print axioms dead_fwd_step
#print axioms dead_bwd_step
#print axioms dead_norm
#print axioms dead_endOf
#print axioms dead_keeps
#print axioms deadKeeps
#print axioms switch_field
#print axioms trimBody_uns_mono
#print axioms brOp_none
#print axioms trimBody_open
#print axioms trimBody_append
#print axioms trimBody_crash
#print axioms frameCount_pos
#print axioms CntLe.pos
#print axioms trimOpen_cntLe
#print axioms cntLe_nil
#print axioms casesAcc_spec
#print axioms hsort_sorted
#print axioms cases_spec
#print axioms stree_go
#print axioms treeGo_exec
#print axioms pickHit_cases
#print axioms tag_tree
#print axioms region_keeps
#print axioms tag_walk
#print axioms treeGo_good
#print axioms tag_head
#print axioms tag_keeps_of
#print axioms testOf_spec
#print axioms test_regs
#print axioms chainOf_spec
#print axioms tagHyp_shape
#print axioms revCfg_count
#print axioms labs_sorted
#print axioms labs_into
#print axioms labs_hits
#print axioms tagHyp_of
#print axioms tag_keeps
#print axioms trimWalk_safe
#print axioms kept_pole
#print axioms drop_pole
#print axioms trim_keeps_of
#print axioms trimRun_get
#print axioms trim_keeps
#print axioms trimKeepsBr
#print axioms rub_trimBr
#print axioms hops_trimBr
#print axioms mid_trimBr
#print axioms dead_trimBr
#print axioms trim_trimBr
#print axioms trim_fieldT
#print axioms driverHypT_of
#print axioms optimize_keeps_restT
#print axioms switchTag_out
#print axioms switchPlain_out
#print axioms stree_shape
#print axioms tag_nodes
#print axioms chain_disj
#print axioms tagHyp_out
#print axioms walk_tag_step
#print axioms switchWalk_tag
#print axioms switchChains_keeps_tag
#print axioms nexOf_gt
#print axioms freshIds_spec
#print axioms region_keepsG
#print axioms swB_norm
#print axioms plain_walk
#print axioms plain_tree
#print axioms plain_region
#print axioms plain_head
#print axioms plain_keeps_of
#print axioms plainsOf_rev
#print axioms plain_head_count
#print axioms plain_blocks
#print axioms plabs_sorted
#print axioms plabs_into
#print axioms plabs_hits
#print axioms plainHyp_of
#print axioms plain_keeps
#print axioms plain_tree2
#print axioms gc_disj
#print axioms tagGC_ok
#print axioms plainGC_ok
#print axioms tagHyp_outG
#print axioms plainHyp_outG
#print axioms swi_tag_step
#print axioms swi_plain_step
#print axioms switchWalk_all
#print axioms switchChains_keeps
#print axioms switchKeepsM
#print axioms switch_fieldT
#print axioms driverRestT_of
#print axioms optimize_keeps_restS
#print axioms driverRestS_of_aliasM
#print axioms optimize_keeps_ssa
#print axioms driverHypS_of
#print axioms driverRestSSA_of_aliasM
#print axioms filt_ssa
#print axioms trim_ssa
#print axioms optimize_keeps_ssaR
#print axioms ssk_rub
#print axioms ssk_mid
#print axioms ssk_dead
#print axioms ssaKeepR_of
#print axioms optimize_keeps_ssaH
#print axioms ssk_hops_first
#print axioms hopsSSA_of
#print axioms optimize_keeps_ssaO
#print axioms info_joinL
#print axioms info_joinR
#print axioms info_param
#print axioms hk_sites
#print axioms hk_disj
#print axioms hk_once
#print axioms hopsOnce_proved
#print axioms optimize_keeps_ssaD
#print axioms as_op
#print axioms as_frame
#print axioms as_sem
#print axioms ab_op
#print axioms as_body
#print axioms as_body_at
#print axioms aliasBody_append
#print axioms bodyOK_ssa
#print axioms bodyOK_of
#print axioms bdef_nodup
#print axioms revCfg_sound
#print axioms rvs_rub
#print axioms rvs_shape
#print axioms arev_step
#print axioms aliasWalk_reach
#print axioms ast_start
#print axioms ast_imms
#print axioms ast_entry
#print axioms ast_pars
#print axioms ast_param_names
#print axioms afn_jump
#print axioms afn_goesTo
#print axioms afn_end
#print axioms afn_endOf
#print axioms afn_taken
#print axioms aedge_aok
#print axioms aedge_pass
#print axioms ast_start_names
#print axioms ast_imms_sub
#print axioms aedge_mem
#print axioms aedge_abinv
#print axioms ast_start_keys
#print axioms ast_pars_names
#print axioms awk_op_old
#print axioms awk_body_old
#print axioms awk_block
#print axioms awk_walk
#print axioms awk_fin_ssa
#print axioms awk_finReads_sub
#print axioms nolti_shape
#print axioms nolti_rub
#print axioms nolti_mid
#print axioms nolti_hops
#print axioms driverHypS_of
