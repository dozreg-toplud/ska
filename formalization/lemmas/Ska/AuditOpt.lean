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
import lemmas.Ska.OptTrim
import lemmas.Ska.OptAlias

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
