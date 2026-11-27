import lemmas.Ska.OptAliasPerm
import lemmas.Ska.OptAliasBrz
import lemmas.Ska.OptAliasPickRoot

/-! The axioms of the main theorems of track E (README Gaps 15): the model of
`+alias` under a permutation of `pre`, the invariants of its walk, the choice
of a member, `NoLti` of the result. -/

open Formalization.SkaModel.Opt Formalization.Compiler

#print axioms loobC_joinReg
#print axioms joinReg_comm
#print axioms joinReg_assoc
#print axioms joinReg_idem
#print axioms joinRegE_eq
#print axioms fold1_perm
#print axioms aliasStart_perm
#print axioms aliasStartImms_perm
#print axioms aliasEdges_perm
#print axioms paramInfo_perm
#print axioms aliasPars_perm
#print axioms aliasPars_edges_perm
#print axioms aliasStart_order
#print axioms afin_brz
#print axioms brzInv_walk
#print axioms brzInv_loob
#print axioms revNodup_walk
#print axioms aliasM_inv
#print axioms aliasM_noLti
#print axioms pickR_ext
#print axioms sawRel_root
#print axioms infoRel_of_infoEq
#print axioms tapList_set_nodup
