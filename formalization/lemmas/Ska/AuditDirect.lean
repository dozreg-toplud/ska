import lemmas.Ska.CompDirect
import lemmas.Ska.CompDirectMTop
import lemmas.Ska.CompDirectMGo

/-! The axioms of the theorems of track J (direct calls, `Ska/CompDirect.lean`,
README Gaps 18).  `lake build` prints them; each should be `propext`,
`Classical.choice` and `Quot.sound` at most. -/

open Formalization.SkaModel.Comp

#print axioms tailStep_bwd
#print axioms callStep_bwd
#print axioms needOrdAllocRegs_clean
#print axioms runLC_n2_direct
#print axioms fits_of_split
#print axioms split_of_holds
#print axioms runLCM_eq
#print axioms runLCM_false
#print axioms runLCM_true
#print axioms finishLUCM_eq
#print axioms finishLFC_eq_M
#print axioms finishLUCM_bellContractCallTree7
#print axioms finishLUCM_bellContractCallTreeA
#print axioms finishLUCM_bellContractTopTree
#print axioms finishLUCM_contractNC
#print axioms monoTryLoop_mono
#print axioms holdsN_frame
#print axioms monoTry_go
