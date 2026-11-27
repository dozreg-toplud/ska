import lemmas.Ska.CompHintTop
import lemmas.Ska.CompHintCheck
import lemmas.Ska.CompHintTreeEx
import lemmas.Ska.CompHintMean
import lemmas.Ska.CompHintTreeUEx
import lemmas.Ska.CompHintNest
import lemmas.Ska.CompHintKeepEx

/-! The axioms of the theorems of the hint files (README Gaps 24): only
`propext`, `Classical.choice`, `Quot.sound`. -/

open Formalization.SkaModel Formalization.SkaModel.Comp

#print axioms runLCH_eq
#print axioms finishLUCH_eq
#print axioms finishLFCH_eq
#print axioms minkAs_n11s
#print axioms RunOKGB.minkAs
#print axioms DoneOK.minkAs
#print axioms runLCH_n11s_LC
#print axioms n11s_doneA
#print axioms finishLUCH_n11s
#print axioms finishLUCH_contractN11s
#print axioms finishLUCH_bellContractN11s
#print axioms LOKSM.toH
#print axioms LOKSFM.toH
#print axioms JNewLSM.toH
#print axioms JNewLSFM.toH
#print axioms RunOKLS.minkAs
#print axioms lokS_consFMH
#print axioms lokS_sevenMH
#print axioms done_of_lokSFMH
#print axioms finishLUCH_contractGB
#print axioms LOKSH.n11s
#print axioms minkAsP_n11d
#print axioms runLCH_n11d_safe
#print axioms LOKSH.n11d
#print axioms DoneOK.minkAsP
#print axioms lokSH_callTreeH
#print axioms callTreeH_done
#print axioms finishLUCH_contractCallTreeH
#print axioms finishLUCH_bellContractCallTreeH
#print axioms contract_exCons
#print axioms contract_exSeven
#print axioms MeanOK.meac
#print axioms MeanOK.meaf
#print axioms pastL_unhinted
#print axioms KindU.of_minkEq
#print axioms totalC_cons
#print axioms totalC_seven
#print axioms totalC_five
#print axioms CallTreeHU.kindU
#print axioms CallTreeH.toU
#print axioms lokSHU_callTreeHU
#print axioms callTreeHU_done
#print axioms finishLUCH_contractCallTreeHU
#print axioms finishLUCH_bellContractCallTreeHU
#print axioms contract_s02
#print axioms contract_s03
#print axioms contract_d06
#print axioms lazyBound_apply
#print axioms RunOKGB.quietFront
#print axioms RunOKGB.quietGoal
#print axioms n11sKept_done
#print axioms finishLUCH_contractN11sKept
#print axioms finishLUCH_contractN11sKeptHU
#print axioms noBondH_n0
#print axioms noBondH_n7
#print axioms contract_s01
#print axioms contract_s06
#print axioms goJ_push
#print axioms goJ_pop
#print axioms minkF_n11d_any
