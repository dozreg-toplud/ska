import lemmas.Ska.CompHintTop
import lemmas.Ska.CompHintCheck
import lemmas.Ska.CompHintTreeEx
import lemmas.Ska.CompHintMean
import lemmas.Ska.CompHintTreeUEx
import lemmas.Ska.CompHintNest
import lemmas.Ska.CompHintKeepEx
import lemmas.Ska.CompHintFrameEx
import lemmas.Ska.CompHintSpotEx
import lemmas.Ska.CompHintSpotCheck
import lemmas.Ska.CompHintRegEx

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
#print axioms RunOKGB.toT
#print axioms finishTop_genBT
#print axioms finishLUCH_contractGBT
#print axioms runLCH_n11d_kept_done
#print axioms copyL_bond1
#print axioms frameOK_goes
#print axioms mink_n11d_stop
#print axioms mink_n11d_clue
#print axioms n11dKept_done
#print axioms finishLUCH_contractN11dKept
#print axioms finishLUCH_contractN11dKeptHU
#print axioms clueLOKS_n1
#print axioms contract_d01
#print axioms contract_d02
#print axioms contract_d08
#print axioms contract_d23
#print axioms contract_m01
#print axioms noBondH_n2_none
#print axioms copyL_noBond
#print axioms runOKGBT_sevenL
#print axioms n11dKept_doneOK
#print axioms doneAllT_seven
#print axioms doneAllT_n11dKept
#print axioms doneAllT_callTreeHU
#print axioms finishLUCH_contractDoneAllT
#print axioms contract_d21
#print axioms contract_d14
#print axioms RunOKGBT.bound
#print axioms RegGBT.of_loksf
#print axioms runOKGBT_of_next
#print axioms runOKGBT_done
#print axioms runLCH_n11d_kept_next
#print axioms runLCH_n11d_done_next
#print axioms regGBT_n11dKept
#print axioms n11dKept_doneR
#print axioms finishLUCH_contractN11dKeptR
#print axioms unaryGBT_ok
#print axioms four_doneR
#print axioms contract_d10
#print axioms contract_d19
