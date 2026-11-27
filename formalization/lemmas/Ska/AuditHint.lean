import lemmas.Ska.CompHintTop
import lemmas.Ska.CompHintCheck
import lemmas.Ska.CompHintTreeEx

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
