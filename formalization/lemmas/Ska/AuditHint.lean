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
import lemmas.Ska.CompHintRegKeepEx
import lemmas.Ska.CompHintSurEx
import lemmas.Ska.CompHintSevenCheck
import lemmas.Ska.CompHintTen
import lemmas.Ska.CompHintTenEx
import lemmas.Ska.CompHintSixRegCheck
import lemmas.Ska.CompHintSurOps
import lemmas.Ska.CompHintClsGlue
import lemmas.Ska.CompHintClsTally

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
#print axioms collapseL_lazyReg
#print axioms regGBT_four
#print axioms unaryGTBT_ok
#print axioms regGBT_three
#print axioms RegFT.toReg
#print axioms RegFT.of_loksf
#print axioms regFT_seven
#print axioms RunOKGBT.minkAs
#print axioms RunOKGBT.quietFront
#print axioms RunOKGBT.quietGoal
#print axioms runLCH_n11s_kept_next
#print axioms regGBT_n11sKept
#print axioms minkF_n11d_quiet
#print axioms mink_n11d_quiet
#print axioms mink_n11d_clueQ
#print axioms frameOKQ_goes
#print axioms regGBT_n11dQuiet
#print axioms n11dQuiet_doneR
#print axioms finishLUCH_contractN11dQuietR
#print axioms contract_s05
#print axioms contract_d03
#print axioms contract_d09
#print axioms regGBT_spotArm4
#print axioms contract_spotArm4
#print axioms AgreeUB.part
#print axioms runOKGBT_sevenG
#print axioms frameOK_goesR
#print axioms SurGBT.of_loksf
#print axioms runLCH_n11d_kept_sur
#print axioms surGBT_n11dKept
#print axioms surSeven_done
#print axioms finishLUCH_contractSurSeven
#print axioms runLCH_n4n0_done
#print axioms fitP_cons23
#print axioms contract_d13
#print axioms regGBT_sevenS
#print axioms runLCH_cal
#print axioms runLCH_tailP
#print axioms callLBM_runMH
#print axioms lokSH_directF
#print axioms tailP_doneMH
#print axioms regFT_direct
#print axioms runLCH_n0_one
#print axioms directZ_shape
#print axioms regGBT_spotArm5
#print axioms regGBT_spotArm45
#print axioms runLCH_n10_next
#print axioms pastL_park
#print axioms runLCH_n10_kept
#print axioms surGBT_tenKept
#print axioms surGBT_tenKept'
#print axioms copyL_bondFront
#print axioms minkF_ten_cases
#print axioms mink_ten_bwd
#print axioms runLCH_six_reg
#print axioms six_nextGBT
#print axioms surGBT_six
#print axioms regGBT_six
#print axioms regGBT_d18Q
#print axioms contract_d18
#print axioms pickD_spotTest
#print axioms regGBT_spotSix
#print axioms contract_spotS1
#print axioms shapeH_spotS2
#print axioms sixNH_of_shape
#print axioms regGBT_spotSixW
#print axioms contract_spotS1W
#print axioms contract_spotS1S2
#print axioms into_regLike_sound
#print axioms into_regLike_fit
#print axioms surGBT_tenSpot
#print axioms surGBT_spotS3Ten
#print axioms regGBT_spotArm45F
#print axioms contract_spotArm
#print axioms runLCH_n10_done_next
#print axioms ten_doneS
#print axioms contract_d20
#print axioms runLCH_n11s_kept_sur
#print axioms surGBT_n11sKept
#print axioms surGBT_n11dQuiet
#print axioms collapseL_regLike
#print axioms surGBT_four
#print axioms surGBT_three
#print axioms hcV_sound
#print axioms hintCls_contract
#print axioms contract_spotArmC
#print axioms contract_d10C
#print axioms contract_d13C
#print axioms contract_d18C
#print axioms contract_d20C
#print axioms hv7G_ok
#print axioms minkAs_dropK
#print axioms doneG_of_next
#print axioms finishLUCH_contractDoneG
#print axioms noBondH_cons
#print axioms hinted_crash
#print axioms into_regLike_reg
#print axioms SurGBT.toReg
#print axioms runLCH_mean_eq
#print axioms regGBT_mean
#print axioms runLCH_seven01
#print axioms sixNH_n1
#print axioms pickD_wut
#print axioms Glue.rawMonoH_inFragH'
#print axioms Glue.hintContract_holds
