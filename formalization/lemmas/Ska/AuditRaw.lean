import lemmas.Ska.RawInvTop
import lemmas.Ska.RawInvCheck
import lemmas.Ska.RawInvSix
import lemmas.Ska.RawInvTopX
import lemmas.Ska.RawInvFragX
import lemmas.Ska.RawInvIHX
import lemmas.Ska.RawInvIHXBin
import lemmas.Ska.RawInvIHXSix
import lemmas.Ska.RawInvFinishX
import lemmas.Ska.RawInvEApart

/-!
# Axioms of the main theorems of track D (README Gaps 14)

Only `propext`, `Classical.choice` and `Quot.sound` are allowed.
-/

open Formalization SkaModel Raw

#print axioms defOnceR_of_defUniq
#print axioms defFirst_of_live
#print axioms trimBr_of_noTr
#print axioms defUniq_of
#print axioms passOK_of
#print axioms downPar_of_args
#print axioms run_raw
#print axioms raw_cons
#print axioms raw_n5
#print axioms raw_n10
#print axioms raw_collapse
#print axioms raw_copy
#print axioms raw_split
#print axioms raw_mede
#print axioms raw_into
#print axioms kernLoop_raw
#print axioms raw_sureLoop
#print axioms chase_raw
#print axioms optIn_toStraight
#print axioms optIn_finish
#print axioms optIn_finishLF
#print axioms optIn_finishLU
#print axioms dInvR_finishLF
#print axioms dInvR_finishLU
#print axioms rawDInv_finishLF
#print axioms rawDInv_finishLU
#print axioms optimize_keeps_finishLF
#print axioms optimize_keeps_finishLU
#print axioms run_closed
#print axioms live_cut
#print axioms liveAv_region
#print axioms raw_coerce
#print axioms optIn_finishLF6
#print axioms optIn_finishLF_frag6
#print axioms rawDInv_finishLF_frag6
#print axioms optimize_keeps_finishLF_frag6
#print axioms live_prep
#print axioms live_entry_of_prep
#print axioms liveK_prep
#print axioms acyclic_of_jdownR
#print axioms passOK_ofR
#print axioms downPar_of_argsR
#print axioms chase_rawR
#print axioms chaseFin_rawR
#print axioms optIn_toStraightR
#print axioms optIn_toStraight_prep
#print axioms coerceLazyL_prep
#print axioms run_rawP
#print axioms run_rawU
#print axioms live_prependRk
#print axioms run_rawPK
#print axioms run_rawUK
#print axioms sip_reRank
#print axioms rawX_tail
#print axioms rawX_frag
#print axioms rawX_sevenFrom
#print axioms rawX_seven
#print axioms rawX_four
#print axioms rawX_three
#print axioms rawX_binTail
#print axioms rawX_cons
#print axioms rawX_five
#print axioms rawX_ten
#print axioms rawX_sixTail
#print axioms rawX_sixP
#print axioms sip_forkSure
#print axioms rawX_sixN
#print axioms rawX_six
#print axioms runX_rawIHX
#print axioms argsAboveR_upRk_of_xup
#print axioms runX_rawIHX_up
#print axioms raw_coerceP
#print axioms coI_step
#print axioms coerceLazyL_prepI
#print axioms optIn_finishLFX_of
#print axioms optimize_keeps_finishLFX_of
#print axioms runX_eap
#print axioms lazOK_run
#print axioms optIn_finishLFX
#print axioms optimize_keeps_finishLFX
