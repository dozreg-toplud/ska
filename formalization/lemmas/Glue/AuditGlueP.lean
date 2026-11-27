import lemmas.Glue.InvMemoP
import lemmas.Compiler.PokeLink
import lemmas.Ska.PokeEnc
import lemmas.Ska.SccLoopMsg
import lemmas.Ska.SccLoopCycle

/-!
# Audit of `formalization/LEDGER.md`, track P's route

The names of track P (`Ska/PokeEnc.lean`, `Compiler/PokeLink.lean`) and the
glue on its route (`Glue/InvMemoP.lean`).  A separate file from
`AuditGlue.lean`: `Ska/PokeEnc.lean` and `Compiler/OptLinkAlJReg.lean` both
declare `Compiler.unitNoun_id_inj`, so no file can import both; likewise
`Ska/SccLoopMsg.lean` and `Ska/CompNCJump.lean` (`Comp.isLeaf`), so the
names of track I's `SccLoopMsg` are checked here.  Run:
`systemd-run --user --scope -q -p MemoryMax=3500M -p MemorySwapMax=0 -- lake env lean lemmas/Glue/AuditGlueP.lean`.
-/

namespace Formalization

#check @Compiler.straight_toNoun_inj
#check @Compiler.enc
#check @Compiler.enc_inj
#check @Compiler.cor_enc
#check @Compiler.cor_enc_gap
#check @Compiler.emptySt
#check @Compiler.Flags
#check @Compiler.anaArmP
#check @Compiler.anaHyp_of_armP
#check @Compiler.gap_of_armP
#check @Compiler.invStart_cor
#check @Compiler.FuelOK
#check @Compiler.fuelOK_anaFuel
#check @Compiler.pokeN_full_of
#check @Compiler.FullBranchIs
#check @Compiler.SkaLink
#check @Compiler.JetRootLink
#check @Compiler.SccLink
#check @Compiler.MonoLink
#check @Compiler.OptLink
#check @SkaModel.Comp.msgOrd_abs
#check @SkaModel.SccLoop.cyc_never

#print axioms SkaModel.Glue.anaArmP_memo
#print axioms SkaModel.Glue.pokeS_memoP
#print axioms SkaModel.Glue.fullAnswers_of_cgMP
#print axioms SkaModel.Glue.gap_of_armPM
#print axioms SkaModel.Glue.halting_of_cgMP

end Formalization
