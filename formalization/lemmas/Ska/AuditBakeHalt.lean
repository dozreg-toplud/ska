import lemmas.Ska.BakeHalt
import lemmas.Ska.BakeHaltTie
import lemmas.Ska.BakeHaltNorm

/-! Axioms of the track Q `BakeEnds` file (`Ska/BakeHalt.lean`, `Ska/BakeHaltTie.lean`, README Gaps 31). -/

open Formalization.SkaModel

#print axioms Bake.kapX_sub
#print axioms Bake.kapXS_lt
#print axioms Bake.rebakeG_kapX
#print axioms Bake.bakeLoop_halts_of_drop
#print axioms Bake.bakeLoop_halts
#print axioms Bake.put_drop
#print axioms Bake.touchFold_drop
#print axioms Bake.bakeStep_drop
#print axioms PokeM.bakeEnds_of_halts
#print axioms PokeM.bakeHalts_of_ends
#print axioms PokeM.bakeEnds_mono
#print axioms PokeM.bakeHalts_of_drops
#print axioms PokeM.bakeEnds_of_drops
#print axioms Bake.bakeLoop_halts_of_wf
#print axioms Bake.put_le
#print axioms Bake.touchFold_le
#print axioms Bake.bakeStep_le
#print axioms Bake.bakeStep_drop4
#print axioms Bake.bakeLoop_halts4
#print axioms PokeM.bakeDropsT_of_drops
#print axioms PokeM.bakeHalts_of_dropsT
#print axioms PokeM.bakeEnds_of_dropsT

-- the normal floor (`Ska/BakeHaltNorm.lean`, Gaps 31.7)
#print axioms Bake.bakeLoopG_bakeOf
#print axioms Bake.touchStepN_inv
#print axioms Bake.touchStepN_noTie
#print axioms Bake.bakeStepN_inv
#print axioms Bake.bakeStepN_drop
#print axioms Bake.bakeLoopN_halts_of_drops
#print axioms PokeM.bakeHaltsN_of_drops
#print axioms PokeM.bakeEndsN_of_drops
