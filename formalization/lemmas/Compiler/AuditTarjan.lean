import lemmas.Ska.TarjanSound
import lemmas.Compiler.CompTarjanLink
import lemmas.Compiler.CompTarjanBunt
import lemmas.Compiler.CompSccOfMissEnc

/-! The axioms of track Q's `+tarjan` theorems: the model (`Ska/Tarjan*.lean`)
and the pill link of `+tarjan` and of the miss of `+scc-of`. -/

open Formalization.Tarjan Formalization.Compiler

#print axioms tarjanM_total
#print axioms tarjanM_count
#print axioms tarjanM_spec
#print axioms tjSpec_flop
#print axioms tj_bat
#print axioms tarjanLinkAt_jug
#print axioms sccG_missJ
#print axioms sccG_miss_enc
