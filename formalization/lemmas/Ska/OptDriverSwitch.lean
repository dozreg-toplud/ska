import lemmas.Ska.OptSwitchWalkAll
import lemmas.Ska.OptTrimBr

/-!
# The driver with `+switch-chains` discharged

`+switch-chains` runs once, after the loop of `+optimize` (`optimizeF`), so
the field `switch` of `DriverRestT` asks only that it keep the code on blocks
with `DInvT`, not that it keep an invariant.  With the model (`switchChains`)
as the pass, `switchKeepsM` gives that field (`switch_fieldT`), and the
driver theorem `optimize_keeps_restS` assumes of the passes only the field
`alias` of `DriverRestT`, the real trim pass and the model switch pass.
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock
variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

set_option linter.unusedSectionVars false

/-- **The field `switch`**, for the model of the pass, at `DInvT`. -/
theorem switch_fieldT (sfuel : Nat) {bl bl' : Map Blob} (hb : DInvT bl) (h : switchChains sfuel bl = some bl') :
    KeepsB bl bl' :=
  switch_field (switchKeepsM sfuel) bl bl' hb.1 h

/-- **What the driver still assumes**: `+alias` keeps the code, `DInv`,
`TopoInv` of the filtered `topo` and gives bracketed hints again; the trim
pass is the real one; the switch pass is the model of `+switch-chains` (with
any fuel `sfuel`). -/
structure DriverRestS (fuel sfuel : Nat) (P : Passes Map) : Prop where
  alias : ∀ n (bl : Map Blob) topo rev f bl', DInvT bl → TopoInv bl topo rev → P.alias n bl rev topo = some (f, bl') →
    KeepsB bl bl' ∧ DInvT bl' ∧
      TopoInv bl' (topo.filter fun o => (HoonMap.get bl' o).isSome)
        (revCfg bl' (topo.filter fun o => (HoonMap.get bl' o).isSome))
  trim : P.trim = trimTraceHints
  switch : P.switch = switchChains sfuel

theorem driverRestT_of {fuel sfuel : Nat} {P : Passes Map} (H : DriverRestS fuel sfuel P) : DriverRestT fuel P :=
  ⟨H.alias, H.trim, fun bl bl' hb h => by rw [H.switch] at h; exact switch_fieldT sfuel hb h⟩

/-- **`+optimize` keeps the code** on blocks with `DInvT`, with the real
`+trim-trace-hints` and the model of `+switch-chains`, given that `+alias`
keeps the code and the invariants (`DriverRestS.alias`). -/
theorem optimize_keeps_restS {fuel sfuel : Nat} {P : Passes Map} (H : DriverRestS fuel sfuel P)
    {s s' : Straight Map} (hb : DInvT s.blocks) (h : optimizeF fuel P s = some s') : Keeps s s' :=
  optimize_keeps_restT (driverRestT_of H) hb h

end Opt
end SkaModel
end Formalization
