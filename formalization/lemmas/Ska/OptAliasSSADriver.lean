import lemmas.Ska.OptAliasSSADead

/-!
# The driver with the proved pass fields of `SSAKeepR`

`ssk_rub`, `ssk_mid` and `ssk_dead` discharge the fields `rub`, `middle` and
`dead` of `SSAKeepR` (`ssaKeepR_of`), so **`optimize_keeps_ssaH`** assumes of
the passes of the loop only `HopsSSA`: that `+remove-hops` keeps `AliasSSAB`.
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock
variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

set_option linter.unusedSectionVars false

/-- The field `hops` of `SSAKeepR`: `+remove-hops` keeps `AliasSSAB`. -/
def HopsSSA (Map : Type → Type) [HoonMap Map] [MapKeys Map] (fuel : Nat) : Prop :=
  ∀ (bl : Map Blob) topo rev ch bl', DInvT bl → TopoInv bl topo rev → AliasSSAB bl →
    removeHops fuel bl rev topo = some (ch, bl') → AliasSSAB bl'

theorem ssaKeepR_of {fuel : Nat} (hh : HopsSSA Map fuel) : SSAKeepR Map fuel :=
  ⟨hh, fun _ _ _ _ hs h => ssk_rub h hs, fun _ _ _ _ hs h => ssk_mid h hs,
    fun _ _ _ _ _ hi hs h => ssk_dead hi.1 h hs⟩

/-- **`+optimize` keeps the code** on blocks with `DInvS`, given the field
`alias` (`DriverRestSSA`) and that `+remove-hops` keeps `AliasSSAB`
(`HopsSSA`). -/
theorem optimize_keeps_ssaH {fuel sfuel : Nat} {P : Passes Map} (H : DriverRestSSA fuel sfuel P)
    (hh : HopsSSA Map fuel) {s s' : Straight Map} (hb : DInvS s.blocks) (h : optimizeF fuel P s = some s') :
    Keeps s s' :=
  optimize_keeps_ssaR H (ssaKeepR_of hh) hb h

end Opt
end SkaModel
end Formalization
