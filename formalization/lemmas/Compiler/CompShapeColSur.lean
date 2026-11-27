import lemmas.Compiler.CompSccSix
import lemmas.Ska.ShapeCol

/-!
# The new `ord` against the old one on a fork-free result

`shapeCol` (`Ska/ShapeCol.lean`, the model of `+shape-collapse` with forks)
on the sets of `+comp` (`CSet`): `sureOfS` is `sureOf` (`sureOfS_eq`), so on
a result `nex` of the final pass with no fork and no bond, `shapeCol` is
`sccSur nex cape`, the `ord` of the chain of the top so far
(`shapeCol_sccSur`); under `FinSure` that is the final pass of the top
(`shapeCol_finSure`).  The theorems stated with `sccSur` under `FinSure` are
so the same as with `shapeCol` (README Gaps 9).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

/-- `sureOfS` on `CSet` is `sureOf`. -/
theorem sureOfS_eq (ned : NeedOrd) (lok : CSet) (less : Cape) : sureOfS ned lok less = sureOf ned lok less := by
  simp only [sureOfS, sureOf, sureStepS_eq]

/-- **On a fork-free result the new `ord` is `sccSur`.** -/
theorem shapeCol_sccSur (fuel : Nat) (nex : NextL CSet) (cape : Cape) (h : nex.laz = Lazy.ofSure nex.laz.sure)
    {r : NeedOrd} (hr : sureOf (needToOrd nex.laz.sure.ned) nex.laz.sure.lok cape = some r) :
    shapeCol (fuel + 1) nex.laz cape = some (sccSur nex cape) := by
  have e : shapeCol (fuel + 1) nex.laz cape = sureOf (needToOrd nex.laz.sure.ned) nex.laz.sure.lok cape := by
    conv => { lhs; rw [h] }
    rw [shapeCol_ofSure, sureOfS_eq]
  rw [e, hr]
  simp [sccSur, hr]

/-- **Under `FinSure`, `sccSur` is the model's `+shape-collapse`** of the
final pass of `cu_gate_scc_one_six`. -/
theorem shapeCol_finSure (env : CallEnv) {nm : Nomm} (hn : SixOk nm = true) (ha : Bake.NoAx0 nm)
    (hfs : FinSure env nm) {nex : NextL CSet} {g1 : Gen (TreapMap mugF)}
    (hrun : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))
    (cape : Cape) (fuel : Nat) :
    shapeCol (fuel + 1) nex.laz cape = some (sccSur nex cape) := by
  obtain ⟨h1, h2⟩ := scc_sur_six env hn ha hfs hrun cape
  exact shapeCol_sccSur fuel nex cape h1 h2

end Compiler
end Formalization
