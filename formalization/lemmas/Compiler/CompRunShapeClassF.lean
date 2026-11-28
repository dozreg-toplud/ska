import lemmas.Compiler.CompRunShapeMemberM
import lemmas.Compiler.CompLeapPass
import lemmas.Ska.RunShapeSixDeep
import lemmas.Ska.RunShapeTotal

/-!
# The class of `+run-shape` as facts of the nomm (track A, 2026-11-28)

`RsClsM` asks, at `%6`, that the fuel covers the runs on the same nomm (`SixDeep`) and that the soft
test of the branches returns (`unsS` total), and at `%mean` that `+sound` returns on `p`.  These follow
from facts of the nomm:

* **`sixDeep_noAx0`**: `SixDeep q r sixFuel laz` from `Bake.NoAx0` of the branches (a `rest` of
  `lazeLeaps` never leaps again, `lazeLeaps_idem'`, with the passes of `+pass-both` at nonzero axes,
  `pbt_gate`), as `leapTwice_noAx0`.
* `unsS_total`, `soundS_total` (`Ska/RunShapeTotal.lean`) from `SfClosed`.
* `RsClsF`: `RsClsM` with those conditions replaced by `Bake.NoAx0` and `SfClosed`;
  **`rsClsM_of_F`**; **`memShape_branchTF`**: the sweeps' branch on `RsClsF`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.SccLoop

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **The fuel `sixFuel` covers every `laz`** when the branches have no `%10` at axis `0`. -/
theorem sixDeep_noAx0 {q r : Nomm} (hq : Bake.NoAx0 q) (hr : Bake.NoAx0 r) (laz : Laze CSet) :
    SixDeep q r sixFuel laz := by
  obtain ⟨l, el, pl, -⟩ := pbt_gate passIn_compK q r hq hr
  refine sixDeep_of_idem q r (lazeLeaps_idem' fun pas ep e he => ?_) laz
  rw [el, Option.some.injEq] at ep; subst ep; exact (pl e he).1

/-- **The class as facts of the nomm**: `RsClsM` with `%6` asking `Bake.NoAx0` and `SfClosed` of the
branches, `%mean` `SfClosed` of `p`. -/
def RsClsF (env : ShapeEnv) (cod : Noun) : Nomm → Prop
  | Nomm.n0 _ => True
  | Nomm.n1 _ => True
  | Nomm.n3 p => RsClsF env cod p
  | Nomm.n4 p => RsClsF env cod p
  | Nomm.n7 p q => RsClsF env cod p ∧ RsClsF env cod q
  | Nomm.cons p q => RsClsF env cod p ∧ RsClsF env cod q
  | Nomm.n5 p q => RsClsF env cod p ∧ RsClsF env cod q
  | Nomm.n10 _ v q => RsClsF env cod v ∧ RsClsF env cod q
  | Nomm.n2 p q _ => RsClsF env cod p ∧ RsClsF env cod q
  | Nomm.n6 p q r => RsClsF env cod p ∧ RsClsF env cod q ∧ RsClsF env cod r ∧ Bake.NoAx0 q ∧ Bake.NoAx0 r ∧
      SfClosed env.cod 3 q ∧ SfClosed env.cod 3 r
  | Nomm.n11s _ q _ => RsClsF env cod q ∧ SfClosed env.cod 3 q
  | Nomm.n11d _ h q _ => RsClsF env cod h ∧ RsClsF env cod q ∧ SfClosed env.cod 3 q
  | Nomm.n12 p q => RsClsF env cod p ∧ RsClsF env cod q ∧ CallCode cod (shapeCE env) p ∧
      CallCode cod (shapeCE env) q
  | Nomm.mean p b q _ k => RsClsF env cod p ∧ RsClsF env cod q ∧ SfClosed env.cod 3 q ∧
      CallCode cod (shapeCE env) p ∧ CallCode cod (shapeCE env) q ∧ MeanPure cod env b k ∧
      SfClosed env.cod 3 p

/-- **`RsClsF` gives `RsClsM`.** -/
theorem rsClsM_of_F (env : ShapeEnv) (cod : Noun) : ∀ n, RsClsF env cod n → RsClsM env cod n
  | Nomm.n0 _, _ => trivial
  | Nomm.n1 _, _ => trivial
  | Nomm.n3 p, h => rsClsM_of_F env cod p h
  | Nomm.n4 p, h => rsClsM_of_F env cod p h
  | Nomm.n7 p q, ⟨hp, hq⟩ => ⟨rsClsM_of_F env cod p hp, rsClsM_of_F env cod q hq⟩
  | Nomm.cons p q, ⟨hp, hq⟩ => ⟨rsClsM_of_F env cod p hp, rsClsM_of_F env cod q hq⟩
  | Nomm.n5 p q, ⟨hp, hq⟩ => ⟨rsClsM_of_F env cod p hp, rsClsM_of_F env cod q hq⟩
  | Nomm.n10 _ v q, ⟨hv, hq⟩ => ⟨rsClsM_of_F env cod v hv, rsClsM_of_F env cod q hq⟩
  | Nomm.n2 p q _, ⟨hp, hq⟩ => ⟨rsClsM_of_F env cod p hp, rsClsM_of_F env cod q hq⟩
  | Nomm.n6 p q r, ⟨hp, hq, hr, hq0, hr0, hsq, hsr⟩ =>
    ⟨rsClsM_of_F env cod p hp, rsClsM_of_F env cod q hq, rsClsM_of_F env cod r hr, hq0, hr0,
      unsS_total env hsq hsr, fun laz _ => sixDeep_noAx0 hq0 hr0 laz⟩
  | Nomm.n11s _ q _, ⟨hq, hs⟩ => ⟨rsClsM_of_F env cod q hq, hs⟩
  | Nomm.n11d _ h q _, ⟨hh, hq, hs⟩ => ⟨rsClsM_of_F env cod h hh, rsClsM_of_F env cod q hq, hs⟩
  | Nomm.n12 p q, ⟨hp, hq, hcp, hcq⟩ => ⟨rsClsM_of_F env cod p hp, rsClsM_of_F env cod q hq, hcp, hcq⟩
  | Nomm.mean p b q _ k, ⟨hp, hq, hsq, hcp, hcq, hmp, hsp⟩ =>
    ⟨rsClsM_of_F env cod p hp, rsClsM_of_F env cod q hq, hsq, hcp, hcq, hmp, soundS_total env hsp⟩

/-- **The branch of the sweeps on `RsClsF`**: `memShape_branchTM` with the class as facts of the
nomm. -/
theorem memShape_branchTF (mode : Mode) (hm : mode = Mode.must ∨ mode = Mode.may)
    (jet : Bell → Bool) (xcod : Bell → Option Nomm) (env : CallEnv) (cape : Cape) (DATA FOL : Noun)
    (nm : Nomm) (fuel : Nat) (keep : Bool) (SCC LONG JH ML TOP CA1 CTX : Noun)
    (hK : slot? 63 CTX = some compK) {cod : Noun} (hcode : slot? 2 LONG = some cod)
    (hcn : CodeNomms xcod cod) (hn : RsClsF (shapeEnvOfA jet xcod env) cod nm)
    (hcc : CallCode cod (shapeCE (shapeEnvOfA jet xcod env)) nm)
    (E : RsRest → Prop) (Rl : RsRest → RsRest → Prop) (hR : RlPre Rl) (hE : E (memY CA1))
    (hs : ShapeOKM (memDCtx SCC LONG JH ML TOP (C (C cape.toNoun DATA) FOL)) (shapeEnvOfA jet xcod env)
      E Rl Option.none nm)
    (col sur : NeedOrd) (hlr : lazeRealA jet xcod mode env ⟨nm, cape, DATA, fuel⟩ = some (col, sur)) :
    ∃ (st1 : RSt CSet) (y1 : RsRest), Rl (memY CA1) y1 ∧ E y1 ∧
      MemShapeBranchA jet xcod mode env cape DATA FOL nm fuel keep SCC LONG JH ML TOP CA1 CTX
        col sur (rsGenNoun st1 y1) :=
  memShape_branchTM mode hm jet xcod env cape DATA FOL nm fuel keep SCC LONG JH ML TOP CA1 CTX hK hcode hcn
    (rsClsM_of_F _ cod nm hn) hcc E Rl hR hE hs col sur hlr

end Compiler
end Formalization
