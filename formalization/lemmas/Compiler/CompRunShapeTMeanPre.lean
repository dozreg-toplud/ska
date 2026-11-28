import lemmas.Compiler.CompRunShapeTMeanCut

/-!
# `%mean`, the prefix: `+laze-past-if`, the run of `q`, `+id`, `l-fol` (track A, 2026-11-28)

* **`rsm_pre`**: on the case's subject at the rest `y`, `rsmPreF R` is `R` on `rsmS5` at the rest
  `y1` the run of `q` returns (for any `R`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun}

section
variable (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
  (env : ShapeEnv) (hcn : CodeNomms env.cod cod)
include h7 hcode hcn

/-- **The prefix of `%mean`**: `+laze-past-if` of `simple` over `q` at `y` (`lpi_gate`), the run of
`q` from `y` to `y1`, `+id` at `y1`, the push of `l-fol`; then `R`. -/
theorem rsm_pre (R : Noun) (P : Noun) (b : Bell) (q : Nomm) (BODY : Noun) (k : Option Noun) (sup : Option Nomm)
    (goal : GoalS CSet) (st : RSt CSet) (y y1 : RsRest) (hsf : SfClosed env.cod 3 q) (gol : Laze CSet)
    (st1 : RSt CSet) (e1 : lazePastIf env (simpleS goal) q st = some (gol, st1))
    (hq' : nock (rsCoreG q.toNoun (GoalS.next gol).toNoun (supNoun sup) (rsDoor st1 y ctx)) rsGate
      = (runShape env sup q (GoalS.next gol) st1).map fun r => C r.1.toNoun (rsGenNoun r.2 y1)) :
    nock (rsS (rsSimpleN goal) (meanN P b q.toNoun BODY k) goal.toNoun (supNoun sup) (rsDoor st y ctx)) (rsmPreF R)
      = (runShape env sup q (GoalS.next gol) st1).bind fun r =>
          nock (rsmS5 (Laze.mk SureO.bunt [] [(r.2.idg, r.1)]).toNoun (A r.2.idg) r.1.toNoun gol.toNoun
            (rsSimpleN goal) (meanN P b q.toNoun BODY k) goal.toNoun (supNoun sup)
            (rsDoor { r.2 with idg := r.2.idg + 1 } y1 ctx)) R := by
  have hpi := lpi_gate h7 hcode env hcn q hsf st y (simpleS goal)
  simp only [rsDoor] at hpi
  rw [e1] at hpi
  simp only [rsCoreG, rsDoor, GoalS.toNoun] at hq'
  unfold rsmPreF rsmTis rsmF1 rsmF2 rsmF3 rsmF4
  generalize R = R0
  cases e2 : runShape env sup q (GoalS.next gol) st1 with
  | none =>
    rw [e2] at hq'
    simp [nock_exec, rsS, rsCoreG, rsDoor, rsSimpleN, GoalS.toNoun, meanN, lpi_at', lpiArm, hpi, hq']
  | some r2 =>
    obtain ⟨lf, st2⟩ := r2
    rw [e2] at hq'
    simp [nock_exec, rsS, rsCoreG, rsDoor, rsSimpleN, GoalS.toNoun, meanN, lpi_at', lpiArm, hpi, hq',
      lzp_id_at', comp_id_at, rs_id, rsmS5, Laze.toNoun, Laze.forksNoun, Laze.bondsNoun, SureO.toNoun,
      SureO.bunt, NeedOrd.toNoun, Tag.none, HoonSet.toNoun_empty]

end

end Compiler
end Formalization
