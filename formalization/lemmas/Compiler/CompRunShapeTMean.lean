import lemmas.Compiler.CompRunShapeTMeanNed

/-!
# `+run-shape`: the case `[%mean p b q body k]`, threading the rest (track A, 2026-11-28)

The stages `rsm_pre` (`+laze-past-if`, the run of `q` from `y` to `y1`, `+id`, `l-fol`), `rsm_ned`
(`+mean-konst`, `+callee-need` from `y1` to `y2`: a miss compiles the callee), `rsm_r5`, `rsm_arg`
(`+sound` of `p`) and `rsm_end` (the run of `p` from `y2` to `y3`, `+laze-copy`), put together.

* **`rs_nmeanT`**: the case on `RsAtT`, under `SfClosed` of `q` (for `+laze-past-if`), `MeanPure`
  (for `+mean-konst`), `MeanNeedT` at every rest of `E` (for `+callee-need`) and `+sound` of `p`
  total (`soundS env p ned ≠ none`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun} {E : RsRest → Prop} {Rl : RsRest → RsRest → Prop}

section
variable (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
include hc h7 hcode

/-- **The case `[%mean p b q body k]`, threading the rest.** -/
theorem rs_nmeanT (env : ShapeEnv) (hR : RlPre Rl) (hcn : CodeNomms env.cod cod) (p : Nomm) (b : Bell) (q : Nomm)
    (body : Noun) (k : Option Noun) (sup : Option Nomm) (goal : GoalS CSet) (hg : GoalNZ goal) (st : RSt CSet)
    (hsf : SfClosed env.cod 3 q) (hcp : CallCode cod (shapeCE env) p) (hmp : MeanPure cod env b k)
    (hmn : ∀ y, E y → MeanNeedT ctx env E Rl b k y) (hsnd : ∀ ned, soundS env p ned ≠ Option.none)
    (hq : ∀ l st1, LzNZ l → RsAtT ctx env E Rl q sup (GoalS.next l) st1)
    (hp : ∀ l st1, LzNZ l → RsAtT ctx env E Rl p sup (GoalS.next l) st1) :
    RsAtT ctx env E Rl (Nomm.mean p b q body k) sup goal st := by
  intro y hy
  obtain ⟨⟨gol, st1⟩, e1⟩ := lazePastIf_some env (simpleS goal) q hsf st
  have gnz := lazePastIf_nz env _ q st gol st1 (simpleS_nz goal hg) e1
  obtain ⟨y1, hR1, hy1, hq'⟩ := hq gol st1 gnz y hy
  have hpre := rsm_pre h7 hcode env hcn rsmR5 p.toNoun b q body k sup goal st y y1 hsf gol st1 e1 hq'
  have hL : nock (rsCoreG (Nomm.mean p b q body k).toNoun goal.toNoun (supNoun sup) (rsDoor st y ctx)) rsGate
      = nock (rsS (rsSimpleN goal) (meanN p.toNoun b q.toNoun body k) goal.toNoun (supNoun sup) (rsDoor st y ctx))
        (rsmPreF rsmR5) := by
    rw [rs_push, mean_noun]
    unfold meanN
    rw [rs_disp_mean, rsKmean_eq, rsmArm_eq]
  cases e2 : runShape env sup q (GoalS.next gol) st1 with
  | none =>
    refine ⟨y1, hR1, hy1, ?_⟩
    rw [hL, hpre, e2, runShape_mean]
    simp [e1, e2, bind, StateT.bind]
  | some r2 =>
    obtain ⟨lf, st2⟩ := r2
    obtain ⟨kon, ek⟩ : ∃ kon, meanKonstS env b k = some kon := by
      rcases k with _ | kk
      · exact ⟨false, rfl⟩
      · obtain ⟨V, pu, -, -, hpu⟩ := hmp (by simp)
        exact ⟨pu, by simp [meanKonstS, hpu]⟩
    have hnd : ∃ (ned : NeedOrd) (y2 : RsRest), Rl y1 y2 ∧ E y2 ∧
        rsmNedM env b k { st2 with idg := st2.idg + 1 } = some (ned, { st2 with idg := st2.idg + 1 }) ∧
        nock (rsmS5 (Laze.mk SureO.bunt [] [(st2.idg, lf)]).toNoun (A st2.idg) lf.toNoun gol.toNoun (rsSimpleN goal)
          (meanN p.toNoun b q.toNoun body k) goal.toNoun (supNoun sup)
          (rsDoor { st2 with idg := st2.idg + 1 } y1 ctx)) rsmNed
          = some (C ned.toNoun (rsGenNoun { st2 with idg := st2.idg + 1 } y2)) := by
      cases kon with
      | false =>
        obtain ⟨nb, e, hn⟩ := hmn y1 hy1 ek
        obtain ⟨y2, hR2, hy2, hne⟩ := hn { st2 with idg := st2.idg + 1 }
        exact ⟨nb, y2, hR2, hy2, by simp [rsmNedM, shLiftS, ek, e, bind, StateT.bind],
          rsm_ned hc hcode env b k hmp _ _ _ _ _ _ _ _ _ _ _ y1 y2 false ek nb (fun _ => hne)
            (fun h => absurd h (by simp))⟩
      | true =>
        exact ⟨NeedOrd.none, y1, hR.refl y1, hy1,
          by simp [rsmNedM, shLiftS, ek, bind, StateT.bind, pure, StateT.pure],
          rsm_ned hc hcode env b k hmp _ _ _ _ _ _ _ _ _ _ _ y1 y1 true ek NeedOrd.none
            (fun h => absurd h (by simp)) (fun _ => ⟨rfl, rfl⟩)⟩
    obtain ⟨ned, y2, hR2, hy2, hnm, hnp⟩ := hnd
    obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp (hsnd ned)
    have hr5 := rsm_r5 _ _ _ _ _ _ _ _ _ y1 y2 _ hnp
    have harg := rsm_arg hc h7 hcode env hcn p b q.toNoun body k ned s hs
      (Laze.mk SureO.bunt [] [(st2.idg, lf)]).toNoun (A st2.idg) lf.toNoun gol.toNoun (rsSimpleN goal)
      goal.toNoun (supNoun sup) { st2 with idg := st2.idg + 1 } y2
    cases e5 : rsmArgM env p ned { st2 with idg := st2.idg + 1 } with
    | none =>
      refine ⟨y2, hR.trans hR1 hR2, hy2, ?_⟩
      rw [e5] at harg
      rw [hL, hpre, e2]
      simp only [Option.bind_some]
      rw [hr5, harg, runShape_mean]
      simp [e1, e2, idS, hnm, e5, bind, StateT.bind]
    | some r5 =>
      obtain ⟨la, st5⟩ := r5
      rw [e5] at harg
      have gla := lzNZ_argM env p ned _ la st5 e5
      obtain ⟨y3, hR3, hy3, hp'⟩ := hp la st5 gla y2 hy2
      have hend := rsm_end hc h7 env p sup b q.toNoun body k la (Laze.mk SureO.bunt [] [(st2.idg, lf)]) st5 y2 y3
        ned.toNoun (A st2.idg) lf.toNoun gol.toNoun (rsSimpleN goal) goal.toNoun { st2 with idg := st2.idg + 1 } y2
        hp'
      refine ⟨y3, hR.trans hR1 (hR.trans hR2 hR3), hy3, ?_⟩
      rw [hL, hpre, e2]
      simp only [Option.bind_some]
      rw [hr5, harg]
      simp only [Option.map_some, Option.bind_some]
      rw [hend, runShape_mean]
      cases e6 : runShape env sup p (GoalS.next la) st5 <;>
        simp [e1, e2, idS, hnm, e5, e6, bind, StateT.bind, shLiftS]

end

end Compiler
end Formalization
