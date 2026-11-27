import lemmas.Compiler.CompRunShapeTwo

/-!
# `+run-shape`: the indirect `[2 p q ~]` (track A, 2026-11-27)

`rsdI` of `CompRunShapeTwoCut.lean` (the branch `?~  info.nomm` of `[%2 *]`): the shape of
`[5 p q]` (`rs_n5W`).  **`rs_n2iW`**.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

section
variable (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
include hc h7 hcode

/-- **The indirect case `[2 p q ~]`**: the run of `q` under `[%next this]`, `+laze-past` of its
`laze` over `p`, the run of `p` under `[%next this]`, `+laze-copy` of the two. -/
theorem rs_n2iW (env : ShapeEnv) (p q : Nomm) (sup : Option Nomm) (goal : GoalS CSet) (st : RSt CSet)
    (hcp : CallCode cod (shapeCE env) p)
    (hq : ∀ st1, RsAt ctx env q sup (GoalS.next thisL) st1)
    (hp : ∀ st1, RsAt ctx env p sup (GoalS.next thisL) st1) :
    RsAt ctx env (Nomm.n2 p q Option.none) sup goal st := by
  intro y
  simp only [Nomm.toNoun]
  rw [rs_push, rs_disp_n2]
  simp only [unitNoun]
  have hq' := hq st y
  simp only [rsCoreG, rsDoor, GoalS.toNoun, thisL_noun] at hq'
  rw [rsK2_eq]
  unfold rsdArm rsdI
  cases e1 : runShape env sup q (GoalS.next thisL) st with
  | none =>
    rw [e1] at hq'
    simp [nock_exec, rsS, rsCoreG, rsDoor, hq', runShape, e1, bind, StateT.bind]
  | some r1 =>
    obtain ⟨lq, st1⟩ := r1
    rw [e1] at hq'
    have hpa := lzp_gate h7 hcode env p hcp st1 y lq
    simp only [rsDoor] at hpa
    cases e2 : lazePast env lq p st1 with
    | none =>
      rw [e2] at hpa
      simp [nock_exec, rsS, rsCoreG, rsDoor, hq', runShape, e1, bind, StateT.bind, lzp_at', lzpArm, hpa, e2]
    | some r2 =>
      obtain ⟨lq', st2⟩ := r2
      rw [e2] at hpa
      have hp' := hp st2 y
      simp only [rsCoreG, rsDoor, GoalS.toNoun, thisL_noun] at hp'
      cases e3 : runShape env sup p (GoalS.next thisL) st2 with
      | none =>
        rw [e3] at hp'
        simp [nock_exec, rsS, rsCoreG, rsDoor, hq', runShape, e1, bind, StateT.bind, lzp_at', lzpArm, hpa, e2,
          hp', e3]
      | some r3 =>
        obtain ⟨lp, st3⟩ := r3
        rw [e3] at hp'
        have hlc := lc_all hc h7 (rsGenNoun st3 y) lp lq'
        cases e4 : lazeCopy lp lq' with
        | none =>
          rw [e4] at hlc
          simp [nock_exec, rsS, rsCoreG, rsDoor, hq', runShape, e1, bind, StateT.bind, lzp_at', lzpArm, hpa, e2,
            hp', e3, lc_at', lc_arm, hlc, e4, liftS]
        | some l =>
          rw [e4] at hlc
          simp [nock_exec, rsS, rsCoreG, rsDoor, hq', runShape, e1, bind, StateT.bind, lzp_at', lzpArm, hpa, e2,
            hp', e3, lc_at', lc_arm, hlc, e4, liftS]

end

end Compiler
end Formalization
