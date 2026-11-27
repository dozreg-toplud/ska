import lemmas.Compiler.CompRunShapeECases

/-!
# `+run-shape`: the case `[12 p q]` (track A, 2026-11-28)

`rsK12` is the case `%5` (`rsK5`) under a `%toss` hint whose clue is the test `?=([12 *] nomm)`
(`rsK12_eq`), and the model runs `[12 p q]` as `[5 p q]`.  `CallCode` of `n12` is `True`, while its
`+laze-past` over `p` reads the callees of `p` (`lzp_gate`), so the case takes
`CallCode cod (shapeCE env) p` as a hypothesis.

* `rs_disp_n12`, `rsK12_eq`, `rs12_hint`;
* **`rs_n12E`**: the case on `RsAtE`;
* `twelveNz`: the case keeps `LzNZ`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun} {E : RsRest → Prop}

theorem rs_disp_n12 (t s goal sup D : Noun) :
    nock (rsS s (C (A 12) t) goal sup D) rsDol = nock (rsS s (C (A 12) t) goal sup D) rsK12 := by
  nock_open rsDol
  simp [nock_exec, rsS, rsCoreG, rsTc, rsT]

/-- The clue of the `%toss` hint of `rsK12`. -/
def rs12Clue : Noun :=
  (C (A 6) (C (C (A 3) (C (A 0) (A 124))) (C (C (A 5) (C (C (A 1) (A 12)) (C (A 0) (A 248)))) (C (A 1) (A 1)))))

theorem rsK12_eq : rsK12 = C (A 11) (C (C (A 0x73736f74) rs12Clue) rsK5) := rfl

/-- The hint: its clue returns, then the body of `%5`. -/
theorem rs12_hint (t s goal sup D : Noun) :
    nock (rsS s (C (A 12) t) goal sup D) rsK12 = nock (rsS s (C (A 12) t) goal sup D) rsK5 := by
  rw [rsK12_eq]
  generalize rsK5 = K
  simp [nock_exec, rsS, rsCoreG, rs12Clue]

section
variable (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
include hc h7 hcode

/-- **The case `[12 p q]`**: as `[5 p q]` (`rs_n5E`): the run of `q` under `[%next this]`,
`+laze-past` of its `laze` over `p`, the run of `p` under `[%next this]`, `+laze-copy` of the two. -/
theorem rs_n12E (env : ShapeEnv) (p q : Nomm) (sup : Option Nomm) (goal : GoalS CSet) (st : RSt CSet)
    (hcp : CallCode cod (shapeCE env) p)
    (hq : ∀ st1, RsAtE ctx env E q sup (GoalS.next thisL) st1)
    (hp : ∀ st1, RsAtE ctx env E p sup (GoalS.next thisL) st1) :
    RsAtE ctx env E (Nomm.n12 p q) sup goal st := by
  intro y hy
  simp only [Nomm.toNoun]
  rw [rs_push, rs_disp_n12, rs12_hint]
  have hq' := hq st y hy
  simp only [rsCoreG, rsDoor, GoalS.toNoun, thisL_noun] at hq'
  unfold rsK5
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
      have hp' := hp st2 y hy
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
            hp', e3, lc_at', lc_arm, hlc, e4, shLiftS]
        | some l =>
          rw [e4] at hlc
          simp [nock_exec, rsS, rsCoreG, rsDoor, hq', runShape, e1, bind, StateT.bind, lzp_at', lzpArm, hpa, e2,
            hp', e3, lc_at', lc_arm, hlc, e4, shLiftS]

end

/-- **The case `[12 p q]` keeps `LzNZ`**, given that the runs of `p` and `q` under `[%next this]` do. -/
theorem twelveNz (env : ShapeEnv) (p q : Nomm) (sup : Option Nomm) (goal : GoalS CSet)
    (hrp : ∀ st l st1, runShape env sup p (GoalS.next thisL) st = some (l, st1) → LzNZ l)
    (hrq : ∀ st l st1, runShape env sup q (GoalS.next thisL) st = some (l, st1) → LzNZ l)
    (st : RSt CSet) (l : Laze CSet) (st1 : RSt CSet)
    (e : runShape env sup (Nomm.n12 p q) goal st = some (l, st1)) : LzNZ l := by
  simp only [runShape] at e
  obtain ⟨l2, s1, e1, e⟩ := sm_bind_some e
  obtain ⟨l2', s2, e2, e⟩ := sm_bind_some e
  obtain ⟨l1, s3, e3, e⟩ := sm_bind_some e
  have h2 := hrq _ _ _ e1
  exact lazeCopyEnd_nz (hrp _ _ _ e3) (lazePast_nz env l2 p _ l2' s2 h2 e2) e

end Compiler
end Formalization
