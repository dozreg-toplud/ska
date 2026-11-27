import lemmas.Compiler.CompRunShapeElevenCut
import lemmas.Compiler.CompRunShapePastIf
import lemmas.Compiler.CompRunShapeECases
import lemmas.Compiler.CompRunShapeWhole
import lemmas.Compiler.Safe

/-!
# `+run-shape`: the hints `[11 tag q]` and `[11 [tag h] q]` (track A, 2026-11-28)

The case `rsK11` (`rs11Arm`, cut in `CompRunShapeElevenCut.lean`) against `runShape` on
`Nomm.n11s` and `Nomm.n11d`, on `RsAtE`.  Beside the recursive runs, the case reads `+laze-past-if`
(`lpi_gate`, so the hint's formula `q` must be closed for `+sound-far`: `SfClosed env.cod 3 q`),
`+id`, `+safe-nomm` (`safe_nomm_pill`, on `ana` at axis `63` of `ctx`), `+laze-past` over `h`
(`lzp_gate`, `CallCode` of `h`) and `+laze-copy`.

* `rs_disp_n11`, `rsK11_eq`, `rs11_sts` (the test is `hintStatic`), `rs11_dt` (`hintDynamic`);
* **`rs_n11sE`**: the static case; **`rs_n11dE`**: the dynamic case;
* `elevenSNz`, `elevenDNz`: they keep `LzNZ`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun} {E : RsRest → Prop}

theorem rs_disp_n11 (t s goal sup D : Noun) :
    nock (rsS s (C (A 11) t) goal sup D) rsDol = nock (rsS s (C (A 11) t) goal sup D) rsK11 := by
  nock_open rsDol
  simp [nock_exec, rsS, rsCoreG, rsTc, rsT]

theorem rsK11_eq : rsK11 = rs11Arm := by simp [rsK11, rs11_at]

/-- The test `?=(hint-static p.nomm)` is `hintStatic`. -/
theorem rs11_sts (S : Noun) (tag : Nat) (h : slot? 498 S = some (A tag)) :
    nock S rs11Sts = some (loob (hintStatic tag)) := by
  unfold rs11Sts
  by_cases h1 : tag = 0x79617278
  · subst h1; simp [nock_exec, h, eqCode_atom, hintStatic, HintTag.xray, HintTag.bout, loob]
  · by_cases h2 : tag = 0x74756f62
    · subst h2; simp [nock_exec, h, eqCode_atom, hintStatic, HintTag.xray, HintTag.bout, loob]
    · simp [nock_exec, h, eqCode_atom, hintStatic, HintTag.xray, HintTag.bout, loob, h1, h2, Ne.symm h1,
        Ne.symm h2]

set_option hygiene false in
local macro "dt_case" : tactic => `(tactic| (subst_vars; simp [nock_exec, h, eqCode_atom, hintDynamic,
  HintTag.bout, HintTag.xray, HintTag.spin, HintTag.jinx, HintTag.live, HintTag.slog, Tag.hunk, Tag.hand,
  Tag.lose, Tag.mean, Tag.spot, loob]))

/-- The test `?=(hint-dynamic p.p.nomm)` is `hintDynamic`. -/
theorem rs11_dt (S : Noun) (tag : Nat) (h : slot? 996 S = some (A tag)) :
    nock S rs11Dt = some (loob (hintDynamic tag)) := by
  unfold rs11Dt
  by_cases e1 : tag = 0x79617278; · dt_case
  by_cases e2 : tag = 0x6e697073; · dt_case
  by_cases e3 : tag = 0x74756f62; · dt_case
  by_cases e4 : tag = 0x6b6e7568; · dt_case
  by_cases e5 : tag = 0x646e6168; · dt_case
  by_cases e6 : tag = 0x676f6c73; · dt_case
  by_cases e7 : tag = 0x6e61656d; · dt_case
  by_cases e8 : tag = 0x65736f6c; · dt_case
  by_cases e9 : tag = 0x746f7073; · dt_case
  by_cases e10 : tag = 0x786e696a; · dt_case
  by_cases e11 : tag = 0x6576696c; · dt_case
  simp [nock_exec, h, eqCode_atom, hintDynamic, HintTag.bout, HintTag.xray, HintTag.spin, HintTag.jinx,
    HintTag.live, HintTag.slog, Tag.hunk, Tag.hand, Tag.lose, Tag.mean, Tag.spot, loob, e1, e2, e3, e4, e5, e6,
    e7, e8, e9, e10, e11, Ne.symm e1, Ne.symm e2, Ne.symm e3, Ne.symm e4, Ne.symm e5, Ne.symm e6, Ne.symm e7,
    Ne.symm e8, Ne.symm e9, Ne.symm e10, Ne.symm e11]

theorem rs11_arm_eq : rs11Arm = C (A 6) (C rs11Atom (C (C (A 6) (C rs11Sts (C rs11Sy rs11Sn))) rs11Dy)) := rfl

theorem rs11_dy_eq : rs11Dy = C (A 6) (C rs11Dt (C rs11Dd rs11Dn)) := rfl

/-- **The static hint takes the branch of `hintStatic`.** -/
theorem rs11_disp_s (s goal sup D : Noun) (tag : Nat) (t : Noun) :
    nock (rsS s (C (A 11) (C (A tag) t)) goal sup D) rs11Arm
      = if hintStatic tag then nock (rsS s (C (A 11) (C (A tag) t)) goal sup D) rs11Sy
        else nock (rsS s (C (A 11) (C (A tag) t)) goal sup D) rs11Sn := by
  have hsts := rs11_sts (rsS s (C (A 11) (C (A tag) t)) goal sup D) tag (by simp [rsS, rsCoreG, nock_exec])
  rw [rs11_arm_eq]
  generalize rs11Sts = TS at hsts
  generalize rs11Sy = SY
  generalize rs11Sn = SN
  generalize rs11Dy = DY
  simp only [rsS, rsCoreG] at hsts
  cases hs : hintStatic tag <;> rw [hs] at hsts <;> simp [nock_exec, rsS, rsCoreG, rs11Atom, hsts, loob]

/-- **The dynamic hint takes the branch of `hintDynamic`.** -/
theorem rs11_disp_d (s goal sup D : Noun) (tag : Nat) (H t : Noun) :
    nock (rsS s (C (A 11) (C (C (A tag) H) t)) goal sup D) rs11Arm
      = if hintDynamic tag then nock (rsS s (C (A 11) (C (C (A tag) H) t)) goal sup D) rs11Dd
        else nock (rsS s (C (A 11) (C (C (A tag) H) t)) goal sup D) rs11Dn := by
  have hdt := rs11_dt (rsS s (C (A 11) (C (C (A tag) H) t)) goal sup D) tag (by simp [rsS, rsCoreG, nock_exec])
  rw [rs11_arm_eq, rs11_dy_eq]
  generalize rs11Dt = TD at hdt
  generalize rs11Sts = TS
  generalize rs11Sy = SY
  generalize rs11Sn = SN
  generalize rs11Dd = DD
  generalize rs11Dn = DN
  simp only [rsS, rsCoreG] at hdt
  cases hs : hintDynamic tag <;> rw [hs] at hdt <;> simp [nock_exec, rsS, rsCoreG, rs11Atom, hdt, loob]

section
variable (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
  (env : ShapeEnv) (hcn : CodeNomms env.cod cod)
include hc h7 hcode hcn

/-- **The static hint `[11 tag q]`**: off `hint-static`, the run of `q` on the goal; on it,
`+laze-past-if` of `simple` over `q`, the run of `q` on that, and a bond with a new identifier. -/
theorem rs_n11sE (tag : Nat) (q : Nomm) (body : Noun) (sup : Option Nomm) (goal : GoalS CSet)
    (hg : GoalNZ goal) (st : RSt CSet) (hsf : SfClosed env.cod 3 q)
    (hq : ∀ st1, RsAtE ctx env E q sup goal st1)
    (hqn : ∀ l st1, LzNZ l → RsAtE ctx env E q sup (GoalS.next l) st1) :
    RsAtE ctx env E (Nomm.n11s tag q body) sup goal st := by
  intro y hy
  simp only [Nomm.toNoun]
  rw [rs_push, rs_disp_n11, rsK11_eq, rs11_disp_s]
  cases hs : hintStatic tag with
  | false =>
    have hq' := hq st y hy
    simp only [rsCoreG, rsDoor] at hq'
    simp only [Bool.false_eq_true, if_false]
    unfold rs11Sn
    simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, hs, hq']
  | true =>
    simp only [if_true]
    have hpi := lpi_gate h7 hcode env hcn q hsf st y (simpleS goal)
    simp only [rsDoor] at hpi
    obtain ⟨⟨gol, st1⟩, e1⟩ := lazePastIf_some env (simpleS goal) q hsf st
    rw [e1] at hpi
    have gnz := lazePastIf_nz env _ q st gol st1 (simpleS_nz goal hg) e1
    have hq' := hqn gol st1 gnz y hy
    simp only [rsCoreG, rsDoor, GoalS.toNoun] at hq'
    unfold rs11Sy
    cases e2 : runShape env sup q (GoalS.next gol) st1 with
    | none =>
      rw [e2] at hq'
      simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, hs, rsSimpleN, GoalS.toNoun,
        lpi_at', lpiArm, hpi, e1, hq', e2, bind, StateT.bind]
    | some r2 =>
      obtain ⟨lf, st2⟩ := r2
      rw [e2] at hq'
      simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, hs, rsSimpleN, GoalS.toNoun,
        lpi_at', lpiArm, hpi, e1, hq', e2, bind, StateT.bind, lzp_id_at', comp_id_at, idS, rs_id, pure,
        StateT.pure, Laze.toNoun, Laze.forksNoun, Laze.bondsNoun, SureO.toNoun, SureO.bunt, NeedOrd.toNoun,
        Tag.none, HoonSet.toNoun_empty]

/-- **The dynamic hint `[11 [tag h] q]`**: off `hint-dynamic`, the run of `q` on the goal, and unless
`+safe-nomm h`, `+laze-past` of it over `h`, the run of `h` under `[%next none]` and `+laze-copy`; on
it, `+laze-past-if` of `simple` over `q`, the run of `q` on that in a bond with a new identifier, the
run of `h` under `[%next this]` and `+laze-copy`. -/
theorem rs_n11dE (tag : Nat) (h q : Nomm) (body : Noun) (sup : Option Nomm) (goal : GoalS CSet)
    (hg : GoalNZ goal) (st : RSt CSet) (hsf : SfClosed env.cod 3 q) (hch : CallCode cod (shapeCE env) h)
    (hq : ∀ st1, RsAtE ctx env E q sup goal st1)
    (hqn : ∀ l st1, LzNZ l → RsAtE ctx env E q sup (GoalS.next l) st1)
    (hhn : ∀ st1, RsAtE ctx env E h sup (GoalS.next noneL) st1)
    (hht : ∀ st1, RsAtE ctx env E h sup (GoalS.next thisL) st1) :
    RsAtE ctx env E (Nomm.n11d tag h q body) sup goal st := by
  intro y hy
  simp only [Nomm.toNoun]
  rw [rs_push, rs_disp_n11, rsK11_eq, rs11_disp_d]
  cases hs : hintDynamic tag with
  | false =>
    simp only [Bool.false_eq_true, if_false]
    unfold rs11Dn rs11Sn
    have hq' := hq st y hy
    simp only [rsCoreG, rsDoor] at hq'
    have ha := whl_ana h7
    have hsa : slot? 5494 ana = some safe_nomm.arm := safe_nomm.arm_at
    have hsn := safe_nomm_pill h
    cases e1 : runShape env sup q goal st with
    | none =>
      rw [e1] at hq'
      simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, hs, hq', e1, bind, StateT.bind]
    | some r1 =>
      obtain ⟨lf, st1⟩ := r1
      rw [e1] at hq'
      cases hsafe : safeNomm h with
      | true =>
        simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, hs, hq', e1, bind, StateT.bind, ha, hsa, safe_nomm_arm,
          hsn, hsafe, loob, pure, StateT.pure]
      | false =>
        have hpa := lzp_gate h7 hcode env h hch st1 y lf
        simp only [rsDoor] at hpa
        cases e2 : lazePast env lf h st1 with
        | none =>
          rw [e2] at hpa
          simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, hs, hq', e1, bind, StateT.bind, ha, hsa, safe_nomm_arm,
            hsn, hsafe, loob, lzp_at', lzpArm, hpa, e2]
        | some r2 =>
          obtain ⟨lf', st2⟩ := r2
          rw [e2] at hpa
          have hh' := hhn st2 y hy
          simp only [rsCoreG, rsDoor, GoalS.toNoun, noneL_noun] at hh'
          cases e3 : runShape env sup h (GoalS.next noneL) st2 with
          | none =>
            rw [e3] at hh'
            simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, hs, hq', e1, bind, StateT.bind, ha, hsa, safe_nomm_arm,
              hsn, hsafe, loob, lzp_at', lzpArm, hpa, e2, hh', e3]
          | some r3 =>
            obtain ⟨lt, st3⟩ := r3
            rw [e3] at hh'
            have hlc := lc_all hc h7 (rsGenNoun st3 y) lt lf'
            cases e4 : lazeCopy lt lf' with
            | none =>
              rw [e4] at hlc
              simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, hs, hq', e1, bind, StateT.bind, ha, hsa,
                safe_nomm_arm, hsn, hsafe, loob, lzp_at', lzpArm, hpa, e2, hh', e3, lc_at', lc_arm, hlc, e4, shLiftS]
            | some l =>
              rw [e4] at hlc
              simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, hs, hq', e1, bind, StateT.bind, ha, hsa,
                safe_nomm_arm, hsn, hsafe, loob, lzp_at', lzpArm, hpa, e2, hh', e3, lc_at', lc_arm, hlc, e4, shLiftS]
  | true =>
    simp only [if_true]
    have hpi := lpi_gate h7 hcode env hcn q hsf st y (simpleS goal)
    simp only [rsDoor] at hpi
    obtain ⟨⟨gol, st1⟩, e1⟩ := lazePastIf_some env (simpleS goal) q hsf st
    rw [e1] at hpi
    have gnz := lazePastIf_nz env _ q st gol st1 (simpleS_nz goal hg) e1
    have hq' := hqn gol st1 gnz y hy
    simp only [rsCoreG, rsDoor, GoalS.toNoun] at hq'
    unfold rs11Dd
    cases e2 : runShape env sup q (GoalS.next gol) st1 with
    | none =>
      rw [e2] at hq'
      simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, hs, rsSimpleN, GoalS.toNoun,
        lpi_at', lpiArm, hpi, e1, hq', e2, bind, StateT.bind]
    | some r2 =>
      obtain ⟨lf, st2⟩ := r2
      rw [e2] at hq'
      have hh' := hht { st2 with idg := st2.idg + 1 } y hy
      simp only [rsCoreG, rsDoor, GoalS.toNoun, thisL_noun] at hh'
      cases e3 : runShape env sup h (GoalS.next thisL) { st2 with idg := st2.idg + 1 } with
      | none =>
        rw [e3] at hh'
        simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, hs, rsSimpleN, GoalS.toNoun,
          lpi_at', lpiArm, hpi, e1, hq', e2, bind, StateT.bind, lzp_id_at', comp_id_at, idS, rs_id, pure,
          StateT.pure, Laze.toNoun, Laze.forksNoun, Laze.bondsNoun, SureO.toNoun, SureO.bunt, NeedOrd.toNoun,
          Tag.none, HoonSet.toNoun_empty, hh', e3]
      | some r3 =>
        obtain ⟨lt, st3⟩ := r3
        rw [e3] at hh'
        have hlc := lc_all hc h7 (rsGenNoun st3 y) lt (Laze.mk SureO.bunt [] [(st2.idg, lf)])
        cases e4 : lazeCopy lt (Laze.mk SureO.bunt [] [(st2.idg, lf)]) with
        | none =>
          rw [e4] at hlc
          have e4' := e4
          simp only [SureO.bunt] at e4'
          simp only [Laze.toNoun, Laze.forksNoun, Laze.bondsNoun, SureO.toNoun, SureO.bunt, NeedOrd.toNoun,
            Tag.none, HoonSet.toNoun_empty] at hlc
          simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, hs, rsSimpleN, GoalS.toNoun,
            lpi_at', lpiArm, hpi, e1, hq', e2, bind, StateT.bind, lzp_id_at', comp_id_at, idS, rs_id, pure,
            StateT.pure, Laze.toNoun, Laze.forksNoun, Laze.bondsNoun, SureO.toNoun, SureO.bunt, NeedOrd.toNoun,
            Tag.none, HoonSet.toNoun_empty, hh', e3, lc_at', lc_arm, hlc, e4, e4', shLiftS]
        | some l =>
          rw [e4] at hlc
          have e4' := e4
          simp only [SureO.bunt] at e4'
          simp only [Laze.toNoun, Laze.forksNoun, Laze.bondsNoun, SureO.toNoun, SureO.bunt, NeedOrd.toNoun,
            Tag.none, HoonSet.toNoun_empty] at hlc
          simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, hs, rsSimpleN, GoalS.toNoun,
            lpi_at', lpiArm, hpi, e1, hq', e2, bind, StateT.bind, lzp_id_at', comp_id_at, idS, rs_id, pure,
            StateT.pure, Laze.toNoun, Laze.forksNoun, Laze.bondsNoun, SureO.toNoun, SureO.bunt, NeedOrd.toNoun,
            Tag.none, HoonSet.toNoun_empty, hh', e3, lc_at', lc_arm, hlc, e4, e4', shLiftS]

end

/-- **The static hint keeps `LzNZ`**, given that the runs of `q` do. -/
theorem elevenSNz (env : ShapeEnv) (tag : Nat) (q : Nomm) (body : Noun) (sup : Option Nomm) (goal : GoalS CSet)
    (hg : GoalNZ goal) (hrq : ∀ g st l st1, GoalNZ g → runShape env sup q g st = some (l, st1) → LzNZ l)
    (st : RSt CSet) (l : Laze CSet) (st1 : RSt CSet)
    (e : runShape env sup (Nomm.n11s tag q body) goal st = some (l, st1)) : LzNZ l := by
  simp only [runShape] at e
  cases hs : hintStatic tag
  · simp only [hs, Bool.not_false, if_true] at e; exact hrq goal st l st1 hg e
  · simp only [hs, Bool.not_true, Bool.false_eq_true, if_false] at e
    obtain ⟨gol, s1, e1, e⟩ := sm_bind_some e
    obtain ⟨lf, s2, e2, e⟩ := sm_bind_some e
    obtain ⟨i, s3, e3, e⟩ := sm_bind_some e
    simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    rw [← e.1]
    have hf := hrq (GoalS.next gol) _ _ _ (lazePastIf_nz env _ q st gol s1 (simpleS_nz goal hg) e1) e2
    exact ⟨fun y hy => absurd hy (HoonSet.mem_empty y), trivial, hf, trivial⟩

/-- **The dynamic hint keeps `LzNZ`**, given that the runs of `h` and `q` do. -/
theorem elevenDNz (env : ShapeEnv) (tag : Nat) (h q : Nomm) (body : Noun) (sup : Option Nomm)
    (goal : GoalS CSet) (hg : GoalNZ goal)
    (hrq : ∀ g st l st1, GoalNZ g → runShape env sup q g st = some (l, st1) → LzNZ l)
    (hrh : ∀ g st l st1, GoalNZ g → runShape env sup h g st = some (l, st1) → LzNZ l)
    (st : RSt CSet) (l : Laze CSet) (st1 : RSt CSet)
    (e : runShape env sup (Nomm.n11d tag h q body) goal st = some (l, st1)) : LzNZ l := by
  simp only [runShape] at e
  cases hs : hintDynamic tag
  · simp only [hs, Bool.not_false, if_true] at e
    obtain ⟨lf, s1, e1, e⟩ := sm_bind_some e
    have h1 := hrq goal st lf s1 hg e1
    cases hsafe : safeNomm h
    · simp only [hsafe, Bool.false_eq_true, if_false] at e
      obtain ⟨lf', s2, e2, e⟩ := sm_bind_some e
      obtain ⟨lt, s3, e3, e⟩ := sm_bind_some e
      exact lazeCopyEnd_nz (hrh (GoalS.next noneL) _ _ _ lzNZ_noneL e3) (lazePast_nz env lf h _ lf' s2 h1 e2) e
    · simp only [hsafe, if_true, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
      rw [← e.1]; exact h1
  · simp only [hs, Bool.not_true, Bool.false_eq_true, if_false] at e
    obtain ⟨gol, s1, e1, e⟩ := sm_bind_some e
    obtain ⟨lf, s2, e2, e⟩ := sm_bind_some e
    obtain ⟨i, s3, e3, e⟩ := sm_bind_some e
    obtain ⟨lt, s4, e4, e⟩ := sm_bind_some e
    have hf := hrq (GoalS.next gol) _ _ _ (lazePastIf_nz env _ q st gol s1 (simpleS_nz goal hg) e1) e2
    have hb : LzNZ (Laze.mk SureO.bunt [] [(i, lf)] : Laze CSet) :=
      ⟨fun y hy => absurd hy (HoonSet.mem_empty y), trivial, hf, trivial⟩
    exact lazeCopyEnd_nz (hrh (GoalS.next thisL) _ _ _ lzNZ_thisL e4) hb e

end Compiler
end Formalization
