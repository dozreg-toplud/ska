import lemmas.Compiler.CompRunShapeTDefs
import lemmas.Compiler.CompRunShapeTwelve
import lemmas.Compiler.CompRunShapeEleven

/-!
# `+run-shape`: `%12` and the hints `%11` threading the rest (track A, 2026-11-28)

The threaded copies (on `RsAtT`) of `rs_n12E` (`CompRunShapeTwelve.lean`), `rs_n11sE` and
`rs_n11dE` (`CompRunShapeEleven.lean`): each recursive run moves the rest of `gen`, the helper arms
after it (`+laze-past`, `+laze-past-if`, `+id`, `+laze-copy`) run at the rest it returns.  None of
these cases reads `cache` itself.

* **`rs_n12T`**, **`rs_n11sT`**, **`rs_n11dT`**.
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

/-- **The case `[12 p q]`, threading the rest** (`rs_n12E`). -/
theorem rs_n12T (env : ShapeEnv) (hR : RlPre Rl) (p q : Nomm) (sup : Option Nomm) (goal : GoalS CSet)
    (st : RSt CSet) (hcp : CallCode cod (shapeCE env) p)
    (hq : ∀ st1, RsAtT ctx env E Rl q sup (GoalS.next thisL) st1)
    (hp : ∀ st1, RsAtT ctx env E Rl p sup (GoalS.next thisL) st1) :
    RsAtT ctx env E Rl (Nomm.n12 p q) sup goal st := by
  intro y hy
  simp only [Nomm.toNoun]
  rw [rs_push, rs_disp_n12, rs12_hint]
  obtain ⟨y1, hR1, hy1, hq'⟩ := hq st y hy
  simp only [rsCoreG, rsDoor, GoalS.toNoun, thisL_noun] at hq'
  unfold rsK5
  cases e1 : runShape env sup q (GoalS.next thisL) st with
  | none =>
    rw [e1] at hq'
    refine ⟨y1, hR1, hy1, ?_⟩
    simp [nock_exec, rsS, rsCoreG, rsDoor, hq', runShape, e1, bind, StateT.bind]
  | some r1 =>
    obtain ⟨lq, st1⟩ := r1
    rw [e1] at hq'
    have hpa := lzp_gate h7 hcode env p hcp st1 y1 lq
    simp only [rsDoor] at hpa
    cases e2 : lazePast env lq p st1 with
    | none =>
      rw [e2] at hpa
      refine ⟨y1, hR1, hy1, ?_⟩
      simp [nock_exec, rsS, rsCoreG, rsDoor, hq', runShape, e1, bind, StateT.bind, lzp_at', lzpArm, hpa, e2]
    | some r2 =>
      obtain ⟨lq', st2⟩ := r2
      rw [e2] at hpa
      obtain ⟨y2, hR2, hy2, hp'⟩ := hp st2 y1 hy1
      simp only [rsCoreG, rsDoor, GoalS.toNoun, thisL_noun] at hp'
      refine ⟨y2, hR.trans hR1 hR2, hy2, ?_⟩
      cases e3 : runShape env sup p (GoalS.next thisL) st2 with
      | none =>
        rw [e3] at hp'
        simp [nock_exec, rsS, rsCoreG, rsDoor, hq', runShape, e1, bind, StateT.bind, lzp_at', lzpArm, hpa, e2,
          hp', e3]
      | some r3 =>
        obtain ⟨lp, st3⟩ := r3
        rw [e3] at hp'
        have hlc := lc_all hc h7 (rsGenNoun st3 y2) lp lq'
        cases e4 : lazeCopy lp lq' with
        | none =>
          rw [e4] at hlc
          simp [nock_exec, rsS, rsCoreG, rsDoor, hq', runShape, e1, bind, StateT.bind, lzp_at', lzpArm, hpa, e2,
            hp', e3, lc_at', lc_arm, hlc, e4, shLiftS]
        | some l =>
          rw [e4] at hlc
          simp [nock_exec, rsS, rsCoreG, rsDoor, hq', runShape, e1, bind, StateT.bind, lzp_at', lzpArm, hpa, e2,
            hp', e3, lc_at', lc_arm, hlc, e4, shLiftS]

/-- **The static hint `[11 tag q]`, threading the rest** (`rs_n11sE`). -/
theorem rs_n11sT (env : ShapeEnv) (hR : RlPre Rl) (hcn : CodeNomms env.cod cod) (tag : Nat) (q : Nomm)
    (body : Noun) (sup : Option Nomm) (goal : GoalS CSet)
    (hg : GoalNZ goal) (st : RSt CSet) (hsf : SfClosed env.cod 3 q)
    (hq : ∀ st1, RsAtT ctx env E Rl q sup goal st1)
    (hqn : ∀ l st1, LzNZ l → RsAtT ctx env E Rl q sup (GoalS.next l) st1) :
    RsAtT ctx env E Rl (Nomm.n11s tag q body) sup goal st := by
  intro y hy
  simp only [Nomm.toNoun]
  rw [rs_push, rs_disp_n11, rsK11_eq, rs11_disp_s]
  cases hs : hintStatic tag with
  | false =>
    obtain ⟨y1, hR1, hy1, hq'⟩ := hq st y hy
    simp only [rsCoreG, rsDoor] at hq'
    refine ⟨y1, hR1, hy1, ?_⟩
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
    obtain ⟨y1, hR1, hy1, hq'⟩ := hqn gol st1 gnz y hy
    simp only [rsCoreG, rsDoor, GoalS.toNoun] at hq'
    refine ⟨y1, hR1, hy1, ?_⟩
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

/-- **The dynamic hint `[11 [tag h] q]`, threading the rest** (`rs_n11dE`). -/
theorem rs_n11dT (env : ShapeEnv) (hR : RlPre Rl) (hcn : CodeNomms env.cod cod) (tag : Nat) (h q : Nomm)
    (body : Noun) (sup : Option Nomm) (goal : GoalS CSet)
    (hg : GoalNZ goal) (st : RSt CSet) (hsf : SfClosed env.cod 3 q) (hch : CallCode cod (shapeCE env) h)
    (hq : ∀ st1, RsAtT ctx env E Rl q sup goal st1)
    (hqn : ∀ l st1, LzNZ l → RsAtT ctx env E Rl q sup (GoalS.next l) st1)
    (hhn : ∀ st1, RsAtT ctx env E Rl h sup (GoalS.next noneL) st1)
    (hht : ∀ st1, RsAtT ctx env E Rl h sup (GoalS.next thisL) st1) :
    RsAtT ctx env E Rl (Nomm.n11d tag h q body) sup goal st := by
  intro y hy
  simp only [Nomm.toNoun]
  rw [rs_push, rs_disp_n11, rsK11_eq, rs11_disp_d]
  cases hs : hintDynamic tag with
  | false =>
    simp only [Bool.false_eq_true, if_false]
    unfold rs11Dn rs11Sn
    obtain ⟨y1, hR1, hy1, hq'⟩ := hq st y hy
    simp only [rsCoreG, rsDoor] at hq'
    have ha := whl_ana h7
    have hsa : slot? 5494 ana = some safe_nomm.arm := safe_nomm.arm_at
    have hsn := safe_nomm_pill h
    cases e1 : runShape env sup q goal st with
    | none =>
      rw [e1] at hq'
      refine ⟨y1, hR1, hy1, ?_⟩
      simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, hs, hq', e1, bind, StateT.bind]
    | some r1 =>
      obtain ⟨lf, st1⟩ := r1
      rw [e1] at hq'
      cases hsafe : safeNomm h with
      | true =>
        refine ⟨y1, hR1, hy1, ?_⟩
        simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, hs, hq', e1, bind, StateT.bind, ha, hsa, safe_nomm_arm,
          hsn, hsafe, loob, pure, StateT.pure]
      | false =>
        have hpa := lzp_gate h7 hcode env h hch st1 y1 lf
        simp only [rsDoor] at hpa
        cases e2 : lazePast env lf h st1 with
        | none =>
          rw [e2] at hpa
          refine ⟨y1, hR1, hy1, ?_⟩
          simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, hs, hq', e1, bind, StateT.bind, ha, hsa, safe_nomm_arm,
            hsn, hsafe, loob, lzp_at', lzpArm, hpa, e2]
        | some r2 =>
          obtain ⟨lf', st2⟩ := r2
          rw [e2] at hpa
          obtain ⟨y2, hR2, hy2, hh'⟩ := hhn st2 y1 hy1
          simp only [rsCoreG, rsDoor, GoalS.toNoun, noneL_noun] at hh'
          refine ⟨y2, hR.trans hR1 hR2, hy2, ?_⟩
          cases e3 : runShape env sup h (GoalS.next noneL) st2 with
          | none =>
            rw [e3] at hh'
            simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, hs, hq', e1, bind, StateT.bind, ha, hsa, safe_nomm_arm,
              hsn, hsafe, loob, lzp_at', lzpArm, hpa, e2, hh', e3]
          | some r3 =>
            obtain ⟨lt, st3⟩ := r3
            rw [e3] at hh'
            have hlc := lc_all hc h7 (rsGenNoun st3 y2) lt lf'
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
    obtain ⟨y1, hR1, hy1, hq'⟩ := hqn gol st1 gnz y hy
    simp only [rsCoreG, rsDoor, GoalS.toNoun] at hq'
    unfold rs11Dd
    cases e2 : runShape env sup q (GoalS.next gol) st1 with
    | none =>
      rw [e2] at hq'
      refine ⟨y1, hR1, hy1, ?_⟩
      simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, hs, rsSimpleN, GoalS.toNoun,
        lpi_at', lpiArm, hpi, e1, hq', e2, bind, StateT.bind]
    | some r2 =>
      obtain ⟨lf, st2⟩ := r2
      rw [e2] at hq'
      obtain ⟨y2, hR2, hy2, hh'⟩ := hht { st2 with idg := st2.idg + 1 } y1 hy1
      simp only [rsCoreG, rsDoor, GoalS.toNoun, thisL_noun] at hh'
      refine ⟨y2, hR.trans hR1 hR2, hy2, ?_⟩
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
        have hlc := lc_all hc h7 (rsGenNoun st3 y2) lt (Laze.mk SureO.bunt [] [(st2.idg, lf)])
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

end Compiler
end Formalization
