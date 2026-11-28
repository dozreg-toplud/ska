import lemmas.Compiler.CompRunShapeTDefs
import lemmas.Compiler.CompRunShapeECases

/-!
# `+run-shape`: the cases threading the rest of `gen` (track A, 2026-11-28)

The case lemmas of `CompRunShapeECases.lean` on `RsAtT` (`CompRunShapeTDefs.lean`): each recursive
run moves the rest from `y` to some `y'` of `E` with `Rl y y'`, and the pushes after it (the helper
arms, which keep every rest) and the next runs read the new rest.  The proofs are those of the
`RsAtE` versions with every push after a run instantiated at the rest it returns.

`rs_n3T`, `rs_n4T`, `rs_n7T`, `rs_n5T`, `rs_consNT`, `rs_consPT`, `rs_consDT`, `rs_consT`,
`rs_n10T`, `rs_n2iT`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun} {E : RsRest → Prop} {Rl : RsRest → RsRest → Prop}

/-- **The case `[3 p]`** from the run of `p` on the goal and on `[%next this]`. -/
theorem rs_n3T (hc : CompIn ctx) (env : ShapeEnv) (hR : RlPre Rl) (p : Nomm) (sup : Option Nomm)
    (goal : GoalS CSet) (st : RSt CSet) (hp1 : RsAtT ctx env E Rl p sup goal st)
    (hp2 : RsAtT ctx env E Rl p sup (GoalS.next thisL) st) :
    RsAtT ctx env E Rl (Nomm.n3 p) sup goal st := by
  intro y hy
  obtain ⟨y1, hR1, hy1, h1⟩ := hp1 y hy
  obtain ⟨y2, hR2, hy2, h2⟩ := hp2 y hy
  simp only [rsCoreG, rsDoor, GoalS.toNoun, thisL_noun] at h1 h2
  cases goal with
  | pick =>
    refine ⟨y2, hR2, hy2, ?_⟩
    simp only [Nomm.toNoun]
    rw [rs_push, rs_disp_n3]
    nock_open rsK3
    simp only [GoalS.toNoun] at h1
    simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, GoalS.toNoun]
    exact h2
  | done =>
    refine ⟨y2, hR2, hy2, ?_⟩
    simp only [Nomm.toNoun]
    rw [rs_push, rs_disp_n3]
    nock_open rsK3
    simp only [GoalS.toNoun] at h1
    simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, GoalS.toNoun]
    exact h2
  | next l =>
    have hl := lne_all hc (rsGenNoun st y) l
    cases e : noneEq l
    · refine ⟨y2, hR2, hy2, ?_⟩
      simp only [Nomm.toNoun]
      rw [rs_push, rs_disp_n3]
      nock_open rsK3
      rw [e] at hl
      simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, GoalS.toNoun, lne_at', lneArm, hl, e, loob]
      exact h2
    · refine ⟨y1, hR1, hy1, ?_⟩
      simp only [Nomm.toNoun]
      rw [rs_push, rs_disp_n3]
      nock_open rsK3
      rw [e] at hl
      simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, GoalS.toNoun, lne_at', lneArm, hl, e, loob]
      exact h1

/-- **The case `[4 p]`**: `p` under `[%next this]`. -/
theorem rs_n4T (env : ShapeEnv) (hR : RlPre Rl) (p : Nomm) (sup : Option Nomm) (goal : GoalS CSet)
    (st : RSt CSet) (hp : RsAtT ctx env E Rl p sup (GoalS.next thisL) st) :
    RsAtT ctx env E Rl (Nomm.n4 p) sup goal st := by
  intro y hy
  simp only [Nomm.toNoun]
  rw [rs_push, rs_disp_n4]
  obtain ⟨y1, hR1, hy1, hp'⟩ := hp y hy
  refine ⟨y1, hR1, hy1, ?_⟩
  simp only [rsCoreG, rsDoor, GoalS.toNoun, thisL_noun] at hp'
  nock_open rsK4
  simp [nock_exec, rsS, rsCoreG, rsDoor, runShape]
  exact hp'

/-- **The case `[7 p q]`** from the run of `q` and the run of `p` on the `laze` that `q`
returns, at the rest the run of `q` returns. -/
theorem rs_n7T (env : ShapeEnv) (hR : RlPre Rl) (p q : Nomm) (sup : Option Nomm) (goal : GoalS CSet)
    (st : RSt CSet) (hq : RsAtT ctx env E Rl q (some p) goal st)
    (hp : ∀ l st1, runShape env (some p) q goal st = some (l, st1) → RsAtT ctx env E Rl p sup (GoalS.next l) st1) :
    RsAtT ctx env E Rl (Nomm.n7 p q) sup goal st := by
  intro y hy
  obtain ⟨y1, hR1, hy1, hq'⟩ := hq y hy
  simp only [rsCoreG, supNoun, unitNoun, rsDoor] at hq'
  cases e : runShape env (some p) q goal st with
  | none =>
    refine ⟨y, hR.refl y, hy, ?_⟩
    simp only [Nomm.toNoun]
    rw [rs_push, rs_disp_n7]
    nock_open rsK7
    rw [e] at hq'
    simp [nock_exec, rsS, rsCoreG, rsDoor, hq', runShape, e, bind, StateT.bind]
  | some r =>
    obtain ⟨l, st1⟩ := r
    rw [e] at hq'
    obtain ⟨y2, hR2, hy2, hp'⟩ := hp l st1 e y1 hy1
    refine ⟨y2, hR.trans hR1 hR2, hy2, ?_⟩
    simp only [Nomm.toNoun]
    rw [rs_push, rs_disp_n7]
    nock_open rsK7
    simp only [rsCoreG, rsDoor, GoalS.toNoun] at hp'
    simp [nock_exec, rsS, rsCoreG, rsDoor, hq', runShape, e, bind, StateT.bind]
    exact hp'

section
variable (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
include hc h7 hcode

/-- **The case `[5 p q]`**: the run of `q` under `[%next this]`, `+laze-past` of its `laze` over
`p`, the run of `p` under `[%next this]`, `+laze-copy` of the two, each at the rest the last run
returned. -/
theorem rs_n5T (env : ShapeEnv) (hR : RlPre Rl) (p q : Nomm) (sup : Option Nomm) (goal : GoalS CSet)
    (st : RSt CSet) (hcp : CallCode cod (shapeCE env) p)
    (hq : ∀ st1, RsAtT ctx env E Rl q sup (GoalS.next thisL) st1)
    (hp : ∀ st1, RsAtT ctx env E Rl p sup (GoalS.next thisL) st1) :
    RsAtT ctx env E Rl (Nomm.n5 p q) sup goal st := by
  intro y hy
  simp only [Nomm.toNoun]
  rw [rs_push, rs_disp_n5]
  obtain ⟨y1, hR1, hy1, hq'⟩ := hq st y hy
  simp only [rsCoreG, rsDoor, GoalS.toNoun, thisL_noun] at hq'
  unfold rsK5
  cases e1 : runShape env sup q (GoalS.next thisL) st with
  | none =>
    refine ⟨y, hR.refl y, hy, ?_⟩
    rw [e1] at hq'
    simp [nock_exec, rsS, rsCoreG, rsDoor, hq', runShape, e1, bind, StateT.bind]
  | some r1 =>
    obtain ⟨lq, st1⟩ := r1
    rw [e1] at hq'
    have hpa := lzp_gate h7 hcode env p hcp st1 y1 lq
    simp only [rsDoor] at hpa
    cases e2 : lazePast env lq p st1 with
    | none =>
      refine ⟨y1, hR1, hy1, ?_⟩
      rw [e2] at hpa
      simp [nock_exec, rsS, rsCoreG, rsDoor, hq', runShape, e1, bind, StateT.bind, lzp_at', lzpArm, hpa, e2]
    | some r2 =>
      obtain ⟨lq', st2⟩ := r2
      rw [e2] at hpa
      obtain ⟨y2, hR2, hy2, hp'⟩ := hp st2 y1 hy1
      refine ⟨y2, hR.trans hR1 hR2, hy2, ?_⟩
      simp only [rsCoreG, rsDoor, GoalS.toNoun, thisL_noun] at hp'
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

/-- **The cons case under `[%next laz]`**, threading the rest (`rs_consNE`). -/
theorem rs_consNT (env : ShapeEnv) (hR : RlPre Rl) (p q : Nomm) (sup : Option Nomm) (laz : Laze CSet)
    (hl : LzNZ laz) (st : RSt CSet) (hcp : CallCode cod (shapeCE env) p) (hcq : CallCode cod (shapeCE env) q)
    (hq : ∀ l st1, LzNZ l → RsAtT ctx env E Rl q sup (GoalS.next l) st1)
    (hp : ∀ l st1, LzNZ l → RsAtT ctx env E Rl p sup (GoalS.next l) st1) :
    RsAtT ctx env E Rl (Nomm.cons p q) sup (GoalS.next laz) st := by
  intro y hy
  simp only [Nomm.toNoun]
  rw [rs_push, rs_disp_c]
  obtain ⟨hed, tel, es⟩ := lazeSplit_ex laz hl
  obtain ⟨hnz, tnz⟩ := lazeSplit_nz laz hl hed tel es
  have hsp := lsp_all hc (rsGenNoun st y) laz hl
  rw [es] at hsp
  simp only [Option.map_some] at hsp
  have hpa1 := lzp_gate h7 hcode env q hcq st y hed
  simp only [rsDoor] at hpa1
  unfold rsKc
  cases e2 : lazePast env hed q st with
  | none =>
    refine ⟨y, hR.refl y, hy, ?_⟩
    rw [e2] at hpa1
    simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, consNext, GoalS.toNoun, rsSimpleN, simpleS, es, shLiftS,
      bind, StateT.bind, lsp_at', lsp_arm, hsp, lzp_at', lzpArm, hpa1, e2]
  | some r2 =>
    obtain ⟨hed', st1⟩ := r2
    rw [e2] at hpa1
    obtain ⟨y1, hR1, hy1, hq'⟩ := hq tel st1 tnz y hy
    simp only [rsCoreG, rsDoor, GoalS.toNoun] at hq'
    cases e3 : runShape env sup q (GoalS.next tel) st1 with
    | none =>
      refine ⟨y, hR.refl y, hy, ?_⟩
      rw [e3] at hq'
      simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, consNext, GoalS.toNoun, rsSimpleN, simpleS, es, shLiftS,
        bind, StateT.bind, lsp_at', lsp_arm, hsp, lzp_at', lzpArm, hpa1, e2, hq', e3]
    | some r3 =>
      obtain ⟨l2, st2⟩ := r3
      rw [e3] at hq'
      have hpa2 := lzp_gate h7 hcode env p hcp st2 y1 l2
      simp only [rsDoor] at hpa2
      cases e4 : lazePast env l2 p st2 with
      | none =>
        refine ⟨y1, hR1, hy1, ?_⟩
        rw [e4] at hpa2
        simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, consNext, GoalS.toNoun, rsSimpleN, simpleS, es, shLiftS,
          bind, StateT.bind, lsp_at', lsp_arm, hsp, lzp_at', lzpArm, hpa1, e2, hq', e3, hpa2, e4]
      | some r4 =>
        obtain ⟨l2', st3⟩ := r4
        rw [e4] at hpa2
        obtain ⟨y2, hR2, hy2, hp'⟩ := hp hed' st3 (lazePast_nz env hed q st hed' st1 hnz e2) y1 hy1
        refine ⟨y2, hR.trans hR1 hR2, hy2, ?_⟩
        simp only [rsCoreG, rsDoor, GoalS.toNoun] at hp'
        cases e5 : runShape env sup p (GoalS.next hed') st3 with
        | none =>
          rw [e5] at hp'
          simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, consNext, GoalS.toNoun, rsSimpleN, simpleS, es, shLiftS,
            bind, StateT.bind, lsp_at', lsp_arm, hsp, lzp_at', lzpArm, hpa1, e2, hq', e3, hpa2, e4, hp', e5]
        | some r5 =>
          obtain ⟨l1, st4⟩ := r5
          rw [e5] at hp'
          have hlc := lc_all hc h7 (rsGenNoun st4 y2) l1 l2'
          cases e6 : lazeCopy l1 l2' with
          | none =>
            rw [e6] at hlc
            simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, consNext, GoalS.toNoun, rsSimpleN, simpleS, es,
              shLiftS, bind, StateT.bind, lsp_at', lsp_arm, hsp, lzp_at', lzpArm, hpa1, e2, hq', e3, hpa2, e4, hp',
              e5, lc_at', lc_arm, hlc, e6]
          | some l =>
            rw [e6] at hlc
            simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, consNext, GoalS.toNoun, rsSimpleN, simpleS, es,
              shLiftS, bind, StateT.bind, lsp_at', lsp_arm, hsp, lzp_at', lzpArm, hpa1, e2, hq', e3, hpa2, e4, hp',
              e5, lc_at', lc_arm, hlc, e6]

/-- **The cons case under `%pick`**, threading the rest (`rs_consPE`). -/
theorem rs_consPT (env : ShapeEnv) (hR : RlPre Rl) (p q : Nomm) (sup : Option Nomm) (st : RSt CSet)
    (hcp : CallCode cod (shapeCE env) p)
    (hq : ∀ st1, RsAtT ctx env E Rl q sup (GoalS.next noneL) st1)
    (hp : ∀ st1, RsAtT ctx env E Rl p sup (GoalS.next noneL) st1) :
    RsAtT ctx env E Rl (Nomm.cons p q) sup GoalS.pick st := by
  intro y hy
  simp only [Nomm.toNoun]
  rw [rs_push, rs_disp_c]
  obtain ⟨y1, hR1, hy1, hq'⟩ := hq st y hy
  simp only [rsCoreG, rsDoor, GoalS.toNoun, noneL_noun] at hq'
  unfold rsKc
  cases e1 : runShape env sup q (GoalS.next noneL) st with
  | none =>
    refine ⟨y, hR.refl y, hy, ?_⟩
    rw [e1] at hq'
    simp [nock_exec, rsS, rsCoreG, rsDoor, GoalS.toNoun, hq', runShape, e1, bind, StateT.bind]
  | some r1 =>
    obtain ⟨lq, st1⟩ := r1
    rw [e1] at hq'
    have hpa := lzp_gate h7 hcode env p hcp st1 y1 lq
    simp only [rsDoor] at hpa
    cases e2 : lazePast env lq p st1 with
    | none =>
      refine ⟨y1, hR1, hy1, ?_⟩
      rw [e2] at hpa
      simp [nock_exec, rsS, rsCoreG, rsDoor, GoalS.toNoun, hq', runShape, e1, bind, StateT.bind, lzp_at', lzpArm,
        hpa, e2]
    | some r2 =>
      obtain ⟨lq', st2⟩ := r2
      rw [e2] at hpa
      obtain ⟨y2, hR2, hy2, hp'⟩ := hp st2 y1 hy1
      refine ⟨y2, hR.trans hR1 hR2, hy2, ?_⟩
      simp only [rsCoreG, rsDoor, GoalS.toNoun, noneL_noun] at hp'
      cases e3 : runShape env sup p (GoalS.next noneL) st2 with
      | none =>
        rw [e3] at hp'
        simp [nock_exec, rsS, rsCoreG, rsDoor, GoalS.toNoun, hq', runShape, e1, bind, StateT.bind, lzp_at', lzpArm,
          hpa, e2, hp', e3]
      | some r3 =>
        obtain ⟨lp, st3⟩ := r3
        rw [e3] at hp'
        have hlc := lc_all hc h7 (rsGenNoun st3 y2) lp lq'
        cases e4 : lazeCopy lp lq' with
        | none =>
          rw [e4] at hlc
          simp [nock_exec, rsS, rsCoreG, rsDoor, GoalS.toNoun, hq', runShape, e1, bind, StateT.bind, lzp_at',
            lzpArm, hpa, e2, hp', e3, lc_at', lc_arm, hlc, e4, shLiftS]
        | some l =>
          rw [e4] at hlc
          simp [nock_exec, rsS, rsCoreG, rsDoor, GoalS.toNoun, hq', runShape, e1, bind, StateT.bind, lzp_at',
            lzpArm, hpa, e2, hp', e3, lc_at', lc_arm, hlc, e4, shLiftS]

/-- **The cons case under `%done`**: the gate runs again under `[%next this]`. -/
theorem rs_consDT (env : ShapeEnv) (hR : RlPre Rl) (p q : Nomm) (sup : Option Nomm) (st : RSt CSet)
    (hn : RsAtT ctx env E Rl (Nomm.cons p q) sup (GoalS.next thisL) st) :
    RsAtT ctx env E Rl (Nomm.cons p q) sup GoalS.done st := by
  intro y hy
  obtain ⟨y1, hR1, hy1, hn'⟩ := hn y hy
  refine ⟨y1, hR1, hy1, ?_⟩
  simp only [rsCoreG, rsDoor, GoalS.toNoun, thisL_noun, Nomm.toNoun] at hn'
  simp only [Nomm.toNoun]
  rw [rs_push, rs_disp_c]
  unfold rsKc
  simp [nock_exec, rsS, rsCoreG, rsDoor, GoalS.toNoun, hn']
  rfl

/-- **The cons case** on every goal of `GoalNZ`, threading the rest. -/
theorem rs_consT (env : ShapeEnv) (hR : RlPre Rl) (p q : Nomm) (sup : Option Nomm) (goal : GoalS CSet)
    (hg : GoalNZ goal) (st : RSt CSet) (hcp : CallCode cod (shapeCE env) p) (hcq : CallCode cod (shapeCE env) q)
    (hq : ∀ l st1, LzNZ l → RsAtT ctx env E Rl q sup (GoalS.next l) st1)
    (hp : ∀ l st1, LzNZ l → RsAtT ctx env E Rl p sup (GoalS.next l) st1) :
    RsAtT ctx env E Rl (Nomm.cons p q) sup goal st := by
  cases goal with
  | next laz => exact rs_consNT hc h7 hcode env hR p q sup laz hg st hcp hcq hq hp
  | pick =>
    exact rs_consPT hc h7 hcode env hR p q sup st hcp (fun st1 => hq _ st1 lzNZ_noneL)
      (fun st1 => hp _ st1 lzNZ_noneL)
  | done =>
    exact rs_consDT hc h7 hcode env hR p q sup st
      (rs_consNT hc h7 hcode env hR p q sup thisL lzNZ_thisL st hcp hcq hq hp)

/-- **The case `[10 [a v] q]`** on every goal of `GoalNZ`, threading the rest. -/
theorem rs_n10T (env : ShapeEnv) (hR : RlPre Rl) (a : Nat) (v q : Nomm) (sup : Option Nomm) (goal : GoalS CSet)
    (hg : GoalNZ goal) (st : RSt CSet) (hcv : CallCode cod (shapeCE env) v) (hcq : CallCode cod (shapeCE env) q)
    (hq : ∀ l st1, LzNZ l → RsAtT ctx env E Rl q sup (GoalS.next l) st1)
    (hv : ∀ l st1, LzNZ l → RsAtT ctx env E Rl v sup (GoalS.next l) st1) :
    RsAtT ctx env E Rl (Nomm.n10 a v q) sup goal st := by
  intro y hy
  simp only [Nomm.toNoun]
  rw [rs_push, rs_disp_n10]
  have hsi := lzi_all hc h7 (rsGenNoun st y) a (simpleS goal) (simpleS_nz goal hg)
  unfold rsK10
  cases e1 : lazeInto a (simpleS goal) with
  | none =>
    refine ⟨y, hR.refl y, hy, ?_⟩
    rw [e1] at hsi
    simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, GoalS.toNoun, rsSimpleN, shLiftS, bind, StateT.bind,
      lzi_at', lzi_arm, hsi, e1]
  | some dr =>
    obtain ⟨don, rec⟩ := dr
    rw [e1] at hsi
    simp only [Option.map_some] at hsi
    obtain ⟨dnz, rnz⟩ := lazeInto_nz a (simpleS goal) (simpleS_nz goal hg) don rec e1
    have hpa1 := lzp_gate h7 hcode env v hcv st y rec
    simp only [rsDoor] at hpa1
    cases e2 : lazePast env rec v st with
    | none =>
      refine ⟨y, hR.refl y, hy, ?_⟩
      rw [e2] at hpa1
      simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, GoalS.toNoun, rsSimpleN, shLiftS, bind, StateT.bind,
        lzi_at', lzi_arm, hsi, e1, lzp_at', lzpArm, hpa1, e2]
    | some r2 =>
      obtain ⟨rec', st1⟩ := r2
      rw [e2] at hpa1
      obtain ⟨y1, hR1, hy1, hv'⟩ := hv don st1 dnz y hy
      simp only [rsCoreG, rsDoor, GoalS.toNoun] at hv'
      cases e3 : runShape env sup v (GoalS.next don) st1 with
      | none =>
        refine ⟨y, hR.refl y, hy, ?_⟩
        rw [e3] at hv'
        simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, GoalS.toNoun, rsSimpleN, shLiftS, bind, StateT.bind,
          lzi_at', lzi_arm, hsi, e1, lzp_at', lzpArm, hpa1, e2, hv', e3]
      | some r3 =>
        obtain ⟨ld, st2⟩ := r3
        rw [e3] at hv'
        have hpa2 := lzp_gate h7 hcode env q hcq st2 y1 ld
        simp only [rsDoor] at hpa2
        cases e4 : lazePast env ld q st2 with
        | none =>
          refine ⟨y1, hR1, hy1, ?_⟩
          rw [e4] at hpa2
          simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, GoalS.toNoun, rsSimpleN, shLiftS, bind, StateT.bind,
            lzi_at', lzi_arm, hsi, e1, lzp_at', lzpArm, hpa1, e2, hv', e3, hpa2, e4]
        | some r4 =>
          obtain ⟨ld', st3⟩ := r4
          rw [e4] at hpa2
          obtain ⟨y2, hR2, hy2, hq'⟩ := hq rec' st3 (lazePast_nz env rec v st rec' st1 rnz e2) y1 hy1
          refine ⟨y2, hR.trans hR1 hR2, hy2, ?_⟩
          simp only [rsCoreG, rsDoor, GoalS.toNoun] at hq'
          cases e5 : runShape env sup q (GoalS.next rec') st3 with
          | none =>
            rw [e5] at hq'
            simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, GoalS.toNoun, rsSimpleN, shLiftS, bind, StateT.bind,
              lzi_at', lzi_arm, hsi, e1, lzp_at', lzpArm, hpa1, e2, hv', e3, hpa2, e4, hq', e5]
          | some r5 =>
            obtain ⟨lr, st4⟩ := r5
            rw [e5] at hq'
            have hlc := lc_all hc h7 (rsGenNoun st4 y2) lr ld'
            cases e6 : lazeCopy lr ld' with
            | none =>
              rw [e6] at hlc
              simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, GoalS.toNoun, rsSimpleN, shLiftS, bind, StateT.bind,
                lzi_at', lzi_arm, hsi, e1, lzp_at', lzpArm, hpa1, e2, hv', e3, hpa2, e4, hq', e5, lc_at', lc_arm,
                hlc, e6]
            | some l =>
              rw [e6] at hlc
              simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, GoalS.toNoun, rsSimpleN, shLiftS, bind, StateT.bind,
                lzi_at', lzi_arm, hsi, e1, lzp_at', lzpArm, hpa1, e2, hv', e3, hpa2, e4, hq', e5, lc_at', lc_arm,
                hlc, e6]

/-- **The indirect case `[2 p q ~]`**, threading the rest (`rs_n2iE`). -/
theorem rs_n2iT (env : ShapeEnv) (hR : RlPre Rl) (p q : Nomm) (sup : Option Nomm) (goal : GoalS CSet)
    (st : RSt CSet) (hcp : CallCode cod (shapeCE env) p)
    (hq : ∀ st1, RsAtT ctx env E Rl q sup (GoalS.next thisL) st1)
    (hp : ∀ st1, RsAtT ctx env E Rl p sup (GoalS.next thisL) st1) :
    RsAtT ctx env E Rl (Nomm.n2 p q Option.none) sup goal st := by
  intro y hy
  simp only [Nomm.toNoun]
  rw [rs_push, rs_disp_n2]
  simp only [unitNoun]
  obtain ⟨y1, hR1, hy1, hq'⟩ := hq st y hy
  simp only [rsCoreG, rsDoor, GoalS.toNoun, thisL_noun] at hq'
  rw [rsK2_eq]
  unfold rsdArm rsdI
  cases e1 : runShape env sup q (GoalS.next thisL) st with
  | none =>
    refine ⟨y, hR.refl y, hy, ?_⟩
    rw [e1] at hq'
    simp [nock_exec, rsS, rsCoreG, rsDoor, hq', runShape, e1, bind, StateT.bind]
  | some r1 =>
    obtain ⟨lq, st1⟩ := r1
    rw [e1] at hq'
    have hpa := lzp_gate h7 hcode env p hcp st1 y1 lq
    simp only [rsDoor] at hpa
    cases e2 : lazePast env lq p st1 with
    | none =>
      refine ⟨y1, hR1, hy1, ?_⟩
      rw [e2] at hpa
      simp [nock_exec, rsS, rsCoreG, rsDoor, hq', runShape, e1, bind, StateT.bind, lzp_at', lzpArm, hpa, e2]
    | some r2 =>
      obtain ⟨lq', st2⟩ := r2
      rw [e2] at hpa
      obtain ⟨y2, hR2, hy2, hp'⟩ := hp st2 y1 hy1
      refine ⟨y2, hR.trans hR1 hR2, hy2, ?_⟩
      simp only [rsCoreG, rsDoor, GoalS.toNoun, thisL_noun] at hp'
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

end

end Compiler
end Formalization
