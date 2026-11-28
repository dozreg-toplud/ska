import lemmas.Ska.RawInvCLRunLD

/-!
# The frame and the labels of the n-ary runs with direct calls (`runLCM env false` on `PlainD`)

README Gaps 14 (b), track D (fork `kxf`).  The n-ary top run (`finishLFC`)
is `runLCM env false` (`finishLFC_eq_M`), whose `%2` is `callL` for every
`info` (`callLM_false`): a direct call goes through its `%cal` path (no memo
key, no ring, `sof` false: `+need-ord-alloc-regs`, the call block `[%jmp b
sub-v]` under `%done`, else `+simple-next`, `+kerf` and `[%cal b sub-v pro]
%hop out`; then `q` for nothing at the call block, `+past`, `p` for the
callee's need `sub-ned` at the continuation, `+copy`).

* `kxf_frameRun_*`: the arms of `frameRunM_plainD` (`RawInvCLRunLD.lean`)
  for `runLCM env false`, the text theirs (a script copy).
* `kxf_df_calBlock`, `kxf_frame_calPath`, `kxf_frame_callB`: the frame of
  the direct call with `mono` `|` (the drop path and the `%cal` path).
* **`frameRunF_plainD`**: every run of `runLCM env false` on `PlainD` has the
  frame, with no precondition.
* `kxf_htl_calPath`, `kxf_htl_callB`, `kxf_labRun` (a script copy of
  `kdl_labRun`): **`labRunF_plainD`**, `LabUniq` and `Fresh` at run level.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The arms with no call -/

/-- **The frame of `%0`.** -/
theorem kxf_frameRun_n0 (env : CallEnv) (sup : Option Nomm) (ax : Nat) :
    FrameRun (runLCM (S := S) (Map := Map) env false sup (Nomm.n0 ax)) := by
  intro goal region g0 g1 nex h
  simp only [runLCM] at h
  split at h
  · obtain ⟨d, n⟩ := frame_bombL h
    exact ⟨d.none, fun y hy => (n y hy).elim⟩
  obtain ⟨nx, ga, ha, h⟩ := bind_some h
  obtain ⟨d, gr⟩ := frame_simpleNextL ha
  split at h
  · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨d.none, gr⟩
  · cases hf : fromL ax nx.laz with
    | none => simp only [hf] at h; cases h
    | some laz' =>
      simp only [hf, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨d.none, fun y hy => gr y ?_⟩
      have FE : FromEnt ax ((nx.th.there, nx.laz) :: entries nx.laz) ((nx.th.there, laz') :: entries laz') :=
        FromEnt.cons hf (fromL_ent ax nx.laz laz' hf)
      obtain ⟨e', he', hm⟩ := (hy : GRegL (CGoalL.next laz' nx.th) y)
      obtain ⟨e, he, -, hn, -⟩ := fromEnt_back FE he'
      exact (⟨e, he, hn y hm⟩ : GRegL (CGoalL.next nx.laz nx.th) y)

/-- **The frame of `%1`.** -/
theorem kxf_frameRun_n1 (env : CallEnv) (sup : Option Nomm) (k : Noun) :
    FrameRun (runLCM (S := S) (Map := Map) env false sup (Nomm.n1 k)) := by
  intro goal region g0 g1 nex h
  cases goal with
  | done =>
    simp only [runLCM] at h
    obtain ⟨r, ga, ha, h⟩ := bind_some h
    obtain ⟨da, rfl, -⟩ := df_re (Q := FG g0 (CGoalL.done : CGoalL S)) ha
    obtain ⟨o, gb, hb, h⟩ := bind_some h
    obtain ⟨db, -, -⟩ := df_emit (Raw.blobWr_one (Q := FG g0 (CGoalL.done : CGoalL S)) (p := Pole.imm k g0.re)
      (fun x hx => by simp only [poleWr, List.mem_singleton] at hx; exact Or.inl (Nat.le_of_eq hx.symm)) _) hb
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact frX_of (da.trans db) fun y hy => (lReg_bunt hy).elim
  | pick z o =>
    simp only [runLCM] at h
    split at h
    · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact frX_of (DF.refl _ _) fun y hy => (lReg_bunt hy).elim
    · split at h
      · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact frX_of (DF.refl _ _) fun y hy => (lReg_bunt hy).elim
      · obtain ⟨d, n⟩ := frame_bombL h
        exact ⟨d.none, fun y hy => (n y hy).elim⟩
  | next laz th =>
    simp only [runLCM] at h
    obtain ⟨o, ga, ha, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine frX_of ((frame_medeL ha).mono fun y hy => ?_) fun y hy => (lReg_bunt hy).elim
    rcases hy with e | e
    · exact Or.inl e
    · exact Or.inr (gregL_next.mpr e)

/-! ## `%3` and `%4` -/

/-- **The frame of `%3`.** -/
theorem kxf_frameRun_n3 (env : CallEnv) (sup : Option Nomm) {p : Nomm}
    (hp : FrameRun (runLCM (S := S) (Map := Map) env false sup p)) :
    FrameRun (runLCM (S := S) (Map := Map) env false sup (Nomm.n3 p)) := by
  intro goal region g0 g1 nex h
  cases goal with
  | pick z o =>
    simp only [runLCM] at h
    obtain ⟨r, ga, ha, h⟩ := bind_some h
    obtain ⟨oc, gb, hb, h⟩ := bind_some h
    exact frame_tail hp (DF.refl _ _) ha (fun _ => blobWr_nil _ _) hb h
  | done =>
    simp only [runLCM] at h
    obtain ⟨⟨o0, o1⟩, ga, ha, h⟩ := bind_some h
    obtain ⟨r, gb, hb, h⟩ := bind_some h
    obtain ⟨oc, gc, hc, h⟩ := bind_some h
    exact frame_tail hp ((frame_doneBlocks ha).mono fun _ e => Or.inl e) hb (fun _ => blobWr_nil _ _) hc h
  | next laz th =>
    simp only [runLCM] at h
    by_cases hn : noneEquivalentL laz = true
    · rw [if_pos hn] at h; exact hp _ _ _ _ _ h
    · rw [if_neg hn] at h
      obtain ⟨a, ga, ha, h⟩ := bind_some h
      obtain ⟨dA, rA⟩ := frame_collapseL ha
      have hS : ∀ y, (g0.re ≤ y ∨ LReg laz y) → FG g0 (CGoalL.next laz th) y := fun y hy => by
        rcases hy with e | e
        · exact Or.inl e
        · exact Or.inr (gregL_next.mpr e)
      cases a with
      | none => cases h
      | some x =>
        obtain ⟨r, there⟩ := x
        have hr := hS r (rA r there rfl)
        obtain ⟨⟨z, o'⟩, gb, hb, h⟩ := bind_some h
        have dB := frame_forl hb
        have rA' : g0.re ≤ ga.re := dA.1
        obtain ⟨r', gc, hc, h⟩ := bind_some h
        obtain ⟨oc, gd, hd, h⟩ := bind_some h
        refine frame_tail hp ((dA.mono hS).trans (dB.mono fun y hy => ?_)) hc (fun _ => blobWr_nil _ _) hd h
        rcases hy with e | e
        · subst e; exact hr
        · exact Or.inl (by omega)

/-- **The frame of `%4`.** -/
theorem kxf_frameRun_n4 (env : CallEnv) (sup : Option Nomm) {p : Nomm}
    (hp : FrameRun (runLCM (S := S) (Map := Map) env false sup p)) :
    FrameRun (runLCM (S := S) (Map := Map) env false sup (Nomm.n4 p)) := by
  intro goal region g0 g1 nex h
  cases goal with
  | done =>
    simp only [runLCM] at h
    obtain ⟨pro, ga, ha, h⟩ := bind_some h
    obtain ⟨da, rfl, ea⟩ := df_re (Q := FG g0 (CGoalL.done : CGoalL S)) ha
    obtain ⟨arg, gb, hb, h⟩ := bind_some h
    obtain ⟨oc, gc, hc, h⟩ := bind_some h
    exact frame_tail hp da hb (fun _ => Raw.blobWr_one (fun x hx => by
      simp only [poleWr, List.mem_singleton] at hx; exact Or.inl (Nat.le_of_eq hx.symm)) _) hc h
  | pick z o =>
    simp only [runLCM] at h
    obtain ⟨pro, ga, ha, h⟩ := bind_some h
    obtain ⟨da, rfl, ea⟩ := df_re (Q := FG g0 (CGoalL.pick z o : CGoalL S)) ha
    obtain ⟨arg, gb, hb, h⟩ := bind_some h
    obtain ⟨oc, gc, hc, h⟩ := bind_some h
    exact frame_tail hp da hb (fun _ => Raw.blobWr_one (fun x hx => by
      simp only [poleWr, List.mem_singleton] at hx; exact Or.inl (Nat.le_of_eq hx.symm)) _) hc h
  | next laz th =>
    simp only [runLCM] at h
    obtain ⟨a, ga, ha, h⟩ := bind_some h
    obtain ⟨dA, rA⟩ := frame_collapseL ha
    have hS : ∀ y, (g0.re ≤ y ∨ LReg laz y) → FG g0 (CGoalL.next laz th) y := fun y hy => by
      rcases hy with e | e
      · exact Or.inl e
      · exact Or.inr (gregL_next.mpr e)
    have rA' : g0.re ≤ ga.re := dA.1
    obtain ⟨⟨pro, th'⟩, gb, hb, h⟩ := bind_some h
    have P : DF (FG g0 (CGoalL.next laz th)) ga gb ∧ FG g0 (CGoalL.next laz th) pro := by
      cases a with
      | some x =>
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        exact ⟨DF.refl _ _, hS _ (rA _ _ rfl)⟩
      | none =>
        obtain ⟨r, gc, hc, hb⟩ := bind_some hb
        obtain ⟨dc, rfl, -⟩ := df_re (Q := FG g0 (CGoalL.next laz th)) hc
        split at hb
        · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hb
          exact ⟨dc, Or.inl rA'⟩
        · cases hb
    obtain ⟨arg, gc, hc, h⟩ := bind_some h
    obtain ⟨oc, gd, hd, h⟩ := bind_some h
    exact frame_tail hp ((dA.mono hS).trans P.1) hc (fun _ => Raw.blobWr_one (fun x hx => by
      simp only [poleWr, List.mem_singleton] at hx; subst hx; exact P.2) _) hd h

/-! ## `%5` and `%7` -/

/-- **The frame of `%5`.** -/
theorem kxf_frameRun_n5 (env : CallEnv) (sup : Option Nomm) {p q : Nomm}
    (hp : FrameRun (runLCM (S := S) (Map := Map) env false sup p)) (hq : FrameRun (runLCM (S := S) (Map := Map) env false sup q)) :
    FrameRun (runLCM (S := S) (Map := Map) env false sup (Nomm.n5 p q)) := by
  intro goal region g0 g1 nex h
  simp only [runLCM] at h
  obtain ⟨rp, ga, ha, h⟩ := bind_some h
  obtain ⟨da, rfl, ea⟩ := df_re (Q := FG g0 goal) ha
  obtain ⟨rq, gb, hb, h⟩ := bind_some h
  obtain ⟨db, rfl, eb⟩ := df_re (Q := FG g0 goal) hb
  obtain ⟨o, gc, hc, h⟩ := bind_some h
  have P : DF (FG g0 goal) gb gc := by
    cases goal with
    | pick z o' => exact (df_emit (blobWr_nil _ _) hc).1
    | done =>
      obtain ⟨⟨o0, o1⟩, gx, hx, hc⟩ := bind_some hc
      have dx := frame_doneBlocks hx
      exact (dx.mono fun _ e => Or.inl (by omega)).trans (df_emit (blobWr_nil _ _) hc).1
    | next laz th =>
      obtain ⟨a, gx, hx, hc⟩ := bind_some hc
      obtain ⟨dA, rA⟩ := frame_collapseL hx
      have hS : ∀ y, (gb.re ≤ y ∨ LReg laz y) → FG g0 (CGoalL.next laz th) y := fun y hy => by
        rcases hy with e | e
        · exact Or.inl (by omega)
        · exact Or.inr (gregL_next.mpr e)
      have rA' : gb.re ≤ gx.re := dA.1
      cases a with
      | none =>
        dsimp only at hc
        split at hc
        · refine (dA.mono hS).trans (df_emit (Raw.blobWr_one (fun x hx => ?_) _) hc).1
          simp [poleWr] at hx
        · cases hc
      | some x =>
        obtain ⟨r, there⟩ := x
        have hr := hS r (rA r there rfl)
        dsimp only at hc
        obtain ⟨⟨z, o'⟩, gy, hy, hc⟩ := bind_some hc
        have dB := frame_forl hy
        refine (dA.mono hS).trans ((dB.mono fun y hy => ?_).trans (df_emit (blobWr_nil _ _) hc).1)
        rcases hy with e | e
        · subst e; exact hr
        · exact Or.inl (by omega)
  have rc : gb.re ≤ gc.re := P.1
  obtain ⟨nq, gd, hd, h⟩ := bind_some h
  obtain ⟨nq', ge, he, h⟩ := bind_some h
  obtain ⟨np, gf, hf, h⟩ := bind_some h
  obtain ⟨dC, lC⟩ := frame_chain (G := FG g0 goal) hq hp
    (fun y hy => Or.inl (by have e : y = ga.re := lReg_ofSure.mp hy; omega))
    (fun y hy => Or.inl (by have e : y = g0.re := lReg_ofSure.mp hy; omega))
    (fun y hy => Or.inl (by omega)) hd he hf h
  exact frX_of ((da.trans db).trans (P.trans dC)) lC

/-- **The frame of `%7`.** -/
theorem kxf_frameRun_n7 (env : CallEnv) (sup : Option Nomm) {p q : Nomm}
    (hq : FrameRun (runLCM (S := S) (Map := Map) env false (some p) q)) (hp : FrameRun (runLCM (S := S) (Map := Map) env false sup p)) :
    FrameRun (runLCM (S := S) (Map := Map) env false sup (Nomm.n7 p q)) := by
  intro goal region g0 g1 nex h
  simp only [runLCM] at h
  obtain ⟨nexq, gq, hrq, hrp⟩ := bind_some h
  have F1 := hq _ _ _ _ _ hrq
  exact frX_sub (frL_iff.mp F1.1) F1.2 (hp _ _ _ _ _ hrp)

/-! ## The induction -/


/-- **The frame of a cons.** -/
theorem kxf_frameRun_cons (env : CallEnv) (sup : Option Nomm) {p q : Nomm}
    (hp : FrameRun (runLCM (S := S) (Map := Map) env false sup p)) (hq : FrameRun (runLCM (S := S) (Map := Map) env false sup q)) :
    FrameRun (runLCM (S := S) (Map := Map) env false sup (Nomm.cons p q)) := by
  intro goal region g0 g' nex h
  simp only [runLCM] at h
  obtain ⟨goal', g1, hg, h⟩ := bind_some h
  have P : DF (FG g0 goal) g0 g1 ∧ ∀ y, GRegL goal' y → FG g0 goal y := by
    cases goal with
    | done =>
      obtain ⟨r, ga, ha, hg⟩ := bind_some hg
      obtain ⟨da, rfl, ea⟩ := df_re (Q := FG g0 (CGoalL.done : CGoalL S)) ha
      obtain ⟨o, gb, hb, hg⟩ := bind_some hg
      obtain ⟨db, -, eb⟩ := df_emit (blobWr_nil (FG g0 (CGoalL.done : CGoalL S)) _) hb
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hg
      obtain ⟨rfl, rfl⟩ := hg
      refine ⟨da.trans db, fun y hy => Or.inl ?_⟩
      have e : y = g0.re := gregL_ofSure.mp hy
      omega
    | next laz th =>
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hg
      obtain ⟨rfl, rfl⟩ := hg
      exact ⟨DF.refl _ _, fun y hy => Or.inr hy⟩
    | pick z o =>
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hg
      obtain ⟨rfl, rfl⟩ := hg
      exact ⟨DF.refl _ _, fun y hy => Or.inr hy⟩
  obtain ⟨d1, gr1⟩ := P
  have r1 : g0.re ≤ g1.re := d1.1
  cases goal' with
  | pick z o =>
    obtain ⟨o', g2, h2, h⟩ := bind_some h
    obtain ⟨d2, -, e2⟩ := df_emit (blobWr_nil (FG g0 goal) _) h2
    obtain ⟨n2, g3, h3, h⟩ := bind_some h
    obtain ⟨n2', g4, h4, h⟩ := bind_some h
    obtain ⟨n1, g5, h5, h6⟩ := bind_some h
    obtain ⟨dC, lC⟩ := frame_chain (G := FG g0 goal) hq hp (fun y hy => (lReg_bunt hy).elim)
      (fun y hy => (lReg_bunt hy).elim) (fun y hy => Or.inl (by omega)) h3 h4 h5 h6
    exact frX_of (d1.trans (d2.trans dC)) lC
  | done => cases h
  | next laz th =>
    obtain ⟨⟨hed, tel, o⟩, g2, h2, h⟩ := bind_some h
    obtain ⟨d2, lh, lt⟩ := frame_splitL h2
    obtain ⟨nexh, g3, h3, h⟩ := bind_some h
    obtain ⟨d3, l3⟩ := frame_pastL h3
    obtain ⟨n2, g4, h4, h⟩ := bind_some h
    obtain ⟨n2', g5, h5, h⟩ := bind_some h
    obtain ⟨n1, g6, h6, h7⟩ := bind_some h
    have r2 : g1.re ≤ g2.re := d2.1
    have r3 : g2.re ≤ g3.re := d3.1
    have hL : ∀ y, LReg laz y → FG g0 goal y := fun y hy => gr1 y (gregL_next.mpr hy)
    have hS : ∀ y, (g1.re ≤ y ∨ LReg laz y) → FG g0 goal y := fun y hy => by
      rcases hy with e | e
      · exact Or.inl (by omega)
      · exact hL y e
    obtain ⟨dC, lC⟩ := frame_chain (G := FG g0 goal) hq hp
      (fun y hy => hS y ((lt y hy).symm))
      (fun y hy => hS y ((lh y (l3 y hy)).symm))
      (fun y hy => Or.inl (by omega)) h4 h5 h6 h7
    exact frX_of (d1.trans ((d2.mono hS).trans ((d3.mono fun _ h => h.elim).trans dC))) lC

/-- **The frame of `%10`.** -/
theorem kxf_frameRun_n10 (env : CallEnv) (sup : Option Nomm) {a : Nat} {v q : Nomm}
    (hv : FrameRun (runLCM (S := S) (Map := Map) env false sup v)) (hq : FrameRun (runLCM (S := S) (Map := Map) env false sup q)) :
    FrameRun (runLCM (S := S) (Map := Map) env false sup (Nomm.n10 a v q)) := by
  intro goal region g0 g' nex h
  simp only [runLCM] at h
  obtain ⟨next, g1, h1, h⟩ := bind_some h
  obtain ⟨d1, gr1⟩ := frame_simpleNextL h1
  obtain ⟨⟨don, rec, o⟩, g2, h2, h⟩ := bind_some h
  obtain ⟨d2, ld, lr⟩ := frame_intoL h2
  obtain ⟨nexR, g3, h3, h⟩ := bind_some h
  obtain ⟨d3, l3⟩ := frame_pastL h3
  obtain ⟨n2, g4, h4, h⟩ := bind_some h
  obtain ⟨n2', g5, h5, h⟩ := bind_some h
  obtain ⟨n1, g6, h6, h7⟩ := bind_some h
  have r1 : g0.re ≤ g1.re := d1.1
  have r2 : g1.re ≤ g2.re := d2.1
  have r3 : g2.re ≤ g3.re := d3.1
  have hL : ∀ y, LReg next.laz y → FG g0 goal y := fun y hy => Or.symm (gr1 y (gregL_goal.mpr hy))
  have hS : ∀ y, (g1.re ≤ y ∨ LReg next.laz y) → FG g0 goal y := fun y hy => by
    rcases hy with e | e
    · exact Or.inl (by omega)
    · exact hL y e
  obtain ⟨dC, lC⟩ := frame_chain (G := FG g0 goal) hv hq
    (fun y hy => hS y ((ld y hy).symm))
    (fun y hy => hS y ((lr y (l3 y hy)).symm))
    (fun y hy => Or.inl (by omega)) h4 h5 h6 h7
  exact frX_of ((d1.mono fun _ h => h.elim).trans ((d2.mono hS).trans ((d3.mono fun _ h => h.elim).trans dC))) lC


/-! ## The direct call with `mono` `|` -/

/-- **The `%cal` call block after `+simple-next` and `+kerf`** writes only
fresh registers and the goal's. -/
theorem kxf_df_calBlock {Q : Nat → Prop} {b : Bell} {v : List Nat} {goal : CGoalL S} {g g' : Comp.Gen Map}
    {cb : Nat} (hQ : ∀ y, g.re ≤ y → Q y) (hG : ∀ y, GRegL goal y → Q y)
    (h : (do
        let nex ← simpleNextL goal
        let (out, pro) ← kerf nex
        emit ⟨[], [Pole.cal b v pro], Termin.hop (jmp0 out)⟩ : CM Map Nat) g = some (cb, g')) : DF Q g g' := by
  obtain ⟨nex0, g1, h1, h⟩ := bind_some h
  obtain ⟨⟨out, pro⟩, g2, h2, h3⟩ := bind_some h
  obtain ⟨d1, gr1⟩ := frame_simpleNextL h1
  obtain ⟨d2, hpro⟩ := frame_kerf h2
  have r1 : g.re ≤ g1.re := d1.1
  have hL : ∀ y, LReg nex0.laz y → Q y := fun y hy => by
    rcases gr1 y (gregL_goal.mpr hy) with e | e
    · exact hG y e
    · exact hQ y e
  have hP : Q pro := by
    rcases hpro with e | e
    · exact hQ pro (by omega)
    · exact hL pro e
  obtain ⟨d3, -, -⟩ := df_emit (Q := Q) (kdl_bw1 (p := Pole.cal b v pro) rfl hP _) h3
  refine (d1.mono fun _ e => e.elim).trans ((d2.mono fun y hy => ?_).trans d3)
  rcases hy with e | e
  · exact hQ y (by omega)
  · exact hL y e

/-- **The `%cal` path of a direct call** (`callL`, no memo key, no ring,
`sof` false). -/
theorem kxf_frame_calPath (env : CallEnv) {p q : Nomm} {rp rq : CGoalL S → List Nat → CM Map (NextL S)}
    (hp : FrameRun rp) (hq : FrameRun rq) (b : Bell) (bNed : NeedOrd) (goal : CGoalL S) (region : List Nat)
    {g0 g' : Comp.Gen Map} {nex : NextL S}
    (h : (needOrdAllocRegs bNed >>= fun subNed =>
        (match goal with
          | CGoalL.done => emit ⟨[], [], Termin.jmp b (flattenNeed subNed)⟩
          | g => do
              let nex ← simpleNextL g
              let (out, pro) ← kerf nex
              emit ⟨[], [Pole.cal b (flattenNeed subNed) pro], Termin.hop (jmp0 out)⟩ : CM Map Nat) >>= fun cb =>
        (if safeFolFol q = true then pure ⟨ofSure Sure.bunt, jmp0 cb⟩
          else rq (CGoalL.next (ofSure Sure.bunt) (jmp0 cb)) region : CM Map (NextL S)) >>= fun nexFol =>
        pastL env.cod nexFol p region >>= fun nexFol =>
        rp (CGoalL.next (ofSure ⟨subNed, HoonSet.empty⟩) nexFol.th) region >>= fun nexSub =>
        copyL nexSub nexFol.laz : CM Map (NextL S)) g0 = some (nex, g')) : FrX goal g0 g' nex := by
  obtain ⟨subNed, g1, h1, h⟩ := bind_some h
  obtain ⟨⟨k, e1⟩, le1, -, hN⟩ := needOrdAllocRegs_spec bNed g0 g1 subNed h1
  have d1 : DF (FG g0 goal) g0 g1 := df_gen (by rw [e1]) le1
  obtain ⟨cb, g2, h2, h⟩ := bind_some h
  have d2 : DF (FG g0 goal) g1 g2 := by
    cases goal with
    | done => exact (df_emit (blobWr_nil _ _) h2).1
    | next laz th => exact kxf_df_calBlock (fun y hy => Or.inl (by omega)) (fun y hy => Or.inr hy) h2
    | pick z o => exact kxf_df_calBlock (fun y hy => Or.inl (by omega)) (fun y hy => Or.inr hy) h2
  have r2 : g1.re ≤ g2.re := d2.1
  obtain ⟨nq, g3, h3, h⟩ := bind_some h
  obtain ⟨nq', g4, h4, h⟩ := bind_some h
  obtain ⟨np, g5, h5, h6⟩ := bind_some h
  have h3' : kdlFol q rq (CGoalL.next (ofSure Sure.bunt) (jmp0 cb)) region g2 = some (nq, g3) := h3
  obtain ⟨dC, lC⟩ := frame_chain (G := FG g0 goal) (kdl_frame_fol q hq) hp (fun y hy => absurd hy lReg_bunt)
    (fun y hy => Or.inl (hN y (lReg_ofSure.mp hy)).1)
    (fun y hy => Or.inl (by omega)) h3' h4 h5 h6
  exact frX_of (d1.trans (d2.trans dC)) lC

/-- **The frame of a direct call with `mono` `|`**, for any sub-runs with
the frame. -/
theorem kxf_frame_callB (env : CallEnv) (sup : Option Nomm) {p q : Nomm}
    {rp rq : CGoalL S → List Nat → CM Map (NextL S)} (hp : FrameRun rp) (hq : FrameRun rq) (b : Bell)
    (key : Option Noun) :
    FrameRun (fun goal region => (callL env rp rq p q (some (b, key)) sup goal region : CM Map (NextL S))) := by
  intro goal region g0 g' nex h
  cases goal with
  | next laz th =>
    by_cases hd : (env.pure b && noneEquivalentL laz) = true
    · simp only [callL, hd, if_true] at h
      obtain ⟨nq, g1, h1, h⟩ := bind_some h
      obtain ⟨nq', g2, h2, h⟩ := bind_some h
      obtain ⟨np, g3, h3, h4⟩ := bind_some h
      have h1' : kdlFol q rq (CGoalL.next (ofSure Sure.bunt) th) region g0 = some (nq, g1) := h1
      obtain ⟨dC, lC⟩ := frame_chain (G := FG g0 (CGoalL.next laz th)) (kdl_frame_fol q hq) hp
        (fun y hy => absurd hy lReg_bunt) (fun y hy => absurd hy lReg_bunt) (fun y hy => Or.inl hy) h1' h2 h3 h4
      exact frX_of dC lC
    · simp only [callL, hd, Bool.false_eq_true, if_false] at h
      cases key with
      | some k => simp only at h <;> cases h
      | none =>
        cases hr : env.ring b with
        | some _ => simp only [hr] at h <;> cases h
        | none =>
          cases hn : env.need b with
          | none => simp only [hr, hn] at h <;> cases h
          | some bNed =>
            cases hs : env.sof (made p sup) p q b bNed with
            | true => simp only [hr, hn, hs, if_true] at h <;> cases h
            | false =>
              simp only [hr, hn, hs, Bool.false_eq_true, if_false] at h
              exact kxf_frame_calPath env hp hq b bNed (CGoalL.next laz th) region h
  | pick z o =>
    simp only [callL] at h
    cases key with
    | some k => simp only at h <;> cases h
    | none =>
      cases hr : env.ring b with
      | some _ => simp only [hr] at h <;> cases h
      | none =>
        cases hn : env.need b with
        | none => simp only [hr, hn] at h <;> cases h
        | some bNed =>
          cases hs : env.sof (made p sup) p q b bNed with
          | true => simp only [hr, hn, hs, if_true] at h <;> cases h
          | false =>
            simp only [hr, hn, hs, Bool.false_eq_true, if_false] at h
            exact kxf_frame_calPath env hp hq b bNed (CGoalL.pick z o) region h
  | done =>
    simp only [callL] at h
    cases key with
    | some k => simp only at h <;> cases h
    | none =>
      cases hr : env.ring b with
      | some _ => simp only [hr] at h <;> cases h
      | none =>
        cases hn : env.need b with
        | none => simp only [hr, hn] at h <;> cases h
        | some bNed =>
          cases hs : env.sof (made p sup) p q b bNed with
          | true => simp only [hr, hn, hs, if_true] at h <;> cases h
          | false =>
            simp only [hr, hn, hs, Bool.false_eq_true, if_false] at h
            exact kxf_frame_calPath env hp hq b bNed CGoalL.done region h

/-! ## The induction -/

/-- **Every run of `runLCM env false` on `PlainD` has the frame**, with no
precondition. -/
theorem frameRunF_plainD (env : CallEnv) :
    ∀ (nm : Nomm), PlainD nm → ∀ (sup : Option Nomm), FrameRun (runLCM (S := S) (Map := Map) env false sup nm)
  | Nomm.n0 ax, _, sup => kxf_frameRun_n0 env sup ax
  | Nomm.n1 k, _, sup => kxf_frameRun_n1 env sup k
  | Nomm.n3 p, h, sup => kxf_frameRun_n3 env sup (frameRunF_plainD env p h sup)
  | Nomm.n4 p, h, sup => kxf_frameRun_n4 env sup (frameRunF_plainD env p h sup)
  | Nomm.n5 p q, h, sup =>
    kxf_frameRun_n5 env sup (frameRunF_plainD env p h.1 sup) (frameRunF_plainD env q h.2 sup)
  | Nomm.cons p q, h, sup =>
    kxf_frameRun_cons env sup (frameRunF_plainD env p h.1 sup) (frameRunF_plainD env q h.2 sup)
  | Nomm.n7 p q, h, sup =>
    kxf_frameRun_n7 env sup (frameRunF_plainD env q h.2 (some p)) (frameRunF_plainD env p h.1 sup)
  | Nomm.n10 _ v q, h, sup =>
    kxf_frameRun_n10 env sup (frameRunF_plainD env v h.1 sup) (frameRunF_plainD env q h.2 sup)
  | Nomm.n2 p q Option.none, h, sup => fun goal region g0 g1 nex e => by
    simp only [runLCM] at e
    rw [callLM_none] at e
    exact kdl_frame_callL env sup (frameRunF_plainD env p h.1 sup) (frameRunF_plainD env q h.2 sup) goal region
      g0 g1 nex e
  | Nomm.n2 p q (some (b, key)), h, sup => fun goal region g0 g1 nex e => by
    simp only [runLCM] at e
    rw [callLM_false] at e
    exact kxf_frame_callB env sup (frameRunF_plainD env p h.1 sup) (frameRunF_plainD env q h.2 sup) b key goal
      region g0 g1 nex e
  | Nomm.n6 _ _ _, h, _ => h.elim
  | Nomm.n11s _ _ _, h, _ => h.elim
  | Nomm.n11d _ _ _ _, h, _ => h.elim
  | Nomm.n12 _ _, h, _ => h.elim
  | Nomm.mean _ _ _ _ _, h, _ => h.elim

/-! ## Labels and `Fresh` -/

/-- **The `%cal` path with labels.** -/
theorem kxf_htl_calPath (L : LabSteps S Map) (env : CallEnv) {p q : Nomm}
    {rp rq : CGoalL S → List Nat → CM Map (NextL S)}
    (hp : HRL (Map := Map) rp) (hq : HRL (Map := Map) rq) (b : Bell) (bNed : NeedOrd) (goal : CGoalL S)
    (region : List Nat) :
    HT (fun g => GFL (Map := Map) goal g ∧ LG goal g)
      (needOrdAllocRegs bNed >>= fun subNed =>
        (match goal with
          | CGoalL.done => emit ⟨[], [], Termin.jmp b (flattenNeed subNed)⟩
          | g => do
              let nex ← simpleNextL g
              let (out, pro) ← kerf nex
              emit ⟨[], [Pole.cal b (flattenNeed subNed) pro], Termin.hop (jmp0 out)⟩ : CM Map Nat) >>= fun cb =>
        (if safeFolFol q = true then pure ⟨ofSure Sure.bunt, jmp0 cb⟩
          else rq (CGoalL.next (ofSure Sure.bunt) (jmp0 cb)) region : CM Map (NextL S)) >>= fun nexFol =>
        pastL env.cod nexFol p region >>= fun nexFol =>
        rp (CGoalL.next (ofSure ⟨subNed, HoonSet.empty⟩) nexFol.th) region >>= fun nexSub =>
        copyL nexSub nexFol.laz : CM Map (NextL S))
      (fun nex g => Fresh g nex.th ∧ LG nex.goal g) := by
  refine HT.weak (P := GFL (Map := Map) goal) ?_ (fun _ h => h.1)
  refine HT.bind' (HT.quiet (kdl_qm_needOrd bNed) (stab_gfl goal)) fun subNed => ?_
  refine HT.bind' (R := fun (cb : Nat) (g : Comp.Gen Map) => Fresh g (jmp0 cb)) ?_ fun cb => ?_
  · cases goal with
    | done =>
      exact HT.conseq (ht_emitJ (P := fun _ => True) rfl (js_nil rfl) stab_true) (fun _ _ => trivial)
        (fun _ _ h => h.2)
    | next laz th =>
      refine HT.bind' (ht_simpleNextL _) fun nex => HT.bind' (ht_kerf _) fun a => ?_
      rcases a with ⟨out, pro⟩
      exact HT.conseq (ht_emitJ rfl (js_hop fun g h => h) (stab_fresh _)) (fun _ h => h) (fun _ _ h => h.2)
    | pick z o =>
      refine HT.bind' (ht_simpleNextL _) fun nex => HT.bind' (ht_kerf _) fun a => ?_
      rcases a with ⟨out, pro⟩
      exact HT.conseq (ht_emitJ rfl (js_hop fun g h => h) (stab_fresh _)) (fun _ h => h) (fun _ _ h => h.2)
  · exact HT.weak (htl_bin L env.cod (rq := kdlFol q rq) p hp (kdl_hrl_fol q hq) (ofSure Sure.bunt)
      (ofSure ⟨subNed, HoonSet.empty⟩) (jmp0 cb) region) fun g h => ⟨h, ll_ofSure _ _, ll_ofSure _ _⟩

/-- **The direct call with `mono` `|` with labels.** -/
theorem kxf_htl_callB (L : LabSteps S Map) (env : CallEnv) (sup : Option Nomm) {p q : Nomm}
    {rp rq : CGoalL S → List Nat → CM Map (NextL S)}
    (b : Bell) (key : Option Noun) (hp : HRL (Map := Map) rp) (hq : HRL (Map := Map) rq) (goal : CGoalL S)
    (region : List Nat) :
    HT (fun g => GFL (Map := Map) goal g ∧ LG goal g) (callL env rp rq p q (some (b, key)) sup goal region : CM Map (NextL S))
      (fun nex g => Fresh g nex.th ∧ LG nex.goal g) := by
  constructor
  intro g0 nex g' A hP h
  cases goal with
  | next laz th =>
    by_cases hd : (env.pure b && noneEquivalentL laz) = true
    · simp only [callL, hd, if_true] at h
      exact (htl_bin L env.cod (rq := kdlFol q rq) p hp (kdl_hrl_fol q hq) (ofSure Sure.bunt) (ofSure Sure.bunt) th
        region).run g0 nex g' A ⟨hP.1, ll_ofSure _ _, ll_ofSure _ _⟩ h
    · simp only [callL, hd, Bool.false_eq_true, if_false] at h
      cases key with
      | some k => simp only at h <;> cases h
      | none =>
        cases hr : env.ring b with
        | some _ => simp only [hr] at h <;> cases h
        | none =>
          cases hn : env.need b with
          | none => simp only [hr, hn] at h <;> cases h
          | some bNed =>
            cases hs : env.sof (made p sup) p q b bNed with
            | true => simp only [hr, hn, hs, if_true] at h <;> cases h
            | false =>
              simp only [hr, hn, hs, Bool.false_eq_true, if_false] at h
              exact (kxf_htl_calPath L env hp hq b bNed (CGoalL.next laz th) region).run g0 nex g' A hP h
  | pick z o =>
    simp only [callL] at h
    cases key with
    | some k => simp only at h <;> cases h
    | none =>
      cases hr : env.ring b with
      | some _ => simp only [hr] at h <;> cases h
      | none =>
        cases hn : env.need b with
        | none => simp only [hr, hn] at h <;> cases h
        | some bNed =>
          cases hs : env.sof (made p sup) p q b bNed with
          | true => simp only [hr, hn, hs, if_true] at h <;> cases h
          | false =>
            simp only [hr, hn, hs, Bool.false_eq_true, if_false] at h
            exact (kxf_htl_calPath L env hp hq b bNed (CGoalL.pick z o) region).run g0 nex g' A hP h
  | done =>
    simp only [callL] at h
    cases key with
    | some k => simp only at h <;> cases h
    | none =>
      cases hr : env.ring b with
      | some _ => simp only [hr] at h <;> cases h
      | none =>
        cases hn : env.need b with
        | none => simp only [hr, hn] at h <;> cases h
        | some bNed =>
          cases hs : env.sof (made p sup) p q b bNed with
          | true => simp only [hr, hn, hs, if_true] at h <;> cases h
          | false =>
            simp only [hr, hn, hs, Bool.false_eq_true, if_false] at h
            exact (kxf_htl_calPath L env hp hq b bNed CGoalL.done region).run g0 nex g' A hP h

theorem kxf_labRun (env : CallEnv) (L : LabSteps S Map) : ∀ (nm : Nomm), PlainD nm → ∀ (sup : Option Nomm),
    HRL (Map := Map) (runLCM (S := S) env false sup nm)
  | Nomm.cons p q, h, sup, goal, region => by
    have ihp := kxf_labRun env L p h.1 sup
    have ihq := kxf_labRun env L q h.2 sup
    unfold runLCM
    refine HT.bind' (Q := fun (nex : NextL S) (g : Comp.Gen Map) => Fresh g nex.th ∧ LG nex.goal g)
      (R := fun (goal' : CGoalL S) (g : Comp.Gen Map) => GFL goal' g ∧ LG goal' g) ?_ fun goal' => ?_
    · cases goal with
      | done =>
        refine HT.weak (P := fun _ => True) ?_ (fun _ _ => trivial)
        exact HT.bind' (HT.quiet QM.re' stab_true) fun r =>
          HT.bind' (ht_emitJ rfl (js_nil rfl) stab_true) fun o => HT.pure' fun g h => ⟨h.2, lg_ofSure _ _ _⟩
      | next laz th => exact HT.pure' fun g h => h
      | pick z o => exact HT.pure' fun g h => h
    · cases goal' with
      | pick z o =>
        exact HT.bind' (HT.conseq (ht_emitJ rfl (js_nil rfl) stab_true) (fun _ _ => trivial) (fun _ _ h => h))
          fun o => HT.weak (htl_bin L env.cod p ihp ihq _ _ _ _) fun g h => ⟨h.2, ll_ofSure _ _, ll_ofSure _ _⟩
      | done => exact HT.fail
      | next laz th =>
        refine HT.bind' (HT.weak (htl_splitL L ⟨laz, th⟩) fun g h => h) fun a => ?_
        rcases a with ⟨hed, tel, o⟩
        refine HT.bind' (HT.weak (HT.frame (htl_pastL L env.cod ⟨hed, jmp0 o⟩ q region) (stab_ll tel))
          fun g h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩) fun nexh => ?_
        exact HT.weak (htl_bin L env.cod p ihp ihq tel nexh.laz nexh.th region) fun g h => ⟨h.1.1, h.2, h.1.2⟩
  | Nomm.n0 ax, _, sup, goal, region => by
    unfold runLCM
    refine HT.ite' _ (htl_bombL _) (HT.bind' (htl_simpleNextL _) fun nex => HT.ite' _ (HT.pure' fun g h => h) ?_)
    cases hf : Lazy.fromL ax nex.laz with
    | none => exact HT.fail
    | some laz => exact HT.pure' fun g h => ⟨h.1, L.fromL (Q := fun n => n < g.bo) hf h.2.1 h.2.2⟩
  | Nomm.n1 k, _, sup, goal, region => by
    unfold runLCM
    cases goal with
    | done =>
      refine HT.weak (P := fun _ => True) ?_ (fun _ _ => trivial)
      exact HT.bind' (HT.quiet QM.re' stab_true) fun r =>
        HT.bind' (ht_emitJ rfl (js_nil rfl) stab_true) fun o => HT.pure' fun g h => ⟨h.2, lg_ofSure _ _ _⟩
    | pick z o =>
      exact HT.ite' _ (HT.pure' fun g h => ⟨h.1.1, lg_ofSure _ _ _⟩)
        (HT.ite' _ (HT.pure' fun g h => ⟨h.1.2, lg_ofSure _ _ _⟩) (htl_bombL _))
    | next laz th =>
      exact HT.bind' (HT.weak (ht_medeL _ _ _) fun _ h => h.1) fun o => HT.pure' fun g h => ⟨h, lg_ofSure _ _ _⟩
  | Nomm.n3 p, h, sup, goal, region => by
    have ih := kxf_labRun env L p h sup
    unfold runLCM
    cases goal with
    | pick z o =>
      refine HT.weak (P := GFL (Map := Map) (CGoalL.pick (S := S) z o)) ?_ (fun _ h => h.1)
      exact HT.bind' (HT.quiet QM.re' (stab_gfl (CGoalL.pick (S := S) z o))) fun r =>
        htl_tail ih rfl (js_two rfl fun g h => h) (stab_gfl (CGoalL.pick (S := S) z o)) (fun _ => lazyReg r) _
    | done =>
      refine HT.bind' (HT.conseq ht_doneBlocks (fun _ _ => trivial) (fun _ _ h => h)) fun a => ?_
      rcases a with ⟨o0, o1⟩
      exact HT.bind' (HT.quiet QM.re' (stab_and (stab_fresh _) (stab_fresh _))) fun r =>
        htl_tail ih rfl (js_two rfl fun g h => h) (stab_and (stab_fresh _) (stab_fresh _)) (fun _ => lazyReg r) _
    | next laz th =>
      refine HT.ite' _ (ih _ _) (HT.bind' (HT.weak (ht_collapse ⟨laz, th⟩) fun _ h => h.1) fun a => ?_)
      rcases a with _ | ⟨r, o⟩
      · exact HT.fail
      · refine HT.bind' (HT.conseq (ht_forl r o) (fun _ h => h r o rfl) (fun _ _ h => h)) fun x => ?_
        rcases x with ⟨z, o'⟩
        exact HT.bind' (HT.quiet QM.re' (stab_and (stab_fresh _) (stab_fresh _))) fun r' =>
          htl_tail ih rfl (js_two rfl fun g h => h) (stab_and (stab_fresh _) (stab_fresh _)) (fun _ => lazyReg r') _
  | Nomm.n4 p, h, sup, goal, region => by
    have ih := kxf_labRun env L p h sup
    unfold runLCM
    cases goal with
    | done =>
      refine HT.weak (P := fun _ => True) ?_ (fun _ _ => trivial)
      exact HT.bind' (HT.quiet QM.re' stab_true) fun _ => HT.bind' (HT.quiet QM.re' stab_true) fun arg =>
        htl_tail ih rfl (js_nil rfl) stab_true (fun _ => lazyReg arg) _
    | pick z o =>
      refine HT.weak (P := GFL (Map := Map) (CGoalL.pick (S := S) z o)) ?_ (fun _ h => h.1)
      exact HT.bind' (HT.quiet QM.re' (stab_gfl (CGoalL.pick (S := S) z o))) fun _ =>
        HT.bind' (HT.quiet QM.re' (stab_gfl (CGoalL.pick (S := S) z o))) fun arg =>
          htl_tail ih rfl (js_two rfl fun g h => h) (stab_gfl (CGoalL.pick (S := S) z o)) (fun _ => lazyReg arg) _
    | next laz th =>
      refine HT.bind' (HT.weak (HT.frame (ht_collapse ⟨laz, th⟩) (stab_fresh th)) fun _ h => ⟨h.1, h.1⟩)
        fun a => ?_
      refine HT.bind' (Q := fun (nex : NextL S) (g : Comp.Gen Map) => Fresh g nex.th ∧ LG nex.goal g)
        (R := fun (x : Nat × Nat) (g : Comp.Gen Map) => Fresh g (jmp0 x.2)) ?_ fun x => ?_
      · cases a with
        | some x => exact HT.pure' fun g h => h.1 x.1 x.2 rfl
        | none =>
          refine HT.bind' (HT.conseq (ht_qf QM.re' th) (fun _ h => h.2) (fun _ _ h => h)) fun r => ?_
          exact HT.ite' _ (HT.pure' fun g h => fresh_jmp0 h) HT.fail
      · rcases x with ⟨pro, th'⟩
        exact HT.bind' (ht_qf QM.re' _) fun arg =>
          htl_tail ih rfl (js_hop fun g h => h) (stab_fresh _) (fun _ => lazyReg arg) _
  | Nomm.n5 p q, h, sup, goal, region => by
    have ihp := kxf_labRun env L p h.1 sup
    have ihq := kxf_labRun env L q h.2 sup
    unfold runLCM
    refine HT.weak (P := GFL (Map := Map) goal) ?_ (fun _ h => h.1)
    refine HT.bind' (HT.quiet QM.re' (stab_gfl goal)) fun rp => HT.bind' (HT.quiet QM.re' (stab_gfl goal)) fun rq =>
      HT.bind' (R := fun (o : Nat) (g : Comp.Gen Map) => Fresh g (jmp0 o)) ?_ fun o =>
        HT.weak (htl_bin L env.cod p ihp ihq _ _ _ _) fun g h => ⟨h, ll_ofSure _ _, ll_ofSure _ _⟩
    cases goal with
    | pick z o =>
      exact HT.conseq (ht_emitJ rfl (js_two rfl fun g h => h) (stab_gfl (CGoalL.pick (S := S) z o))) (fun _ h => h)
        (fun _ _ h => h.2)
    | done =>
      refine HT.bind' (HT.conseq ht_doneBlocks (fun _ _ => trivial) (fun _ _ h => h)) fun a => ?_
      rcases a with ⟨o0, o1⟩
      exact HT.conseq (ht_emitJ rfl (js_two rfl fun g h => h) (stab_and (stab_fresh _) (stab_fresh _)))
        (fun _ h => h) (fun _ _ h => h.2)
    | next laz th =>
      refine HT.bind' (HT.weak (HT.frame (ht_collapse ⟨laz, th⟩) (stab_fresh th)) fun _ h => ⟨h, h⟩) fun a => ?_
      cases a with
      | none =>
        refine HT.ite' _ ?_ HT.fail
        exact HT.conseq (ht_emitJ rfl (js_hop fun g h => fresh_jmp0 h) (stab_fresh th)) (fun _ h => h.2)
          (fun _ _ h => h.2)
      | some x =>
        rcases x with ⟨r, o⟩
        refine HT.bind' (HT.conseq (ht_forl r o) (fun _ h => h.1 r o rfl) (fun _ _ h => h)) fun x => ?_
        rcases x with ⟨z, o'⟩
        exact HT.conseq (ht_emitJ rfl (js_two rfl fun g h => h) (stab_and (stab_fresh _) (stab_fresh _)))
          (fun _ h => h) (fun _ _ h => h.2)
  | Nomm.n7 p q, h, sup, goal, region => by
    unfold runLCM
    exact HT.bind' (kxf_labRun env L q h.2 (some p) goal region) fun nex =>
      HT.weak (kxf_labRun env L p h.1 sup nex.goal region) fun _ h => h
  | Nomm.n10 a v q, h, sup, goal, region => by
    have ihv := kxf_labRun env L v h.1 sup
    have ihq := kxf_labRun env L q h.2 sup
    unfold runLCM
    refine HT.bind' (htl_simpleNextL _) fun next => HT.bind' (HT.weak (htl_intoL L _ _) fun g h => h) fun x => ?_
    rcases x with ⟨don, rec, o⟩
    refine HT.bind' (HT.weak (HT.frame (htl_pastL L env.cod ⟨rec, jmp0 o⟩ v region) (stab_ll don))
      fun g h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩) fun nexR => ?_
    exact HT.weak (htl_bin L env.cod q ihq ihv don nexR.laz nexR.th region) fun g h => ⟨h.1.1, h.2, h.1.2⟩
  | Nomm.n2 p q Option.none, h, sup, goal, region => by
    unfold runLCM
    rw [callLM_none]
    exact htl_callL L env p q sup (kxf_labRun env L p h.1 sup) (kxf_labRun env L q h.2 sup) goal region
  | Nomm.n2 p q (some (b, key)), h, sup, goal, region => by
    unfold runLCM
    rw [callLM_false]
    exact kxf_htl_callB L env sup b key (kxf_labRun env L p h.1 sup) (kxf_labRun env L q h.2 sup) goal region

/-- **`LabUniq` and `Fresh` at run level on `PlainD`** (`runLCM env false`,
direct calls included). -/
theorem labRunF_plainD (env : CallEnv) : ∀ (nm : Nomm), PlainD nm → ∀ (sup : Option Nomm),
    HRL (Map := Map) (runLCM (S := S) env false sup nm) :=
  kxf_labRun env labSteps

end Raw
end SkaModel
end Formalization
