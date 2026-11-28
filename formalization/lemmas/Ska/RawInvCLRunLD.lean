import lemmas.Ska.RawInvCLFrameRun
import lemmas.Ska.RawInvCLLabAll
import lemmas.Ska.RawInvCLSABase
import lemmas.Ska.CompRunLCM
import lemmas.Ska.RawInvCLPlainD
import lemmas.Ska.CompTopOK

/-!
# The frame of a run with direct calls (`runLCM env true` on `PlainD`)

README Gaps 14 (b), track D (fork `kdl`).  The liveness induction `LRL`
asks, at the second run of `%5`, cons, `%10` and the calls, the frame of the
first run (`FrameRun`, `RawInvCLFrame.lean`).  Here it is for the runs with
the flag `mono` and DIRECT calls:

* `kdl_frameRun_*`: the arms of `frameRun_plain` (`RawInvCLFrameRun.lean`,
  `RawInvCLFrameCons.lean`) for `runLCM env true`, the text theirs.
* `kdl_frame_callL`: the indirect call for any sub-runs with the frame.
* `kdl_df_monoTryLoop`, `kdl_frame_monoBlocks`: the blocks of
  `+mono-try-call` write only fresh registers (and `+kerf`'s `pro`).
* `kdl_frame_callDM`: the direct call (the drop path and the
  `monoBlocks` path).
* **`frameRunM_plainD`**: every run of `runLCM env true` on `PlainD` has the
  frame, with no precondition.
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
theorem kdl_frameRun_n0 (env : CallEnv) (sup : Option Nomm) (ax : Nat) :
    FrameRun (runLCM (S := S) (Map := Map) env true sup (Nomm.n0 ax)) := by
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
theorem kdl_frameRun_n1 (env : CallEnv) (sup : Option Nomm) (k : Noun) :
    FrameRun (runLCM (S := S) (Map := Map) env true sup (Nomm.n1 k)) := by
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
theorem kdl_frameRun_n3 (env : CallEnv) (sup : Option Nomm) {p : Nomm}
    (hp : FrameRun (runLCM (S := S) (Map := Map) env true sup p)) :
    FrameRun (runLCM (S := S) (Map := Map) env true sup (Nomm.n3 p)) := by
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
theorem kdl_frameRun_n4 (env : CallEnv) (sup : Option Nomm) {p : Nomm}
    (hp : FrameRun (runLCM (S := S) (Map := Map) env true sup p)) :
    FrameRun (runLCM (S := S) (Map := Map) env true sup (Nomm.n4 p)) := by
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
theorem kdl_frameRun_n5 (env : CallEnv) (sup : Option Nomm) {p q : Nomm}
    (hp : FrameRun (runLCM (S := S) (Map := Map) env true sup p)) (hq : FrameRun (runLCM (S := S) (Map := Map) env true sup q)) :
    FrameRun (runLCM (S := S) (Map := Map) env true sup (Nomm.n5 p q)) := by
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
theorem kdl_frameRun_n7 (env : CallEnv) (sup : Option Nomm) {p q : Nomm}
    (hq : FrameRun (runLCM (S := S) (Map := Map) env true (some p) q)) (hp : FrameRun (runLCM (S := S) (Map := Map) env true sup p)) :
    FrameRun (runLCM (S := S) (Map := Map) env true sup (Nomm.n7 p q)) := by
  intro goal region g0 g1 nex h
  simp only [runLCM] at h
  obtain ⟨nexq, gq, hrq, hrp⟩ := bind_some h
  have F1 := hq _ _ _ _ _ hrq
  exact frX_sub (frL_iff.mp F1.1) F1.2 (hp _ _ _ _ _ hrp)

/-! ## The induction -/


/-- **The frame of a cons.** -/
theorem kdl_frameRun_cons (env : CallEnv) (sup : Option Nomm) {p q : Nomm}
    (hp : FrameRun (runLCM (S := S) (Map := Map) env true sup p)) (hq : FrameRun (runLCM (S := S) (Map := Map) env true sup q)) :
    FrameRun (runLCM (S := S) (Map := Map) env true sup (Nomm.cons p q)) := by
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
theorem kdl_frameRun_n10 (env : CallEnv) (sup : Option Nomm) {a : Nat} {v q : Nomm}
    (hv : FrameRun (runLCM (S := S) (Map := Map) env true sup v)) (hq : FrameRun (runLCM (S := S) (Map := Map) env true sup q)) :
    FrameRun (runLCM (S := S) (Map := Map) env true sup (Nomm.n10 a v q)) := by
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


/-! ## The calls -/

/-- **The frame of the indirect call**, for any sub-runs with the frame. -/
theorem kdl_frame_callL (env : CallEnv) (sup : Option Nomm) {p q : Nomm}
    {rp rq : CGoalL S → List Nat → CM Map (NextL S)} (hp : FrameRun rp) (hq : FrameRun rq) :
    FrameRun (fun goal region => (callL env rp rq p q Option.none sup goal region : CM Map (NextL S))) := by
  intro goal region g0 g' nex h
  simp only [callL] at h
  obtain ⟨nex0, g1, h1, h⟩ := bind_some h
  obtain ⟨⟨out, pro⟩, g2, h2, h⟩ := bind_some h
  obtain ⟨rSub, ga, ha, h⟩ := bind_some h
  rw [re_apply] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  obtain ⟨rFol, gb, hb, h⟩ := bind_some h
  rw [re_apply] at hb
  simp only [Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  obtain ⟨o, g3, h3, h⟩ := bind_some h
  obtain ⟨nexF, g4, h4, h⟩ := bind_some h
  obtain ⟨nexF', g5, h5, h⟩ := bind_some h
  obtain ⟨nexS, g6, h6, h7⟩ := bind_some h
  obtain ⟨d1, gr1⟩ := frame_simpleNextL h1
  obtain ⟨d2, hpro⟩ := frame_kerf h2
  have r1 : g0.re ≤ g1.re := d1.1
  have r2 : g1.re ≤ g2.re := d2.1
  have hL : ∀ y, LReg nex0.laz y → FG g0 goal y := fun y hy => by
    rcases gr1 y (gregL_goal.mpr hy) with e | e
    · exact Or.inr e
    · exact Or.inl e
  have dR : DF (FG g0 goal) g2 { { g2 with re := g2.re + 1 } with re := g2.re + 1 + 1 } :=
    df_gen rfl (by show g2.re ≤ g2.re + 1 + 1; omega)
  have hQp : FG g0 goal pro := by
    rcases hpro with e | e
    · exact Or.inl (by omega)
    · exact hL pro e
  obtain ⟨d3, -, e3⟩ := df_emit (blobWr_one (Q := FG g0 goal) (p := Pole.nok g2.re (g2.re + 1) pro) (fun x hx => by
    simp only [poleWr, List.mem_cons, List.mem_nil_iff, or_false] at hx; rw [hx]; exact hQp) _) h3
  have e3' : g3.re = g2.re + 1 + 1 := e3
  obtain ⟨dC, lC⟩ := frame_chain (G := FG g0 goal) hq hp
    (fun y hy => Or.inl (by have := lReg_ofSure.mp hy; simp only [lazyReg, NMem] at this; omega))
    (fun y hy => Or.inl (by have := lReg_ofSure.mp hy; simp only [lazyReg, NMem] at this; omega))
    (fun y hy => Or.inl (by omega)) h4 h5 h6 h7
  refine ⟨(d1.mono fun _ h => h.elim).trans ((d2.mono fun y hy => ?_).trans (dR.trans (d3.trans dC))),
    fun y hy => ?_⟩
  · rcases hy with e | e
    · exact Or.inl (by omega)
    · exact hL y e
  · rcases lC y (gregL_goal.mp hy) with e | e
    · exact Or.inr e
    · exact Or.inl e

/-- **The blocks of `+mono-try-call` write only fresh registers and the
registers of the callee's need.** -/
theorem kdl_df_monoTryLoop (fail : Nat) : ∀ (ned : Need) (r o : Nat) (g g' : Comp.Gen Map) (x : Nat),
    monoTryLoop fail ned r o g = some (x, g') → DF (fun y => g.re ≤ y ∨ NMem ned y) g g'
  | Need.none, r, o, g, g', x, h => by
    simp only [monoTryLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact DF.refl _ _
  | Need.this rn, r, o, g, g', x, h => by
    simp only [monoTryLoop] at h
    split at h
    · cases h
    · exact (df_emit (blobWr_one (fun y hy => by
        simp only [poleWr, List.mem_cons, List.mem_nil_iff, or_false] at hy
        exact Or.inr hy) _) h).1
  | Need.pair hn tn, r, o, g, g', x, h => by
    simp only [monoTryLoop] at h
    obtain ⟨rt, g1, h1, h⟩ := bind_some h
    obtain ⟨d1, e1, f1⟩ := df_re (Q := fun y => g.re ≤ y ∨ NMem (Need.pair hn tn) y) h1
    obtain ⟨rh, g2, h2, h⟩ := bind_some h
    obtain ⟨d2, e2, f2⟩ := df_re (Q := fun y => g.re ≤ y ∨ NMem (Need.pair hn tn) y) h2
    obtain ⟨ot, g3, h3, h⟩ := bind_some h
    have d3 := kdl_df_monoTryLoop fail tn rt o g2 g3 ot h3
    obtain ⟨oh, g4, h4, h⟩ := bind_some h
    have d4 := kdl_df_monoTryLoop fail hn rh ot g3 g4 oh h4
    obtain ⟨os, g5, h5, h⟩ := bind_some h
    have r3 : g2.re ≤ g3.re := d3.1
    obtain ⟨d5, -, -⟩ := df_emit (Q := fun y => g.re ≤ y ∨ NMem (Need.pair hn tn) y) (b :=
      ⟨[], [Pole.hed r rh, Pole.tal r rt], Termin.hop (jmp0 oh)⟩) (by
        refine ⟨fun x hx => absurd hx List.not_mem_nil, opsWr_cons ?_ (opsWr_cons ?_ (opsWr_nil _))⟩
        · intro y hy; simp only [poleWr, List.mem_cons, List.mem_nil_iff, or_false] at hy; subst hy; omega
        · intro y hy; simp only [poleWr, List.mem_cons, List.mem_nil_iff, or_false] at hy; subst hy; omega) h5
    obtain ⟨d6, -, -⟩ := df_emit (Q := fun y => g.re ≤ y ∨ NMem (Need.pair hn tn) y) (blobWr_nil _ _) h
    refine d1.trans (d2.trans ((d3.mono fun y hy => ?_).trans ((d4.mono fun y hy => ?_).trans (d5.trans d6))))
    · rcases hy with hy | hy
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inr hy)
    · rcases hy with hy | hy
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl hy)
  | Need.both rn hn tn, r, o, g, g', x, h => by
    simp only [monoTryLoop] at h
    obtain ⟨rt, g1, h1, h⟩ := bind_some h
    obtain ⟨d1, e1, f1⟩ := df_re (Q := fun y => g.re ≤ y ∨ NMem (Need.both rn hn tn) y) h1
    obtain ⟨rh, g2, h2, h⟩ := bind_some h
    obtain ⟨d2, e2, f2⟩ := df_re (Q := fun y => g.re ≤ y ∨ NMem (Need.both rn hn tn) y) h2
    obtain ⟨ot, g3, h3, h⟩ := bind_some h
    have d3 := kdl_df_monoTryLoop fail tn rt o g2 g3 ot h3
    obtain ⟨oh, g4, h4, h⟩ := bind_some h
    have d4 := kdl_df_monoTryLoop fail hn rh ot g3 g4 oh h4
    have r3 : g2.re ≤ g3.re := d3.1
    split at h
    · cases h
    obtain ⟨os, g5, h5, h⟩ := bind_some h
    obtain ⟨d5, -, -⟩ := df_emit (Q := fun y => g.re ≤ y ∨ NMem (Need.both rn hn tn) y) (b :=
      ⟨[], [Pole.hed r rh, Pole.tal r rt, Pole.mov r rn], Termin.hop (jmp0 oh)⟩) (by
        refine ⟨fun x hx => absurd hx List.not_mem_nil, opsWr_cons ?_ (opsWr_cons ?_ (opsWr_cons ?_ (opsWr_nil _)))⟩
        · intro y hy; simp only [poleWr, List.mem_cons, List.mem_nil_iff, or_false] at hy; subst hy; omega
        · intro y hy; simp only [poleWr, List.mem_cons, List.mem_nil_iff, or_false] at hy; subst hy; omega
        · intro y hy; simp only [poleWr, List.mem_cons, List.mem_nil_iff, or_false] at hy; subst hy
          exact Or.inr (Or.inl rfl)) h5
    obtain ⟨d6, -, -⟩ := df_emit (Q := fun y => g.re ≤ y ∨ NMem (Need.both rn hn tn) y) (blobWr_nil _ _) h
    refine d1.trans (d2.trans ((d3.mono fun y hy => ?_).trans ((d4.mono fun y hy => ?_).trans (d5.trans d6))))
    · rcases hy with hy | hy
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inr (Or.inr hy))
    · rcases hy with hy | hy
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inr (Or.inl hy))

theorem kdl_bw1 {Q : Nat → Prop} {p : Pole} {x : Nat} (hp : poleWr p = [x]) (hx : Q x) (fin : Termin) :
    BlobWr Q ⟨[], [p], fin⟩ :=
  blobWr_one (fun y hy => by rw [hp] at hy; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy; subst hy; exact hx) _

/-- **The call blocks of a direct call write only fresh registers, the
callee's need's and `+kerf`'s `pro`**; `sub-pes` is fresh. -/
theorem kdl_frame_monoBlocks {Q : Nat → Prop} {b : Bell} {subNed : Need} {goal : CGoalL S} {g g' : Comp.Gen Map}
    {x : Nat × Nat} (hQ : ∀ y, g.re ≤ y → Q y) (hN : ∀ y, NMem subNed y → Q y) (hG : ∀ y, GRegL goal y → Q y)
    (h : monoBlocks b subNed goal g = some (x, g')) : DF Q g g' ∧ g.re ≤ x.1 := by
  have hT : ∀ {g1 g2 : Comp.Gen Map} {opt sub pes o : Nat}, g.re ≤ g1.re →
      monoTryCall subNed opt sub pes g1 = some (o, g2) → DF Q g1 g2 := fun {g1 g2 opt sub pes o} le e =>
    (kdl_df_monoTryLoop pes subNed sub opt g1 g2 o e).mono fun y hy => by
      rcases hy with hy | hy
      · exact hQ y (by omega)
      · exact hN y hy
  cases goal with
  | done =>
    simp only [monoBlocks] at h
    obtain ⟨sp, g1, h1, h⟩ := bind_some h
    obtain ⟨d1, e1, f1⟩ := df_re (Q := Q) h1
    obtain ⟨opt, g2, h2, h⟩ := bind_some h
    obtain ⟨d2, -, f2⟩ := df_emit (Q := Q) (blobWr_nil _ _) h2
    obtain ⟨pes, g3, h3, h⟩ := bind_some h
    obtain ⟨d3, -, f3⟩ := df_emit (Q := Q) (blobWr_nil _ _) h3
    obtain ⟨o, g4, h4, h⟩ := bind_some h
    have d4 := hT (by omega) h4
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨d1.trans (d2.trans (d3.trans d4)), by simp only; omega⟩
  | pick z o0 =>
    simp only [monoBlocks] at h
    obtain ⟨nx, g1, h1, h⟩ := bind_some h
    obtain ⟨d1, gr1⟩ := frame_simpleNextL h1
    obtain ⟨⟨out, pro⟩, g2, h2, h⟩ := bind_some h
    obtain ⟨d2, hpro⟩ := frame_kerf h2
    have r1 : g.re ≤ g1.re := d1.1
    have r2 : g1.re ≤ g2.re := d2.1
    have hL : ∀ y, LReg nx.laz y → Q y := fun y hy => by
      rcases gr1 y (gregL_goal.mpr hy) with e | e
      · exact hG y e
      · exact hQ y e
    have hP : Q pro := by
      rcases hpro with e | e
      · exact hQ pro (by omega)
      · exact hL pro e
    obtain ⟨mg, g3, h3, h⟩ := bind_some h
    obtain ⟨d3, e3, f3⟩ := df_re (Q := Q) h3
    obtain ⟨sp, g4, h4, h⟩ := bind_some h
    obtain ⟨d4, e4, f4⟩ := df_re (Q := Q) h4
    obtain ⟨om, g5, h5, h⟩ := bind_some h
    obtain ⟨d5, -, f5⟩ := df_emit (Q := Q) (b := ⟨[mg], [Pole.mov mg pro], Termin.hop (jmp0 out)⟩)
      ⟨fun y hy => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy; subst hy; exact hQ _ (by omega),
        opsWr_cons (fun y hy => by simp only [poleWr, List.mem_cons, List.mem_nil_iff, or_false] at hy; subst hy; exact hP)
          (opsWr_nil _)⟩ h5
    obtain ⟨po, g6, h6, h⟩ := bind_some h
    obtain ⟨d6, e6, f6⟩ := df_re (Q := Q) h6
    obtain ⟨pp, g7, h7, h⟩ := bind_some h
    obtain ⟨d7, e7, f7⟩ := df_re (Q := Q) h7
    obtain ⟨opt, g8, h8, h⟩ := bind_some h
    obtain ⟨d8, -, f8⟩ := df_emit (Q := Q) (kdl_bw1 (p := Pole.cal b (flattenNeed subNed) po) rfl (hQ _ (by omega)) _) h8
    obtain ⟨pes, g9, h9, h⟩ := bind_some h
    obtain ⟨d9, -, f9⟩ := df_emit (Q := Q) (kdl_bw1 (p := Pole.csl b sp pp) rfl (hQ _ (by omega)) _) h9
    obtain ⟨o, g10, h10, h⟩ := bind_some h
    have d10 := hT (by omega) h10
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨(d1.mono fun _ e => e.elim).trans ((d2.mono fun y hy => ?_).trans (d3.trans (d4.trans (d5.trans
      (d6.trans (d7.trans (d8.trans (d9.trans d10)))))))), by simp only; omega⟩
    rcases hy with e | e
    · exact hQ y (by omega)
    · exact hL y e
  | next laz th =>
    simp only [monoBlocks] at h
    obtain ⟨nx, g1, h1, h⟩ := bind_some h
    obtain ⟨d1, gr1⟩ := frame_simpleNextL h1
    obtain ⟨⟨out, pro⟩, g2, h2, h⟩ := bind_some h
    obtain ⟨d2, hpro⟩ := frame_kerf h2
    have r1 : g.re ≤ g1.re := d1.1
    have r2 : g1.re ≤ g2.re := d2.1
    have hL : ∀ y, LReg nx.laz y → Q y := fun y hy => by
      rcases gr1 y (gregL_goal.mpr hy) with e | e
      · exact hG y e
      · exact hQ y e
    have hP : Q pro := by
      rcases hpro with e | e
      · exact hQ pro (by omega)
      · exact hL pro e
    obtain ⟨mg, g3, h3, h⟩ := bind_some h
    obtain ⟨d3, e3, f3⟩ := df_re (Q := Q) h3
    obtain ⟨sp, g4, h4, h⟩ := bind_some h
    obtain ⟨d4, e4, f4⟩ := df_re (Q := Q) h4
    obtain ⟨om, g5, h5, h⟩ := bind_some h
    obtain ⟨d5, -, f5⟩ := df_emit (Q := Q) (b := ⟨[mg], [Pole.mov mg pro], Termin.hop (jmp0 out)⟩)
      ⟨fun y hy => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy; subst hy; exact hQ _ (by omega),
        opsWr_cons (fun y hy => by simp only [poleWr, List.mem_cons, List.mem_nil_iff, or_false] at hy; subst hy; exact hP)
          (opsWr_nil _)⟩ h5
    obtain ⟨po, g6, h6, h⟩ := bind_some h
    obtain ⟨d6, e6, f6⟩ := df_re (Q := Q) h6
    obtain ⟨pp, g7, h7, h⟩ := bind_some h
    obtain ⟨d7, e7, f7⟩ := df_re (Q := Q) h7
    obtain ⟨opt, g8, h8, h⟩ := bind_some h
    obtain ⟨d8, -, f8⟩ := df_emit (Q := Q) (kdl_bw1 (p := Pole.cal b (flattenNeed subNed) po) rfl (hQ _ (by omega)) _) h8
    obtain ⟨pes, g9, h9, h⟩ := bind_some h
    obtain ⟨d9, -, f9⟩ := df_emit (Q := Q) (kdl_bw1 (p := Pole.csl b sp pp) rfl (hQ _ (by omega)) _) h9
    obtain ⟨o, g10, h10, h⟩ := bind_some h
    have d10 := hT (by omega) h10
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨(d1.mono fun _ e => e.elim).trans ((d2.mono fun y hy => ?_).trans (d3.trans (d4.trans (d5.trans
      (d6.trans (d7.trans (d8.trans (d9.trans d10)))))))), by simp only; omega⟩
    rcases hy with e | e
    · exact hQ y (by omega)
    · exact hL y e

/-- The first run of a direct call's chain: `q`, or nothing when its
formula is safe (`safeFolFol`). -/
def kdlFol (q : Nomm) (rq : CGoalL S → List Nat → CM Map (NextL S)) : CGoalL S → List Nat → CM Map (NextL S)
  | CGoalL.next l th, region => if safeFolFol q then pure ⟨ofSure Sure.bunt, th⟩ else rq (CGoalL.next l th) region
  | goal, region => rq goal region

theorem kdl_frame_fol (q : Nomm) {rq : CGoalL S → List Nat → CM Map (NextL S)} (hq : FrameRun rq) :
    FrameRun (kdlFol q rq) := by
  intro goal region g0 g1 nex h
  cases goal with
  | next l th =>
    simp only [kdlFol] at h
    split at h
    · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact frX_of (DF.refl _ _) fun y hy => absurd hy lReg_bunt
    · exact hq _ _ _ _ _ h
  | pick z o => exact hq _ _ _ _ _ h
  | done => exact hq _ _ _ _ _ h

/-- **The `monoBlocks` path of a direct call.** -/
theorem kdl_frame_dmPath (env : CallEnv) {p q : Nomm} {rp rq : CGoalL S → List Nat → CM Map (NextL S)}
    (hp : FrameRun rp) (hq : FrameRun rq) (b : Bell) (bNed : NeedOrd) (goal : CGoalL S) (region : List Nat)
    {g0 g' : Comp.Gen Map} {nex : NextL S}
    (h : (needOrdAllocRegs bNed >>= fun subNed => monoBlocks b subNed goal >>= fun x =>
        (if safeFolFol q = true then pure ⟨ofSure Sure.bunt, jmp0 x.2⟩
          else rq (CGoalL.next (ofSure Sure.bunt) (jmp0 x.2)) region : CM Map (NextL S)) >>= fun nexFol =>
        pastL env.cod nexFol p region >>= fun nexFol =>
        rp (CGoalL.next (ofSure (lazyReg x.1)) nexFol.th) region >>= fun nexSub =>
        copyL nexSub nexFol.laz : CM Map (NextL S)) g0 = some (nex, g')) : FrX goal g0 g' nex := by
  obtain ⟨subNed, g1, h1, h⟩ := bind_some h
  obtain ⟨⟨k, e1⟩, le1, -, hN⟩ := needOrdAllocRegs_spec bNed g0 g1 subNed h1
  have d1 : DF (FG g0 goal) g0 g1 := df_gen (by rw [e1]) le1
  obtain ⟨⟨sp, cb⟩, g2, h2, h⟩ := bind_some h
  obtain ⟨d2, hsp⟩ := kdl_frame_monoBlocks (Q := FG g0 goal) (fun y hy => Or.inl (by omega))
    (fun y hy => Or.inl (hN y hy).1) (fun y hy => Or.inr hy) h2
  have r2 : g1.re ≤ g2.re := d2.1
  obtain ⟨nq, g3, h3, h⟩ := bind_some h
  obtain ⟨nq', g4, h4, h⟩ := bind_some h
  obtain ⟨np, g5, h5, h6⟩ := bind_some h
  have h3' : kdlFol q rq (CGoalL.next (ofSure Sure.bunt) (jmp0 cb)) region g2 = some (nq, g3) := h3
  obtain ⟨dC, lC⟩ := frame_chain (G := FG g0 goal) (kdl_frame_fol q hq) hp (fun y hy => absurd hy lReg_bunt)
    (fun y hy => Or.inl (by
      have := lReg_ofSure.mp hy; simp only [lazyReg, NMem] at this; simp only at hsp; omega))
    (fun y hy => Or.inl (by omega)) h3' h4 h5 h6
  exact frX_of (d1.trans (d2.trans dC)) lC

/-- **The frame of a direct call**, for any sub-runs with the frame. -/
theorem kdl_frame_callDM (env : CallEnv) {p q : Nomm} {rp rq : CGoalL S → List Nat → CM Map (NextL S)}
    (hp : FrameRun rp) (hq : FrameRun rq) (b : Bell) (key : Option Noun) :
    FrameRun (fun goal region => (callDM env rp rq p q b key goal region : CM Map (NextL S))) := by
  intro goal region g0 g' nex h
  cases goal with
  | next laz th =>
    by_cases hd : (env.pure b && noneEquivalentL laz) = true
    · simp only [callDM, hd, if_true] at h
      obtain ⟨nq, g1, h1, h⟩ := bind_some h
      obtain ⟨nq', g2, h2, h⟩ := bind_some h
      obtain ⟨np, g3, h3, h4⟩ := bind_some h
      have h1' : kdlFol q rq (CGoalL.next (ofSure Sure.bunt) th) region g0 = some (nq, g1) := h1
      obtain ⟨dC, lC⟩ := frame_chain (G := FG g0 (CGoalL.next laz th)) (kdl_frame_fol q hq) hp
        (fun y hy => absurd hy lReg_bunt) (fun y hy => absurd hy lReg_bunt) (fun y hy => Or.inl hy) h1' h2 h3 h4
      exact frX_of dC lC
    · simp only [callDM, hd, Bool.false_eq_true, if_false] at h
      cases key with
      | some k => simp only at h <;> cases h
      | none =>
        cases hr : env.ring b with
        | some _ => simp only [hr] at h <;> cases h
        | none =>
          cases hn : env.need b with
          | none => simp only [hr, hn] at h <;> cases h
          | some bNed =>
            simp only [hr, hn] at h
            exact kdl_frame_dmPath env hp hq b bNed _ region h
  | pick z o =>
    simp only [callDM] at h
    cases key with
    | some k => simp only at h <;> cases h
    | none =>
      cases hr : env.ring b with
      | some _ => simp only [hr] at h <;> cases h
      | none =>
        cases hn : env.need b with
        | none => simp only [hr, hn] at h <;> cases h
        | some bNed =>
          simp only [hr, hn] at h
          exact kdl_frame_dmPath env hp hq b bNed _ region h
  | done =>
    simp only [callDM] at h
    cases key with
    | some k => simp only at h <;> cases h
    | none =>
      cases hr : env.ring b with
      | some _ => simp only [hr] at h <;> cases h
      | none =>
        cases hn : env.need b with
        | none => simp only [hr, hn] at h <;> cases h
        | some bNed =>
          simp only [hr, hn] at h
          exact kdl_frame_dmPath env hp hq b bNed _ region h

/-! ## The induction -/

/-- **Every run of `runLCM env true` on `PlainD` has the frame**, with no
precondition. -/
theorem frameRunM_plainD (env : CallEnv) :
    ∀ (nm : Nomm), PlainD nm → ∀ (sup : Option Nomm), FrameRun (runLCM (S := S) (Map := Map) env true sup nm)
  | Nomm.n0 ax, _, sup => kdl_frameRun_n0 env sup ax
  | Nomm.n1 k, _, sup => kdl_frameRun_n1 env sup k
  | Nomm.n3 p, h, sup => kdl_frameRun_n3 env sup (frameRunM_plainD env p h sup)
  | Nomm.n4 p, h, sup => kdl_frameRun_n4 env sup (frameRunM_plainD env p h sup)
  | Nomm.n5 p q, h, sup =>
    kdl_frameRun_n5 env sup (frameRunM_plainD env p h.1 sup) (frameRunM_plainD env q h.2 sup)
  | Nomm.cons p q, h, sup =>
    kdl_frameRun_cons env sup (frameRunM_plainD env p h.1 sup) (frameRunM_plainD env q h.2 sup)
  | Nomm.n7 p q, h, sup =>
    kdl_frameRun_n7 env sup (frameRunM_plainD env q h.2 (some p)) (frameRunM_plainD env p h.1 sup)
  | Nomm.n10 _ v q, h, sup =>
    kdl_frameRun_n10 env sup (frameRunM_plainD env v h.1 sup) (frameRunM_plainD env q h.2 sup)
  | Nomm.n2 p q Option.none, h, sup => fun goal region g0 g1 nex e => by
    simp only [runLCM] at e
    rw [callLM_none] at e
    exact kdl_frame_callL env sup (frameRunM_plainD env p h.1 sup) (frameRunM_plainD env q h.2 sup) goal region
      g0 g1 nex e
  | Nomm.n2 p q (some (b, key)), h, sup => fun goal region g0 g1 nex e => by
    simp only [runLCM, callLM] at e
    exact kdl_frame_callDM env (frameRunM_plainD env p h.1 sup) (frameRunM_plainD env q h.2 sup) b key goal
      region g0 g1 nex e
  | Nomm.n6 _ _ _, h, _ => h.elim
  | Nomm.n11s _ _ _, h, _ => h.elim
  | Nomm.n11d _ _ _ _, h, _ => h.elim
  | Nomm.n12 _ _, h, _ => h.elim
  | Nomm.mean _ _ _ _ _, h, _ => h.elim

/-! ## Labels and `Fresh` with direct calls -/

theorem kdl_qm_needOrd (bNed : NeedOrd) : QM (Map := Map) (needOrdAllocRegs bNed) :=
  ⟨fun g x g' h => by
    obtain ⟨⟨k, e⟩, -⟩ := needOrdAllocRegs_spec bNed g g' x h
    subst e; exact quiet_reg g k⟩

theorem kdl_batc1 {g : Comp.Gen Map} {p : Pole} {x m : Nat} {y : Nat} (h : HasPar m [y] g) :
    BATC g.blocks ⟨[], [p], Termin.hop ⟨[some x], m⟩⟩ := by
  obtain ⟨b, hb, hp⟩ := h
  refine ⟨fun j hj => ?_, fun ht => by simp [Compiler.twoWay] at ht⟩
  simp only [finJumps, List.mem_cons, List.not_mem_nil, or_false] at hj
  subst hj
  exact ⟨b, hb, by rw [hp]; rfl⟩

/-- **`+mono-try-call`'s blocks keep `ATS`** and end at a `Fresh` block. -/
theorem kdl_ht_monoTryLoop (fail : Nat) : ∀ (ned : Need) (r o : Nat),
    HT (Map := Map) (fun g => Fresh g (jmp0 o) ∧ Fresh g (jmp0 fail)) (monoTryLoop fail ned r o)
      (fun x g => Fresh g (jmp0 x) ∧ Fresh g (jmp0 fail))
  | Need.none, r, o => by
    simp only [monoTryLoop]; exact HT.pure' fun g h => h
  | Need.this rn, r, o => by
    simp only [monoTryLoop]
    refine HT.ite' _ HT.fail ?_
    exact HT.conseq (ht_emitJ rfl (js_hop fun g h => h.1) (stab_and (stab_fresh _) (stab_fresh _)))
      (fun _ h => h) (fun _ _ h => ⟨h.2, h.1.2⟩)
  | Need.pair hn tn, r, o => by
    simp only [monoTryLoop]
    refine HT.bind' (HT.quiet QM.re' (stab_and (stab_fresh _) (stab_fresh _))) fun rt => ?_
    refine HT.bind' (HT.quiet QM.re' (stab_and (stab_fresh _) (stab_fresh _))) fun rh => ?_
    refine HT.bind' (kdl_ht_monoTryLoop fail tn rt o) fun ot => ?_
    refine HT.bind' (kdl_ht_monoTryLoop fail hn rh ot) fun oh => ?_
    refine HT.bind' (ht_emitJ rfl (js_hop fun g h => h.1) (stab_and (stab_fresh _) (stab_fresh _))) fun os => ?_
    exact HT.conseq (ht_emitJ (P := fun g => Fresh g (jmp0 fail) ∧ Fresh g (jmp0 os)) rfl
      (js_two rfl fun g h => ⟨h.2, h.1⟩) (stab_and (stab_fresh _) (stab_fresh _)))
      (fun _ h => ⟨h.1.2, h.2⟩) (fun _ _ h => ⟨h.2, h.1.1⟩)
  | Need.both rn hn tn, r, o => by
    simp only [monoTryLoop]
    refine HT.bind' (HT.quiet QM.re' (stab_and (stab_fresh _) (stab_fresh _))) fun rt => ?_
    refine HT.bind' (HT.quiet QM.re' (stab_and (stab_fresh _) (stab_fresh _))) fun rh => ?_
    refine HT.bind' (kdl_ht_monoTryLoop fail tn rt o) fun ot => ?_
    refine HT.bind' (kdl_ht_monoTryLoop fail hn rh ot) fun oh => ?_
    refine HT.ite' _ HT.fail ?_
    refine HT.bind' (ht_emitJ rfl (js_hop fun g h => h.1) (stab_and (stab_fresh _) (stab_fresh _))) fun os => ?_
    exact HT.conseq (ht_emitJ (P := fun g => Fresh g (jmp0 fail) ∧ Fresh g (jmp0 os)) rfl
      (js_two rfl fun g h => ⟨h.2, h.1⟩) (stab_and (stab_fresh _) (stab_fresh _)))
      (fun _ h => ⟨h.1.2, h.2⟩) (fun _ _ h => ⟨h.2, h.1.1⟩)

/-- **The call blocks of a direct call keep `ATS`**: the result's call block
is `Fresh`. -/
theorem kdl_ht_monoBlocks (b : Bell) (subNed : Need) (goal : CGoalL S) :
    HT (Map := Map) (GFL (Map := Map) goal) (monoBlocks b subNed goal) (fun x g => Fresh g (jmp0 x.2)) := by
  cases goal with
  | done =>
    simp only [monoBlocks]
    refine HT.weak (P := fun _ => True) ?_ (fun _ _ => trivial)
    refine HT.bind' (HT.quiet QM.re' stab_true) fun sp => ?_
    refine HT.bind' (ht_emitJ rfl (js_nil rfl) stab_true) fun opt => ?_
    refine HT.bind' (ht_emitJ rfl (js_nil rfl) (stab_and stab_true (stab_fresh (jmp0 opt)))) fun pes => ?_
    refine HT.bind' (HT.conseq (kdl_ht_monoTryLoop pes subNed sp opt) (fun _ h => ⟨h.1.2, h.2⟩)
      (fun _ _ h => h)) fun o => ?_
    exact HT.pure' fun g h => h.1
  | pick z o0 =>
    simp only [monoBlocks]
    refine HT.bind' (ht_simpleNextL _) fun nex => HT.bind' (ht_kerf _) fun a => ?_
    rcases a with ⟨out, pro⟩
    refine HT.bind' (ht_qf QM.re' _) fun mg => HT.bind' (ht_qf QM.re' _) fun sp => ?_
    refine HT.bind' (HT.emit' (fun g h => batc_fresh (js_hop (P := fun g => Fresh g (jmp0 out)) (fun g h => h) g h))
      (stab_fresh _)) fun om => ?_
    refine HT.bind' (HT.weak (HT.quiet QM.re' (stab_hasPar om [mg])) fun _ h => h.2) fun po => ?_
    refine HT.bind' (HT.quiet QM.re' (stab_hasPar om [mg])) fun pp => ?_
    refine HT.bind' (HT.emit' (fun g h => kdl_batc1 h) (stab_hasPar om [mg])) fun opt => ?_
    refine HT.bind' (HT.emit' (fun g h => kdl_batc1 h.1) (stab_and (stab_hasPar om [mg]) (stab_hasPar opt [])))
      fun pes => ?_
    refine HT.bind' (HT.conseq (kdl_ht_monoTryLoop pes subNed sp opt)
      (fun _ h => ⟨fresh_of_hasPar h.1.2, fresh_of_hasPar h.2⟩) (fun _ _ h => h)) fun o => ?_
    exact HT.pure' fun g h => h.1
  | next laz th =>
    simp only [monoBlocks]
    refine HT.bind' (ht_simpleNextL _) fun nex => HT.bind' (ht_kerf _) fun a => ?_
    rcases a with ⟨out, pro⟩
    refine HT.bind' (ht_qf QM.re' _) fun mg => HT.bind' (ht_qf QM.re' _) fun sp => ?_
    refine HT.bind' (HT.emit' (fun g h => batc_fresh (js_hop (P := fun g => Fresh g (jmp0 out)) (fun g h => h) g h))
      (stab_fresh _)) fun om => ?_
    refine HT.bind' (HT.weak (HT.quiet QM.re' (stab_hasPar om [mg])) fun _ h => h.2) fun po => ?_
    refine HT.bind' (HT.quiet QM.re' (stab_hasPar om [mg])) fun pp => ?_
    refine HT.bind' (HT.emit' (fun g h => kdl_batc1 h) (stab_hasPar om [mg])) fun opt => ?_
    refine HT.bind' (HT.emit' (fun g h => kdl_batc1 h.1) (stab_and (stab_hasPar om [mg]) (stab_hasPar opt [])))
      fun pes => ?_
    refine HT.bind' (HT.conseq (kdl_ht_monoTryLoop pes subNed sp opt)
      (fun _ h => ⟨fresh_of_hasPar h.1.2, fresh_of_hasPar h.2⟩) (fun _ _ h => h)) fun o => ?_
    exact HT.pure' fun g h => h.1

/-- `kdlFol` keeps `HRL`. -/
theorem kdl_hrl_fol (q : Nomm) {rq : CGoalL S → List Nat → CM Map (NextL S)} (hq : HRL (Map := Map) rq) :
    HRL (Map := Map) (kdlFol q rq) := by
  intro goal region
  cases goal with
  | next l th =>
    simp only [kdlFol]
    exact HT.ite' _ (HT.pure' fun g h => ⟨h.1, lg_ofSure _ _ _⟩) (hq _ _)
  | pick z o => exact hq _ _
  | done => exact hq _ _

/-- **The `monoBlocks` path with labels.** -/
theorem kdl_htl_dmPath (L : LabSteps S Map) (env : CallEnv) {p q : Nomm} {rp rq : CGoalL S → List Nat → CM Map (NextL S)}
    (hp : HRL (Map := Map) rp) (hq : HRL (Map := Map) rq) (b : Bell) (bNed : NeedOrd) (goal : CGoalL S)
    (region : List Nat) :
    HT (fun g => GFL (Map := Map) goal g ∧ LG goal g)
      (needOrdAllocRegs bNed >>= fun subNed => monoBlocks b subNed goal >>= fun x =>
        (if safeFolFol q = true then pure ⟨ofSure Sure.bunt, jmp0 x.2⟩
          else rq (CGoalL.next (ofSure Sure.bunt) (jmp0 x.2)) region : CM Map (NextL S)) >>= fun nexFol =>
        pastL env.cod nexFol p region >>= fun nexFol =>
        rp (CGoalL.next (ofSure (lazyReg x.1)) nexFol.th) region >>= fun nexSub =>
        copyL nexSub nexFol.laz : CM Map (NextL S))
      (fun nex g => Fresh g nex.th ∧ LG nex.goal g) := by
  refine HT.weak (P := GFL (Map := Map) goal) ?_ (fun _ h => h.1)
  refine HT.bind' (HT.quiet (kdl_qm_needOrd bNed) (stab_gfl goal)) fun subNed => ?_
  refine HT.bind' (kdl_ht_monoBlocks b subNed goal) fun x => ?_
  exact HT.weak (htl_bin L env.cod (rq := kdlFol q rq) p hp (kdl_hrl_fol q hq) (ofSure Sure.bunt)
    (ofSure (lazyReg x.1)) (jmp0 x.2) region) fun g h => ⟨h, ll_ofSure _ _, ll_ofSure _ _⟩

/-- **The direct call with labels.** -/
theorem kdl_htl_callDM (L : LabSteps S Map) (env : CallEnv) {p q : Nomm} {rp rq : CGoalL S → List Nat → CM Map (NextL S)}
    (b : Bell) (key : Option Noun) (hp : HRL (Map := Map) rp) (hq : HRL (Map := Map) rq) (goal : CGoalL S)
    (region : List Nat) :
    HT (fun g => GFL (Map := Map) goal g ∧ LG goal g) (callDM env rp rq p q b key goal region : CM Map (NextL S))
      (fun nex g => Fresh g nex.th ∧ LG nex.goal g) := by
  constructor
  intro g0 nex g' A hP h
  cases goal with
  | next laz th =>
    by_cases hd : (env.pure b && noneEquivalentL laz) = true
    · simp only [callDM, hd, if_true] at h
      exact (htl_bin L env.cod (rq := kdlFol q rq) p hp (kdl_hrl_fol q hq) (ofSure Sure.bunt) (ofSure Sure.bunt) th
        region).run g0 nex g' A ⟨hP.1, ll_ofSure _ _, ll_ofSure _ _⟩ h
    · simp only [callDM, hd, Bool.false_eq_true, if_false] at h
      cases key with
      | some k => simp only at h <;> cases h
      | none =>
        cases hr : env.ring b with
        | some _ => simp only [hr] at h <;> cases h
        | none =>
          cases hn : env.need b with
          | none => simp only [hr, hn] at h <;> cases h
          | some bNed =>
            simp only [hr, hn] at h
            exact (kdl_htl_dmPath L env hp hq b bNed _ region).run g0 nex g' A hP h
  | pick z o =>
    simp only [callDM] at h
    cases key with
    | some k => simp only at h <;> cases h
    | none =>
      cases hr : env.ring b with
      | some _ => simp only [hr] at h <;> cases h
      | none =>
        cases hn : env.need b with
        | none => simp only [hr, hn] at h <;> cases h
        | some bNed =>
          simp only [hr, hn] at h
          exact (kdl_htl_dmPath L env hp hq b bNed _ region).run g0 nex g' A hP h
  | done =>
    simp only [callDM] at h
    cases key with
    | some k => simp only at h <;> cases h
    | none =>
      cases hr : env.ring b with
      | some _ => simp only [hr] at h <;> cases h
      | none =>
        cases hn : env.need b with
        | none => simp only [hr, hn] at h <;> cases h
        | some bNed =>
          simp only [hr, hn] at h
          exact (kdl_htl_dmPath L env hp hq b bNed _ region).run g0 nex g' A hP h

theorem kdl_labRun (env : CallEnv) (L : LabSteps S Map) : ∀ (nm : Nomm), PlainD nm → ∀ (sup : Option Nomm),
    HRL (Map := Map) (runLCM (S := S) env true sup nm)
  | Nomm.cons p q, h, sup, goal, region => by
    have ihp := kdl_labRun env L p h.1 sup
    have ihq := kdl_labRun env L q h.2 sup
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
    have ih := kdl_labRun env L p h sup
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
    have ih := kdl_labRun env L p h sup
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
    have ihp := kdl_labRun env L p h.1 sup
    have ihq := kdl_labRun env L q h.2 sup
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
    exact HT.bind' (kdl_labRun env L q h.2 (some p) goal region) fun nex =>
      HT.weak (kdl_labRun env L p h.1 sup nex.goal region) fun _ h => h
  | Nomm.n10 a v q, h, sup, goal, region => by
    have ihv := kdl_labRun env L v h.1 sup
    have ihq := kdl_labRun env L q h.2 sup
    unfold runLCM
    refine HT.bind' (htl_simpleNextL _) fun next => HT.bind' (HT.weak (htl_intoL L _ _) fun g h => h) fun x => ?_
    rcases x with ⟨don, rec, o⟩
    refine HT.bind' (HT.weak (HT.frame (htl_pastL L env.cod ⟨rec, jmp0 o⟩ v region) (stab_ll don))
      fun g h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩) fun nexR => ?_
    exact HT.weak (htl_bin L env.cod q ihq ihv don nexR.laz nexR.th region) fun g h => ⟨h.1.1, h.2, h.1.2⟩
  | Nomm.n2 p q Option.none, h, sup, goal, region => by
    unfold runLCM
    rw [callLM_none]
    exact htl_callL L env p q sup (kdl_labRun env L p h.1 sup) (kdl_labRun env L q h.2 sup) goal region
  | Nomm.n2 p q (some (b, key)), h, sup, goal, region => by
    unfold runLCM
    exact kdl_htl_callDM L env b key (kdl_labRun env L p h.1 sup) (kdl_labRun env L q h.2 sup) goal region

/-- **`LabUniq` and `Fresh` at run level on `PlainD`** (`runLCM env true`,
direct calls included). -/
theorem labRunM_plainD (env : CallEnv) : ∀ (nm : Nomm), PlainD nm → ∀ (sup : Option Nomm),
    HRL (Map := Map) (runLCM (S := S) env true sup nm) :=
  kdl_labRun env labSteps

/-! ## The liveness with direct calls -/

/-- **`LRL` for `runLCM env true`.** -/
abbrev kdlLRLM (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (env : CallEnv)
    (sup : Option Nomm) (nm : Nomm) : Prop :=
  ∀ (K : Nat → Nat → Prop) (goal : CGoalL S) (region : List Nat) (g0 g1 : Comp.Gen Map) (nex : NextL S),
    IL K goal g0 → LG goal g0 → runLCM env true sup nm goal region g0 = some (nex, g1) →
      JL K nex g1 ∧ LiveC K goal g0 g1 nex

theorem kdl_lrl_of_lr {env : CallEnv} {sup : Option Nomm} {nm : Nomm}
    (h : LiveRun (Map := Map) IL JL (runLCM (S := S) env true sup nm)) : kdlLRLM S Map env sup nm :=
  fun K goal region g0 g1 nex hI _ hr => h K goal region g0 g1 nex hI hr

/-- **`%0`, both halves** (the run of `runLC`). -/
theorem kdl_liveRun_n0 (env : CallEnv) (sup : Option Nomm) (ax : Nat) :
    LiveRun (Map := Map) IL JL (runLCM (S := S) env true sup (Nomm.n0 ax)) := by
  intro K goal region g0 g1 nex hI h
  rw [runLCM_true env (plainN_noDirect (Nomm.n0 ax) trivial) sup goal region] at h
  exact liveRun_n0 env sup ax K goal region g0 g1 nex hI h

/-- **`%1`, both halves** (the run of `runLC`). -/
theorem kdl_liveRun_n1 (env : CallEnv) (sup : Option Nomm) (k : Noun) :
    LiveRun (Map := Map) IL JL (runLCM (S := S) env true sup (Nomm.n1 k)) := by
  intro K goal region g0 g1 nex hI h
  rw [runLCM_true env (plainN_noDirect (Nomm.n1 k) trivial) sup goal region] at h
  exact liveRun_n1 env sup k K goal region g0 g1 nex hI h

theorem kdl_cons_tail (env : CallEnv) (sup : Option Nomm) {p q : Nomm} (hp : PlainD p) (hq : PlainD q)
    (ihp : kdlLRLM S Map env sup p) (ihq : kdlLRLM S Map env sup q) {K : Nat → Nat → Prop} {region : List Nat}
    {hT tel : Lazy S} {thq : Jmp} {g2 g3 g4 g5 g6 : Comp.Gen Map} {nq nq' np nex : NextL S}
    (hIq : IL (fun x y => K x y ∨ lazK thq.there hT x y) (CGoalL.next tel thq) g2)
    (hIh : IL K (CGoalL.next hT thq) g2) (hap : ∀ y, LReg hT y → ¬ LReg tel y)
    (lh : LabUniq hT) (lt : LabUniq tel) (lhb : ∀ e ∈ entries hT, e.1 < g2.bo)
    (ltb : ∀ e ∈ entries tel, e.1 < g2.bo)
    (h1 : runLCM env true sup q (CGoalL.next tel thq) region g2 = some (nq, g3))
    (h2 : pastL env.cod nq p region g3 = some (nq', g4))
    (h3 : runLCM env true sup p (CGoalL.next hT nq'.th) region g4 = some (np, g5))
    (h4 : copyL np nq'.laz g5 = some (nex, g6)) :
    JL K nex g6 ∧ ∀ r, LiveK (unpM g6) (fun x y => K x y ∨ lazK nex.th.there nex.laz x y) nex.th.there r →
      GLiveKL (unpM g2) (fun x y => K x y ∨ lazK thq.there hT x y) (CGoalL.next tel thq) r := by
  obtain ⟨Jq, Lq⟩ := ihq _ _ region g2 g3 nq hIq ⟨lt, ltb⟩ h1
  obtain ⟨Ip, Lpast⟩ := pastL_spec Jq h2
  have Fq := frameRunM_plainD env q hq sup _ region g2 g3 nq h1
  have Dpast := frame_pastL h2
  obtain ⟨-, KP23, -, lq1, lq2⟩ := (labRunM_plainD (S := S) (Map := Map) env q hq sup
    (CGoalL.next tel thq) region).run g2 nq g3 hIq.ats ⟨hIq.goal.1, lt, ltb⟩ h1
  obtain ⟨-, KP34, -⟩ := (ht_pastL env.cod nq p region).run g3 nq' g4 Jq.ats Jq.goal.1 h2
  obtain ⟨LU2, -⟩ := lab_pastL h2 lq1 lq2
  rcases nq' with ⟨second, ⟨a2, s2⟩⟩
  obtain ⟨_, _, _, ha2⟩ := (Ip.goal : GoalL g4 (CGoalL.next second ⟨a2, s2⟩)).1
  simp only at ha2
  subst ha2
  have hTlt : ∀ y, LReg hT y → y < g2.re := fun y hy => (hIh.greg_lt (gregL_next.mpr hy)).1
  have hrs : ∀ y, LReg second y → ¬ LReg hT y := by
    intro y hy hh
    rcases Fq.2 y (gregL_goal.mpr (Dpast.2 y hy)) with h | h
    · exact hap y hh (gregL_next.mp h)
    · have := hTlt y hh; omega
  have FL : FrL (CGoalL.next tel thq) g2 g4 :=
    frL_iff.mpr ((frL_iff.mp Fq.1).trans (Dpast.1.mono fun y h => h.elim))
  have Is : IL (fun x y => K x y ∨ lazK s2 second x y) (CGoalL.next second (⟨[], s2⟩ : Jmp)) g4 :=
    (il_addKills Ip).monoK fun x y h => h.elim (fun h => Or.inl (Or.inl h)) Or.inr
  have KP24 := KP23.trans KP34
  have Ip' : IL (fun x y => K x y ∨ lazK s2 second x y) (CGoalL.next hT (⟨[], s2⟩ : Jmp)) g4 :=
    il_glueT hIh Is (frL_iff.mp FL) KP24
      (fun y hy hq' => hq'.elim (fun h => by have := hTlt y hy; omega) fun h => hap y hy (gregL_next.mp h))
      Ip.goal.1
  have lhb' : ∀ e ∈ entries hT, e.1 < g4.bo := fun e he => Nat.lt_of_lt_of_le (lhb e he) KP24.2.1
  obtain ⟨Jp, Lp⟩ := ihp _ _ region g4 g5 np Ip' ⟨lh, lhb'⟩ h3
  have Fp := frameRunM_plainD env p hp sup _ region g4 g5 np h3
  obtain ⟨-, KP45, -, LU1, -⟩ := (labRunM_plainD (S := S) (Map := Map) env p hp sup
    (CGoalL.next hT (⟨[], s2⟩ : Jmp)) region).run g4 np g5 Ip'.ats ⟨Ip'.goal.1, lh, lhb'⟩ h3
  have hslt : ∀ y, LReg second y → y < g4.re := fun y hy => (Ip.greg_lt (gregL_next.mpr hy)).1
  have Ig : IL K (CGoalL.next second (jmp0 s2)) g5 :=
    il_glueT (Ip.monoK fun x y h => Or.inl h) (Jp.monoK fun x y h => Or.inl h) (frL_iff.mp Fp.1) KP45
      (fun y hy hq' => hq'.elim (fun h => by have := hslt y hy; omega) fun h => hrs y hy (gregL_next.mp h))
      (fresh_kp Ip.goal.1 KP45)
  have TA : TreesApart np.th.there np.laz s2 second := by
    intro e he e' he' y hy hy'
    have hg : GRegL (CGoalL.next np.laz np.th) y := ⟨e, he, hy⟩
    have hs : LReg second y := (gregL_next (th := jmp0 s2)).mp ⟨e', he', hy'⟩
    rcases Fp.2 y hg with h | h
    · exact hrs y hs (gregL_next.mp h)
    · have := hslt y hs; omega
  obtain ⟨Inex, Lc⟩ := (copyL_spec (S := S) (Map := Map)) K np second s2 g5 g6 nex
    (Jp.monoK fun x y h => Or.inl h) Ig TA LU1 LU2 h4
  refine ⟨Inex, fun r hl => ?_⟩
  have h5 : LiveK (unpM g4) (fun x y => (K x y ∨ lazK s2 second x y) ∨ lazK s2 hT x y) s2 r := Lp r (Lc r hl)
  have hns : ¬ NMem hT.sure.ned r := fun hm => h5.nk (Or.inr ⟨(s2, hT), List.mem_cons_self, rfl, hm⟩)
  have h5' : LiveK (unpM g4) (fun x y => (K x y ∨ lazK thq.there hT x y) ∨ lazK s2 second x y) s2 r := by
    refine h5.mono_r fun x hx => ?_
    rcases hx with (hx | ⟨e, he, ex, hm⟩) | hx
    · exact Or.inl (Or.inl hx)
    · rcases List.mem_cons.mp he with rfl | he
      · exact (hns hm).elim
      · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, ex, hm⟩
    · exact Or.inl (Or.inr hx)
  exact Lq r (Lpast r h5')

/-! ## The three goals -/

/-- **The cons under `%pick`**: a `bom` block, then the tail for `bunt`
goals; nothing is live at the `bom` block. -/
theorem kdl_liveRun_cons_pick (env : CallEnv) (sup : Option Nomm) {p q : Nomm} (hp : PlainD p) (hq : PlainD q)
    (ihp : kdlLRLM S Map env sup p) (ihq : kdlLRLM S Map env sup q) {K : Nat → Nat → Prop} {region : List Nat}
    {z o0 : Jmp} {g0 g1 : Comp.Gen Map} {nex : NextL S} (hI : IL K (CGoalL.pick z o0 : CGoalL S) g0)
    (h : (do
      let o ← emit ⟨[], [], Termin.bom Option.none⟩
      let nex2 ← runLCM env true sup q (CGoalL.next (ofSure Sure.bunt) (jmp0 o)) region
      let nex2 ← pastL env.cod nex2 p region
      let nex1 ← runLCM env true sup p (CGoalL.next (ofSure Sure.bunt) nex2.th) region
      copyL nex1 nex2.laz : CM Map (NextL S)) g0 = some (nex, g1)) :
    JL K nex g1 ∧ LiveC K (CGoalL.pick z o0) g0 g1 nex := by
  obtain ⟨o, ga, ha, h⟩ := bind_some h
  rw [emit_apply] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  obtain ⟨nq, gc, h1, h⟩ := bind_some h
  obtain ⟨nq', gd, h2, h⟩ := bind_some h
  obtain ⟨np, ge, h3, h4⟩ := bind_some h
  have I0 : IL K (CGoalL.next (ofSure (Sure.bunt : Sure S)) (jmp0 g0.bo))
      (g0.emitted ⟨[], [], Termin.bom Option.none⟩) :=
    il_emitGoal (R := g0.re) hI (Nat.le_refl _) rfl (batc_fresh fun j hj => by simp [finJumps] at hj)
      (blobIn_nil_fin trivial) (fun r hr => by simp [blockDefs] at hr) (fun r hr => hr.elim) trivial
  have nk : ∀ x y, ¬ lazK (S := S) g0.bo (ofSure Sure.bunt) x y := fun x y hk => (lazK_ofSure.mp hk).2.elim
  have I1 : IL (fun x y => K x y ∨ lazK (jmp0 g0.bo).there (ofSure (Sure.bunt : Sure S)) x y)
      (CGoalL.next (ofSure (Sure.bunt : Sure S)) (jmp0 g0.bo)) (g0.emitted ⟨[], [], Termin.bom Option.none⟩) :=
    I0.monoK fun x y h => h.elim id fun hk => (nk x y hk).elim
  have hnb : ∀ y, ¬ LReg (ofSure (Sure.bunt : Sure S)) y := fun y hy => (lReg_ofSure.mp hy).elim
  have hent : ∀ e ∈ entries (ofSure (Sure.bunt : Sure S)), e.1 < (g0.emitted ⟨[], [], Termin.bom Option.none⟩).bo :=
    fun e he => by rw [entries_ofSure] at he; exact absurd he List.not_mem_nil
  obtain ⟨J, L⟩ := kdl_cons_tail env sup hp hq ihp ihq I1 I0 (fun y hy _ => hnb y hy) (labUniq_ofSure _)
    (labUniq_ofSure _) hent hent h1 h2 h3 h4
  refine ⟨J, fun r hl => ?_⟩
  have A := L r hl
  have hget := unpM_emitted_self (g := g0) hI.ats.1 ⟨[], [], Termin.bom Option.none⟩
  exfalso
  cases A with
  | here hb' hr _ =>
    have hb2 := hget.symm.trans hb'
    cases hb2
    obtain ⟨-, hy | ⟨-, hy⟩⟩ := hr
    · simp [renBlob, OpsRF] at hy
    · simp [renBlob, renFin, finRegs] at hy
  | next hb' hj _ _ _ =>
    have hb2 := hget.symm.trans hb'
    cases hb2
    simp [renBlob, renFin, getJmps] at hj

/-- **The cons under `%next`**, from the spec of `+split`. -/
theorem kdl_liveRun_cons_next (env : CallEnv) (sup : Option Nomm) {p q : Nomm} (hp : PlainD p) (hq : PlainD q)
    (ihp : kdlLRLM S Map env sup p) (ihq : kdlLRLM S Map env sup q) (hS : SplitSpecL S Map) {K : Nat → Nat → Prop}
    {region : List Nat} {laz : Lazy S} {th : Jmp} {g0 g1 : Comp.Gen Map} {nex : NextL S}
    (hI : IL K (CGoalL.next laz th) g0) (hL : LG (CGoalL.next laz th) g0)
    (h : (do
      let (hed, tel, o) ← splitL ⟨laz, th⟩
      let nexh ← pastL env.cod ⟨hed, jmp0 o⟩ q region
      let nex2 ← runLCM env true sup q (CGoalL.next tel nexh.th) region
      let nex2 ← pastL env.cod nex2 p region
      let nex1 ← runLCM env true sup p (CGoalL.next nexh.laz nex2.th) region
      copyL nex1 nex2.laz : CM Map (NextL S)) g0 = some (nex, g1)) :
    JL K nex g1 ∧ LiveC K (CGoalL.next laz th) g0 g1 nex := by
  obtain ⟨⟨hed, tel, o⟩, ga, hsp, h⟩ := bind_some h
  obtain ⟨nexh, gb, hph, h⟩ := bind_some h
  obtain ⟨nq, gc, h1, h⟩ := bind_some h
  obtain ⟨nq', gd, h2, h⟩ := bind_some h
  obtain ⟨np, ge, h3, h4⟩ := bind_some h
  obtain ⟨Ih, It, TA, Ls⟩ := hS K laz th g0 ga hed tel o hI hsp
  obtain ⟨LUh, LUt, Bh, Bt⟩ := lab_splitL (Q := (· < g0.bo)) hsp hL.1 hL.2
  obtain ⟨-, KP0a, -⟩ := (ht_splitL ⟨laz, th⟩).run g0 _ ga hI.ats hI.goal.1 hsp
  have Ih' : IL (fun x y => K x y ∨ lazK (jmp0 o).there tel x y) (CGoalL.next hed (jmp0 o)) ga := il_killsOf Ih It
  obtain ⟨Ih2, Lh⟩ := pastL_spec (nex := ⟨hed, jmp0 o⟩) Ih' hph
  obtain ⟨-, KPab, -⟩ := (ht_pastL env.cod ⟨hed, jmp0 o⟩ q region).run ga nexh gb Ih.ats Ih.goal.1 hph
  have Dh := frame_pastL hph
  have IhK : IL K (CGoalL.next nexh.laz nexh.th) gb := Ih2.monoK fun x y h => Or.inl h
  have hIq : IL (fun x y => K x y ∨ lazK nexh.th.there nexh.laz x y) (CGoalL.next tel nexh.th) gb :=
    il_glueT (It.monoK fun x y h => Or.inl h) (il_addKills IhK) Dh.1 KPab (fun _ _ h => h) Ih2.goal.1
  have hap : ∀ y, LReg nexh.laz y → ¬ LReg tel y := fun y hy ht => by
    obtain ⟨e, he, hm⟩ := lreg_mem o (Dh.2 y hy)
    obtain ⟨e', he', hm'⟩ := lreg_mem o ht
    exact TA e he e' he' y hm hm'
  obtain ⟨LUH, LBH⟩ := lab_pastL hph LUh (fun e he => Nat.lt_of_lt_of_le (Bh e he) KP0a.2.1)
  have ltb : ∀ e ∈ entries tel, e.1 < gb.bo := fun e he => Nat.lt_of_lt_of_le (Bt e he) (KP0a.trans KPab).2.1
  obtain ⟨J, L⟩ := kdl_cons_tail env sup hp hq ihp ihq hIq IhK hap LUH LUt LBH ltb h1 h2 h3 h4
  refine ⟨J, fun r hl => ?_⟩
  have A := L r hl
  have hnt : ¬ NMem tel.sure.ned r := fun hm => A.nk (Or.inr ⟨(nexh.th.there, tel), List.mem_cons_self, rfl, hm⟩)
  have B : LiveK (unpM gb) (fun x y => (K x y ∨ lazK o tel x y) ∨ lazK nexh.th.there nexh.laz x y)
      nexh.th.there r := by
    refine A.mono_r fun x hx => ?_
    rcases hx with (hx | ⟨e, he, ex, hm⟩) | hx
    · exact Or.inl (Or.inl hx)
    · rcases List.mem_cons.mp he with rfl | he
      · exact (hnt hm).elim
      · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, ex, hm⟩
    · exact Or.inl (Or.inr hx)
  have C := Lh r B
  exact Ls r (C.mono_r fun x hx => by
    rcases hx with (h | h) | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr h))

/-- **The cons, every goal**, from `LRL` of its parts and the spec of
`+split`. -/
theorem kdl_liveRun_consL (env : CallEnv) (sup : Option Nomm) {p q : Nomm} (hp : PlainD p) (hq : PlainD q)
    (ihp : kdlLRLM S Map env sup p) (ihq : kdlLRLM S Map env sup q) (hS : SplitSpecL S Map) :
    kdlLRLM S Map env sup (Nomm.cons p q) := by
  intro K goal region g0 g1 nex hI hL h
  simp only [runLCM] at h
  obtain ⟨goal', ga, hga, h⟩ := bind_some h
  cases goal with
  | pick z o0 =>
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hga
    obtain ⟨rfl, rfl⟩ := hga
    exact kdl_liveRun_cons_pick env sup hp hq ihp ihq hI h
  | next laz th =>
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hga
    obtain ⟨rfl, rfl⟩ := hga
    exact kdl_liveRun_cons_next env sup hp hq ihp ihq hS hI hL h
  | done =>
    obtain ⟨r, gx, hx, hga⟩ := bind_some hga
    obtain ⟨o, gy, hy, hga⟩ := bind_some hga
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hga
    obtain ⟨rfl, rfl⟩ := hga
    have hsn : (simpleNextL (CGoalL.done : CGoalL S) : CM Map (NextL S)) g0 =
        some (⟨ofSure (lazyReg (S := S) r), jmp0 o⟩, gy) := by
      simp only [simpleNextL, bind_apply, hx, Option.bind_some, hy, pure_apply]
      rfl
    have I1 : IL K (CGoalL.next (ofSure (lazyReg (S := S) r)) (jmp0 o)) gy := il_simpleNextL hI hsn
    obtain ⟨J, L⟩ := kdl_liveRun_cons_next env sup hp hq ihp ihq hS I1 (lg_ofSure _ _ _) h
    exact ⟨J, LiveC.trans (liveC_simpleNextL_done hI.ats.1 (hI.cond_ge (Nat.le_refl _)) hsn) L⟩


theorem kdl_ten_tail (env : CallEnv) (sup : Option Nomm) {v q : Nomm} (hv : PlainD v) (hq : PlainD q)
    (ihv : kdlLRLM S Map env sup v) (ihq : kdlLRLM S Map env sup q) {K : Nat → Nat → Prop} {region : List Nat}
    {d rec : Lazy S} {o : Nat} {g2 g3 g4 g5 g6 g7 : Comp.Gen Map} {nR nD nD' nQ nex : NextL S}
    (Id : IL K (CGoalL.next d (jmp0 o)) g2) (Ir : IL K (CGoalL.next rec (jmp0 o)) g2)
    (hap : ∀ y, LReg d y → ¬ LReg rec y) (ld : LabUniq d ∧ ∀ e ∈ entries d, e.1 < g2.bo)
    (lr : LabUniq rec ∧ ∀ e ∈ entries rec, e.1 < g2.bo)
    (h2 : pastL env.cod ⟨rec, jmp0 o⟩ v region g2 = some (nR, g3))
    (h3 : runLCM env true sup v (CGoalL.next d nR.th) region g3 = some (nD, g4))
    (h4 : pastL env.cod nD q region g4 = some (nD', g5))
    (h5 : runLCM env true sup q (CGoalL.next nR.laz nD'.th) region g5 = some (nQ, g6))
    (h6 : copyL nQ nD'.laz g6 = some (nex, g7)) :
    JL K nex g7 ∧ ∀ y, LiveK (unpM g7) (fun x z => K x z ∨ lazK nex.th.there nex.laz x z) nex.th.there y →
      LiveK (unpM g2) (fun x z => (K x z ∨ lazK o d x z) ∨ lazK o rec x z) o y := by
  -- `+past` of the recipient, with the donor's kills
  have Ir2 : IL (fun x y => K x y ∨ lazK o d x y) (CGoalL.next rec (jmp0 o)) g2 := il_addKillsOf Ir Id
  obtain ⟨IR3, LpR⟩ := pastL_spec Ir2 h2
  have DpR := frame_pastL h2
  obtain ⟨A3, KP23, -, lR1, lR2⟩ := (htl_pastL (S := S) (Map := Map) labSteps env.cod ⟨rec, jmp0 o⟩ v region).run
    g2 nR g3 Ir.ats ⟨Ir.goal.1, lr⟩ h2
  rcases nR with ⟨R, ⟨aR, sR⟩⟩
  obtain ⟨_, _, _, haR⟩ := (IR3.goal : GoalL g3 (CGoalL.next R ⟨aR, sR⟩)).1
  simp only at haR
  subst haR
  have hRrec : ∀ y, LReg R y → LReg rec y := DpR.2
  have hRlt : ∀ y, LReg R y → y < g3.re := fun y hy => (IR3.greg_lt (gregL_next.mpr hy)).1
  -- `v` for "`d` at `sR`", with the recipient's kills
  have Iv : IL (fun x y => K x y ∨ lazK sR R x y) (CGoalL.next d (⟨[], sR⟩ : Jmp)) g3 :=
    il_carry Id ((il_addKills IR3).monoK fun x y h => h.elim (fun h => Or.inl (Or.inl h)) Or.inr) KP23
      DpR.1.1 DpR.1.2.1 (fun y _ hd => (DpR.1.2.2 y hd).elim id False.elim) IR3.goal.1
  obtain ⟨Jv, Lv⟩ := ihv _ _ region g3 g4 nD Iv ⟨ld.1, fun e he => Nat.lt_of_lt_of_le (ld.2 e he) KP23.2.1⟩ h3
  have Fv := frameRunM_plainD env v hv sup _ region g3 g4 nD h3
  obtain ⟨A4, KP34, -, lD1, lD2⟩ := (labRunM_plainD (S := S) (Map := Map) env v hv sup
    (CGoalL.next d (⟨[], sR⟩ : Jmp)) region).run g3 nD g4 A3
    ⟨Iv.goal.1, ld.1, fun e he => Nat.lt_of_lt_of_le (ld.2 e he) KP23.2.1⟩ h3
  -- `+past` over `q`
  obtain ⟨Ip5, Lp5⟩ := pastL_spec Jv h4
  have Dp5 := frame_pastL h4
  obtain ⟨LU2, -⟩ := lab_pastL h4 lD1 lD2
  obtain ⟨-, KP45, -⟩ := (ht_pastL (S := S) (Map := Map) env.cod nD q region).run g4 nD' g5 A4 Jv.goal.1 h4
  rcases nD' with ⟨second, ⟨a2, s2⟩⟩
  obtain ⟨_, _, _, ha2⟩ := (Ip5.goal : GoalL g5 (CGoalL.next second ⟨a2, s2⟩)).1
  simp only at ha2
  subst ha2
  have FL35 : DF (FG g3 (CGoalL.next d (⟨[], sR⟩ : Jmp))) g3 g5 :=
    (frL_iff.mp Fv.1).trans (Dp5.1.mono fun y h => h.elim)
  have hsec : ∀ y, LReg second y → ¬ LReg R y := by
    intro y hy hR
    rcases Fv.2 y (gregL_goal.mpr (Dp5.2 y hy)) with h | h
    · exact hap y (gregL_next.mp h) (hRrec y hR)
    · have := hRlt y hR; omega
  -- `q` for "`R` at `s2`", with `second`'s kills
  have IQ : IL (fun x y => K x y ∨ lazK s2 second x y) (CGoalL.next R (⟨[], s2⟩ : Jmp)) g5 :=
    il_carry IR3 ((il_addKills Ip5).monoK fun x y h => h.elim (fun h => Or.inl (Or.inl h)) Or.inr)
      (KP34.trans KP45) FL35.1 FL35.2.1 (fun y hy hd => by
        rcases FL35.2.2 y hd with h | h | h
        · exact h
        · have := hRlt y hy; omega
        · exact (hap y (gregL_next.mp h) (hRrec y hy)).elim) Ip5.goal.1
  have LGq : LG (CGoalL.next R (⟨[], s2⟩ : Jmp)) g5 :=
    ⟨lR1, fun e he => Nat.lt_of_lt_of_le (lR2 e he) (KP34.trans KP45).2.1⟩
  obtain ⟨Jq, Lq⟩ := ihq _ _ region g5 g6 nQ IQ LGq h5
  have Fq := frameRunM_plainD env q hq sup _ region g5 g6 nQ h5
  obtain ⟨-, KP56, -, LU1, -⟩ := (labRunM_plainD (S := S) (Map := Map) env q hq sup
    (CGoalL.next R (⟨[], s2⟩ : Jmp)) region).run g5 nQ g6 Ip5.ats ⟨IQ.goal.1, LGq⟩ h5
  -- the copy
  have Ig : IL K (CGoalL.next second (jmp0 s2)) g6 :=
    il_glueL (Ip5.monoK fun x y h => Or.inl h) Jq (fun x y h => Or.inl h) Fq KP56 hsec
  have TA : TreesApart nQ.th.there nQ.laz s2 second := by
    intro e he e' he' y hy hy'
    have hg : GRegL (CGoalL.next nQ.laz nQ.th) y := ⟨e, he, hy⟩
    have hlt := ((Ip5.goal : GoalL g5 (CGoalL.next second (⟨[], s2⟩ : Jmp))).2.2 e' he').2.2 y hy'
    rcases Fq.2 y hg with h | h
    · exact hsec y ((gregL_next (th := jmp0 s2)).mp ⟨e', he', hy'⟩) (gregL_next.mp h)
    · have := hlt.1; omega
  obtain ⟨Inex, Lc⟩ := (copyL_spec (S := S) (Map := Map)) K nQ second s2 g6 g7 nex
    (Jq.monoK fun x y h => Or.inl h) Ig TA LU1 LU2 h6
  refine ⟨Inex, fun y hl => ?_⟩
  -- q's run
  have l5 : LiveK (unpM g5) (fun x z => (K x z ∨ lazK s2 second x z) ∨ lazK s2 R x z) s2 y := Lq y (Lc y hl)
  have nR0 : ¬ NMem R.sure.ned y := fun hm => l5.nk (Or.inr ⟨(s2, R), List.mem_cons_self, rfl, hm⟩)
  have l5' : LiveK (unpM g5) (fun x z => (K x z ∨ lazK sR R x z) ∨ lazK s2 second x z) s2 y := by
    refine l5.mono_r fun x hx => ?_
    rcases hx with (hx | ⟨e, he, ex, hm⟩) | hx
    · exact Or.inl (Or.inl hx)
    · rcases List.mem_cons.mp he with rfl | he
      · exact (nR0 hm).elim
      · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, ex, hm⟩
    · exact Or.inl (Or.inr hx)
  -- `+past` over `q`, then `v`'s run
  have l3 : LiveK (unpM g3) (fun x z => (K x z ∨ lazK sR R x z) ∨ lazK sR d x z) sR y := Lv y (Lp5 y l5')
  have nd0 : ¬ NMem d.sure.ned y := fun hm => l3.nk (Or.inr ⟨(sR, d), List.mem_cons_self, rfl, hm⟩)
  have l3' : LiveK (unpM g3) (fun x z => (K x z ∨ lazK o d x z) ∨ lazK sR R x z) sR y := by
    refine l3.mono_r fun x hx => ?_
    rcases hx with (hx | ⟨e, he, ex, hm⟩) | hx
    · exact Or.inl (Or.inl hx)
    · rcases List.mem_cons.mp he with rfl | he
      · exact (nd0 hm).elim
      · exact Or.inr ⟨e, List.mem_cons_of_mem _ he, ex, hm⟩
    · exact Or.inl (Or.inr hx)
  exact LpR y l3'

/-! ## The arm -/

/-- **The arm `%10`** in the form `LRL`, from the spec of `+into`. -/
theorem kdl_liveRun_n10L (hInto : IntoSpecL S Map) (env : CallEnv) (sup : Option Nomm) {a : Nat} {v q : Nomm}
    (hv : PlainD v) (hq : PlainD q) (ihv : kdlLRLM S Map env sup v) (ihq : kdlLRLM S Map env sup q) :
    kdlLRLM S Map env sup (Nomm.n10 a v q) := by
  intro K goal region g0 g7 nex hI hG h
  simp only [runLCM] at h
  obtain ⟨next, g1, h0, h⟩ := bind_some h
  obtain ⟨⟨d, rec, o⟩, g2, h1, h⟩ := bind_some h
  obtain ⟨nR, g3, h2, h⟩ := bind_some h
  obtain ⟨nD, g4, h3, h⟩ := bind_some h
  obtain ⟨nD', g5, h4, h⟩ := bind_some h
  obtain ⟨nQ, g6, h5, h6⟩ := bind_some h
  have I1 : IL K next.goal g1 := il_simpleNextL hI h0
  have L1 : LiveC K goal g0 g1 next := by
    cases goal with
    | next laz th =>
      simp only [simpleNextL, pure_apply, Option.some.injEq, Prod.mk.injEq] at h0
      obtain ⟨rfl, rfl⟩ := h0
      exact liveC_refl
    | done => exact liveC_simpleNextL_done hI.ats.1 (hI.cond_ge (Nat.le_refl _)) h0
    | pick z o => exact liveC_simpleNextL_pick hI h0
  obtain ⟨A1, -, -, LG1⟩ := (htl_simpleNextL (S := S) (Map := Map) goal).run g0 next g1 hI.ats
    ⟨gfl_of_il hI, hG⟩ h0
  rcases next with ⟨L, th⟩
  obtain ⟨Id, Ir, hap, Lin⟩ := hInto K L th a g1 g2 d rec o I1 h1
  obtain ⟨-, -, -, ld, lr⟩ := (htl_intoL (S := S) (Map := Map) labSteps ⟨L, th⟩ a).run g1 _ g2 A1
    ⟨I1.goal.1, LG1⟩ h1
  obtain ⟨J, Lt⟩ := kdl_ten_tail env sup hv hq ihv ihq Id Ir hap ld lr h2 h3 h4 h5 h6
  exact ⟨J, fun y hl => L1 y (Lin y (Lt y hl))⟩

/-- The field `n10` in the form `LRL`, from the spec of `+into`. -/
theorem kdl_armsL_n10L (hInto : IntoSpecL S Map) (env : CallEnv) :
    ∀ sup a v q, PlainD v → PlainD q → kdlLRLM S Map env sup v → kdlLRLM S Map env sup q →
      kdlLRLM S Map env sup (Nomm.n10 a v q) :=
  fun sup _ _ _ hv hq ihv ihq => kdl_liveRun_n10L hInto env sup hv hq ihv ihq


theorem kdl_liveRun_n4_doneL (env : CallEnv) (sup : Option Nomm) {p : Nomm}
    (ih : kdlLRLM S Map env sup p) {K : Nat → Nat → Prop} {region : List Nat}
    {g0 g1 : Comp.Gen Map} {nex : NextL S} (hI : IL K (CGoalL.done : CGoalL S) g0)
    (h : runLCM env true sup (Nomm.n4 p) (CGoalL.done : CGoalL S) region g0 = some (nex, g1)) :
    JL K nex g1 ∧ LiveC K CGoalL.done g0 g1 nex := by
  have hd : g0.drop = false := hI.ats.1
  simp only [runLCM] at h
  obtain ⟨pro, ga, ha, h⟩ := bind_some h
  rw [re_apply] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  obtain ⟨arg, gb, hb, h⟩ := bind_some h
  rw [re_apply] at hb
  simp only [Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  obtain ⟨o, gc, hc, h⟩ := bind_some h
  rw [emit_apply] at hc
  simp only [Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  have u0 : unproxy g0.cond g0.re = g0.re := unproxy_none (hI.cond_ge (Nat.le_refl _))
  have u1 : unproxy g0.cond (g0.re + 1) = g0.re + 1 := unproxy_none (hI.cond_ge (Nat.le_succ _))
  refine liveRun_thenL (nex1 := ⟨ofSure (lazyReg (g0.re + 1)), jmp0 g0.bo⟩) ih (lg_ofSure _ _ _) ?_ ?_ h
  · exact il_emitGoal (R := g0.re + 1 + 1) hI (by omega) rfl
      (batc_fresh fun j hj => by simp [finJumps] at hj)
      ⟨fun x hx => by simp at hx, by
        intro q hq x hx
        simp only [List.mem_singleton] at hq
        subst hq
        simp only [Comp.poleRegs, List.mem_cons, List.not_mem_nil, or_false] at hx
        omega, show g0.re < g0.re + 1 + 1 by omega⟩
      (fun r hr => by simp [blockDefs, aliasDst] at hr; omega)
      (fun r hr => by
        have e : r = g0.re + 1 := hr
        subst e; exact ⟨Nat.le_succ _, by omega, by simp [blockDefs, aliasDst]⟩) trivial
  · refine liveC_emitG hI _ _ _ (fun r hr hn => hn ?_) (fun j hj => by simp [renBlob, renFin, getJmps] at hj)
    obtain ⟨-, hr | ⟨hnd, hr⟩⟩ := hr
    · have e : r = g0.re + 1 := by
        simpa [renBlob, renPole, OpsRF, aliasReads, aliasDst, Opt.poleRegs, u0, u1] using hr
      exact e
    · exact (hnd (by simpa [renBlob, renPole, renFin, finRegs, defsOf, aliasDst, u0, u1] using hr)).elim

/-- **`%4` under `%pick`, both halves.** -/
theorem kdl_liveRun_n4_pickL (env : CallEnv) (sup : Option Nomm) {p : Nomm}
    (ih : kdlLRLM S Map env sup p) {K : Nat → Nat → Prop} {z o : Jmp}
    {region : List Nat} {g0 g1 : Comp.Gen Map} {nex : NextL S} (hI : IL K (CGoalL.pick z o : CGoalL S) g0)
    (h : runLCM env true sup (Nomm.n4 p) (CGoalL.pick z o : CGoalL S) region g0 = some (nex, g1)) :
    JL K nex g1 ∧ LiveC K (CGoalL.pick z o) g0 g1 nex := by
  have hd : g0.drop = false := hI.ats.1
  obtain ⟨hz, ho⟩ := (hI.goal : GoalL g0 (CGoalL.pick z o))
  obtain ⟨bz, hbz, -, az⟩ := hz
  obtain ⟨bo', hbo, -, ao⟩ := ho
  simp only [runLCM] at h
  obtain ⟨pro, ga, ha, h⟩ := bind_some h
  rw [re_apply] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  obtain ⟨arg, gb, hb, h⟩ := bind_some h
  rw [re_apply] at hb
  simp only [Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  obtain ⟨o', gc, hc, h⟩ := bind_some h
  rw [emit_apply] at hc
  simp only [Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  have u0 : unproxy g0.cond g0.re = g0.re := unproxy_none (hI.cond_ge (Nat.le_refl _))
  have u1 : unproxy g0.cond (g0.re + 1) = g0.re + 1 := unproxy_none (hI.cond_ge (Nat.le_succ _))
  refine liveRun_thenL (nex1 := ⟨ofSure (lazyReg (g0.re + 1)), jmp0 g0.bo⟩) ih (lg_ofSure _ _ _) ?_ ?_ h
  · exact il_emitGoal (R := g0.re + 1 + 1) hI (by omega) rfl
      (batc_fresh fun j hj => by
        simp only [finJumps, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        · exact hI.goal.1
        · exact hI.goal.2)
      ⟨fun x hx => by simp at hx, by
        intro q hq x hx
        simp only [List.mem_singleton] at hq
        subst hq
        simp only [Comp.poleRegs, List.mem_cons, List.not_mem_nil, or_false] at hx
        omega, ⟨show g0.re < g0.re + 1 + 1 by omega, jmpIn_nil az, jmpIn_nil ao⟩⟩
      (fun r hr => by simp [blockDefs, aliasDst] at hr; omega)
      (fun r hr => by
        have e : r = g0.re + 1 := hr
        subst e; exact ⟨Nat.le_succ _, by omega, by simp [blockDefs, aliasDst]⟩) trivial
  · refine liveC_emitG hI _ _ _ (fun r hr hn => (hn ?_).elim) (fun j hj => ?_)
    · obtain ⟨-, hr | ⟨hnd, hr⟩⟩ := hr
      · have e : r = g0.re + 1 := by
          simpa [renBlob, renPole, OpsRF, aliasReads, aliasDst, Opt.poleRegs, u0, u1] using hr
        exact e
      · exact (hnd (by simpa [renBlob, renPole, renFin, finRegs, jmpRegs, renJmp_nil _ az, renJmp_nil _ ao,
          defsOf, aliasDst, u0, u1, az, ao] using hr)).elim
    · simp only [renBlob, renFin, getJmps, renJmp_nil _ az, renJmp_nil _ ao, List.mem_cons, List.not_mem_nil,
        or_false] at hj
      rcases hj with rfl | rfl
      · exact ⟨hI.lab hbz, fun r hl _ _ => Or.inl hl⟩
      · exact ⟨hI.lab hbo, fun r hl _ _ => Or.inr hl⟩

/-- **The tail of `%4` under `%next`**: the `%inc` block into `pro`, hopping
to `there`, then the operand for its argument. -/
theorem kdl_liveRun_n4_tailL (env : CallEnv) (sup : Option Nomm) {p : Nomm}
    (ih : kdlLRLM S Map env sup p) {K : Nat → Nat → Prop} {region : List Nat}
    {pro there : Nat} {g1 g2 : Comp.Gen Map} {nex : NextL S}
    (hI : IL K (CGoalL.next (ofSure (lazyReg (S := S) pro)) (jmp0 there)) g1)
    (h : (do
      let arg ← re
      let o ← emit ⟨[], [Pole.inc arg pro], Termin.hop (jmp0 there)⟩
      runLCM env true sup p (CGoalL.next (ofSure (lazyReg (S := S) arg)) (jmp0 o)) region : CM Map (NextL S)) g1 =
        some (nex, g2)) :
    JL K nex g2 ∧ LiveC K (CGoalL.next (ofSure (lazyReg (S := S) pro)) (jmp0 there)) g1 g2 nex := by
  have hd : g1.drop = false := hI.ats.1
  obtain ⟨arg, ga, ha, h⟩ := bind_some h
  rw [re_apply] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  obtain ⟨o, gc, hc, h⟩ := bind_some h
  rw [emit_apply] at hc
  simp only [Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  obtain ⟨hF, -, hE⟩ := (hI.goal : GoalL g1 (CGoalL.next (ofSure (lazyReg (S := S) pro)) (jmp0 there)))
  obtain ⟨bt, hbt, -, -⟩ := hF
  have hpro : pro < g1.re ∧ ¬ Defd g1.blocks pro :=
    (hE _ (List.mem_cons_self ..)).2.2 pro (show pro = pro from rfl)
  have hkey : HoonMap.get g1.cond pro = Option.none := by
    cases e : HoonMap.get g1.cond pro with
    | none => rfl
    | some v => exact ((hI.cond _ v e).2.2.1 (gregL_ofSure.mpr rfl)).elim
  have upro : unproxy g1.cond pro = pro := unproxy_none hkey
  have u1 : unproxy g1.cond g1.re = g1.re := unproxy_none (hI.cond_ge (Nat.le_refl _))
  refine liveRun_thenL (nex1 := ⟨ofSure (lazyReg (S := S) g1.re), jmp0 g1.bo⟩) ih (lg_ofSure _ _ _) ?_ ?_ h
  · exact il_emitGoal' (R := g1.re + 1) hI (by omega) rfl (batc_fresh fun j hj => by
        simp only [finJumps, List.mem_singleton] at hj
        subst hj; exact hI.goal.1)
      ⟨fun x hx => by simp at hx, by
        intro q hq x hx
        simp only [List.mem_singleton] at hq
        subst hq
        simp only [Comp.poleRegs, List.mem_cons, List.not_mem_nil, or_false] at hx
        omega, fun x hx => by simp [jmp0] at hx⟩
      (fun r hr => by
        simp [blockDefs, aliasDst] at hr
        subst hr; exact hkey)
      (fun r hr => by
        have e : r = g1.re := hr
        subst e; refine ⟨Nat.le_refl _, by omega, ?_⟩
        simp only [blockDefs, aliasDst, List.nil_append, List.filterMap_cons, List.filterMap_nil,
          List.mem_singleton]
        omega) trivial
  · refine liveC_emitG hI _ _ _ (fun r hr hn => (hn ?_).elim) (fun j hj => ?_)
    · obtain ⟨-, hr | ⟨hnd, hr⟩⟩ := hr
      · have hne : g1.re ≠ pro := by omega
        have e : r = g1.re := by
          simpa [renBlob, renPole, OpsRF, aliasReads, aliasDst, Opt.poleRegs, u1, upro, List.erase_cons, hne]
            using hr
        exact e
      · simp [renBlob, renFin, finRegs, jmpRegs, jmp0, renJmp] at hr
    · simp only [renBlob, renFin, getJmps, List.mem_singleton] at hj
      subst hj
      refine ⟨hI.lab hbt, fun r hl hnd _ => ?_⟩
      have hr : r ≠ pro := fun e => hnd (by
        subst e; simp [renBlob, renPole, blockDefs, aliasDst, upro])
      exact hl.mono_r fun x hk => hk.elim id fun hz => (hr ((lazK_ofSure.mp hz).2)).elim

/-- **`%4` under `%next`, both halves**, from the spec of `+collapse-lazy-atom`. -/
theorem kdl_liveRun_n4_nextL (env : CallEnv) (sup : Option Nomm) {p : Nomm} (hC : CollapseSpecL S Map)
    (ih : kdlLRLM S Map env sup p) {K : Nat → Nat → Prop} {laz : Lazy S} {th : Jmp}
    {region : List Nat} {g0 g1 : Comp.Gen Map} {nex : NextL S} (hI : IL K (CGoalL.next laz th) g0)
    (h : runLCM env true sup (Nomm.n4 p) (CGoalL.next laz th) region g0 = some (nex, g1)) :
    JL K nex g1 ∧ LiveC K (CGoalL.next laz th) g0 g1 nex := by
  simp only [runLCM] at h
  obtain ⟨a, ga, ha, h⟩ := bind_some h
  obtain ⟨⟨pro, there⟩, gb, hb, h⟩ := bind_some h
  have T : IL K (CGoalL.next (ofSure (lazyReg (S := S) pro)) (jmp0 there)) gb ∧
      LiveC K (CGoalL.next laz th) g0 gb ⟨ofSure (lazyReg (S := S) pro), jmp0 there⟩ := by
    cases a with
    | some x =>
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact hC K laz th g0 ga pro there hI ha
    | none =>
      obtain ⟨hn, hargs, rfl⟩ := collapseL_none ha
      obtain ⟨r, gc, hc, hb⟩ := bind_some hb
      rw [re_apply] at hc
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      simp only [hargs, if_true, pure_apply, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hb
      exact il_live_none hI hn hargs
  obtain ⟨J, L⟩ := kdl_liveRun_n4_tailL env sup ih T.1 h
  exact ⟨J, T.2.trans L⟩

/-- **`%4` under every goal, both halves**, from the spec of
`+collapse-lazy-atom`. -/
theorem kdl_liveRun_n4L (env : CallEnv) (sup : Option Nomm) {p : Nomm} (hC : CollapseSpecL S Map)
    (ih : kdlLRLM S Map env sup p) :
    kdlLRLM S Map env sup (Nomm.n4 p) := by
  intro K goal region g0 g1 nex hI hG h
  cases goal with
  | done => exact kdl_liveRun_n4_doneL env sup ih hI h
  | pick z o => exact kdl_liveRun_n4_pickL env sup ih hI h
  | next laz th => exact kdl_liveRun_n4_nextL env sup hC ih hI h

/-- **The `%clq` block for a `%pick` goal**, then the operand for its
register: `%3` under `%pick`, and the tail of `%3` under `%done` and
`%next`. -/
theorem kdl_liveRun_clqL (env : CallEnv) (sup : Option Nomm) {p : Nomm}
    (ih : kdlLRLM S Map env sup p) {K : Nat → Nat → Prop} {z o : Jmp}
    {region : List Nat} {g0 g1 : Comp.Gen Map} {nex : NextL S} (hI : IL K (CGoalL.pick z o : CGoalL S) g0)
    (h : (do
      let r ← re
      let oc ← emit ⟨[], [], Termin.clq r z o⟩
      runLCM env true sup p (CGoalL.next (ofSure (lazyReg (S := S) r)) (jmp0 oc)) region : CM Map (NextL S)) g0 =
        some (nex, g1)) :
    JL K nex g1 ∧ LiveC K (CGoalL.pick z o) g0 g1 nex := by
  have hd : g0.drop = false := hI.ats.1
  obtain ⟨hz, ho⟩ := (hI.goal : GoalL g0 (CGoalL.pick z o))
  obtain ⟨bz, hbz, -, az⟩ := hz
  obtain ⟨bo', hbo, -, ao⟩ := ho
  obtain ⟨r, ga, ha, h⟩ := bind_some h
  rw [re_apply] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  obtain ⟨o', gc, hc, h⟩ := bind_some h
  rw [emit_apply] at hc
  simp only [Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  have u0 : unproxy g0.cond g0.re = g0.re := unproxy_none (hI.cond_ge (Nat.le_refl _))
  refine liveRun_thenL (nex1 := ⟨ofSure (lazyReg (S := S) g0.re), jmp0 g0.bo⟩) ih (lg_ofSure _ _ _) ?_ ?_ h
  · exact il_emitGoal (R := g0.re + 1) hI (by omega) rfl
      (batc_fresh fun j hj => by
        simp only [finJumps, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        · exact hI.goal.1
        · exact hI.goal.2)
      ⟨fun x hx => by simp at hx, RegsIn.nil _, ⟨show g0.re < g0.re + 1 by omega, jmpIn_nil az, jmpIn_nil ao⟩⟩
      (fun r hr => by simp [blockDefs] at hr)
      (fun r hr => by
        have e : r = g0.re := hr
        subst e; exact ⟨Nat.le_refl _, by omega, by simp [blockDefs]⟩) trivial
  · refine liveC_emitG hI _ _ _ (fun r hr hn => (hn ?_).elim) (fun j hj => ?_)
    · obtain ⟨-, hr | ⟨-, hr⟩⟩ := hr
      · simp [renBlob, OpsRF] at hr
      · exact (show r = g0.re by
          simpa [renBlob, renFin, finRegs, jmpRegs, renJmp_nil _ az, renJmp_nil _ ao, u0, az, ao] using hr)
    · simp only [renBlob, renFin, getJmps, renJmp_nil _ az, renJmp_nil _ ao, List.mem_cons, List.not_mem_nil,
        or_false] at hj
      rcases hj with rfl | rfl
      · exact ⟨hI.lab hbz, fun r hl _ _ => Or.inl hl⟩
      · exact ⟨hI.lab hbo, fun r hl _ _ => Or.inr hl⟩

/-- **`%3` under every goal, both halves**, from the specs of
`+collapse-lazy-atom` and `+forl`. -/
theorem kdl_liveRun_n3L (env : CallEnv) (sup : Option Nomm) {p : Nomm} (hC : CollapseSpecL S Map)
    (hF : ForlSpecL S Map) (ih : kdlLRLM S Map env sup p) :
    kdlLRLM S Map env sup (Nomm.n3 p) := by
  intro K goal region g0 g1 nex hI hG h
  cases goal with
  | pick z o =>
    simp only [runLCM] at h
    exact kdl_liveRun_clqL env sup ih hI h
  | done =>
    simp only [runLCM] at h
    obtain ⟨⟨o0, o1⟩, ga, ha, h⟩ := bind_some h
    obtain ⟨I, D⟩ := doneBlocks_spec hI ha
    obtain ⟨J, L⟩ := kdl_liveRun_clqL env sup ih I h
    exact ⟨J, fun r hl => (D r (L r hl)).elim⟩
  | next laz th =>
    simp only [runLCM] at h
    by_cases hn : noneEquivalentL laz = true
    · rw [if_pos hn] at h; exact ih K _ region g0 g1 nex hI hG h
    · rw [if_neg hn] at h
      obtain ⟨a, ga, ha, h⟩ := bind_some h
      cases a with
      | none => cases h
      | some x =>
        obtain ⟨r, there⟩ := x
        obtain ⟨I1, L1⟩ := hC K laz th g0 ga r there hI ha
        obtain ⟨⟨z, o'⟩, gb, hb, h⟩ := bind_some h
        obtain ⟨I2, L2⟩ := hF K r there ga gb z o' I1 hb
        obtain ⟨J, L⟩ := kdl_liveRun_clqL env sup ih I2 h
        exact ⟨J, fun y hl => L1 y (L2 y (L y hl))⟩

/-- **The tail of `%5`** from the goal "`rq` at `o`": `JL` of the result,
and a register live at its entry is not `rp` and is live for that goal. -/
theorem kdl_five_tailL (env : CallEnv) (sup : Option Nomm) {p q : Nomm} (hp : PlainD p) (hq : PlainD q)
    (ihp : kdlLRLM S Map env sup p) (ihq : kdlLRLM S Map env sup q) {K : Nat → Nat → Prop} {region : List Nat}
    {rp rq o : Nat} {g3 g4 g5 g6 g7 : Comp.Gen Map} {nq nq' np nex : NextL S}
    (hI : IL K (CGoalL.next (ofSure (lazyReg (S := S) rq)) (jmp0 o)) g3)
    (hrp : rp < g3.re) (hdp : ¬ Defd g3.blocks rp) (hkp : HoonMap.get g3.cond rp = Option.none) (hne : rp ≠ rq)
    (h1 : runLCM env true sup q (CGoalL.next (ofSure (lazyReg (S := S) rq)) (jmp0 o)) region g3 = some (nq, g4))
    (h2 : pastL env.cod nq p region g4 = some (nq', g5))
    (h3 : runLCM env true sup p (CGoalL.next (ofSure (lazyReg (S := S) rp)) nq'.th) region g5 = some (np, g6))
    (h4 : copyL np nq'.laz g6 = some (nex, g7)) :
    JL K nex g7 ∧ ∀ r, LiveK (unpM g7) (fun x y => K x y ∨ lazK nex.th.there nex.laz x y) nex.th.there r →
      r ≠ rp ∧ GLiveKL (unpM g3) K (CGoalL.next (ofSure (lazyReg (S := S) rq)) (jmp0 o)) r := by
  obtain ⟨Jq, Lq⟩ := ihq K _ region g3 g4 nq hI (lg_ofSure _ _ _) h1
  obtain ⟨Ip, Lpast⟩ := pastL_spec Jq h2
  have Fq := frameRunM_plainD env q hq sup _ region g3 g4 nq h1
  have Dpast := frame_pastL h2
  obtain ⟨-, -, -, lq1, lq2⟩ := (labRunM_plainD (S := S) (Map := Map) env q hq sup
    (CGoalL.next (ofSure (lazyReg (S := S) rq)) (jmp0 o)) region).run g3 nq g4 hI.ats
    ⟨hI.goal.1, lg_ofSure _ _ _⟩ h1
  obtain ⟨LU2, -⟩ := lab_pastL h2 lq1 lq2
  rcases nq' with ⟨second, ⟨a2, s2⟩⟩
  obtain ⟨_, _, _, ha2⟩ := (Ip.goal : GoalL g5 (CGoalL.next second ⟨a2, s2⟩)).1
  simp only at ha2
  subst ha2
  have hrs : ∀ y, LReg second y → y ≠ rp := by
    intro y hy e
    rcases Fq.2 y (gregL_goal.mpr (Dpast.2 y hy)) with h | h
    · exact hne (e.symm.trans (gregL_ofSure.mp h))
    · omega
  have FL : FrL (CGoalL.next (ofSure (lazyReg (S := S) rq)) (jmp0 o)) g3 g5 :=
    frL_iff.mpr ((frL_iff.mp Fq.1).trans (Dpast.1.mono fun y h => h.elim))
  have Ip' : IL (fun x y => K x y ∨ lazK s2 second x y)
      (CGoalL.next (ofSure (lazyReg (S := S) rp)) (⟨[], s2⟩ : Jmp)) g5 :=
    il_lazyReg_after (il_addKills Ip) FL hrp hdp hkp (fun hg => hne (gregL_ofSure.mp hg)) Ip.goal.1
  obtain ⟨Jp, Lp⟩ := ihp _ _ region g5 g6 np Ip' (lg_ofSure _ _ _) h3
  have Fp := frameRunM_plainD env p hp sup _ region g5 g6 np h3
  obtain ⟨-, KP56, -, LU1, -⟩ := (labRunM_plainD (S := S) (Map := Map) env p hp sup
    (CGoalL.next (ofSure (lazyReg (S := S) rp)) (⟨[], s2⟩ : Jmp)) region).run g5 np g6 Ip.ats
    ⟨Ip.goal.1, lg_ofSure _ _ _⟩ h3
  have Ig : IL K (CGoalL.next second (jmp0 s2)) g6 :=
    il_glue Ip Jp (fun x y h => Or.inl h) Fp KP56 hrs
  have TA : TreesApart np.th.there np.laz s2 second := by
    intro e he e' he' y hy hy'
    have hg : GRegL (CGoalL.next np.laz np.th) y := ⟨e, he, hy⟩
    have hlt := ((Ip.goal : GoalL g5 (CGoalL.next second (⟨[], s2⟩ : Jmp))).2.2 e' he').2.2 y hy'
    rcases Fp.2 y hg with h | h
    · exact hrs y ((gregL_next (th := jmp0 s2)).mp ⟨e', he', hy'⟩) (gregL_ofSure.mp h)
    · have := hlt.1; omega
  obtain ⟨Inex, Lc⟩ := (copyL_spec (S := S) (Map := Map)) K np second s2 g6 g7 nex
    (Jp.monoK fun x y h => Or.inl h) Ig TA LU1 LU2 h4
  refine ⟨Inex, fun r hl => ?_⟩
  have h5 : LiveK (unpM g5) (fun x y => (K x y ∨ lazK s2 second x y) ∨
      lazK s2 (ofSure (lazyReg (S := S) rp)) x y) s2 r := Lp r (Lc r hl)
  have hne' : r ≠ rp := fun e => h5.nk (Or.inr (lazK_ofSure.mpr ⟨rfl, e⟩))
  have h5' : LiveK (unpM g5) (fun x y => K x y ∨ lazK s2 second x y) s2 r := h5.mono fun x y h => Or.inl h
  exact ⟨hne', Lq r (Lpast r h5')⟩

/-- **The arm `%5`, both halves**, from `LR` of its parts. -/
theorem kdl_liveRun_n5L (env : CallEnv) (sup : Option Nomm) {p q : Nomm} (hp : PlainD p) (hq : PlainD q)
    (ihp : kdlLRLM S Map env sup p) (ihq : kdlLRLM S Map env sup q) : kdlLRLM S Map env sup (Nomm.n5 p q) := by
  intro K goal region g0 g1 nex hI hG h
  simp only [runLCM] at h
  obtain ⟨rp, ga, ha, h⟩ := bind_some h
  obtain ⟨erp, ar, abl, acd, abo, adr⟩ := re_state ha
  obtain ⟨rq, gb, hb, h⟩ := bind_some h
  obtain ⟨erq, br, bbl, bcd, bbo, bdr⟩ := re_state hb
  obtain ⟨o, gc, hc, h⟩ := bind_some h
  obtain ⟨nq, gd, h1, h⟩ := bind_some h
  obtain ⟨nq', ge, h2, h⟩ := bind_some h
  obtain ⟨np, gf, h3, h4⟩ := bind_some h
  subst erp erq
  have Ib : IL K goal gb := il_re_up hI (by omega) (bbl.trans abl) (bcd.trans acd) (bbo.trans abo) (bdr.trans adr)
  have hU : unpM gb = unpM g0 := by simp only [unpM, bbl, abl, bcd, acd]
  have hpl : g0.re < gb.re := by omega
  have hql : ga.re < gb.re := by omega
  have hne : g0.re ≠ ga.re := by omega
  have hdp : ¬ Defd gb.blocks g0.re := by
    rw [bbl, abl]; intro hd; have := defd_lt hI.regs hd; omega
  have hdq : ¬ Defd gb.blocks ga.re := by
    rw [bbl, abl]; intro hd; have := defd_lt hI.regs hd; omega
  have hkp : HoonMap.get gb.cond g0.re = Option.none := by rw [bcd, acd]; exact hI.cond_ge (Nat.le_refl _)
  have hkq : HoonMap.get gb.cond ga.re = Option.none := by rw [bcd, acd]; exact hI.cond_ge (by omega)
  have hgp : ¬ GRegL goal g0.re := fun hg => by have := (hI.greg_lt hg).1; omega
  have hgq : ¬ GRegL goal ga.re := fun hg => by have := (hI.greg_lt hg).1; omega
  have O : OPh K goal gb gc g0.re ga.re o := by
    cases goal with
    | pick z o0 => exact oph_eqq Ib hpl hql hne hdp hdq hkp hkq hc
    | done =>
      obtain ⟨⟨o0, o1⟩, gx, hx, hc'⟩ := bind_some hc
      obtain ⟨Ix, Dead⟩ := doneBlocks_spec Ib hx
      have dx := frame_doneBlocks hx
      obtain ⟨p1, p2, p3⟩ := df_keep dx hpl (by omega) hdp hkp
      obtain ⟨q1, q2, q3⟩ := df_keep dx hql (by omega) hdq hkq
      obtain ⟨O1, O2, O3⟩ := oph_eqq Ix p1 q1 hne p2 q2 p3 q3 hc'
      exact ⟨O1, fun r hr hl => (Dead r (O2 r hr hl)).elim, O3⟩
    | next laz th =>
      obtain ⟨a, gx, hx, hc'⟩ := bind_some hc
      obtain ⟨dA, rA⟩ := frame_collapseL hx
      have nlp : ¬ (gb.re ≤ g0.re ∨ LReg laz g0.re) := fun h => h.elim (fun h => by omega)
        fun h => hgp (gregL_next.mpr h)
      have nlq : ¬ (gb.re ≤ ga.re ∨ LReg laz ga.re) := fun h => h.elim (fun h => by omega)
        fun h => hgq (gregL_next.mpr h)
      obtain ⟨p1, p2, p3⟩ := df_keep dA hpl nlp hdp hkp
      obtain ⟨q1, q2, q3⟩ := df_keep dA hql nlq hdq hkq
      cases a with
      | none =>
        obtain ⟨hn, hargs, rfl⟩ := collapseL_none hx
        dsimp only at hc'
        rw [if_pos hargs] at hc'
        exact oph_equ Ib hn hargs hpl hql hdp hdq hkp hkq hc'
      | some x =>
        obtain ⟨r0, o0⟩ := x
        dsimp only at hc'
        obtain ⟨⟨z, o1⟩, gy, hy, hc''⟩ := bind_some hc'
        obtain ⟨I1, L1⟩ := collapseSpecL K laz th gb gx r0 o0 Ib hx
        obtain ⟨I2, L2⟩ := forlSpecL K r0 o0 gx gy z o1 I1 hy
        have dB := frame_forl hy
        have r0f := rA r0 o0 rfl
        have xr : gb.re ≤ gx.re := dA.1
        obtain ⟨p1', p2', p3'⟩ := df_keep dB p1 (fun h => h.elim (fun e => nlp (e ▸ r0f)) fun h => by omega)
          p2 p3
        obtain ⟨q1', q2', q3'⟩ := df_keep dB q1 (fun h => h.elim (fun e => nlq (e ▸ r0f)) fun h => by omega)
          q2 q3
        obtain ⟨O1, O2, O3⟩ := oph_eqq I2 p1' q1' hne p2' q2' p3' q3' hc''
        exact ⟨O1, fun r hr hl => L1 r (L2 r (O2 r hr hl)), O3⟩
  obtain ⟨O1, O2, O3, O4, O5⟩ := O
  obtain ⟨J, L⟩ := kdl_five_tailL env sup hp hq ihp ihq O1 O3 O4 O5 hne h1 h2 h3 h4
  refine ⟨J, fun r hl => ?_⟩
  obtain ⟨hr, hg⟩ := L r hl
  have := O2 r hr hg
  rw [hU] at this
  exact this

/-- **The arm `%2` (the indirect call), both halves**, from `LR` of its
parts. -/
theorem kdl_liveRun_n2L (env : CallEnv) (sup : Option Nomm) {p q : Nomm} (hp : PlainD p) (hq : PlainD q)
    (ihp : kdlLRLM S Map env sup p) (ihq : kdlLRLM S Map env sup q) : kdlLRLM S Map env sup (Nomm.n2 p q Option.none) := by
  intro K goal region g0 g1 nex hI hG h
  simp only [runLCM, callLM, callL] at h
  obtain ⟨ns, ga, ha, h⟩ := bind_some h
  obtain ⟨⟨out, pro⟩, gb, hb, h⟩ := bind_some h
  obtain ⟨rSub, gc, hc, h⟩ := bind_some h
  obtain ⟨erS, cr, cbl, ccd, cbo, cdr⟩ := re_state hc
  obtain ⟨rFol, gd, hd, h⟩ := bind_some h
  obtain ⟨erF, dr, dbl, dcd, dbo, ddr⟩ := re_state hd
  obtain ⟨o, ge, he, h⟩ := bind_some h
  obtain ⟨nq, gf, h1, h⟩ := bind_some h
  obtain ⟨nq', gg, h2, h⟩ := bind_some h
  obtain ⟨np, gh, h3, h4⟩ := bind_some h
  subst erS erF
  have Ia : IL K ns.goal ga := il_simpleNextL hI ha
  have La : LiveC K goal g0 ga ns := liveC_simpleNextL hI ha
  obtain ⟨Ib, Lb⟩ := kerfSpecL K ns ga gb out pro Ia hb
  have Id : IL K (CGoalL.next (ofSure (lazyReg (S := S) pro)) (jmp0 out)) gd :=
    il_re_up Ib (by omega) (dbl.trans cbl) (dcd.trans ccd) (dbo.trans cbo) (ddr.trans cdr)
  have hU : unpM gd = unpM gb := by simp only [unpM, dbl, cbl, dcd, ccd]
  have hpro : pro < gb.re := (Ib.entry_regs (o := out) _ List.mem_cons_self pro rfl).1
  have hpl : gb.re < gd.re := by omega
  have hql : gc.re < gd.re := by omega
  have hne : gb.re ≠ gc.re := by omega
  have hdp : ¬ Defd gd.blocks gb.re := by
    rw [dbl, cbl]; intro hd'; have := defd_lt Ib.regs hd'; omega
  have hdq : ¬ Defd gd.blocks gc.re := by
    rw [dbl, cbl]; intro hd'; have := defd_lt Ib.regs hd'; omega
  have hkp : HoonMap.get gd.cond gb.re = Option.none := by rw [dcd, ccd]; exact Ib.cond_ge (Nat.le_refl _)
  have hkq : HoonMap.get gd.cond gc.re = Option.none := by rw [dcd, ccd]; exact Ib.cond_ge (by omega)
  obtain ⟨O1, O2, O3, O4, O5⟩ := oph_nok Id hpl hql hne (by omega) (by omega) hdp hdq hkp hkq he
  obtain ⟨J, L⟩ := kdl_five_tailL env sup hp hq ihp ihq O1 O3 O4 O5 hne h1 h2 h3 h4
  refine ⟨J, fun r hl => ?_⟩
  obtain ⟨hr, hg⟩ := L r hl
  have h5 := O2 r hr hg
  rw [hU] at h5
  exact La r (Lb r h5)

/-- **`%7` with the label clause**: `q` for the goal, then `p` for `q`'s
result, whose `LG` comes from `labRun_plain`. -/
theorem kdl_liveRun_n7L (env : CallEnv) (sup : Option Nomm) {p q : Nomm} (hq : PlainD q)
    (ihq : kdlLRLM S Map env (some p) q) (ihp : kdlLRLM S Map env sup p) : kdlLRLM S Map env sup (Nomm.n7 p q) := by
  intro K goal region g0 g2 nex hI hG h
  simp only [runLCM] at h
  obtain ⟨nex1, g1, h1, h2⟩ := bind_some h
  obtain ⟨J1, L1⟩ := ihq K goal region g0 g1 nex1 hI hG h1
  have G1 : LG nex1.goal g1 :=
    ((labRunM_plainD (S := S) (Map := Map) env q hq (some p) goal region).run g0 nex1 g1 hI.ats
      ⟨gfl_of_il hI, hG⟩ h1).2.2.2
  obtain ⟨J2, L2⟩ := ihp K nex1.goal region g1 g2 nex (jl_il J1) G1 h2
  exact ⟨J2, L1.trans L2⟩

/-- **The arms not closed yet, in the `LRL` form.** -/
structure kdlArmsLL (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (env : CallEnv) :
    Prop where
  cons : ∀ sup p q, PlainD p → PlainD q → kdlLRLM S Map env sup p → kdlLRLM S Map env sup q →
    kdlLRLM S Map env sup (Nomm.cons p q)
  n10 : ∀ sup a v q, PlainD v → PlainD q → kdlLRLM S Map env sup v → kdlLRLM S Map env sup q →
    kdlLRLM S Map env sup (Nomm.n10 a v q)
  dm : ∀ sup p q b key, PlainD p → PlainD q → kdlLRLM S Map env sup p → kdlLRLM S Map env sup q →
    kdlLRLM S Map env sup (Nomm.n2 p q (some (b, key)))

/-- **The run-level liveness with calls on all of `PlainD`**, with the label
clause, from the arms not closed yet. -/
theorem kdl_liveRun_plainOfL (env : CallEnv) (A : kdlArmsLL S Map env) :
    ∀ (nm : Nomm), PlainD nm → ∀ (sup : Option Nomm), kdlLRLM S Map env sup nm
  | Nomm.n0 ax, _, sup => kdl_lrl_of_lr (kdl_liveRun_n0 env sup ax)
  | Nomm.n1 k, _, sup => kdl_lrl_of_lr (kdl_liveRun_n1 env sup k)
  | Nomm.n3 p, h, sup => kdl_liveRun_n3L env sup collapseSpecL forlSpecL (kdl_liveRun_plainOfL env A p h sup)
  | Nomm.n4 p, h, sup => kdl_liveRun_n4L env sup collapseSpecL (kdl_liveRun_plainOfL env A p h sup)
  | Nomm.n5 p q, h, sup =>
    kdl_liveRun_n5L env sup h.1 h.2 (kdl_liveRun_plainOfL env A p h.1 sup) (kdl_liveRun_plainOfL env A q h.2 sup)
  | Nomm.cons p q, h, sup =>
    A.cons sup p q h.1 h.2 (kdl_liveRun_plainOfL env A p h.1 sup) (kdl_liveRun_plainOfL env A q h.2 sup)
  | Nomm.n7 p q, h, sup =>
    kdl_liveRun_n7L env sup h.2 (kdl_liveRun_plainOfL env A q h.2 (some p)) (kdl_liveRun_plainOfL env A p h.1 sup)
  | Nomm.n10 a v q, h, sup =>
    A.n10 sup a v q h.1 h.2 (kdl_liveRun_plainOfL env A v h.1 sup) (kdl_liveRun_plainOfL env A q h.2 sup)
  | Nomm.n2 p q Option.none, h, sup =>
    kdl_liveRun_n2L env sup h.1 h.2 (kdl_liveRun_plainOfL env A p h.1 sup) (kdl_liveRun_plainOfL env A q h.2 sup)
  | Nomm.n2 p q (some (b, key)), h, sup =>
    A.dm sup p q b key h.1 h.2 (kdl_liveRun_plainOfL env A p h.1 sup) (kdl_liveRun_plainOfL env A q h.2 sup)
  | Nomm.n6 _ _ _, h, _ => h.elim
  | Nomm.n11s _ _ _, h, _ => h.elim
  | Nomm.n11d _ _ _ _, h, _ => h.elim
  | Nomm.n12 _ _, h, _ => h.elim
  | Nomm.mean _ _ _ _ _, h, _ => h.elim


/-- The cons and `%10` arms in the `kdlLRLM` form, from the specs of
`+split` and `+into`. -/
theorem kdl_armsLL_of (env : CallEnv) (hS : SplitSpecL S Map) (hI : IntoSpecL S Map) :
    (∀ sup p q, PlainD p → PlainD q → kdlLRLM S Map env sup p → kdlLRLM S Map env sup q →
      kdlLRLM S Map env sup (Nomm.cons p q)) ∧
    (∀ sup a v q, PlainD v → PlainD q → kdlLRLM S Map env sup v → kdlLRLM S Map env sup q →
      kdlLRLM S Map env sup (Nomm.n10 a v q)) :=
  ⟨fun sup _ _ hp hq ihp ihq => kdl_liveRun_consL env sup hp hq ihp ihq hS, kdl_armsL_n10L hI env⟩

/-- **The run-level liveness with direct calls on `PlainD`**, from the arm
of the direct call alone (`hDM`, the field `dm` of `kdlArmsLL`): every other
arm is proved (cons and `%10` from `splitSpecL`, `intoSpecL`). -/
theorem liveRunM_plainD_of (env : CallEnv)
    (hDM : ∀ sup p q b key, PlainD p → PlainD q → kdlLRLM S Map env sup p → kdlLRLM S Map env sup q →
      kdlLRLM S Map env sup (Nomm.n2 p q (some (b, key)))) :
    ∀ (nm : Nomm), PlainD nm → ∀ (sup : Option Nomm), kdlLRLM S Map env sup nm :=
  kdl_liveRun_plainOfL env ⟨(kdl_armsLL_of env splitSpecL intoSpecL).1, (kdl_armsLL_of env splitSpecL intoSpecL).2, hDM⟩


end Raw
end SkaModel
end Formalization
