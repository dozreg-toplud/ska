import lemmas.Ska.RawInvCLFrameCons
import lemmas.Ska.RawInvCLFrameCol

/-!
# The frame of a run with calls: the induction on `PlainN`

README Gaps 14 (b), track D.  Every run of `runLC` on `PlainN` has the
frame `FrX` (`FrL` and the result's goal registers are the goal's or fresh),
with no precondition: **`frameRun_plain`**.  The arms: `frameRun_n0`
(`+bomb`, `+simple-next`, `+from`), `frameRun_n1` (`+mede`), `frameRun_n3`,
`frameRun_n4` (a local block, then the sub-run for a fresh register:
`frame_tail`), `frameRun_n5` (its `o` block, then `frame_chain`),
`frameRun_n7` (`frX_sub`), and those of `RawInvCLFrameCons.lean`
(`frameRun_cons`, `frameRun_n10`) and `RawInvCLFrameCall.lean`
(`frameRun_n2`).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **A local step, a fresh register, a block, then the sub-run** for the
goal "that register at the block". -/
theorem frame_tail {rp : CGoalL S → List Nat → CM Map (NextL S)} (hp : FrameRun rp) {goal : CGoalL S}
    {g0 g1 g2 g3 g4 : Comp.Gen Map} {r o : Nat} {b : Blob} {nex : NextL S} {region : List Nat}
    (h1 : DF (FG g0 goal) g0 g1) (h2 : (re : CM Map Nat) g1 = some (r, g2))
    (hb : r = g1.re → BlobWr (FG g0 goal) b) (h3 : (emit b : CM Map Nat) g2 = some (o, g3))
    (h4 : rp (CGoalL.next (ofSure (lazyReg (S := S) r)) (jmp0 o)) region g3 = some (nex, g4)) :
    FrX goal g0 g4 nex := by
  obtain ⟨d2, er, -⟩ := df_re (Q := FG g0 goal) h2
  obtain ⟨d3, -, -⟩ := df_emit (hb er) h3
  have r1 : g0.re ≤ g1.re := h1.1
  exact frX_sub (h1.trans (d2.trans d3)) (greg_lazyReg (by omega)) (hp _ _ _ _ _ h4)

/-- No footprint is in every footprint. -/
theorem DF.none {Q : Nat → Prop} {g g' : Comp.Gen Map} (h : DF (fun _ => False) g g') : DF Q g g' :=
  h.mono fun _ h => h.elim

/-! ## `%0` and `%1` -/

/-- **The frame of `%0`.** -/
theorem frameRun_n0 (env : CallEnv) (sup : Option Nomm) (ax : Nat) :
    FrameRun (runLC (S := S) (Map := Map) env sup (Nomm.n0 ax)) := by
  intro goal region g0 g1 nex h
  simp only [runLC] at h
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
theorem frameRun_n1 (env : CallEnv) (sup : Option Nomm) (k : Noun) :
    FrameRun (runLC (S := S) (Map := Map) env sup (Nomm.n1 k)) := by
  intro goal region g0 g1 nex h
  cases goal with
  | done =>
    simp only [runLC] at h
    obtain ⟨r, ga, ha, h⟩ := bind_some h
    obtain ⟨da, rfl, -⟩ := df_re (Q := FG g0 (CGoalL.done : CGoalL S)) ha
    obtain ⟨o, gb, hb, h⟩ := bind_some h
    obtain ⟨db, -, -⟩ := df_emit (Raw.blobWr_one (Q := FG g0 (CGoalL.done : CGoalL S)) (p := Pole.imm k g0.re)
      (fun x hx => by simp only [poleWr, List.mem_singleton] at hx; exact Or.inl (Nat.le_of_eq hx.symm)) _) hb
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact frX_of (da.trans db) fun y hy => (lReg_bunt hy).elim
  | pick z o =>
    simp only [runLC] at h
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
    simp only [runLC] at h
    obtain ⟨o, ga, ha, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine frX_of ((frame_medeL ha).mono fun y hy => ?_) fun y hy => (lReg_bunt hy).elim
    rcases hy with e | e
    · exact Or.inl e
    · exact Or.inr (gregL_next.mpr e)

/-! ## `%3` and `%4` -/

/-- **The frame of `%3`.** -/
theorem frameRun_n3 (env : CallEnv) (sup : Option Nomm) {p : Nomm}
    (hp : FrameRun (runLC (S := S) (Map := Map) env sup p)) :
    FrameRun (runLC (S := S) (Map := Map) env sup (Nomm.n3 p)) := by
  intro goal region g0 g1 nex h
  cases goal with
  | pick z o =>
    simp only [runLC] at h
    obtain ⟨r, ga, ha, h⟩ := bind_some h
    obtain ⟨oc, gb, hb, h⟩ := bind_some h
    exact frame_tail hp (DF.refl _ _) ha (fun _ => blobWr_nil _ _) hb h
  | done =>
    simp only [runLC] at h
    obtain ⟨⟨o0, o1⟩, ga, ha, h⟩ := bind_some h
    obtain ⟨r, gb, hb, h⟩ := bind_some h
    obtain ⟨oc, gc, hc, h⟩ := bind_some h
    exact frame_tail hp ((frame_doneBlocks ha).mono fun _ e => Or.inl e) hb (fun _ => blobWr_nil _ _) hc h
  | next laz th =>
    simp only [runLC] at h
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
theorem frameRun_n4 (env : CallEnv) (sup : Option Nomm) {p : Nomm}
    (hp : FrameRun (runLC (S := S) (Map := Map) env sup p)) :
    FrameRun (runLC (S := S) (Map := Map) env sup (Nomm.n4 p)) := by
  intro goal region g0 g1 nex h
  cases goal with
  | done =>
    simp only [runLC] at h
    obtain ⟨pro, ga, ha, h⟩ := bind_some h
    obtain ⟨da, rfl, ea⟩ := df_re (Q := FG g0 (CGoalL.done : CGoalL S)) ha
    obtain ⟨arg, gb, hb, h⟩ := bind_some h
    obtain ⟨oc, gc, hc, h⟩ := bind_some h
    exact frame_tail hp da hb (fun _ => Raw.blobWr_one (fun x hx => by
      simp only [poleWr, List.mem_singleton] at hx; exact Or.inl (Nat.le_of_eq hx.symm)) _) hc h
  | pick z o =>
    simp only [runLC] at h
    obtain ⟨pro, ga, ha, h⟩ := bind_some h
    obtain ⟨da, rfl, ea⟩ := df_re (Q := FG g0 (CGoalL.pick z o : CGoalL S)) ha
    obtain ⟨arg, gb, hb, h⟩ := bind_some h
    obtain ⟨oc, gc, hc, h⟩ := bind_some h
    exact frame_tail hp da hb (fun _ => Raw.blobWr_one (fun x hx => by
      simp only [poleWr, List.mem_singleton] at hx; exact Or.inl (Nat.le_of_eq hx.symm)) _) hc h
  | next laz th =>
    simp only [runLC] at h
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
theorem frameRun_n5 (env : CallEnv) (sup : Option Nomm) {p q : Nomm}
    (hp : FrameRun (runLC (S := S) (Map := Map) env sup p)) (hq : FrameRun (runLC (S := S) (Map := Map) env sup q)) :
    FrameRun (runLC (S := S) (Map := Map) env sup (Nomm.n5 p q)) := by
  intro goal region g0 g1 nex h
  simp only [runLC] at h
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
theorem frameRun_n7 (env : CallEnv) (sup : Option Nomm) {p q : Nomm}
    (hq : FrameRun (runLC (S := S) (Map := Map) env (some p) q)) (hp : FrameRun (runLC (S := S) (Map := Map) env sup p)) :
    FrameRun (runLC (S := S) (Map := Map) env sup (Nomm.n7 p q)) := by
  intro goal region g0 g1 nex h
  rw [runLC_n7] at h
  obtain ⟨nexq, gq, hrq, hrp⟩ := bind_some h
  have F1 := hq _ _ _ _ _ hrq
  exact frX_sub (frL_iff.mp F1.1) F1.2 (hp _ _ _ _ _ hrp)

/-! ## The induction -/

/-- **Every run of `runLC` on `PlainN` has the frame**, with no
precondition. -/
theorem frameRun_plain (env : CallEnv) :
    ∀ (nm : Nomm), PlainN nm → ∀ (sup : Option Nomm), FrameRun (runLC (S := S) (Map := Map) env sup nm)
  | Nomm.n0 ax, _, sup => frameRun_n0 env sup ax
  | Nomm.n1 k, _, sup => frameRun_n1 env sup k
  | Nomm.n3 p, h, sup => frameRun_n3 env sup (frameRun_plain env p h sup)
  | Nomm.n4 p, h, sup => frameRun_n4 env sup (frameRun_plain env p h sup)
  | Nomm.n5 p q, h, sup =>
    frameRun_n5 env sup (frameRun_plain env p h.1 sup) (frameRun_plain env q h.2 sup)
  | Nomm.cons p q, h, sup =>
    frameRun_cons env sup (frameRun_plain env p h.1 sup) (frameRun_plain env q h.2 sup)
  | Nomm.n7 p q, h, sup =>
    frameRun_n7 env sup (frameRun_plain env q h.2 (some p)) (frameRun_plain env p h.1 sup)
  | Nomm.n10 _ v q, h, sup =>
    frameRun_n10 env sup (frameRun_plain env v h.1 sup) (frameRun_plain env q h.2 sup)
  | Nomm.n2 p q Option.none, h, sup =>
    frameRun_n2 env sup (frameRun_plain env p h.1 sup) (frameRun_plain env q h.2 sup)
  | Nomm.n2 _ _ (some _), h, _ => h.elim
  | Nomm.n6 _ _ _, h, _ => h.elim
  | Nomm.n11s _ _ _, h, _ => h.elim
  | Nomm.n11d _ _ _ _, h, _ => h.elim
  | Nomm.n12 _ _, h, _ => h.elim
  | Nomm.mean _ _ _ _ _, h, _ => h.elim

end Raw
end SkaModel
end Formalization
