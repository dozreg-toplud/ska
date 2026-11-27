import lemmas.Ska.RawInvCLFrameCall

/-!
# The frame of a run with calls: cons and `%10`

README Gaps 14 (b), track D.  **`frameRun_cons`**: the frame of `[p q]`
from the frames of `p` and `q` (under `%done` a fresh `%don` block first;
under `%pick` a `%bom` block and the chain with empty needs; under `%next`
`+split`, `+past` of the head, then the chain `q`, `+past`, `p`, `+copy`,
`frame_chain`).  **`frameRun_n10`**: the same for `[10 [a v] q]` with
`+simple-next` and `+into` in front.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- The frame of a run from the footprint of its steps and of its result's
lazy tree. -/
theorem frX_of {goal : CGoalL S} {g0 g1 : Comp.Gen Map} {nex : NextL S} (d : DF (FG g0 goal) g0 g1)
    (l : ∀ y, LReg nex.laz y → FG g0 goal y) : FrX goal g0 g1 nex :=
  ⟨d, fun y hy => Or.symm (l y (gregL_goal.mp hy))⟩

theorem lReg_bunt {y : Nat} : ¬ LReg (ofSure (Sure.bunt : Sure S)) y := fun hy => by
  have := lReg_ofSure.mp hy
  simp [Sure.bunt, NMem] at this

/-- **The frame of a cons.** -/
theorem frameRun_cons (env : CallEnv) (sup : Option Nomm) {p q : Nomm}
    (hp : FrameRun (runLC (S := S) (Map := Map) env sup p)) (hq : FrameRun (runLC (S := S) (Map := Map) env sup q)) :
    FrameRun (runLC (S := S) (Map := Map) env sup (Nomm.cons p q)) := by
  intro goal region g0 g' nex h
  simp only [runLC] at h
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
theorem frameRun_n10 (env : CallEnv) (sup : Option Nomm) {a : Nat} {v q : Nomm}
    (hv : FrameRun (runLC (S := S) (Map := Map) env sup v)) (hq : FrameRun (runLC (S := S) (Map := Map) env sup q)) :
    FrameRun (runLC (S := S) (Map := Map) env sup (Nomm.n10 a v q)) := by
  intro goal region g0 g' nex h
  simp only [runLC] at h
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

end Raw
end SkaModel
end Formalization
