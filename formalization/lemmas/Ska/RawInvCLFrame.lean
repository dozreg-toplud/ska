import lemmas.Ska.RawInvCLPast
import lemmas.Ska.RawInvGen

/-!
# The frame of a run with calls: definitions and steps

README Gaps 14 (b), track D.  The second run of `%5`, cons, `%10` and `%2`
asks registers allocated before the first run, so its precondition `IL`
needs the first run's frame (`FrL` of `RawInvCLPast.lean`, checked by
`defsB` and `gregB` of `RawInvCLCheckIJ.lean`).  The frame holds of every
run with no precondition at all: it is about which registers the code
writes, not about the state's shape.

* `DF Q g g'`: the frame of a step with the footprint `Q` (`re` grows,
  `cond` grows only by keys from the old `re` on, a register defined after
  the step was defined before it or is in `Q`); `FrL goal g0 g1` is
  `DF (FG g0 goal) g0 g1` (`frL_iff`).  `DF.refl`, `DF.trans`, `DF.mono`.
* The steps: `df_re`, `df_emit`, `df_addOps`, `df_proxy`, `df_setTag`,
  `df_sureRequireLook`, `df_walkLazy` (a walk whose gate has the frame at
  every entry).
* `FrX goal g0 g1 nex`: `FrL` and the result's goal registers are the
  goal's or fresh (`gregB`); `FrameRun rp`: every run of `rp` has it.
  `frX_sub` (a local step, then a sub-run), `frX_post` (a run, then a local
  step), `frX_refl`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The frame of a step -/

/-- **The frame of a step with the footprint `Q`.** -/
def DF (Q : Nat → Prop) (g g' : Comp.Gen Map) : Prop :=
  g.re ≤ g'.re ∧ (∀ k v, HoonMap.get g'.cond k = some v → HoonMap.get g.cond k = some v ∨ g.re ≤ k) ∧
    ∀ y, Defd g'.blocks y → Defd g.blocks y ∨ Q y

/-- The footprint of a run from `g0` for `goal`: fresh registers and the
goal's. -/
def FG (g0 : Comp.Gen Map) (goal : CGoalL S) (y : Nat) : Prop := g0.re ≤ y ∨ GRegL goal y

theorem frL_iff {goal : CGoalL S} {g0 g1 : Comp.Gen Map} : FrL goal g0 g1 ↔ DF (FG g0 goal) g0 g1 := Iff.rfl

theorem DF.refl (Q : Nat → Prop) (g : Comp.Gen Map) : DF Q g g :=
  ⟨Nat.le_refl _, fun _ _ h => Or.inl h, fun _ h => Or.inl h⟩

theorem DF.trans {Q : Nat → Prop} {a b c : Comp.Gen Map} (h1 : DF Q a b) (h2 : DF Q b c) : DF Q a c := by
  obtain ⟨r1, c1, d1⟩ := h1
  obtain ⟨r2, c2, d2⟩ := h2
  refine ⟨Nat.le_trans r1 r2, fun k v hk => ?_, fun y hy => ?_⟩
  · rcases c2 k v hk with h | h
    · exact c1 k v h
    · exact Or.inr (Nat.le_trans r1 h)
  · rcases d2 y hy with h | h
    · exact d1 y h
    · exact Or.inr h

theorem DF.mono {Q Q' : Nat → Prop} (hQ : ∀ y, Q y → Q' y) {g g' : Comp.Gen Map} (h : DF Q g g') : DF Q' g g' :=
  ⟨h.1, h.2.1, fun y hy => (h.2.2 y hy).imp_right (hQ y)⟩

/-- A step that keeps `cond`, lets `re` grow and writes only `Q`. -/
theorem df_wroteIn {Q : Nat → Prop} {g g' : Comp.Gen Map} (hr : g.re ≤ g'.re) (hc : g'.cond = g.cond)
    (w : WroteIn Q g g') : DF Q g g' :=
  ⟨hr, fun k v hk => Or.inl (by rw [← hc]; exact hk), fun _ hy => defd_of_wroteIn w hy⟩

/-- A step that changes only `re` upwards. -/
theorem df_gen {Q : Nat → Prop} {g g' : Comp.Gen Map} (e : g' = { g with re := g'.re }) (hr : g.re ≤ g'.re) :
    DF Q g g' := by
  refine ⟨hr, fun k v hk => Or.inl ?_, fun y hy => Or.inl ?_⟩
  · rw [e] at hk; exact hk
  · rw [e] at hy; exact hy

/-! ## The steps -/

theorem df_re {Q : Nat → Prop} {g g' : Comp.Gen Map} {r : Nat} (h : (re : CM Map Nat) g = some (r, g')) :
    DF Q g g' ∧ r = g.re ∧ g'.re = g.re + 1 := by
  simp only [re, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨df_gen rfl (Nat.le_succ _), rfl, rfl⟩

theorem df_emitted {Q : Nat → Prop} {g : Comp.Gen Map} {b : Blob} (hb : BlobWr Q b) : DF Q g (g.emitted b) :=
  df_wroteIn (Nat.le_refl _) rfl (wroteIn_emitted hb)

theorem df_emit {Q : Nat → Prop} {g g' : Comp.Gen Map} {b : Blob} {o : Nat} (hb : BlobWr Q b)
    (h : (emit b : CM Map Nat) g = some (o, g')) : DF Q g g' ∧ o = g.bo ∧ g'.re = g.re := by
  rw [emit_apply] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨df_emitted hb, rfl, rfl⟩

/-- A block with no parameter whose ops write nothing. -/
theorem blobWr_nil (Q : Nat → Prop) (fin : Termin) : BlobWr Q ⟨[], [], fin⟩ :=
  ⟨fun _ h => absurd h List.not_mem_nil, opsWr_nil Q⟩

theorem blobWr_one {Q : Nat → Prop} {p : Pole} (hp : ∀ x ∈ poleWr p, Q x) (fin : Termin) :
    BlobWr Q ⟨[], [p], fin⟩ :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun q hq x hx => by
    rw [List.mem_singleton] at hq; subst hq; exact hp x hx⟩

theorem df_addOps {Q : Nat → Prop} {g g' : Comp.Gen Map} {o : Nat} {ops : List Pole} {u : Unit}
    (hA : OpsWr Q ops) (h : addOps o ops g = some (u, g')) : DF Q g g' := by
  have w := wroteIn_addOps hA h
  have e : g'.re = g.re ∧ g'.cond = g.cond := by
    unfold addOps at h
    split at h
    · cases h; exact ⟨rfl, rfl⟩
    · obtain ⟨b, -, e⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at e
      obtain ⟨-, rfl⟩ := e
      exact ⟨rfl, rfl⟩
  exact df_wroteIn (Nat.le_of_eq e.1.symm) e.2 w

theorem df_proxy {Q : Nat → Prop} {g g' : Comp.Gen Map} {r o p : Nat} (h : proxy r o g = some (p, g')) :
    DF Q g g' ∧ p = g.re ∧ g'.re = g.re + 1 := by
  unfold proxy at h
  dsimp only at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨df_gen rfl (Nat.le_succ _), rfl, rfl⟩
  · obtain ⟨tag, -, e⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    refine ⟨⟨Nat.le_succ _, fun k v hk => ?_, fun y hy => Or.inl hy⟩, rfl, rfl⟩
    by_cases hk' : k = g.re
    · exact Or.inr (Nat.le_of_eq hk'.symm)
    · left
      simpa [HoonMap.get_put, hk'] using hk

theorem df_setTag {Q : Nat → Prop} {g g' : Comp.Gen Map} {o : Nat} {region : List Nat} {u : Unit}
    (h : setTag o region g = some (u, g')) : DF Q g g' := by
  simp only [setTag, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  split
  · exact DF.refl Q g
  · exact ⟨Nat.le_refl _, fun _ _ h => Or.inl h, fun _ h => Or.inl h⟩

theorem df_sureRequireLook {Q : Nat → Prop} {sur : Sure S} {ned : Need} {g g' : Comp.Gen Map}
    (h : sureRequireLook sur g = some (ned, g')) :
    DF Q g g' ∧ ∀ r, NMem ned r → NMem sur.ned r ∨ g.re ≤ r := by
  have L := sureRequireLook_spec h
  obtain ⟨k, e⟩ := L.gen
  refine ⟨df_gen (by rw [e]) L.le, fun r hr => (L.mem r hr).imp_right fun h => h.1⟩

/-- **A walk whose gate has the frame `Q` at every entry has it.** -/
theorem df_walkLazy {f : Nat → Sure S → CM Map Unit} {Q : Nat → Prop} {o : Nat} {l : Lazy S}
    {g g' : Comp.Gen Map}
    (hf : ∀ e ∈ (o, l) :: entries l, ∀ a b, DF Q g a → f e.1 e.2.sure a = some ((), b) → DF Q a b)
    (h : walkLazy f o l g = some ((), g')) : DF Q g g' :=
  walkLazy_inv (W := fun a => DF Q g a) (fun e he a b ha hb => ha.trans (hf e he a b ha hb)) (DF.refl Q g) h

/-! ## The frame of a run -/

/-- **The frame of a run**: `FrL`, and a register of the result's lazy tree
is one of the goal's or fresh. -/
def FrX (goal : CGoalL S) (g0 g1 : Comp.Gen Map) (nex : NextL S) : Prop :=
  FrL goal g0 g1 ∧ ∀ y, GRegL nex.goal y → GRegL goal y ∨ g0.re ≤ y

/-- **Every run of `rp` has the frame** (no precondition). -/
def FrameRun (rp : CGoalL S → List Nat → CM Map (NextL S)) : Prop :=
  ∀ (goal : CGoalL S) (region : List Nat) (g0 g1 : Comp.Gen Map) (nex : NextL S),
    rp goal region g0 = some (nex, g1) → FrX goal g0 g1 nex

/-- **A local step, then a sub-run** for a goal whose registers are the
goal's or fresh. -/
theorem frX_sub {goal goal' : CGoalL S} {g0 g1 g2 : Comp.Gen Map} {nex : NextL S}
    (h1 : DF (FG g0 goal) g0 g1) (hg : ∀ y, GRegL goal' y → GRegL goal y ∨ g0.re ≤ y)
    (h2 : FrX goal' g1 g2 nex) : FrX goal g0 g2 nex := by
  have r1 := h1.1
  refine ⟨h1.trans (DF.mono (fun y hy => ?_) (frL_iff.mp h2.1)), fun y hy => ?_⟩
  · rcases hy with hy | hy
    · exact Or.inl (Nat.le_trans r1 hy)
    · rcases hg y hy with h | h
      · exact Or.inr h
      · exact Or.inl h
  · rcases h2.2 y hy with h | h
    · exact hg y h
    · exact Or.inr (Nat.le_trans r1 h)

/-- **A run, then a local step** whose footprint is fresh or the goal's. -/
theorem frX_post {goal : CGoalL S} {g0 g1 g2 : Comp.Gen Map} {nex nex' : NextL S} {Q : Nat → Prop}
    (h1 : FrX goal g0 g1 nex) (h2 : DF Q g1 g2) (hQ : ∀ y, Q y → FG g0 goal y)
    (hg : ∀ y, GRegL nex'.goal y → GRegL goal y ∨ g0.re ≤ y) : FrX goal g0 g2 nex' :=
  ⟨(frL_iff.mp h1.1).trans (h2.mono hQ), hg⟩

theorem frX_refl {goal : CGoalL S} {g0 g1 : Comp.Gen Map} {nex : NextL S} (h1 : DF (FG g0 goal) g0 g1)
    (hg : ∀ y, GRegL nex.goal y → GRegL goal y ∨ g0.re ≤ y) : FrX goal g0 g1 nex := ⟨h1, hg⟩

/-- The goal "a fresh register at `j`" has fresh registers only. -/
theorem greg_lazyReg {goal : CGoalL S} {g0 : Comp.Gen Map} {r : Nat} {j : Jmp} (hr : g0.re ≤ r) :
    ∀ y, GRegL (CGoalL.next (ofSure (lazyReg (S := S) r)) j) y → GRegL goal y ∨ g0.re ≤ y := fun y hy => by
  have e : y = r := gregL_ofSure.mp hy
  subst e; exact Or.inr hr

/-- The goal "no need at `j`" has no register. -/
theorem greg_bunt {goal : CGoalL S} {g0 : Comp.Gen Map} {j : Jmp} :
    ∀ y, GRegL (CGoalL.next (ofSure (Sure.bunt : Sure S)) j) y → GRegL goal y ∨ g0.re ≤ y := fun y hy => by
  have := gregL_ofSure.mp hy
  exact absurd this (by simp [Sure.bunt, NMem])


/-! ## Registers of a lazy tree -/

/-- `y` is a register of a sure need of the lazy tree `laz` (the root's or
an entry's). -/
def LReg (laz : Lazy S) (y : Nat) : Prop := NMem laz.sure.ned y ∨ ∃ e ∈ entries laz, NMem e.2.sure.ned y

theorem gregL_next {laz : Lazy S} {th : Jmp} {y : Nat} : GRegL (CGoalL.next laz th) y ↔ LReg laz y := by
  simp only [GRegL, LReg, List.mem_cons, exists_eq_or_imp]

theorem gregL_goal {nex : NextL S} {y : Nat} : GRegL nex.goal y ↔ LReg nex.laz y := gregL_next

theorem lReg_ofSure {s : Sure S} {y : Nat} : LReg (ofSure s) y ↔ NMem s.ned y := by
  rw [← gregL_next (th := jmp0 0)]; exact gregL_ofSure

/-! ## `+simple-next` and `+bomb` -/

theorem frame_simpleNextL {goal : CGoalL S} {g g' : Comp.Gen Map} {nex : NextL S}
    (h : simpleNextL goal g = some (nex, g')) :
    DF (fun _ => False) g g' ∧ ∀ y, GRegL nex.goal y → GRegL goal y ∨ g.re ≤ y := by
  cases goal with
  | next laz th =>
    simp only [simpleNextL, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨DF.refl _ _, fun y hy => Or.inl hy⟩
  | done =>
    simp only [simpleNextL] at h
    obtain ⟨r, g1, h1, h⟩ := bind_some h
    obtain ⟨d1, rfl, e1⟩ := df_re (Q := fun _ => False) h1
    obtain ⟨o, g2, h2, h⟩ := bind_some h
    obtain ⟨d2, -, e2⟩ := df_emit (blobWr_nil (fun _ => False) _) h2
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨d1.trans d2, fun y hy => Or.inr ?_⟩
    have e : y = g.re := gregL_ofSure.mp hy
    omega
  | pick z o =>
    simp only [simpleNextL] at h
    obtain ⟨r, g1, h1, h⟩ := bind_some h
    obtain ⟨d1, rfl, e1⟩ := df_re (Q := fun _ => False) h1
    obtain ⟨o', g2, h2, h⟩ := bind_some h
    obtain ⟨d2, -, e2⟩ := df_emit (blobWr_nil (fun _ => False) _) h2
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨d1.trans d2, fun y hy => Or.inr ?_⟩
    have e : y = g.re := gregL_ofSure.mp hy
    omega

theorem frame_bombL {miss : Option Nat} {g g' : Comp.Gen Map} {nex : NextL S}
    (h : (bombL miss : CM Map (NextL S)) g = some (nex, g')) :
    DF (fun _ => False) g g' ∧ ∀ y, ¬ GRegL nex.goal y := by
  simp only [bombL] at h
  obtain ⟨o, g1, h1, h⟩ := bind_some h
  obtain ⟨d1, -, -⟩ := df_emit (blobWr_nil (fun _ => False) _) h1
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨d1, fun y hy => ?_⟩
  have := gregL_ofSure.mp hy
  exact absurd this (by simp [Sure.bunt, NMem])

end Raw
end SkaModel
end Formalization
