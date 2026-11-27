import lemmas.Ska.RawInvCLFrameSplit

/-!
# The frame of a run with calls: `+collapse-lazy-atom`, `+forl`, `+done-blocks`, `+mede`

README Gaps 14 (b), track D.  The local steps of `%1`, `%3`, `%4`, `%5`
write only fresh registers and registers of their goal's lazy tree.

* `df_crashNeed`, `df_medeLoop` (no `NB` hypothesis), `df_collapseGate`;
* **`frame_collapseL`**: `+collapse-lazy-atom` writes fresh registers and
  registers of the goal's lazy tree, and the register it returns is one of
  those;
* **`frame_forl`** (`r` and fresh registers), **`frame_doneBlocks`** (fresh
  registers), **`frame_medeL`** (fresh registers and the goal's).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## `+crash-need` and the loop of `+mede` -/

/-- **`+crash-need` writes registers of its need and fresh ones.** -/
theorem df_crashNeed {Q : Nat → Prop} {o : Nat} {atom : Sum Nat Nat} {ned : Need} {g g' : Comp.Gen Map} {u : Unit}
    (hn : ∀ y, NMem ned y → Q y) (hm : Ple Q g.re) (h : crashNeed o atom ned g = some (u, g')) : DF Q g g' := by
  cases atom with
  | inr p =>
    simp only [crashNeed] at h
    exact df_addOps (opsWr_cons (p := Pole.cel p) (fun x hx => by simp [poleWr] at hx)
      (fun q hq => opsWr_fill (fun x hx => hn x hx) q (crashFill_sub p ned hq))) h
  | inl n =>
    simp only [crashNeed] at h
    obtain ⟨r, g1, h1, h⟩ := bind_some h
    obtain ⟨d1, rfl, -⟩ := df_re (Q := Q) h1
    refine d1.trans (df_addOps (opsWr_cons (p := Pole.imm (A n) g.re) (fun x hx => ?_)
      (opsWr_cons (p := Pole.cel g.re) (fun x hx => by simp [poleWr] at hx)
        (opsWr_fill fun x hx => hn x hx))) h)
    simp only [poleWr, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rw [hx]; exact hm _ (Nat.le_refl _)

/-- **The loop of `+mede` writes registers of its need and fresh ones.** -/
theorem df_medeLoop {Q : Nat → Prop} {o : Nat} : ∀ (som : Noun) (ned : Need) (g g' : Comp.Gen Map) (u : Unit),
    (∀ y, NMem ned y → Q y) → Ple Q g.re → medeLoop o som ned g = some (u, g') → DF Q g g'
  | _, Need.none, g, g', u, _, _, h => by
    simp only [medeLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact DF.refl _ g
  | som, Need.this r, g, g', u, hn, _, h => by
    simp only [medeLoop] at h
    exact df_addOps (opsWr_one (p := Pole.imm som r) (fun x hx => by
      simp only [poleWr, List.mem_cons, List.mem_nil_iff, or_false] at hx; exact hn x hx)) h
  | Noun.atom n, Need.pair p q, g, g', u, hn, hm, h => by
    simp only [medeLoop] at h
    exact df_crashNeed hn hm h
  | Noun.cell a b, Need.pair p q, g, g', u, hn, hm, h => by
    simp only [medeLoop] at h
    obtain ⟨u1, g1, h1, h2⟩ := bind_some h
    have d1 := df_medeLoop a p g g1 u1 (fun y hy => hn y (Or.inl hy)) hm h1
    exact d1.trans (df_medeLoop b q g1 g' u (fun y hy => hn y (Or.inr hy)) (ple_trans hm d1.1) h2)
  | Noun.atom n, Need.both r hh t, g, g', u, hn, hm, h => by
    simp only [medeLoop] at h
    exact df_crashNeed hn hm h
  | Noun.cell a b, Need.both r hh t, g, g', u, hn, hm, h => by
    simp only [medeLoop] at h
    obtain ⟨u0, g0, h0, h⟩ := bind_some h
    have d0 : DF Q g g0 := df_addOps (opsWr_one (p := Pole.imm (C a b) r) (fun x hx => by
      simp only [poleWr, List.mem_cons, List.mem_nil_iff, or_false] at hx; exact hn x (Or.inl hx))) h0
    obtain ⟨u1, g1, h1, h2⟩ := bind_some h
    have d1 := df_medeLoop a hh g0 g1 u1 (fun y hy => hn y (Or.inr (Or.inl hy))) (ple_trans hm d0.1) h1
    exact d0.trans (d1.trans (df_medeLoop b t g1 g' u (fun y hy => hn y (Or.inr (Or.inr hy)))
      (ple_trans hm (Nat.le_trans d0.1 d1.1)) h2))

/-! ## `+mede` -/

/-- **`+mede` writes fresh registers and registers of its lazy tree.** -/
theorem frame_medeL {th : Jmp} {som : Noun} {laz : Lazy S} {g g' : Comp.Gen Map} {o : Nat}
    (h : medeL th som laz g = some (o, g')) : DF (fun y => g.re ≤ y ∨ LReg laz y) g g' := by
  unfold medeL at h
  obtain ⟨o1, g1, h1, h⟩ := bind_some h
  obtain ⟨d1, -, e1⟩ := df_emit (blobWr_nil (fun y => g.re ≤ y ∨ LReg laz y) _) h1
  obtain ⟨g2, g3, h2, h⟩ := bind_some h
  cases h2
  split at h
  · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact d1
  obtain ⟨u, g4, h4, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  refine d1.trans (df_walkLazy (Q := fun y => g.re ≤ y ∨ LReg laz y) (fun e he a b ha hb => ?_) h4)
  have hra : g1.re ≤ a.re := ha.1
  obtain ⟨ned, a1, ha1, hb⟩ := bind_some hb
  obtain ⟨da1, hn⟩ := df_sureRequireLook (Q := fun y => g.re ≤ y ∨ LReg laz y) ha1
  refine da1.trans (df_medeLoop som ned a1 b () (fun y hy => ?_) (fun y hy => Or.inl ?_) hb)
  · rcases hn y hy with e' | e'
    · exact Or.inr (lReg_of_entry he e')
    · exact Or.inl (by omega)
  · have := da1.1; omega

/-! ## `+forl` and `+done-blocks` -/

/-- **`+forl` writes `r` (the parameter of `barg`) and fresh registers.** -/
theorem frame_forl {r o : Nat} {g g' : Comp.Gen Map} {x : Nat × Nat} (h : forl r o g = some (x, g')) :
    DF (fun y => y = r ∨ g.re ≤ y) g g' := by
  unfold forl at h
  obtain ⟨r0, g1, h1, h⟩ := bind_some h
  obtain ⟨d1, rfl, e1⟩ := df_re (Q := fun y => y = r ∨ g.re ≤ y) h1
  obtain ⟨r1, g2, h2, h⟩ := bind_some h
  obtain ⟨d2, rfl, e2⟩ := df_re (Q := fun y => y = r ∨ g.re ≤ y) h2
  obtain ⟨barg, g3, h3, h⟩ := bind_some h
  obtain ⟨d3, -, e3⟩ := df_emit (Q := fun y => y = r ∨ g.re ≤ y)
    ⟨fun y hy => by simp only [List.mem_singleton] at hy; exact Or.inl hy, opsWr_nil _⟩ h3
  obtain ⟨if0, g4, h4, h⟩ := bind_some h
  obtain ⟨d4, -, e4⟩ := df_emit (Q := fun y => y = r ∨ g.re ≤ y) (Raw.blobWr_one (p := Pole.imm (A 0) g.re)
    (fun y hy => by simp only [poleWr, List.mem_singleton] at hy; exact Or.inr (by omega)) _) h4
  obtain ⟨if1, g5, h5, h⟩ := bind_some h
  obtain ⟨d5, -, e5⟩ := df_emit (Q := fun y => y = r ∨ g.re ≤ y) (Raw.blobWr_one (p := Pole.imm (A 1) g1.re)
    (fun y hy => by simp only [poleWr, List.mem_singleton] at hy; exact Or.inr (by omega)) _) h5
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact d1.trans (d2.trans (d3.trans (d4.trans d5)))

/-- **`+done-blocks` writes fresh registers.** -/
theorem frame_doneBlocks {g g' : Comp.Gen Map} {x : Nat × Nat}
    (h : (doneBlocks : CM Map (Nat × Nat)) g = some (x, g')) : DF (fun y => g.re ≤ y) g g' := by
  unfold doneBlocks at h
  obtain ⟨r0, g1, h1, h⟩ := bind_some h
  obtain ⟨d1, rfl, e1⟩ := df_re (Q := fun y => g.re ≤ y) h1
  obtain ⟨r1, g2, h2, h⟩ := bind_some h
  obtain ⟨d2, rfl, e2⟩ := df_re (Q := fun y => g.re ≤ y) h2
  obtain ⟨o0, g3, h3, h⟩ := bind_some h
  obtain ⟨d3, -, e3⟩ := df_emit (Q := fun y => g.re ≤ y) (Raw.blobWr_one (p := Pole.imm (A 0) g.re)
    (fun y hy => by simp only [poleWr, List.mem_singleton] at hy; omega) _) h3
  obtain ⟨o1, g4, h4, h⟩ := bind_some h
  obtain ⟨d4, -, e4⟩ := df_emit (Q := fun y => g.re ≤ y) (Raw.blobWr_one (p := Pole.imm (A 1) g1.re)
    (fun y hy => by simp only [poleWr, List.mem_singleton] at hy; omega) _) h4
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact d1.trans (d2.trans (d3.trans d4))

/-! ## `+collapse-lazy-atom` -/

/-- **The gate of `+collapse-lazy-atom` writes registers of the entry's need
and fresh ones** (the proxies are fresh keys). -/
theorem df_collapseGate {Q : Nat → Prop} {r o oLaz : Nat} {sur : Sure S} {a b : Comp.Gen Map}
    (hs : ∀ y, NMem sur.ned y → Q y) (hm : Ple Q a.re) (h : collapseGate r o oLaz sur a = some ((), b)) :
    DF Q a b := by
  unfold collapseGate at h
  obtain ⟨ned, a1, ha1, h⟩ := bind_some h
  obtain ⟨da1, hn⟩ := df_sureRequireLook (Q := Q) ha1
  have hq : ∀ y, NMem ned y → Q y := fun y hy => by
    rcases hn y hy with e | e
    · exact hs y e
    · exact hm y e
  have hm1 : Ple Q a1.re := ple_trans hm da1.1
  have src : ∀ {a2 : Comp.Gen Map} {s : Nat},
      (if oLaz = o then pure r else proxy r oLaz : CM Map Nat) a1 = some (s, a2) → DF Q a1 a2 := by
    intro a2 s hs2
    split at hs2
    · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hs2
      obtain ⟨-, rfl⟩ := hs2
      exact DF.refl _ _
    · exact (df_proxy hs2).1
  split at h
  · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact da1
  · rename_i r'
    split at h
    · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact da1
    obtain ⟨s, a2, ha2, h⟩ := bind_some h
    have d2 := src ha2
    exact da1.trans (d2.trans (df_addOps (opsWr_one (p := Pole.mov s r') (fun x hx => by
      simp only [poleWr, List.mem_singleton] at hx
      exact hq x (by rw [hx]; rfl))) h))
  · obtain ⟨s, a2, ha2, h⟩ := bind_some h
    have d2 := src ha2
    exact da1.trans (d2.trans (df_crashNeed hq (ple_trans hm1 d2.1) h))

/-- **`+collapse-lazy-atom` writes fresh registers and registers of the
goal's lazy tree, and returns one of those.** -/
theorem frame_collapseL {nex : NextL S} {g g' : Comp.Gen Map} {a : Option (Nat × Nat)}
    (h : collapseLazyAtomL nex g = some (a, g')) :
    DF (fun y => g.re ≤ y ∨ LReg nex.laz y) g g' ∧
      ∀ r there, a = some (r, there) → (g.re ≤ r ∨ LReg nex.laz r) := by
  unfold collapseLazyAtomL at h
  split at h
  · cases h
  split at h
  · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨DF.refl _ _, fun r there e => by cases e⟩
  obtain ⟨nedSure, g1, h1, h⟩ := bind_some h
  obtain ⟨d1, hn⟩ := df_sureRequireLook (Q := fun y => g.re ≤ y ∨ LReg nex.laz y) h1
  obtain ⟨⟨r, there⟩, g2, h2, h⟩ := bind_some h
  have P : DF (fun y => g.re ≤ y ∨ LReg nex.laz y) g1 g2 ∧ (g.re ≤ r ∨ LReg nex.laz r) := by
    split at h2
    · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      refine ⟨DF.refl _ _, ?_⟩
      rcases hn _ rfl with e | e
      · exact Or.inr (Or.inl e)
      · exact Or.inl e
    · obtain ⟨r0, g3, h3, h2⟩ := bind_some h2
      obtain ⟨d3, rfl, -⟩ := df_re (Q := fun y => g.re ≤ y ∨ LReg nex.laz y) h3
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      exact ⟨d3, Or.inl d1.1⟩
    · obtain ⟨r0, g3, h3, h2⟩ := bind_some h2
      obtain ⟨d3, rfl, -⟩ := df_re (Q := fun y => g.re ≤ y ∨ LReg nex.laz y) h3
      obtain ⟨o, g4, h4, h2⟩ := bind_some h2
      obtain ⟨d4, -, -⟩ := df_emit (blobWr_nil (fun y => g.re ≤ y ∨ LReg nex.laz y) _) h4
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      exact ⟨d3.trans d4, Or.inl d1.1⟩
    · obtain ⟨o, g4, h4, h2⟩ := bind_some h2
      obtain ⟨d4, -, -⟩ := df_emit (blobWr_nil (fun y => g.re ≤ y ∨ LReg nex.laz y) _) h4
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      refine ⟨d4, ?_⟩
      rcases hn _ (Or.inl rfl) with e | e
      · exact Or.inr (Or.inl e)
      · exact Or.inl e
  obtain ⟨d2, hr⟩ := P
  obtain ⟨g3, g4, h3, h⟩ := bind_some h
  cases h3
  have d12 := d1.trans d2
  split at h
  · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨d12, fun r' there' e => by cases e; exact hr⟩
  obtain ⟨u, g5, h5, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨d12.trans (df_walkLazy (Q := fun y => g.re ≤ y ∨ LReg nex.laz y) (fun e he a b ha hb => ?_) h5),
    fun r' there' e => by cases e; exact hr⟩
  have hra : g2.re ≤ a.re := ha.1
  have hg2 : g.re ≤ g2.re := d12.1
  refine df_collapseGate (fun y hy => ?_) (fun y hy => Or.inl (by omega)) hb
  rcases List.mem_cons.mp he with rfl | he'
  · have e' : y = r := hy
    subst e'; exact hr
  · rw [entries_mkSure ⟨Need.this r, nex.laz.sure.lok⟩ nex.laz] at he'
    exact Or.inr (lReg_of_entry (List.mem_cons_of_mem (0, nex.laz) he') hy)

end Raw
end SkaModel
end Formalization
