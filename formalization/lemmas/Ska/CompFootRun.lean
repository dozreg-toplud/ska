import lemmas.Ska.CompBelowRun

/-!
# Fact (i) for `run`: the write footprint

Fact (i) of README Gaps 12.2: the ops a run emits write no register of its
own result's sure need.  This file states the footprint of a run and proves
its steps and the arms of `run`.

* `poleWr p`: the register an op writes (its destination), `OpsWr Q A`,
  `BlobWr Q b`: every register the ops, or the parameters and ops of a block,
  write satisfies `Q`.
* `WroteIn Q g g'`: every block of `g'` is the block of `g` at that label
  with ops in front that write only registers of `Q`, or a block that writes
  only registers of `Q` (a new block, or one that replaces the old).  So the
  footprint of the run from `g` to `g'` lies in `Q`: the destination of every
  op in a new block and of every op put in front of an old block, and the
  parameters of the new blocks (the targets of the jumps with arguments that
  the run emits are new blocks; the goal's jump is not the run's code).
  The steps: `WroteIn.refl`, `WroteIn.trans`, `WroteIn.mono`, `wroteIn_reg`,
  `wroteIn_re`, `wroteIn_emit`, `wroteIn_addOps`.
* The arms, each with the registers it writes: `wr_splitNeed` (the need
  split), `wr_crashNeed`, `wr_medeLoop`, `wr_mede`, `wr_forl`,
  `wr_doneBlocks`, `wr_simpleNext`, `wr_bomb`, `wr_copyNeed` (registers of
  the two needs copied and none of the copy, when the two needs are distinct
  and apart), `wr_intoLoop`, `wr_collapseLazyAtom`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The registers an op writes -/

/-- The register an op writes (`localPole` and the calls store into it). -/
def poleWr : Pole → List Nat
  | Pole.imm _ d => [d]
  | Pole.mov _ d => [d]
  | Pole.inc _ d => [d]
  | Pole.con _ _ d => [d]
  | Pole.hed _ d => [d]
  | Pole.tal _ d => [d]
  | Pole.spy _ _ d => [d]
  | Pole.nok _ _ d => [d]
  | Pole.cal _ _ d => [d]
  | Pole.caf _ _ d _ => [d]
  | Pole.cam _ _ d _ => [d]
  | Pole.csl _ _ d => [d]
  | Pole.csf _ _ d _ => [d]
  | Pole.csm _ _ d _ => [d]
  | _ => []

/-- Every register the ops write satisfies `Q`. -/
def OpsWr (Q : Nat → Prop) (A : List Pole) : Prop := ∀ p ∈ A, ∀ x ∈ poleWr p, Q x

/-- Every register a block writes (its parameters, the destinations of its
ops) satisfies `Q`. -/
def BlobWr (Q : Nat → Prop) (b : Blob) : Prop := (∀ x ∈ b.par, Q x) ∧ OpsWr Q b.body

theorem OpsWr.mono {Q Q' : Nat → Prop} (h : ∀ x, Q x → Q' x) {A : List Pole} (hA : OpsWr Q A) : OpsWr Q' A :=
  fun p hp x hx => h x (hA p hp x hx)

theorem opsWr_nil (Q : Nat → Prop) : OpsWr Q [] := fun _ hp => absurd hp (List.not_mem_nil)

theorem OpsWr.append {Q : Nat → Prop} {A B : List Pole} (ha : OpsWr Q A) (hb : OpsWr Q B) : OpsWr Q (A ++ B) :=
  fun p hp => (List.mem_append.mp hp).elim (ha p) (hb p)

theorem opsWr_cons {Q : Nat → Prop} {p : Pole} {A : List Pole} (hp : ∀ x ∈ poleWr p, Q x) (hA : OpsWr Q A) :
    OpsWr Q (p :: A) := fun q hq => by
  rcases List.mem_cons.mp hq with e | e
  · rw [e]; exact hp
  · exact hA q e

theorem opsWr_one {Q : Nat → Prop} {p : Pole} (hp : ∀ x ∈ poleWr p, Q x) : OpsWr Q [p] :=
  opsWr_cons hp (opsWr_nil Q)

theorem BlobWr.mono {Q Q' : Nat → Prop} (h : ∀ x, Q x → Q' x) {b : Blob} (hb : BlobWr Q b) : BlobWr Q' b :=
  ⟨fun x hx => h x (hb.1 x hx), hb.2.mono h⟩

/-- A block with no parameters and no body writes nothing. -/
theorem blobWr_fin (Q : Nat → Prop) (f : Termin) : BlobWr Q ⟨[], [], f⟩ :=
  ⟨fun _ hx => absurd hx (List.not_mem_nil), opsWr_nil Q⟩

theorem blobWr_one {Q : Nat → Prop} {p : Pole} (f : Termin) (hp : ∀ x ∈ poleWr p, Q x) : BlobWr Q ⟨[], [p], f⟩ :=
  ⟨fun _ hx => absurd hx (List.not_mem_nil), opsWr_one hp⟩

/-- The ops that fill a need with `0` write its registers. -/
theorem opsWr_fill {Q : Nat → Prop} {ned : Need} (h : ∀ x, NMem ned x → Q x) :
    OpsWr Q ((flattenNeed ned).map fun x => Pole.imm (A 0) x) := by
  intro q hq x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hq
  simp only [poleWr, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rw [hx]; exact h y ((mem_flatten ned y).mp hy)

/-! ## The footprint of a run -/

/-- **Every block of `g'` is the block of `g` with ops in front that write
only registers of `Q`, or writes only registers of `Q`.** -/
def WroteIn (Q : Nat → Prop) (g g' : Gen Map) : Prop :=
  ∀ o b', HoonMap.get g'.blocks o = some b' →
    (∃ b A, HoonMap.get g.blocks o = some b ∧ b' = { b with body := A ++ b.body } ∧ OpsWr Q A) ∨ BlobWr Q b'

theorem WroteIn.refl (Q : Nat → Prop) (g : Gen Map) : WroteIn Q g g := fun _ b' hb =>
  Or.inl ⟨b', [], hb, by simp, opsWr_nil Q⟩

theorem WroteIn.mono {Q Q' : Nat → Prop} (h : ∀ x, Q x → Q' x) {g g' : Gen Map} (w : WroteIn Q g g') :
    WroteIn Q' g g' := fun o b' hb => by
  rcases w o b' hb with ⟨b, A, h1, h2, h3⟩ | w
  · exact Or.inl ⟨b, A, h1, h2, h3.mono h⟩
  · exact Or.inr (w.mono h)

theorem WroteIn.trans {Q : Nat → Prop} {g0 g1 g2 : Gen Map} (a : WroteIn Q g0 g1) (b : WroteIn Q g1 g2) :
    WroteIn Q g0 g2 := fun o b2 hb2 => by
  rcases b o b2 hb2 with ⟨b1, A2, h1, rfl, w2⟩ | w
  · rcases a o b1 h1 with ⟨b0, A1, h0, rfl, w1⟩ | w1
    · refine Or.inl ⟨b0, A2 ++ A1, h0, by simp, w2.append w1⟩
    · exact Or.inr ⟨w1.1, w2.append w1.2⟩
  · exact Or.inr w

theorem wroteIn_same {Q : Nat → Prop} {g g' : Gen Map} (h : g'.blocks = g.blocks) : WroteIn Q g g' :=
  fun o b' hb => by rw [h] at hb; exact WroteIn.refl Q g o b' hb

theorem wroteIn_reg (Q : Nat → Prop) (g : Gen Map) (k : Nat) : WroteIn Q g { g with re := k } :=
  wroteIn_same rfl

theorem wroteIn_re {Q : Nat → Prop} {g g' : Gen Map} {r : Nat} (h : (re : CM Map Nat) g = some (r, g')) :
    WroteIn Q g g' := by
  rw [re_apply] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.2]; exact wroteIn_reg Q g _

theorem wroteIn_of_gen {Q : Nat → Prop} {g g' : Gen Map} (e : g' = { g with re := g'.re }) : WroteIn Q g g' := by
  rw [e]; exact wroteIn_reg Q g _

theorem wroteIn_emitted {Q : Nat → Prop} {g : Gen Map} {b : Blob} (hb : BlobWr Q b) : WroteIn Q g (g.emitted b) := by
  intro o b' h
  simp only [Gen.emitted] at h
  by_cases hd : g.drop = true
  · rw [if_pos hd] at h; exact WroteIn.refl Q g o b' h
  · rw [if_neg hd, HoonMap.get_put] at h
    by_cases e : o = g.bo
    · rw [if_pos e] at h; cases h; exact Or.inr hb
    · rw [if_neg e] at h; exact WroteIn.refl Q g o b' h

theorem wroteIn_emit {Q : Nat → Prop} {g g' : Gen Map} {b : Blob} {o : Nat} (hb : BlobWr Q b)
    (h : (emit b : CM Map Nat) g = some (o, g')) : WroteIn Q g g' := by
  rw [emit_apply] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.2]; exact wroteIn_emitted hb

theorem wroteIn_addOps {Q : Nat → Prop} {g g' : Gen Map} {o : Nat} {ops : List Pole} {u : Unit}
    (hA : OpsWr Q ops) (h : addOps o ops g = some (u, g')) : WroteIn Q g g' := by
  unfold addOps at h
  by_cases hd : g.drop = true
  · rw [if_pos hd] at h; cases h; exact WroteIn.refl Q g
  · rw [if_neg hd] at h
    obtain ⟨b, hb, e⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at e
    rw [← e.2]
    intro o' b' h'
    simp only [HoonMap.get_put] at h'
    by_cases e' : o' = o
    · rw [if_pos e'] at h'; cases h'
      subst e'
      exact Or.inl ⟨b, ops, hb, rfl, hA⟩
    · rw [if_neg e'] at h'; exact WroteIn.refl Q g o' b' h'

end Comp
end SkaModel
end Formalization
