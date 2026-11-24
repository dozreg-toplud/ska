import lemmas.Ska.CompFrame
import lemmas.Ska.CompGrowU
import lemmas.Ska.CompTop

/-!
# Toward the leaf conversion with the relaxed input hypothesis

README Gaps 12.2: to relax `∀ r, NMem ned r → g1.re ≤ r` in the `sem` of
`RunOKP`, `RunOKN` and `RunOKE` to `g1.re ≤ r ∨ NMem nex.laz.sure.ned r`,
the leaf conversion from `RunOK` must show that the code of a run keeps the
registers of its own sure need, which the `Keep` frame of `RunOK` does not
cover.  The footprint (`run_foot`) says which registers the blocks of the
run write; to use it on an execution two facts are needed, and this file
proves them.

* `Clear g`: no block at or above `g.bo`.  It holds of `gen0` and is kept by
  `Grow` and `GrowU` (`Clear.grow`, `Clear.growU`).  Without it a block of
  `g1` at a label of the run could be a block of `g0` that was there before
  the run, about which `WroteIn` says nothing.  With it every block of `g1`
  at a label from `g0.bo` on was made by the run: it writes only the
  footprint and its jumps are those of `JumpsBelow` or `JumpsU`
  (`clear_new`, `clear_newU`).
* `steps_transfer`: a path of one program is a path of every program that has
  the same blocks at the labels the path enters.  So a path through the
  run's blocks in a program built for the proof (the run's blocks and one
  block at the goal's label, nothing else) is a path in the real program up
  to that label.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Path

variable {Map : Type → Type} [HoonMap Map]

/-- **No block at or above `bo`.** -/
def Clear (g : Gen Map) : Prop := ∀ k, g.bo ≤ k → HoonMap.get g.blocks k = none

theorem clear_gen0 : Clear (gen0 : Gen Map) := fun k _ => by simp [gen0, HoonMap.get_empty]

theorem Clear.grow {g g' : Gen Map} (h : Clear g) (G : Grow g g') : Clear g' := fun k hk => by
  cases e : HoonMap.get g'.blocks k with
  | none => rfl
  | some b' =>
    exfalso
    rcases G.new k b' e with ⟨b, hb, _, _⟩ | ⟨_, u, _⟩
    · rw [h k (Nat.le_trans G.bo hk)] at hb; cases hb
    · omega

theorem Clear.growU {g g' : Gen Map} (h : Clear g) (G : GrowU g g') : Clear g' := fun k hk => by
  cases e : HoonMap.get g'.blocks k with
  | none => rfl
  | some b' =>
    exfalso
    rcases G.new k b' e with ⟨b, hb, _, _⟩ | ⟨_, u, _⟩
    · rw [h k (Nat.le_trans G.bo hk)] at hb; cases hb
    · omega

/-- **The blocks of a run, from a clear state**: every block of `g'` at a
label from `g.bo` on writes only the footprint and jumps below its label. -/
theorem clear_new {Q : Nat → Prop} {g g' : Gen Map} (h : Clear g) (G : Grow g g') (W : WroteIn Q g g') :
    ∀ k b, g.bo ≤ k → HoonMap.get g'.blocks k = some b → BlobWr Q b ∧ k < g'.bo ∧ JumpsBelow b.fin k := by
  intro k b hk hb
  have w : BlobWr Q b := by
    rcases W k b hb with ⟨b0, _, h0, _, _⟩ | w
    · rw [h k hk] at h0; cases h0
    · exact w
  rcases G.new k b hb with ⟨b0, h0, _, _⟩ | ⟨_, u, j⟩
  · rw [h k hk] at h0; cases h0
  · exact ⟨w, u, j⟩

/-- `clear_new` for `GrowU`, whose jumps may hop up. -/
theorem clear_newU {Q : Nat → Prop} {g g' : Gen Map} (h : Clear g) (G : GrowU g g') (W : WroteIn Q g g') :
    ∀ k b, g.bo ≤ k → HoonMap.get g'.blocks k = some b →
      BlobWr Q b ∧ k < g'.bo ∧ JumpsU g'.blocks g'.bo k b.fin := by
  intro k b hk hb
  have w : BlobWr Q b := by
    rcases W k b hb with ⟨b0, _, h0, _, _⟩ | w
    · rw [h k hk] at h0; cases h0
    · exact w
  rcases G.new k b hb with ⟨b0, h0, _, _⟩ | ⟨_, u, j⟩
  · rw [h k hk] at h0; cases h0
  · exact ⟨w, u, j⟩

/-! ## The program of the proof -/

/-- The blocks of `src` at the labels of `ks`, put into `m`. -/
def putFrom (src : Map Blob) : List Nat → Map Blob → Map Blob
  | [], m => m
  | k :: ks, m => putFrom src ks (match HoonMap.get src k with | some b => HoonMap.put m k b | none => m)

theorem get_putFrom (src : Map Blob) : ∀ (ks : List Nat) (m : Map Blob) (k : Nat),
    HoonMap.get (putFrom src ks m) k =
      if k ∈ ks ∧ (HoonMap.get src k).isSome then HoonMap.get src k else HoonMap.get m k
  | [], m, k => by simp [putFrom]
  | k0 :: ks, m, k => by
    rw [putFrom, get_putFrom src ks]
    cases e : HoonMap.get src k0 with
    | none =>
      by_cases h : k = k0
      · subst h; simp [e]
      · simp [h]
    | some b =>
      simp only [HoonMap.get_put]
      by_cases h : k = k0
      · subst h; simp [e]
      · simp [h]

/-- **The program of the leaf conversion**: the blocks of `bl` at the labels
from `lo` below `hi`, the block `bz` at `z`, and no other block. -/
def regionProg (c : Straight Map) (bl : Map Blob) (lo hi z : Nat) (bz : Blob) : Straight Map :=
  { c with blocks := putFrom bl (List.range' lo (hi - lo)) (HoonMap.put HoonMap.empty z bz) }

theorem regionProg_in {c : Straight Map} {bl : Map Blob} {lo hi z k : Nat} {bz : Blob} (hz : z < lo)
    (h0 : lo ≤ k) (h1 : k < hi) : HoonMap.get (regionProg c bl lo hi z bz).blocks k = HoonMap.get bl k := by
  simp only [regionProg, get_putFrom, List.mem_range'_1, HoonMap.get_put, HoonMap.get_empty]
  cases HoonMap.get bl k with
  | none => simp; omega
  | some b => simp; omega

theorem regionProg_z {c : Straight Map} {bl : Map Blob} {lo hi z : Nat} {bz : Blob} (hz : z < lo) :
    HoonMap.get (regionProg c bl lo hi z bz).blocks z = some bz := by
  simp only [regionProg, get_putFrom, List.mem_range'_1, HoonMap.get_put, if_pos]
  rw [if_neg (by omega)]

theorem regionProg_out {c : Straight Map} {bl : Map Blob} {lo hi z k : Nat} {bz : Blob}
    (hk : ¬ (lo ≤ k ∧ k < hi)) (hkz : k ≠ z) : HoonMap.get (regionProg c bl lo hi z bz).blocks k = none := by
  simp only [regionProg, get_putFrom, List.mem_range'_1, HoonMap.get_put, HoonMap.get_empty]
  rw [if_neg (by omega), if_neg hkz]

section Transfer
variable {σ : Type} {lib : Lib} {O : Oracle σ} {gul : Noun}

/-- **A path is a path of every program with the same blocks at the labels
it enters.** -/
theorem steps_transfer {c c' : Straight Map} {x y : Cfg σ Map} {es : List (Nat × Nat)}
    (h : Steps lib O c gul x es y) (hb : ∀ a ∈ es, HoonMap.get c'.blocks a.2 = HoonMap.get c.blocks a.2) :
    Steps lib O c' gul x es y := by
  induction h with
  | refl => exact Steps.refl _
  | @step x z y e es s _ ih =>
    refine Steps.step ?_ (ih fun a ha => hb a (List.mem_append_right _ ha))
    cases s with
    | pass h1 h2 => exact Step.pass h1 h2
    | op h1 h2 h3 h4 => exact Step.op h1 h2 h3 h4
    | @jump j b' h1 h2 h3 h4 h5 =>
      exact Step.jump h1 h2 h3 h4 ((hb _ (List.mem_append_left _ (List.mem_singleton_self _))).trans h5)

/-- Every block of the program at a label of `L` writes only `Q`; its jumps
may leave `L`. -/
def WrIn (Q L : Nat → Prop) (c : Straight Map) : Prop :=
  ∀ o b, L o → HoonMap.get c.blocks o = some b → BlobWr Q b

/-- **The frame lemma up to the first exit**: along a path from `x`, whose
block writes only `Q`, through blocks at labels of `L` that write only `Q`,
either every label entered is in `L` and the registers outside `Q` keep their
values to the end, or the path enters a first label outside `L`, at a
configuration whose registers outside `Q` are those of `x`. -/
theorem steps_exit {c : Straight Map} {Q L : Nat → Prop} (hc : WrIn Q L c) {x y : Cfg σ Map}
    {es : List (Nat × Nat)} (h : Steps lib O c gul x es y) (hx : BlobWr Q x.b) :
    ((∀ a ∈ es, L a.2) ∧ ∀ r, ¬ Q r → HoonMap.get y.regs r = HoonMap.get x.regs r) ∨
    ∃ es1 es2 y1, es = es1 ++ es2 ∧ Steps lib O c gul x es1 y1 ∧ Steps lib O c gul y1 es2 y ∧ ¬ L y1.lab ∧
      (∀ a ∈ es1, L a.2 ∨ a.2 = y1.lab) ∧ ∀ r, ¬ Q r → HoonMap.get y1.regs r = HoonMap.get x.regs r := by
  induction h with
  | refl => exact Or.inl ⟨fun a ha => absurd ha List.not_mem_nil, fun _ _ => rfl⟩
  | @step x z y e es s rest ih =>
    have fz : ∀ r, ¬ Q r → HoonMap.get z.regs r = HoonMap.get x.regs r :=
      fun r hr => step_frame s r fun hw => hr (stepWr_sub hx r hw)
    -- the steps inside a block
    have inner : e = [] → BlobWr Q z.b → ((∀ a ∈ e ++ es, L a.2) ∧
        ∀ r, ¬ Q r → HoonMap.get y.regs r = HoonMap.get x.regs r) ∨
        ∃ es1 es2 y1, e ++ es = es1 ++ es2 ∧ Steps lib O c gul x es1 y1 ∧ Steps lib O c gul y1 es2 y ∧
          ¬ L y1.lab ∧ (∀ a ∈ es1, L a.2 ∨ a.2 = y1.lab) ∧
          ∀ r, ¬ Q r → HoonMap.get y1.regs r = HoonMap.get x.regs r := fun he hz => by
      subst he
      rcases ih hz with ⟨l, f⟩ | ⟨es1, es2, y1, e1, s1, s2, n1, l1, f1⟩
      · exact Or.inl ⟨l, fun r hr => (f r hr).trans (fz r hr)⟩
      · refine Or.inr ⟨es1, es2, y1, e1, ?_, s2, n1, l1, fun r hr => (f1 r hr).trans (fz r hr)⟩
        have := Steps.step s s1
        rwa [List.nil_append] at this
    cases s with
    | pass h1 h2 => exact inner rfl ⟨fun _ hr => absurd hr List.not_mem_nil, hx.2⟩
    | op h1 h2 h3 h4 =>
      exact inner rfl ⟨fun r hr => hx.1 r hr, fun p hp' => hx.2 p (by rw [h3]; exact List.mem_cons_of_mem _ hp')⟩
    | @jump j b' h1 h2 h3 h4 h5 =>
      by_cases hl : L j.there
      · rcases ih (hc _ _ hl h5) with ⟨l, f⟩ | ⟨es1, es2, y1, e1, s1, s2, n1, l1, f1⟩
        · refine Or.inl ⟨fun a ha => ?_, fun r hr => (f r hr).trans (fz r hr)⟩
          rcases List.mem_append.mp ha with ha | ha
          · rw [List.mem_singleton] at ha; rw [ha]; exact hl
          · exact l a ha
        · refine Or.inr ⟨[(x.lab, j.there)] ++ es1, es2, y1, by rw [e1, List.append_assoc],
            Steps.step (Step.jump h1 h2 h3 h4 h5) s1, s2, n1, fun a ha => ?_, fun r hr => (f1 r hr).trans (fz r hr)⟩
          rcases List.mem_append.mp ha with ha | ha
          · rw [List.mem_singleton] at ha; rw [ha]; exact Or.inl hl
          · exact l1 a ha
      · refine Or.inr ⟨[(x.lab, j.there)], es, ⟨j.there, b', j.args, x.regs, x.t, x.st⟩, rfl, ?_, rest, hl,
          fun a ha => ?_, fun _ _ => rfl⟩
        · have := Steps.step (Step.jump (c := c) (lib := lib) (O := O) (gul := gul) h1 h2 h3 h4 h5) (Steps.refl _)
          rwa [List.append_nil] at this
        · rw [List.mem_singleton] at ha; rw [ha]; exact Or.inr rfl

/-- **A configuration at a jump runs as the jump**: what is left of its block
is the terminator, which takes `j`, so it runs as `goJ` of `j`. -/
theorem run_jump {c : Straight Map} {x : Cfg σ Map} {j : Jmp} (hp : x.params = []) (hq : x.b.par = [])
    (hb : x.b.body = []) (ht : taken x.regs x.b.fin = some j) :
    Path.run lib O c gul x = goJ lib O c gul x.st x.regs x.t j := by
  obtain ⟨lab, ⟨par, body, fin⟩, params, regs, t, st⟩ := x
  simp only at hp hq hb ht
  subst hp hq hb
  simp only [Path.run, goJ]
  rw [execBlob]
  simp only [ne_eq, not_true_eq_false, or_self, if_false]
  cases fin with
  | lti n r z o =>
    simp only [taken] at ht
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp ht
    simp only [hv, Option.bind_eq_bind, Option.bind_some]; rfl
  | clq r z o =>
    simp only [taken] at ht
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp ht
    simp only [hv, Option.bind_eq_bind, Option.bind_some]; rfl
  | eqq l r z o =>
    simp only [taken] at ht
    obtain ⟨v, hv, h2⟩ := Option.bind_eq_some_iff.mp ht
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h2
    simp only [hv, hw, Option.bind_eq_bind, Option.bind_some]
  | brn r z o =>
    simp only [taken] at ht
    obtain ⟨v, hv, h2⟩ := Option.bind_eq_some_iff.mp ht
    simp only [hv, Option.bind_eq_bind, Option.bind_some]
    by_cases e0 : v = A 0
    · rw [if_pos e0] at h2 ⊢; cases h2; rfl
    · rw [if_neg e0] at h2 ⊢
      by_cases e1 : v = A 1
      · rw [if_pos e1] at h2 ⊢; cases h2; rfl
      · rw [if_neg e1] at h2; cases h2
  | brz r z o =>
    simp only [taken] at ht
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp ht
    simp only [hv, Option.bind_eq_bind, Option.bind_some]
  | hop t' =>
    simp only [taken, Option.some.injEq] at ht
    subst ht; rfl
  | _ => simp [taken] at ht

end Transfer

end Comp
end SkaModel
end Formalization
