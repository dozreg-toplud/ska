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
values to the end, or the path reaches, through labels of `L` only, a
configuration `y1` at its terminator that takes a jump `j` to a first label
outside `L`, and the registers of `y1` outside `Q` are those of `x`.  The
configuration is the one before the jump, whose block is still one of `L`,
so that a second program with the same blocks in `L` and another block at
`j.there` has the same prefix (`steps_transfer`). -/
theorem steps_exit {c : Straight Map} {Q L : Nat → Prop} (hc : WrIn Q L c) {x y : Cfg σ Map}
    {es : List (Nat × Nat)} (h : Steps lib O c gul x es y) (hx : BlobWr Q x.b) :
    ((∀ a ∈ es, L a.2) ∧ ∀ r, ¬ Q r → HoonMap.get y.regs r = HoonMap.get x.regs r) ∨
    ∃ (es1 es2 : List (Nat × Nat)) (y1 : Cfg σ Map) (j : Jmp) (b' : Blob),
      es = es1 ++ [(y1.lab, j.there)] ++ es2 ∧ Steps lib O c gul x es1 y1 ∧
      y1.params = [] ∧ y1.b.par = [] ∧ y1.b.body = [] ∧ taken y1.regs y1.b.fin = some j ∧
      HoonMap.get c.blocks j.there = some b' ∧
      Steps lib O c gul ⟨j.there, b', j.args, y1.regs, y1.t, y1.st⟩ es2 y ∧ ¬ L j.there ∧
      (∀ a ∈ es1, L a.2) ∧ ∀ r, ¬ Q r → HoonMap.get y1.regs r = HoonMap.get x.regs r := by
  induction h with
  | refl => exact Or.inl ⟨fun a ha => absurd ha List.not_mem_nil, fun _ _ => rfl⟩
  | @step x z y e es s rest ih =>
    have fz : ∀ r, ¬ Q r → HoonMap.get z.regs r = HoonMap.get x.regs r :=
      fun r hr => step_frame s r fun hw => hr (stepWr_sub hx r hw)
    -- the steps inside a block
    have inner : e = [] → BlobWr Q z.b → ((∀ a ∈ e ++ es, L a.2) ∧
        ∀ r, ¬ Q r → HoonMap.get y.regs r = HoonMap.get x.regs r) ∨
        ∃ (es1 es2 : List (Nat × Nat)) (y1 : Cfg σ Map) (j : Jmp) (b' : Blob),
          e ++ es = es1 ++ [(y1.lab, j.there)] ++ es2 ∧ Steps lib O c gul x es1 y1 ∧
          y1.params = [] ∧ y1.b.par = [] ∧ y1.b.body = [] ∧ taken y1.regs y1.b.fin = some j ∧
          HoonMap.get c.blocks j.there = some b' ∧
          Steps lib O c gul ⟨j.there, b', j.args, y1.regs, y1.t, y1.st⟩ es2 y ∧ ¬ L j.there ∧
          (∀ a ∈ es1, L a.2) ∧ ∀ r, ¬ Q r → HoonMap.get y1.regs r = HoonMap.get x.regs r := fun he hz => by
      subst he
      rcases ih hz with ⟨l, f⟩ | ⟨es1, es2, y1, j, b', e1, s1, p1, q1, d1, t1, hb1, s2, n1, l1, f1⟩
      · exact Or.inl ⟨l, fun r hr => (f r hr).trans (fz r hr)⟩
      · refine Or.inr ⟨es1, es2, y1, j, b', e1, ?_, p1, q1, d1, t1, hb1, s2, n1, l1,
          fun r hr => (f1 r hr).trans (fz r hr)⟩
        have := Steps.step s s1
        rwa [List.nil_append] at this
    cases s with
    | pass h1 h2 => exact inner rfl ⟨fun _ hr => absurd hr List.not_mem_nil, hx.2⟩
    | op h1 h2 h3 h4 =>
      exact inner rfl ⟨fun r hr => hx.1 r hr, fun p hp' => hx.2 p (by rw [h3]; exact List.mem_cons_of_mem _ hp')⟩
    | @jump j b' h1 h2 h3 h4 h5 =>
      by_cases hl : L j.there
      · rcases ih (hc _ _ hl h5) with ⟨l, f⟩ | ⟨es1, es2, y1, jj, bb, e1, s1, p1, q1, d1, t1, hb1, s2, n1, l1, f1⟩
        · refine Or.inl ⟨fun a ha => ?_, fun r hr => (f r hr).trans (fz r hr)⟩
          rcases List.mem_append.mp ha with ha | ha
          · rw [List.mem_singleton] at ha; rw [ha]; exact hl
          · exact l a ha
        · refine Or.inr ⟨[(x.lab, j.there)] ++ es1, es2, y1, jj, bb, by rw [e1]; simp only [List.append_assoc],
            Steps.step (Step.jump h1 h2 h3 h4 h5) s1, p1, q1, d1, t1, hb1, s2, n1, fun a ha => ?_,
            fun r hr => (f1 r hr).trans (fz r hr)⟩
          rcases List.mem_append.mp ha with ha | ha
          · rw [List.mem_singleton] at ha; rw [ha]; exact hl
          · exact l1 a ha
      · exact Or.inr ⟨[], es, x, j, b', rfl, Steps.refl _, h1, h2, h3, h4, h5, rest, hl,
          fun a ha => absurd ha List.not_mem_nil, fun _ _ => rfl⟩

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

/-! ## The leaf conversion -/

section Leaf
variable {S : Type} [HoonSet S] {σ : Type} {lib : Lib} {O : Oracle σ} {gul : Noun}

/-- A block with no parameters, entered with arguments, crashes. -/
theorem execBlob_args {c : Straight Map} {st : σ} {regs : Map (Option Noun)} {t : Trace} {b : Blob}
    (hp : b.par = []) {args : List (Option Nat)} (ha : args ≠ []) :
    execBlob lib O c gul st regs t b args = none := by
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil ha
  rw [execBlob]
  simp [hp, evalPass, evalPassLoop]

theorem agree_regionProg {c : Straight Map} {g0 g1 : Gen Map} {z : Nat} {bz : Blob} (hz : z < g0.bo) :
    Agree (regionProg c g1.blocks g0.bo g1.bo z bz) g0 g1 := fun _ h0 h1 => regionProg_in hz h0 h1

theorem goJ_regionProg_z {c : Straight Map} {bl : Map Blob} {lo hi : Nat} {j : Jmp} {bz : Blob}
    (hz : j.there < lo) (hj : j.args = []) {st : σ} {R : Map (Option Noun)} {t : Trace} :
    goJ lib O (regionProg c bl lo hi j.there bz) gul st R t j =
      execBlob lib O (regionProg c bl lo hi j.there bz) gul st R t bz [] := by
  simp only [goJ, regionProg_z hz, Option.bind_some, hj]

/-- The block that crashes, put at the goal's label. -/
def bomB : Blob := ⟨[], [], Termin.bom none⟩

/-- The block that returns `0`, put at the goal's label. -/
def zeroB : Blob := ⟨[], [Pole.imm (A 0) 0], Termin.don 0⟩

theorem execBlob_zeroB {c : Straight Map} {st : σ} {R : Map (Option Noun)} {t : Trace} :
    execBlob lib O c gul st R t zeroB [] = some (Tone.zero (A 0), st) := by
  have h := runs_imm (lib := lib) (O := O) (c := c) (gul := gul) (st := st) (t := t) (A 0) 0 R [] (Termin.don 0)
  simp only [List.append_nil] at h
  rw [zeroB, h, execBlob_don', read_store_eq]; rfl

/-- **The leaf conversion, for one jump of the goal.**  Every block of the
run (at a label from `g0.bo` below `g1.bo`) writes only `Q`, and the jump `j`
has no arguments and goes below `g0.bo`.  If in each program
`regionProg c g1.blocks g0.bo g1.bo j.there bz` entering `je` from `regs`
does what entering `j` from some register file does, then one register file
`R'` does it in every program that agrees with `g1` on the run's labels, and
`R'` holds what `regs` holds outside `Q`.  `R'` is the register file of the
configuration before the jump to `j.there` on the path from `je`: the path
in the program with `bomB` at `j.there` returns, so it leaves the run's labels
(in the program with `zeroB` the same path would end the same way, while
there it returns `0`), and it leaves them only to `j.there`, the one label
outside them with a block; the two programs show that the state and the
trace there are those of the start. -/
theorem leaf_exit {Q : Nat → Prop} {g0 g1 : Gen Map}
    (hw : ∀ k b, g0.bo ≤ k → k < g1.bo → HoonMap.get g1.blocks k = some b → BlobWr Q b)
    {st : σ} {t : Trace} {regs : Map (Option Noun)} {je j : Jmp} (hj : j.args = []) (hjl : j.there < g0.bo)
    (c : Straight Map)
    (H : ∀ bz : Blob, ∃ R : Map (Option Noun),
      goJ lib O (regionProg c g1.blocks g0.bo g1.bo j.there bz) gul st regs t je =
        goJ lib O (regionProg c g1.blocks g0.bo g1.bo j.there bz) gul st R t j) :
    ∃ R' : Map (Option Noun), (∀ r, ¬ Q r → HoonMap.get R' r = HoonMap.get regs r) ∧
      ∀ c' : Straight Map, Agree c' g0 g1 → goJ lib O c' gul st regs t je = goJ lib O c' gul st R' t j := by
  obtain ⟨R0, e0⟩ := H bomB
  obtain ⟨R1, e1⟩ := H zeroB
  rw [goJ_regionProg_z hjl hj, bomB, execBlob_bom', ← bomB] at e0
  rw [goJ_regionProg_z hjl hj, execBlob_zeroB] at e1
  by_cases hin : g0.bo ≤ je.there ∧ je.there < g1.bo
  · -- the entry is a block of the run
    have g1in : ∀ bz, HoonMap.get (regionProg c g1.blocks g0.bo g1.bo j.there bz).blocks je.there =
        HoonMap.get g1.blocks je.there := fun _ => regionProg_in hjl hin.1 hin.2
    obtain ⟨b, hb⟩ : ∃ b, HoonMap.get g1.blocks je.there = some b := by
      unfold goJ at e1; rw [g1in] at e1
      cases h : HoonMap.get g1.blocks je.there with
      | none => rw [h] at e1; cases e1
      | some b => exact ⟨b, rfl⟩
    have run0 : ∀ c' : Straight Map, HoonMap.get c'.blocks je.there = some b →
        goJ lib O c' gul st regs t je = Path.run lib O c' gul ⟨je.there, b, je.args, regs, t, st⟩ :=
      fun c' h => by simp only [goJ, h, Option.bind_some, Path.run]
    have r0 := (run0 _ ((g1in bomB).trans hb)).symm.trans e0
    have r1 := (run0 _ ((g1in zeroB).trans hb)).symm.trans e1
    obtain ⟨es, y, hs, he⟩ := (run_iff_path _ _).mp r0
    have wr : WrIn Q (fun k => g0.bo ≤ k ∧ k < g1.bo) (regionProg c g1.blocks g0.bo g1.bo j.there bomB) :=
      fun o b' ho hb' => hw o b' ho.1 ho.2 (by rw [← regionProg_in hjl ho.1 ho.2]; exact hb')
    have same : ∀ (c1 c2 : Straight Map), Agree c1 g0 g1 → Agree c2 g0 g1 → ∀ (es : List (Nat × Nat)),
        (∀ a ∈ es, g0.bo ≤ a.2 ∧ a.2 < g1.bo) → ∀ a ∈ es, HoonMap.get c2.blocks a.2 = HoonMap.get c1.blocks a.2 :=
      fun c1 c2 a1 a2 es hl a ha => (a2 a.2 (hl a ha).1 (hl a ha).2).trans (a1 a.2 (hl a ha).1 (hl a ha).2).symm
    rcases steps_exit wr hs (hw _ _ hin.1 hin.2 hb) with
      ⟨l, _⟩ | ⟨es1, es2, y1, jj, b', _, s1, p1, q1, d1, t1, hb1, _, n1, l1, f1⟩
    · -- a path that ends inside the run ends the same way in the program with `zeroB`
      have s' := steps_transfer (c' := regionProg c g1.blocks g0.bo g1.bo j.there zeroB) hs
        (same _ _ (agree_regionProg hjl) (agree_regionProg hjl) es l)
      have := (steps_run s').trans (endOf_run he)
      rw [r1] at this; cases this
    · -- the path leaves the run at `j.there`
      have hjj : jj.there = j.there := by
        by_cases e : jj.there = j.there
        · exact e
        · rw [regionProg_out n1 e] at hb1; cases hb1
      have rj : Path.run lib O (regionProg c g1.blocks g0.bo g1.bo j.there bomB) gul y1 =
          execBlob lib O (regionProg c g1.blocks g0.bo g1.bo j.there bomB) gul y1.st y1.regs y1.t bomB jj.args := by
        rw [run_jump p1 q1 d1 t1]; simp only [goJ, hjj, regionProg_z hjl, Option.bind_some]
      have r0' := (steps_run s1).symm.trans r0
      rw [rj] at r0'
      have ha : jj.args = [] := by
        by_cases e : jj.args = []
        · exact e
        · rw [execBlob_args rfl e] at r0'; cases r0'
      rw [ha, bomB, execBlob_bom'] at r0'
      simp only [Option.some.injEq, Prod.mk.injEq, Tone.two.injEq] at r0'
      obtain ⟨htt, hst⟩ := r0'
      have ejj : jj = j := by
        cases jj; cases j; simp only at hjj ha hj; subst hjj ha hj; rfl
      refine ⟨y1.regs, f1, fun c' ag' => ?_⟩
      have s' := steps_transfer (c' := c') s1 (same _ _ (agree_regionProg hjl) ag' es1 l1)
      rw [run0 c' ((ag' _ hin.1 hin.2).trans hb), steps_run s', run_jump p1 q1 d1 t1, hst, htt, ejj]
  · -- the entry is the goal's jump
    have hjj : je.there = j.there := by
      by_cases e : je.there = j.there
      · exact e
      · unfold goJ at e1; rw [regionProg_out hin e] at e1; cases e1
    have ha : je.args = [] := by
      by_cases e : je.args = []
      · exact e
      · unfold goJ at e1; rw [hjj, regionProg_z hjl, Option.bind_some, execBlob_args rfl e] at e1; cases e1
    have ejj : je = j := by
      cases je; cases j; simp only at hjj ha hj; subst hjj ha hj; rfl
    exact ⟨regs, fun _ _ => rfl, fun c' _ => by rw [ejj]⟩

/-- Registers that hold, one by one, what some register file holding a noun
for a need holds, hold the noun for the need. -/
theorem holdsN_pointwise : ∀ (ned : Need) {R' : Map (Option Noun)} {n : Noun}, Fits ned n →
    (∀ x, NMem ned x → ∃ R : Map (Option Noun), HoldsN ned R n ∧
      ∀ v, SkaModel.read x R = some v → SkaModel.read x R' = some v) →
    HoldsN ned R' n
  | Need.none, _, _, _, _ => trivial
  | Need.this r, _, _, _, h => by
    obtain ⟨R, hR, k⟩ := h r rfl
    exact k _ hR
  | Need.pair p q, _, Noun.cell a b, hf, h =>
    ⟨holdsN_pointwise p hf.1 fun x hx => by
        obtain ⟨R, hR, k⟩ := h x (Or.inl hx); exact ⟨R, hR.1, k⟩,
     holdsN_pointwise q hf.2 fun x hx => by
        obtain ⟨R, hR, k⟩ := h x (Or.inr hx); exact ⟨R, hR.2, k⟩⟩
  | Need.both r p q, _, Noun.cell a b, hf, h =>
    ⟨by obtain ⟨R, hR, k⟩ := h r (Or.inl rfl); exact k _ hR.1,
     holdsN_pointwise p hf.1 fun x hx => by
        obtain ⟨R, hR, k⟩ := h x (Or.inr (Or.inl hx)); exact ⟨R, hR.2.1, k⟩,
     holdsN_pointwise q hf.2 fun x hx => by
        obtain ⟨R, hR, k⟩ := h x (Or.inr (Or.inr hx)); exact ⟨R, hR.2.2, k⟩⟩
  | Need.pair _ _, _, Noun.atom _, hf, _ => hf.elim
  | Need.both _ _ _, _, Noun.atom _, hf, _ => hf.elim

/-- The jumps of a goal have no arguments and go below `bo`. -/
def LeafJ (bo : Nat) : CGoal S → Prop
  | CGoal.next _ th => th.args = [] ∧ th.there < bo
  | CGoal.pick z o => (z.args = [] ∧ z.there < bo) ∧ (o.args = [] ∧ o.there < bo)
  | CGoal.done => True

/-- **The leaf conversion**: a run that meets `RunOK`, from a state with no
block at or above `g0.bo`, whose blocks write only registers of `Q` (as
`Foot.wr` and `clear_new` give), for a goal whose jumps have no arguments and
go below `g0.bo`, does in every program that agrees with `g1` on the run's
labels what `GoalSem` says with every register outside `Q` kept, and so
with the registers of the result's own sure need kept (`leaf_keep`). -/
theorem leaf_sem {nm : Nomm} {goal : CGoal S} {g0 g1 : Gen Map} {nex : Next S}
    (R : RunOK lib nm goal g0 g1 nex) (d0 : g0.drop = false) {Q : Nat → Prop}
    (hw : ∀ k b, g0.bo ≤ k → k < g1.bo → HoonMap.get g1.blocks k = some b → BlobWr Q b)
    (hj : LeafJ g0.bo goal) {K : Nat → Prop} (hK : ∀ r, K r → ¬ Q r)
    (c : Straight Map) (ag : Agree c g0 g1) (st : σ) (s : Noun) (regs : Map (Option Noun)) (t : Trace)
    (hh : HoldsS nex.laz regs s) :
    GoalSem lib O c gul st K regs t nex.th goal (pureEval nm s) := by
  have S0 : ∀ c', Agree c' g0 g1 →
      GoalSem lib O c' gul st (Keep g0 g1 goal) regs t nex.th goal (pureEval nm s) :=
    fun c' a' => R.sem d0 c' a' σ O st s regs t gul hh
  have conv : ∀ j : Jmp, j.args = [] → j.there < g0.bo →
      (∀ c', Agree c' g0 g1 → ∃ R : Map (Option Noun), goJ lib O c' gul st regs t nex.th = goJ lib O c' gul st R t j) →
      ∃ R' : Map (Option Noun), (∀ r, K r → SkaModel.read r R' = SkaModel.read r regs) ∧
        ∀ c', Agree c' g0 g1 → goJ lib O c' gul st regs t nex.th = goJ lib O c' gul st R' t j :=
    fun j hj hjl H => by
      obtain ⟨R', fr, e⟩ := leaf_exit hw hj hjl c (fun bz => H _ (agree_regionProg hjl))
      exact ⟨R', fun r hr => by simp only [SkaModel.read, fr r (hK r hr)], e⟩
  cases goal with
  | done => exact S0 c ag
  | pick z o =>
    obtain ⟨⟨hz, hzl⟩, ho, hol⟩ := hj
    generalize pureEval nm s = v at S0 ⊢
    rcases v with _ | ⟨(_ | _ | k) | ⟨x, y⟩⟩
    · exact S0 c ag
    · obtain ⟨R', k, e⟩ := conv z hz hzl fun c' a' => by obtain ⟨R, _, e⟩ := S0 c' a'; exact ⟨R, e⟩
      exact ⟨R', k, e c ag⟩
    · obtain ⟨R', k, e⟩ := conv o ho hol fun c' a' => by obtain ⟨R, _, e⟩ := S0 c' a'; exact ⟨R, e⟩
      exact ⟨R', k, e c ag⟩
    · exact S0 c ag
    · exact S0 c ag
  | next laz th =>
    obtain ⟨hth, htl⟩ := hj
    generalize pureEval nm s = v at S0 ⊢
    rcases v with _ | p
    · exact S0 c ag
    · refine ⟨fun f => ?_, fun f => (S0 c ag).2 f⟩
      obtain ⟨R', k, e⟩ := conv th hth htl fun c' a' => by obtain ⟨R, _, _, e⟩ := (S0 c' a').1 f; exact ⟨R, e⟩
      refine ⟨R', holdsN_pointwise laz.ned f.1 fun x _ => ?_, k, e c ag⟩
      obtain ⟨Rx, hRx, _, ex⟩ := (S0 (regionProg c g1.blocks g0.bo g1.bo th.there ⟨[], [], Termin.don x⟩)
        (agree_regionProg htl)).1 f
      refine ⟨Rx, hRx, fun v hv => ?_⟩
      have e2 := (e _ (agree_regionProg htl)).symm.trans ex
      rw [goJ_regionProg_z htl hth, goJ_regionProg_z htl hth, execBlob_don', execBlob_don', hv,
        Option.bind_some] at e2
      cases h : SkaModel.read x R' with
      | none => rw [h] at e2; cases e2
      | some w =>
        rw [h, Option.bind_some] at e2
        simp only [Option.some.injEq, Prod.mk.injEq, Tone.zero.injEq] at e2
        rw [e2.1]

/-- **The leaf conversion with the footprint of the run**: from a clear
state, with `Grow` and the footprint `Foot`, the code keeps every register
allocated before the run or from its end on, and every register of its
result's sure need, outside the goal's need. -/
theorem leaf_keep {nm : Nomm} {goal : CGoal S} {g0 g1 : Gen Map} {nex : Next S}
    (R : RunOK lib nm goal g0 g1 nex) (G : Grow g0 g1) (F : Foot g0 g1 goal nex) (hc : Clear g0)
    (d0 : g0.drop = false) (hj : LeafJ g0.bo goal)
    (c : Straight Map) (ag : Agree c g0 g1) (st : σ) (s : Noun) (regs : Map (Option Noun)) (t : Trace)
    (hh : HoldsS nex.laz regs s) :
    GoalSem lib O c gul st (fun r => (r < g0.re ∨ g1.re ≤ r ∨ NMem nex.laz.ned r) ∧ ¬ GMem goal r)
      regs t nex.th goal (pureEval nm s) :=
  leaf_sem R d0 (fun k b hk _ hb => (clear_new hc G F.wr k b hk hb).1) hj
    (fun r hr hq => by
      obtain ⟨h1, h2, h3⟩ := hq
      rcases hr.1 with e | e | e
      · rcases h2 with h2 | h2
        · omega
        · exact hr.2 h2
      · omega
      · exact h3 e) c ag st s regs t hh

end Leaf


end Comp
end SkaModel
end Formalization
