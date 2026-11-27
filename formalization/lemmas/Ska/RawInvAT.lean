import lemmas.Ska.RawInvStX

/-!
# Raw `+comp` output: `ArityOK` and `TwoNA` of the run, the first fragment

README Gaps 14, track D.  `RunAT` of `RawInvStX.lean` asks `ArityOK` and
`TwoNA` of the raw blocks of the top run.  The induction carries one
relation between the state before and after a run, `GA`: the blocks below
the old `bo` keep their parameters and ends (both ways), a block at a new
label (in `[g.bo, g'.bo)`) passes as many arguments as its targets have
parameters (`BAT`, in the final map) and jumps below `g'.bo`, and no block
lies at or above `g'.bo` that was not there before.  `GA` composes
(`GA.trans`: a new block of the first part keeps its targets in the second,
since they lie below the first part's end), a step that makes no label
(`Quiet` of `CompDown.lean`) is a `GA` (`ga_quiet`), and an `+emit` is one
when the block meets `BAT` in the state it is put in (`ga_emit`).  From the
empty state, `GA` gives `ArityOK` and `TwoNA` (`at_of_ga`).

What the emitted blocks pass: nothing, to a block with no parameter
(`Fresh` of `CompDown.lean`: the goal's jumps, the result of a sub-run by
`DownR.fresh`, a block just emitted) or, for `+forl`, `[r0]` and `[r1]` to
`barg`, whose parameter is `[r]` (`ga_forl`).

* **`run_at`**: `ATIH` for every nomm: a run of `run` (the model of the
  first fragment) from a state whose goal jumps are `Fresh` is a `GA`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

section Base
variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- **A block meets the arity of its targets in `bl`**, and a two-way end
passes no arguments. -/
def BAT (bl : Map Blob) (b : Blob) : Prop :=
  (∀ j ∈ finJumps b.fin, ∀ b2, HoonMap.get bl j.there = some b2 → j.args.length = b2.par.length) ∧
  (Compiler.twoWay b.fin = true → ∀ j ∈ finJumps b.fin, j.args = [])

/-- **`g'` grew from `g`, with the arity of the new blocks.** -/
structure GA (g g' : Comp.Gen Map) : Prop where
  bo : g.bo ≤ g'.bo
  drop : g'.drop = g.drop
  keep : ∀ k b, k < g.bo → HoonMap.get g.blocks k = some b →
    ∃ b', HoonMap.get g'.blocks k = some b' ∧ b'.par = b.par ∧ b'.fin = b.fin
  old : ∀ k b', k < g.bo → HoonMap.get g'.blocks k = some b' →
    ∃ b, HoonMap.get g.blocks k = some b ∧ b'.par = b.par ∧ b'.fin = b.fin
  new : ∀ k b', g.bo ≤ k → k < g'.bo → HoonMap.get g'.blocks k = some b' →
    BAT g'.blocks b' ∧ ∀ j ∈ finJumps b'.fin, j.there < g'.bo
  out : ∀ k b', g'.bo ≤ k → HoonMap.get g'.blocks k = some b' → ∃ b, HoonMap.get g.blocks k = some b

theorem GA.refl (g : Comp.Gen Map) : GA g g where
  bo := Nat.le_refl _
  drop := rfl
  keep := fun _ b _ hb => ⟨b, hb, rfl, rfl⟩
  old := fun _ b _ hb => ⟨b, hb, rfl, rfl⟩
  new := fun _ _ hl hu _ => absurd hu (Nat.not_lt.mpr hl)
  out := fun _ b _ hb => ⟨b, hb⟩

theorem GA.trans {g0 g1 g2 : Comp.Gen Map} (a : GA g0 g1) (b : GA g1 g2) : GA g0 g2 where
  bo := Nat.le_trans a.bo b.bo
  drop := b.drop.trans a.drop
  keep := fun k x hk hx => by
    obtain ⟨x1, h1, p1, f1⟩ := a.keep k x hk hx
    obtain ⟨x2, h2, p2, f2⟩ := b.keep k x1 (Nat.lt_of_lt_of_le hk a.bo) h1
    exact ⟨x2, h2, p2.trans p1, f2.trans f1⟩
  old := fun k x hk hx => by
    obtain ⟨x1, h1, p1, f1⟩ := b.old k x (Nat.lt_of_lt_of_le hk a.bo) hx
    obtain ⟨x0, h0, p0, f0⟩ := a.old k x1 hk h1
    exact ⟨x0, h0, p1.trans p0, f1.trans f0⟩
  new := fun k x hl hu hx => by
    by_cases e : k < g1.bo
    · obtain ⟨x1, h1, p1, f1⟩ := b.old k x e hx
      obtain ⟨⟨B1, B2⟩, J⟩ := a.new k x1 hl e h1
      refine ⟨⟨fun j hj b2 hb2 => ?_, fun ht j hj => ?_⟩, fun j hj => ?_⟩
      · rw [f1] at hj
        obtain ⟨y1, hy1, py1, -⟩ := b.old _ b2 (J j hj) hb2
        rw [py1]; exact B1 j hj y1 hy1
      · rw [f1] at ht hj; exact B2 ht j hj
      · rw [f1] at hj; exact Nat.lt_of_lt_of_le (J j hj) b.bo
    · exact b.new k x (by omega) hu hx
  out := fun k x hk hx => by
    obtain ⟨x1, h1⟩ := b.out k x hk hx
    exact a.out k x1 (Nat.le_trans b.bo hk) h1

/-- **A step that makes no label is a `GA`.** -/
theorem ga_quiet {g g' : Comp.Gen Map} (q : Quiet g g') : GA g g' where
  bo := q.1.bo
  drop := q.1.drop
  keep := q.1.keep
  old := fun k b' hk hb => by
    rcases q.1.new k b' hb with o | ⟨l, -, -⟩
    · exact o
    · omega
  new := fun k b' hl hu _ => by have := q.2; omega
  out := fun k b' hk hb => by
    rcases q.1.new k b' hb with ⟨b, hb', -, -⟩ | ⟨-, u, -⟩
    · exact ⟨b, hb'⟩
    · omega

theorem em_get {g : Comp.Gen Map} {b : Blob} (hd : g.drop = false) (k : Nat) :
    HoonMap.get (g.emitted b).blocks k = if k = g.bo then some b else HoonMap.get g.blocks k := by
  simp only [Gen.emitted, hd, Bool.false_eq_true, if_false, HoonMap.get_put]

/-- **An `+emit` is a `GA`** when the block meets the arity of its targets,
all below the new label. -/
theorem ga_emit {g : Comp.Gen Map} {b : Blob} (hd : g.drop = false) (hB : BAT g.blocks b)
    (hj : ∀ j ∈ finJumps b.fin, j.there < g.bo) : GA g (g.emitted b) where
  bo := Nat.le_succ _
  drop := rfl
  keep := fun k x hk hx => ⟨x, by rw [em_get hd, if_neg (Nat.ne_of_lt hk)]; exact hx, rfl, rfl⟩
  old := fun k x hk hx => by
    rw [em_get hd, if_neg (Nat.ne_of_lt hk)] at hx; exact ⟨x, hx, rfl, rfl⟩
  new := fun k x hl hu hx => by
    have e : k = g.bo := by simp only [emitted_bo] at hu; omega
    rw [em_get hd, if_pos e] at hx
    cases hx
    refine ⟨⟨fun j hjm b2 hb2 => ?_, hB.2⟩, fun j hjm => Nat.lt_succ_of_lt (hj j hjm)⟩
    rw [em_get hd, if_neg (Nat.ne_of_lt (hj j hjm))] at hb2
    exact hB.1 j hjm b2 hb2
  out := fun k x hk hx => by
    simp only [emitted_bo] at hk
    rw [em_get hd, if_neg (by omega)] at hx; exact ⟨x, hx⟩

theorem bat_fresh {g : Comp.Gen Map} {b : Blob} (h : ∀ j ∈ finJumps b.fin, Fresh g j) : BAT g.blocks b := by
  refine ⟨fun j hj b2 hb2 => ?_, fun _ j hj => ?_⟩
  · obtain ⟨b3, h3, p3, a3⟩ := h j hj
    rw [h3] at hb2; cases hb2; simp [a3, p3]
  · obtain ⟨b3, h3, p3, a3⟩ := h j hj
    exact a3

theorem bat_nil {bl : Map Blob} {b : Blob} (h : finJumps b.fin = []) : BAT bl b :=
  ⟨fun j hj => (by rw [h] at hj; cases hj), fun _ j hj => (by rw [h] at hj; cases hj)⟩

/-- An `+emit` of a block whose jumps are `Fresh` and below the label. -/
theorem ga_emitF {g : Comp.Gen Map} {b : Blob} (hd : g.drop = false)
    (hf : ∀ j ∈ finJumps b.fin, Fresh g j ∧ j.there < g.bo) : GA g (g.emitted b) :=
  ga_emit hd (bat_fresh fun j hj => (hf j hj).1) fun j hj => (hf j hj).2

theorem ga_emitN {g : Comp.Gen Map} {b : Blob} (hd : g.drop = false) (h : finJumps b.fin = []) :
    GA g (g.emitted b) :=
  ga_emit hd (bat_nil h) fun j hj => by rw [h] at hj; cases hj

theorem fresh_ga {g g' : Comp.Gen Map} {j : Jmp} (h : Fresh g j) (hl : j.there < g.bo) (a : GA g g') : Fresh g' j := by
  obtain ⟨b, hb, hp, ha⟩ := h
  obtain ⟨b', hb', hp', _⟩ := a.keep _ b hl hb
  exact ⟨b', hb', hp'.trans hp, ha⟩

theorem fresh_jmp0 {g : Comp.Gen Map} {j : Jmp} (h : Fresh g j) : Fresh g (jmp0 j.there) := by
  obtain ⟨b, hb, hp, _⟩ := h
  exact ⟨b, hb, hp, rfl⟩

/-- The goal's jumps are `Fresh`. -/
def GFresh (g : Comp.Gen Map) : CGoal S → Prop
  | CGoal.next _ th => Fresh g th
  | CGoal.pick z o => Fresh g z ∧ Fresh g o
  | CGoal.done => True

theorem fresh_one {g : Comp.Gen Map} {j : Jmp} (h : Fresh g j) (hl : j.there < g.bo) :
    ∀ j' ∈ finJumps (Termin.hop j), Fresh g j' ∧ j'.there < g.bo := by
  intro j' hj'; simp only [finJumps, List.mem_cons, List.not_mem_nil, or_false] at hj'; subst hj'; exact ⟨h, hl⟩

theorem fresh_two {g : Comp.Gen Map} {fin : Termin} {z o : Jmp} (hf : finJumps fin = [z, o]) (hz : Fresh g z)
    (ho : Fresh g o) (hzl : z.there < g.bo) (hol : o.there < g.bo) :
    ∀ j' ∈ finJumps fin, Fresh g j' ∧ j'.there < g.bo := by
  intro j' hj'; rw [hf] at hj'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
  rcases hj' with rfl | rfl
  · exact ⟨hz, hzl⟩
  · exact ⟨ho, hol⟩

/-- **`ArityOK` and `TwoNA` from the empty state.** -/
theorem at_of_ga {g0 g1 : Comp.Gen Map} (a : GA g0 g1) (h0 : ∀ k, HoonMap.get g0.blocks k = Option.none) :
    Compiler.ArityOK g1.blocks ∧ Compiler.TwoNA g1.blocks := by
  have N : ∀ o b, HoonMap.get g1.blocks o = some b → BAT g1.blocks b := by
    intro o b hb
    by_cases e1 : o < g0.bo
    · obtain ⟨b0, h0', -⟩ := a.old o b e1 hb; rw [h0] at h0'; cases h0'
    by_cases e2 : g1.bo ≤ o
    · obtain ⟨b0, h0'⟩ := a.out o b e2 hb; rw [h0] at h0'; cases h0'
    exact (a.new o b (by omega) (by omega) hb).1
  refine ⟨fun o b j b2 hb hj hb2 => (N o b hb).1 j (by rw [← getJmps_eq]; exact hj) b2 hb2,
    fun o b j hb ht hj => (N o b hb).2 ht j (by rw [← getJmps_eq]; exact hj)⟩

end Base

/-! ## The helpers of `run` -/

section Helpers
variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

theorem ga_bomb {miss : Option Nat} {g g' : Comp.Gen Map} {nex : Next S} (h : bomb miss g = some (nex, g'))
    (hd : g.drop = false) : GA g g' := by
  rw [bomb_eq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ga_emitN hd rfl

theorem ga_simpleNext {goal : CGoal S} {g g' : Comp.Gen Map} {nex : Next S}
    (h : simpleNext goal g = some (nex, g')) (hj : GJ g.bo goal) (hf : GFresh g goal) (hd : g.drop = false) :
    GA g g' := by
  cases goal with
  | next laz th =>
    simp only [simpleNext, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact GA.refl g
  | done =>
    simp only [simpleNext, bind_apply, re_apply, emit_apply, Option.bind_some, pure_apply,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (ga_quiet (quiet_re g)).trans (ga_emitN hd rfl)
  | pick z o =>
    simp only [simpleNext, bind_apply, re_apply, emit_apply, Option.bind_some, pure_apply,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (ga_quiet (quiet_re g)).trans (ga_emitF hd (fresh_two rfl hf.1 hf.2 hj.1.2 hj.2.2))

/-- An `+emit` of a hop to a `Fresh` jump, then a step that makes no label. -/
theorem ga_hopQ {j : Jmp} {g g' : Comp.Gen Map} (hd : g.drop = false) (hf : Fresh g j) (hh : j.there < g.bo)
    (q : Quiet (g.emitted ⟨[], [], Termin.hop j⟩) g') : GA g g' :=
  (ga_emitF hd (fresh_one hf hh)).trans (ga_quiet q)

theorem ga_copy {first : Next S} {second : Sure S} {g g' : Comp.Gen Map} {nex : Next S}
    (h : copy first second g = some (nex, g')) (hf : Fresh g first.th) (hh : first.th.there < g.bo)
    (hd : g.drop = false) : GA g g' := by
  simp only [copy] at h
  obtain ⟨o, g0, h0, h⟩ := bind_some h
  rw [emit_apply] at h0
  simp only [Option.some.injEq, Prod.mk.injEq] at h0
  obtain ⟨rfl, rfl⟩ := h0
  obtain ⟨laz, g1, h1', h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [copyLazy] at h1'
  obtain ⟨⟨n1, o1⟩, g2, h2, h1'⟩ := bind_some h1'
  obtain ⟨_, g3, h3, h1'⟩ := bind_some h1'
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1'
  obtain ⟨_, rfl⟩ := h1'
  exact ga_hopQ hd hf hh ((quiet_copyNeed _ _ _ _ _ _ h2).trans (quiet_addOps h3))

theorem ga_split {nex : Next S} {g g' : Comp.Gen Map} {x : Sure S × Sure S × Nat}
    (h : Comp.split nex g = some (x, g')) (hf : Fresh g nex.th) (hh : nex.th.there < g.bo)
    (hd : g.drop = false) : GA g g' := by
  simp only [Comp.split] at h
  obtain ⟨o, g0, h0, h⟩ := bind_some h
  rw [emit_apply] at h0
  simp only [Option.some.injEq, Prod.mk.injEq] at h0
  obtain ⟨rfl, rfl⟩ := h0
  obtain ⟨⟨sh, st⟩, g1, h2, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [splitSure] at h2
  obtain ⟨⟨lh, lt⟩, _, h2⟩ := Option.bind_eq_some_iff.mp h2
  obtain ⟨⟨⟨nh, nt⟩, g2⟩, h3, h4⟩ := Option.map_eq_some_iff.mp h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨_, rfl⟩ := h4
  exact ga_hopQ hd hf hh (quiet_splitNeed h3)

theorem ga_into {nex : Next S} {axe : Nat} {g g' : Comp.Gen Map} {x : Sure S × Sure S × Nat}
    (h : into nex axe g = some (x, g')) (hf : Fresh g nex.th) (hh : nex.th.there < g.bo)
    (hd : g.drop = false) : GA g g' := by
  simp only [into] at h
  obtain ⟨o, g0, h0, h⟩ := bind_some h
  rw [emit_apply] at h0
  simp only [Option.some.injEq, Prod.mk.injEq] at h0
  obtain ⟨rfl, rfl⟩ := h0
  obtain ⟨⟨sd, sr⟩, g1, h2, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [intoSure] at h2
  obtain ⟨⟨ld, lr⟩, _, h2⟩ := Option.bind_eq_some_iff.mp h2
  obtain ⟨⟨⟨nd, nr⟩, g2⟩, h3, h4⟩ := Option.map_eq_some_iff.mp h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨_, rfl⟩ := h4
  refine ga_hopQ hd hf hh ?_
  simp only [intoNeed] at h3
  by_cases a0 : axe = 0
  · simp [a0] at h3
  rw [if_neg a0] at h3
  by_cases a1 : axe = 1
  · rw [if_pos a1] at h3
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
    rw [← h3.2]; exact Quiet.refl _
  rw [if_neg a1] at h3
  exact quiet_intoLoop _ _ _ _ _ _ _ h3

theorem ga_mede {th : Jmp} {som : Noun} {laz : Sure S} {g g' : Comp.Gen Map} {o : Nat}
    (h : mede th som laz g = some (o, g')) (hf : Fresh g th) (hh : th.there < g.bo) (hd : g.drop = false) :
    GA g g' := by
  simp only [mede] at h
  obtain ⟨o', g0, h0, h⟩ := bind_some h
  rw [emit_apply] at h0
  simp only [Option.some.injEq, Prod.mk.injEq] at h0
  obtain ⟨rfl, rfl⟩ := h0
  obtain ⟨g1, g1', h1', h⟩ := bind_some h
  rw [get_apply] at h1'
  simp only [Option.some.injEq, Prod.mk.injEq] at h1'
  obtain ⟨rfl, rfl⟩ := h1'
  simp only [emitted_drop, hd, Bool.false_eq_true, if_false] at h
  obtain ⟨ned, g2, h2, h⟩ := bind_some h
  obtain ⟨_, g3, h3, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ga_hopQ hd hf hh ((quiet_sure h2).trans (quiet_medeLoop _ _ _ _ _ h3))

theorem forl_tail {g2 g3 g4 g5 : Comp.Gen Map} {r o r0 r1 : Nat} (hd2 : g2.drop = false)
    (hf : Fresh g2 (jmp0 o)) (hh : o < g2.bo)
    (e3 : g3 = g2.emitted ⟨[r], [], Termin.hop (jmp0 o)⟩)
    (e4 : g4 = g3.emitted ⟨[], [Pole.imm (A 0) r0], Termin.hop ⟨[some r0], g2.bo⟩⟩)
    (e5 : g5 = g4.emitted ⟨[], [Pole.imm (A 1) r1], Termin.hop ⟨[some r1], g2.bo⟩⟩) :
    GA g2 g5 ∧ Fresh g5 (jmp0 g3.bo) ∧ Fresh g5 (jmp0 g4.bo) ∧ g3.bo < g5.bo ∧ g4.bo < g5.bo := by
  have hd3 : g3.drop = false := by rw [e3]; exact hd2
  have hd4 : g4.drop = false := by rw [e4]; exact hd3
  have b3 : g3.bo = g2.bo + 1 := by rw [e3]; rfl
  have b4 : g4.bo = g3.bo + 1 := by rw [e4]; rfl
  have b5 : g5.bo = g4.bo + 1 := by rw [e5]; rfl
  have A1 : GA g2 g3 := by rw [e3]; exact ga_emitF hd2 (fresh_one (j := jmp0 o) hf hh)
  have barg : HoonMap.get g3.blocks g2.bo = some ⟨[r], [], Termin.hop (jmp0 o)⟩ := by
    rw [e3]; exact emitted_get g2 _ hd2
  have barg4 : HoonMap.get g4.blocks g2.bo = some ⟨[r], [], Termin.hop (jmp0 o)⟩ := by
    rw [e4, em_get hd3, if_neg (by omega)]; exact barg
  have bat : ∀ (bl : Map Blob) (x : Nat) (a : Noun), HoonMap.get bl g2.bo = some ⟨[r], [], Termin.hop (jmp0 o)⟩ →
      BAT bl ⟨[], [Pole.imm a x], Termin.hop ⟨[some x], g2.bo⟩⟩ := fun bl x a hb => by
    refine ⟨fun j hj b2 hb2 => ?_, fun ht => by simp [Compiler.twoWay] at ht⟩
    simp only [finJumps, List.mem_cons, List.not_mem_nil, or_false] at hj
    subst hj; rw [hb] at hb2; cases hb2; rfl
  have lt : ∀ (k x : Nat) (a : Noun), g2.bo < k →
      ∀ j ∈ finJumps (Termin.hop ⟨[some x], g2.bo⟩), j.there < k := fun k x a hk j hj => by
    simp only [finJumps, List.mem_cons, List.not_mem_nil, or_false] at hj
    subst hj; exact hk
  have A2 : GA g3 g4 := by rw [e4]; exact ga_emit hd3 (bat _ _ _ barg) (lt _ _ (A 0) (by omega))
  have A3 : GA g4 g5 := by rw [e5]; exact ga_emit hd4 (bat _ _ _ barg4) (lt _ _ (A 1) (by omega))
  refine ⟨A1.trans (A2.trans A3), ?_, by rw [e5]; exact fresh_emitted hd4 rfl rfl, by omega, by omega⟩
  exact fresh_ga (by rw [e4]; exact fresh_emitted hd3 rfl rfl) (by simp only [jmp0]; omega) A3

/-- **`+forl`**: `barg` hops to the `Fresh` block `o`, `if0` and `if1` pass
one argument to `barg`, whose parameter is one register. -/
theorem ga_forl {r o : Nat} {g g' : Comp.Gen Map} {x : Nat × Nat} (h : forl r o g = some (x, g'))
    (hf : Fresh g (jmp0 o)) (hh : o < g.bo) (hd : g.drop = false) :
    GA g g' ∧ Fresh g' (jmp0 x.1) ∧ Fresh g' (jmp0 x.2) ∧ x.1 < g'.bo ∧ x.2 < g'.bo := by
  simp only [forl, bind_apply, re_apply, emit_apply, Option.bind_some, pure_apply, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have q := (quiet_re g).trans (quiet_re { g with re := g.re + 1 })
  have T := forl_tail (g2 := { { g with re := g.re + 1 } with re := g.re + 1 + 1 }) (r := r) (o := o)
    (r0 := g.re) (r1 := g.re + 1) hd hf hh rfl rfl rfl
  exact ⟨(ga_quiet q).trans T.1, T.2.1, T.2.2.1, T.2.2.2.1, T.2.2.2.2⟩

theorem done_tail {g2 g3 g4 : Comp.Gen Map} {b1 b2 : Blob} (hd2 : g2.drop = false) (h1 : finJumps b1.fin = [])
    (h2 : finJumps b2.fin = []) (hp1 : b1.par = []) (hp2 : b2.par = []) (e3 : g3 = g2.emitted b1)
    (e4 : g4 = g3.emitted b2) :
    GA g2 g4 ∧ Fresh g4 (jmp0 g2.bo) ∧ Fresh g4 (jmp0 g3.bo) ∧ g2.bo < g4.bo ∧ g3.bo < g4.bo := by
  have hd3 : g3.drop = false := by rw [e3]; exact hd2
  have b3 : g3.bo = g2.bo + 1 := by rw [e3]; rfl
  have b4 : g4.bo = g3.bo + 1 := by rw [e4]; rfl
  have A1 : GA g2 g3 := by rw [e3]; exact ga_emitN hd2 h1
  have A2 : GA g3 g4 := by rw [e4]; exact ga_emitN hd3 h2
  refine ⟨A1.trans A2, ?_, by rw [e4]; exact fresh_emitted hd3 hp2 rfl, by omega, by omega⟩
  exact fresh_ga (by rw [e3]; exact fresh_emitted hd2 hp1 rfl) (by simp only [jmp0]; omega) A2

theorem ga_doneBlocks {g g' : Comp.Gen Map} {x : Nat × Nat} (h : (doneBlocks : CM Map (Nat × Nat)) g = some (x, g'))
    (hd : g.drop = false) :
    GA g g' ∧ Fresh g' (jmp0 x.1) ∧ Fresh g' (jmp0 x.2) ∧ x.1 < g'.bo ∧ x.2 < g'.bo := by
  simp only [doneBlocks, bind_apply, re_apply, emit_apply, Option.bind_some, pure_apply, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have q := (quiet_re g).trans (quiet_re { g with re := g.re + 1 })
  have T := done_tail (g2 := { { g with re := g.re + 1 } with re := g.re + 1 + 1 })
    (b1 := ⟨[], [Pole.imm (A 0) g.re], Termin.don g.re⟩) (b2 := ⟨[], [Pole.imm (A 1) (g.re + 1)], Termin.don (g.re + 1)⟩)
    hd rfl rfl rfl rfl rfl rfl
  exact ⟨(ga_quiet q).trans T.1, T.2.1, T.2.2.1, T.2.2.2.1, T.2.2.2.2⟩

/-- **`+collapse-lazy-atom`**: a `GA`, and the block it returns is `Fresh`. -/
theorem ga_collapse {nex : Next S} {g g' : Comp.Gen Map} {a : Option (Nat × Nat)}
    (h : collapseLazyAtom nex g = some (a, g')) (hf : Fresh g nex.th) (hh : nex.th.there < g.bo)
    (hd : g.drop = false) : GA g g' ∧ ∀ r o, a = some (r, o) → Fresh g' (jmp0 o) ∧ o < g'.bo := by
  unfold collapseLazyAtom at h
  by_cases ea : nex.th.args ≠ []
  · rw [if_pos ea] at h; cases h
  rw [if_neg ea] at h
  by_cases en : noneEquivalent nex.laz = true
  · rw [if_pos en] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨GA.refl g, fun r o e => by cases e⟩
  rw [if_neg en] at h
  obtain ⟨ned, g1, h1', h⟩ := bind_some h
  have q1 := quiet_sure h1'
  have hd1 : g1.drop = false := q1.1.drop.trans hd
  have f1 : Fresh g1 (jmp0 nex.th.there) := fresh_ga (fresh_jmp0 hf) hh (ga_quiet q1)
  have hh1 : nex.th.there < g1.bo := by rw [q1.2]; exact hh
  obtain ⟨⟨r, there⟩, g2, h2, h⟩ := bind_some h
  have T : GA g1 g2 ∧ Fresh g2 (jmp0 there) ∧ there < g2.bo := by
    cases ned with
    | this x =>
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      exact ⟨GA.refl _, f1, hh1⟩
    | none =>
      simp only [bind_apply, re_apply, Option.bind_some, pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      exact ⟨ga_quiet (quiet_re _), f1, hh1⟩
    | pair p q =>
      simp only [bind_apply, re_apply, emit_apply, Option.bind_some, pure_apply, Option.some.injEq,
        Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      exact ⟨(ga_quiet (quiet_re _)).trans (ga_emitN hd1 rfl), fresh_emitted hd1 rfl rfl,
        by simp [emitted_bo]⟩
    | both x p q =>
      simp only [bind_apply, emit_apply, Option.bind_some, pure_apply, Option.some.injEq,
        Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      exact ⟨ga_emitN hd1 rfl, fresh_emitted hd1 rfl rfl, by simp [emitted_bo]⟩
  obtain ⟨q3, rfl⟩ := collapse_tail_quiet h
  exact ⟨(ga_quiet q1).trans (T.1.trans (ga_quiet q3)), fun r' o' e => by
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨fresh_ga T.2.1 T.2.2 (ga_quiet q3), by rw [q3.2]; exact T.2.2⟩⟩

end Helpers


/-! ## The cases of `run` -/

section Run
variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- **What `run_at` proves of one nomm.** -/
def ATIH (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] (p : Nomm) : Prop :=
  ∀ (goal : CGoal S) (g0 g1 : Comp.Gen Map) (nex : Next S), GJ g0.bo goal → 1 ≤ g0.bo → g0.drop = false →
    GFresh g0 goal → run p goal g0 = some (nex, g1) → GA g0 g1

/-- The result jump of a run is `Fresh` when the goal's jumps are. -/
theorem entry_fresh {goal : CGoal S} {g0 g1 : Comp.Gen Map} {j : Jmp} (he : Comp.Entry g1 goal j) (hf : GFresh g0 goal)
    (hj : GJ g0.bo goal) (a : GA g0 g1) : Fresh g1 j := by
  rcases he with f | e
  · exact f
  cases goal with
  | next laz th => simp only [GoalJ] at e; subst e; exact fresh_ga hf hj.2 a
  | pick z o =>
    simp only [GoalJ] at e
    rcases e with rfl | rfl
    · exact fresh_ga hf.1 hj.1.2 a
    · exact fresh_ga hf.2 hj.2.2 a
  | done => exact e.elim

/-- **A sub-run for a goal `%next` with a `Fresh` jump**: a `GA`, and its
result is `Fresh` (by `run_down` of track C). -/
theorem sub_at {p : Nomm} (ih : ATIH S Map p) {laz : Sure S} {j : Jmp} {g g1 : Comp.Gen Map} {nex : Next S}
    (hl : 1 ≤ j.there) (hh : j.there < g.bo) (hd : g.drop = false) (hf : Fresh g j)
    (h : run p (CGoal.next laz j) g = some (nex, g1)) :
    GA g g1 ∧ Fresh g1 nex.th ∧ 1 ≤ nex.th.there ∧ nex.th.there < g1.bo := by
  have D := run_down p (CGoal.next laz j) g g1 nex ⟨hl, hh⟩ (by omega) hd h
  exact ⟨ih (CGoal.next laz j) g g1 nex ⟨hl, hh⟩ (by omega) hd hf h, D.fresh hf hh, D.lo, D.hi⟩

/-- A run for the goal of a block just emitted. -/
theorem ga_emit_run {p : Nomm} (ih : ATIH S Map p) {g0 g g1 : Comp.Gen Map} {b : Blob}
    {laz : Sure S} {nex : Next S} (h0 : GA g0 g) (hd : g0.drop = false) (h1 : 1 ≤ g0.bo)
    (hb : ∀ j ∈ finJumps b.fin, Fresh g j ∧ j.there < g.bo) (hp : b.par = [])
    (h : run p (CGoal.next laz (jmp0 g.bo)) (g.emitted b) = some (nex, g1)) : GA g0 g1 := by
  have hd' : g.drop = false := h0.drop.trans hd
  have hb1 : 1 ≤ g.bo := Nat.le_trans h1 h0.bo
  exact h0.trans ((ga_emitF hd' hb).trans (ih (CGoal.next laz (jmp0 g.bo)) (g.emitted b) g1 nex
    ⟨hb1, by simp [jmp0, emitted_bo]⟩
    (by simp only [emitted_bo]; omega) ((emitted_drop g b).trans hd') (fresh_emitted hd' hp rfl) h))

theorem nil_jumps {fin : Termin} (h : finJumps fin = []) {g : Comp.Gen Map} :
    ∀ j ∈ finJumps fin, Fresh g j ∧ j.there < g.bo := fun j hj => by rw [h] at hj; cases hj

theorem run_n0_at {ax : Nat} : ATIH S Map (Nomm.n0 ax) := by
  intro goal g0 g1 nex hj h1 hd hf h
  simp only [run] at h
  by_cases e0 : ax = 0
  · rw [if_pos e0] at h; exact ga_bomb h hd
  rw [if_neg e0] at h
  obtain ⟨n1, g', h2, h⟩ := bind_some h
  have D := ga_simpleNext h2 hj hf hd
  by_cases e1 : ax = 1
  · rw [if_pos e1] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact D
  rw [if_neg e1] at h
  cases hf' : «from» ax n1.laz with
  | none => simp only [hf'] at h; cases h
  | some laz =>
    simp only [hf', pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact D

theorem run_n1_at {k : Noun} : ATIH S Map (Nomm.n1 k) := by
  intro goal g0 g1 nex hj h1 hd hf h
  cases goal with
  | done =>
    simp only [run, bind_apply, re_apply, emit_apply, Option.bind_some, pure_apply, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (ga_quiet (quiet_re _)).trans (ga_emitN hd rfl)
  | pick z o =>
    simp only [run] at h
    by_cases e0 : k = A 0
    · rw [if_pos e0] at h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact GA.refl _
    rw [if_neg e0] at h
    by_cases e1 : k = A 1
    · rw [if_pos e1] at h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact GA.refl _
    rw [if_neg e1] at h
    exact ga_bomb h hd
  | next laz th =>
    simp only [run] at h
    obtain ⟨o, g', h2, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ga_mede h2 hf hj.2 hd

theorem run_n7_at {p q : Nomm} (ihp : ATIH S Map p) (ihq : ATIH S Map q) : ATIH S Map (Nomm.n7 p q) := by
  intro goal g0 g1 nex hj h1 hd hf h
  simp only [run] at h
  obtain ⟨nexq, g', h2, h⟩ := bind_some h
  have Dq := run_down q goal g0 g' nexq hj h1 hd h2
  have Aq := ihq goal g0 g' nexq hj h1 hd hf h2
  have Fq : Fresh g' nexq.th := entry_fresh Dq.entry hf hj Aq
  exact Aq.trans (ihp (CGoal.next _ _) g' g1 nex ⟨Dq.lo, Dq.hi⟩ (Nat.le_trans h1 Dq.grow.bo)
    (Dq.grow.drop.trans hd) Fq h)

theorem run_n4_at {p : Nomm} (ih : ATIH S Map p) : ATIH S Map (Nomm.n4 p) := by
  intro goal g0 g1 nex hj h1 hd hf h
  cases goal with
  | done =>
    simp only [run, bind_apply, re_apply, emit_apply, Option.bind_some] at h
    exact ga_emit_run ih ((ga_quiet (quiet_re _)).trans (ga_quiet (quiet_re _))) hd h1 (nil_jumps rfl) rfl h
  | pick z o =>
    simp only [run, bind_apply, re_apply, emit_apply, Option.bind_some] at h
    exact ga_emit_run ih ((ga_quiet (quiet_re _)).trans (ga_quiet (quiet_re _))) hd h1
      (fresh_two rfl hf.1 hf.2 hj.1.2 hj.2.2) rfl h
  | next laz th =>
    simp only [run] at h
    obtain ⟨a, g2, h2, h⟩ := bind_some h
    have C := ga_collapse h2 hf hj.2 hd
    obtain ⟨⟨pro, th'⟩, g3, h3, h⟩ := bind_some h
    have T : GA g2 g3 ∧ Fresh g3 (jmp0 th') ∧ th' < g3.bo := by
      cases a with
      | some x =>
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
        obtain ⟨rfl, rfl⟩ := h3
        exact ⟨GA.refl _, C.2 _ _ rfl⟩
      | none =>
        simp only [bind_apply, re_apply, Option.bind_some] at h3
        by_cases ea : th.args = []
        · rw [if_pos ea] at h3
          simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h3
          exact ⟨ga_quiet (quiet_re _), fresh_ga (g' := g2) (fresh_jmp0 hf) hj.2 C.1, Nat.lt_of_lt_of_le hj.2 C.1.bo⟩
        · rw [if_neg ea] at h3; cases h3
    simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
    exact ga_emit_run ih (C.1.trans (T.1.trans (ga_quiet (quiet_re _)))) hd h1
      (fresh_one (g := { g3 with re := g3.re + 1 }) T.2.1 T.2.2) rfl h

theorem run_n3_at {p : Nomm} (ih : ATIH S Map p) : ATIH S Map (Nomm.n3 p) := by
  intro goal g0 g1 nex hj h1 hd hf h
  cases goal with
  | done =>
    simp only [run] at h
    obtain ⟨⟨o0, o1⟩, g2, h2, h⟩ := bind_some h
    have B := ga_doneBlocks h2 hd
    simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
    exact ga_emit_run ih (B.1.trans (ga_quiet (quiet_re _))) hd h1
      (fresh_two (g := { g2 with re := g2.re + 1 }) rfl B.2.1 B.2.2.1 B.2.2.2.1 B.2.2.2.2) rfl h
  | pick z o =>
    simp only [run, bind_apply, re_apply, emit_apply, Option.bind_some] at h
    exact ga_emit_run ih (ga_quiet (quiet_re _)) hd h1 (fresh_two rfl hf.1 hf.2 hj.1.2 hj.2.2) rfl h
  | next laz th =>
    simp only [run] at h
    by_cases en : noneEquivalent laz = true
    · rw [if_pos en] at h; exact ih _ g0 g1 nex hj h1 hd hf h
    rw [if_neg en] at h
    obtain ⟨a, g2, h2, h⟩ := bind_some h
    have C := ga_collapse h2 hf hj.2 hd
    cases a with
    | none => cases h
    | some x =>
      obtain ⟨r, o⟩ := x
      have Co := C.2 r o rfl
      simp only at h
      obtain ⟨⟨z, o'⟩, g3, h3, h⟩ := bind_some h
      have F := ga_forl h3 Co.1 Co.2 (C.1.drop.trans hd)
      simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
      exact ga_emit_run ih (C.1.trans (F.1.trans (ga_quiet (quiet_re _)))) hd h1
        (fresh_two (g := { g3 with re := g3.re + 1 }) rfl F.2.1 F.2.2.1 F.2.2.2.1 F.2.2.2.2) rfl h

theorem run_n5_at {p q : Nomm} (ihp : ATIH S Map p) (ihq : ATIH S Map q) : ATIH S Map (Nomm.n5 p q) := by
  intro goal g0 g1 nex hj h1 hd hf h
  simp only [run, bind_apply, re_apply, Option.bind_some] at h
  obtain ⟨⟨o, g2⟩, h2, h⟩ := Option.bind_eq_some_iff.mp h
  have O : GA g0 g2 ∧ Fresh g2 (jmp0 o) ∧ 1 ≤ o ∧ o < g2.bo := by
    have G0 : GA g0 { { g0 with re := g0.re + 1 } with re := g0.re + 1 + 1 } :=
      (ga_quiet (quiet_re _)).trans (ga_quiet (quiet_re _))
    have e : ∀ {j : Jmp}, Fresh g0 j → Fresh ({ { g0 with re := g0.re + 1 } with re := g0.re + 1 + 1 } : Comp.Gen Map) j :=
      fun h => h
    cases goal with
    | pick z o' =>
      simp only [emit_apply, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      exact ⟨G0.trans (ga_emitF hd (fresh_two rfl (e hf.1) (e hf.2) hj.1.2 hj.2.2)), fresh_emitted hd rfl rfl, h1,
        by simp [emitted_bo]⟩
    | done =>
      obtain ⟨⟨o0, o1⟩, g3, h3, h2⟩ := bind_some h2
      have B := ga_doneBlocks h3 hd
      rw [emit_apply] at h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      have hd3 : g3.drop = false := B.1.drop.trans hd
      exact ⟨G0.trans (B.1.trans (ga_emitF hd3 (fresh_two rfl B.2.1 B.2.2.1 B.2.2.2.1 B.2.2.2.2))),
        fresh_emitted hd3 rfl rfl, Nat.le_trans h1 B.1.bo, by simp [emitted_bo]⟩
    | next laz th =>
      obtain ⟨a, g3, h3, h2⟩ := bind_some h2
      have C := ga_collapse h3 (e hf) hj.2 hd
      have hd3 : g3.drop = false := C.1.drop.trans hd
      cases a with
      | none =>
        simp only at h2
        by_cases ea : th.args = []
        · rw [if_pos ea, emit_apply] at h2
          simp only [Option.some.injEq, Prod.mk.injEq] at h2
          obtain ⟨rfl, rfl⟩ := h2
          exact ⟨G0.trans (C.1.trans (ga_emitF hd3 (fresh_one (fresh_ga (e (fresh_jmp0 hf)) hj.2 C.1)
            (Nat.lt_of_lt_of_le hj.2 C.1.bo)))), fresh_emitted hd3 rfl rfl, Nat.le_trans h1 C.1.bo,
            by simp [emitted_bo]⟩
        · rw [if_neg ea] at h2; cases h2
      | some x =>
        obtain ⟨r, o''⟩ := x
        have Co := C.2 r o'' rfl
        simp only at h2
        obtain ⟨⟨z, o'⟩, g4, h4, h2⟩ := bind_some h2
        have F := ga_forl h4 Co.1 Co.2 hd3
        rw [emit_apply] at h2
        simp only [Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        have hd4 : g4.drop = false := F.1.drop.trans hd3
        exact ⟨G0.trans (C.1.trans (F.1.trans (ga_emitF hd4 (fresh_two rfl F.2.1 F.2.2.1 F.2.2.2.1 F.2.2.2.2)))),
          fresh_emitted hd4 rfl rfl, Nat.le_trans h1 (Nat.le_trans C.1.bo F.1.bo), by simp [emitted_bo]⟩
  obtain ⟨⟨nexq, g3⟩, h3, h⟩ := Option.bind_eq_some_iff.mp h
  have Q := sub_at ihq O.2.2.1 O.2.2.2 (O.1.drop.trans hd) O.2.1 h3
  obtain ⟨⟨nexq', g3'⟩, hp, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨rfl, rfl⟩ := past_some hp
  obtain ⟨⟨nexp, g4⟩, h4, h⟩ := Option.bind_eq_some_iff.mp h
  have hd3 : g3.drop = false := Q.1.drop.trans (O.1.drop.trans hd)
  have P := sub_at ihp Q.2.2.1 Q.2.2.2 hd3 Q.2.1 h4
  exact O.1.trans (Q.1.trans (P.1.trans (ga_copy h P.2.1 P.2.2.2 (P.1.drop.trans hd3))))

/-- The two runs and the copy of a cons, for a goal `%next`. -/
theorem cons_next_at {p q : Nomm} (ihp : ATIH S Map p) (ihq : ATIH S Map q)
    {laz : Sure S} {th : Jmp} {g0 g1 : Comp.Gen Map} {nex : Next S}
    (h : (do
      let (hed, tel, o) ← Comp.split ⟨laz, th⟩
      let nexh ← past noCode ⟨hed, jmp0 o⟩ q
      let nex2 ← run q (CGoal.next tel nexh.th)
      let nex2 ← past noCode nex2 p
      let nex1 ← run p (CGoal.next nexh.laz nex2.th)
      copy nex1 nex2.laz : CM Map (Next S)) g0 = some (nex, g1))
    (hl : 1 ≤ th.there) (hh : th.there < g0.bo) (hd : g0.drop = false) (hf : Fresh g0 th) : GA g0 g1 := by
  obtain ⟨⟨hed, tel, o⟩, g2, h2, h⟩ := bind_some h
  obtain ⟨G2, eo, lt2, F2⟩ := split_down h2 hl hh hd
  have A2 := ga_split h2 hf hh hd
  simp only at eo F2 h
  obtain ⟨nexh, g2', hph, h⟩ := bind_some h
  obtain ⟨rfl, rfl⟩ := past_some hph
  obtain ⟨nex2, g3, h3, h⟩ := bind_some h
  have hd2 : g2.drop = false := G2.drop.trans hd
  have Q := sub_at ihq (j := jmp0 o) (by simp only [jmp0]; omega) (by simp only [jmp0]; omega) hd2 F2 h3
  obtain ⟨nex2', g3', hp2, h⟩ := bind_some h
  obtain ⟨rfl, rfl⟩ := past_some hp2
  obtain ⟨nex1, g4, h4, h⟩ := bind_some h
  have hd3 : g3.drop = false := Q.1.drop.trans hd2
  have P := sub_at ihp Q.2.2.1 Q.2.2.2 hd3 Q.2.1 h4
  exact A2.trans (Q.1.trans (P.1.trans (ga_copy h P.2.1 P.2.2.2 (P.1.drop.trans hd3))))

theorem run_cons_at {p q : Nomm} (ihp : ATIH S Map p) (ihq : ATIH S Map q) : ATIH S Map (Nomm.cons p q) := by
  intro goal g0 g1 nex hj h1 hd hf h
  cases goal with
  | done =>
    simp only [run, bind_apply, re_apply, emit_apply, Option.bind_some, pure_apply] at h
    have hd' : ({ g0 with re := g0.re + 1 } : Comp.Gen Map).drop = false := hd
    exact ((ga_quiet (quiet_re _)).trans (ga_emitN hd' rfl)).trans
      (cons_next_at ihp ihq h h1 (by simp [jmp0, emitted_bo]) ((emitted_drop _ _).trans hd')
        (fresh_emitted hd' rfl rfl))
  | next laz th =>
    simp only [run, bind_apply, pure_apply, Option.bind_some] at h
    exact cons_next_at ihp ihq h hj.1 hj.2 hd hf
  | pick z o =>
    simp only [run, bind_apply, pure_apply, emit_apply, Option.bind_some] at h
    obtain ⟨⟨nex2, g3⟩, h3, h⟩ := Option.bind_eq_some_iff.mp h
    have A0 : GA g0 (g0.emitted ⟨[], [], Termin.bom Option.none⟩) := ga_emitN hd rfl
    have Q := sub_at ihq (j := jmp0 g0.bo) h1 (by simp [jmp0, emitted_bo]) ((emitted_drop _ _).trans hd)
      (fresh_emitted hd rfl rfl) h3
    obtain ⟨⟨nex2', g3'⟩, hp, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rfl, rfl⟩ := past_some hp
    obtain ⟨⟨nex1, g4⟩, h4, h⟩ := Option.bind_eq_some_iff.mp h
    have hd3 : g3.drop = false := Q.1.drop.trans ((emitted_drop _ _).trans hd)
    have P := sub_at ihp Q.2.2.1 Q.2.2.2 hd3 Q.2.1 h4
    exact A0.trans (Q.1.trans (P.1.trans (ga_copy h P.2.1 P.2.2.2 (P.1.drop.trans hd3))))

theorem run_n10_at {a : Nat} {v q : Nomm} (ihv : ATIH S Map v) (ihq : ATIH S Map q) :
    ATIH S Map (Nomm.n10 a v q) := by
  intro goal g0 g1 nex hj h1 hd hf h
  simp only [run] at h
  obtain ⟨nex0, g2, h2, h⟩ := bind_some h
  have D0 := simpleNext_down h2 hj hd h1
  have A0 := ga_simpleNext h2 hj hf hd
  have F0 : Fresh g2 nex0.th := entry_fresh D0.entry hf hj A0
  obtain ⟨⟨don, rec, o⟩, g3, h3, h⟩ := bind_some h
  have hd2 : g2.drop = false := A0.drop.trans hd
  obtain ⟨G3, eo, lt3, F3⟩ := into_down h3 D0.lo D0.hi hd2
  have A3 := ga_into h3 F0 D0.hi hd2
  simp only at eo F3 h
  obtain ⟨nexR, g3', hpr, h⟩ := bind_some h
  obtain ⟨rfl, rfl⟩ := past_some hpr
  obtain ⟨nexDon, g4, h4, h⟩ := bind_some h
  have hd3 : g3.drop = false := G3.drop.trans hd2
  have lo := D0.lo
  have hi := D0.hi
  have V := sub_at ihv (j := jmp0 o) (by simp only [jmp0]; omega) (by simp only [jmp0]; omega) hd3 F3 h4
  obtain ⟨nexDon', g4', hpd, h⟩ := bind_some h
  obtain ⟨rfl, rfl⟩ := past_some hpd
  obtain ⟨nexRec, g5, h5, h⟩ := bind_some h
  have hd4 : g4.drop = false := V.1.drop.trans hd3
  have Q := sub_at ihq V.2.2.1 V.2.2.2 hd4 V.2.1 h5
  exact A0.trans (A3.trans (V.1.trans (Q.1.trans (ga_copy h Q.2.1 Q.2.2.2 (Q.1.drop.trans hd4)))))

/-- **Every run of `run` from a state whose goal jumps are `Fresh` is a
`GA`.** -/
theorem run_at : ∀ (nm : Nomm), ATIH S Map nm := by
  intro nm
  induction nm with
  | n0 ax => exact run_n0_at
  | n1 k => exact run_n1_at
  | n7 p q ihp ihq => exact run_n7_at ihp ihq
  | n4 p ih => exact run_n4_at ih
  | n3 p ih => exact run_n3_at ih
  | n5 p q ihp ihq => exact run_n5_at ihp ihq
  | cons p q ihp ihq => exact run_cons_at ihp ihq
  | n2 => intro goal g0 g1 nex _ _ _ _ h; simp only [run] at h; cases h
  | n6 => intro goal g0 g1 nex _ _ _ _ h; simp only [run] at h; cases h
  | n10 a v q ihv ihq => exact run_n10_at ihv ihq
  | n11s => intro goal g0 g1 nex _ _ _ _ h; simp only [run] at h; cases h
  | n11d => intro goal g0 g1 nex _ _ _ _ h; simp only [run] at h; cases h
  | n12 => intro goal g0 g1 nex _ _ _ _ h; simp only [run] at h; cases h
  | mean => intro goal g0 g1 nex _ _ _ _ h; simp only [run] at h; cases h

end Run

end Raw
end SkaModel
end Formalization
