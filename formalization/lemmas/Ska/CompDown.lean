import lemmas.Ska.CompTopOK

/-!
# The blocks of `run` go down

`run_down`: every block that the model of `run` makes jumps only to labels
of at least `1` below its own, and the jump it returns goes to a block with
no parameters or is a jump of its goal.  This holds for every case of the
model, not only on the fragment, because it is a fact about the labels and
not about what the code computes.  `runDown`: so `RunDown` holds of every
nomm, which removes that hypothesis of `finish_bellContract`.

The proof follows one state to the next with `Grow`: labels only grow, the
mode stays, a block that was there keeps its parameters and its terminator
(ops may be put in front of its body), and a block that was not there is at
a fresh label and jumps below it.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-! ## Growing the state -/

/-- The jumps of a terminator go to labels in `[1, k)`. -/
def JumpsBelow (fin : Termin) (k : Nat) : Prop := ∀ j ∈ finJumps fin, 1 ≤ j.there ∧ j.there < k

/-- `g'` grew from `g` as `run` grows its state. -/
structure Grow (g g' : Gen Map) : Prop where
  bo : g.bo ≤ g'.bo
  drop : g'.drop = g.drop
  keep : ∀ k b, k < g.bo → HoonMap.get g.blocks k = some b →
    ∃ b', HoonMap.get g'.blocks k = some b' ∧ b'.par = b.par ∧ b'.fin = b.fin
  new : ∀ k b', HoonMap.get g'.blocks k = some b' →
    (∃ b, HoonMap.get g.blocks k = some b ∧ b'.par = b.par ∧ b'.fin = b.fin) ∨
    (g.bo ≤ k ∧ k < g'.bo ∧ JumpsBelow b'.fin k)

theorem Grow.refl (g : Gen Map) : Grow g g :=
  ⟨Nat.le_refl _, rfl, fun _ b _ hb => ⟨b, hb, rfl, rfl⟩, fun _ b hb => Or.inl ⟨b, hb, rfl, rfl⟩⟩

theorem Grow.trans {g0 g1 g2 : Gen Map} (a : Grow g0 g1) (b : Grow g1 g2) : Grow g0 g2 where
  bo := Nat.le_trans a.bo b.bo
  drop := b.drop.trans a.drop
  keep := fun k x hk hx => by
    obtain ⟨x1, h1, p1, f1⟩ := a.keep k x hk hx
    obtain ⟨x2, h2, p2, f2⟩ := b.keep k x1 (Nat.lt_of_lt_of_le hk a.bo) h1
    exact ⟨x2, h2, p2.trans p1, f2.trans f1⟩
  new := fun k x hx => by
    rcases b.new k x hx with ⟨x1, h1, p1, f1⟩ | ⟨l, u, j⟩
    · rcases a.new k x1 h1 with ⟨x0, h0, p0, f0⟩ | ⟨l', u', j'⟩
      · exact Or.inl ⟨x0, h0, p1.trans p0, f1.trans f0⟩
      · exact Or.inr ⟨l', Nat.lt_of_lt_of_le u' b.bo, by rw [f1]; exact j'⟩
    · exact Or.inr ⟨Nat.le_trans a.bo l, u, j⟩

theorem Grow.down {g g' : Gen Map} (hd : Down g.blocks) (h1 : 1 ≤ g.bo) (hg : Grow g g') : Down g'.blocks := by
  intro k b hb
  rcases hg.new k b hb with ⟨b0, h0, _, f0⟩ | ⟨l, _, j⟩
  · obtain ⟨hk, hj⟩ := hd k b0 h0
    exact ⟨hk, by rw [f0]; exact hj⟩
  · exact ⟨Nat.le_trans h1 l, j⟩

theorem grow_reg (g : Gen Map) (k : Nat) : Grow g { g with re := k } :=
  ⟨Nat.le_refl _, rfl, fun _ b _ hb => ⟨b, hb, rfl, rfl⟩, fun _ b hb => Or.inl ⟨b, hb, rfl, rfl⟩⟩

theorem grow_re (g : Gen Map) : Grow g { g with re := g.re + 1 } := grow_reg g _

theorem grow_emit {g : Gen Map} {b : Blob} (h : JumpsBelow b.fin g.bo) : Grow g (g.emitted b) where
  bo := Nat.le_succ _
  drop := rfl
  keep := fun k b0 hk hb => ⟨b0, by
    simp only [Gen.emitted]; cases g.drop <;> simp [HoonMap.get_put, Nat.ne_of_lt hk, hb], rfl, rfl⟩
  new := fun k b' hb => by
    simp only [Gen.emitted] at hb
    cases hdr : g.drop
    · simp only [hdr, Bool.false_eq_true, if_false, HoonMap.get_put] at hb
      by_cases e : k = g.bo
      · rw [if_pos e] at hb
        cases hb
        subst e
        exact Or.inr ⟨Nat.le_refl _, by simp [Gen.emitted], h⟩
      · rw [if_neg e] at hb
        exact Or.inl ⟨b', hb, rfl, rfl⟩
    · simp only [hdr, if_true] at hb
      exact Or.inl ⟨b', hb, rfl, rfl⟩

theorem grow_addOps {o : Nat} {ops : List Pole} {g g' : Gen Map} {u : Unit}
    (h : addOps o ops g = some (u, g')) : Grow g g' := by
  cases hdr : g.drop
  · obtain ⟨b, hb, rfl⟩ := addOps_spec h hdr
    refine ⟨Nat.le_refl _, rfl, fun k b0 _ hb0 => ?_, fun k b' hb' => ?_⟩
    · by_cases e : k = o
      · subst e; rw [hb] at hb0; cases hb0
        exact ⟨{ b with body := ops ++ b.body }, by simp [HoonMap.get_put], rfl, rfl⟩
      · exact ⟨b0, by simp [HoonMap.get_put, e, hb0], rfl, rfl⟩
    · by_cases e : k = o
      · subst e; simp only [HoonMap.get_put, if_true, Option.some.injEq] at hb'
        subst hb'; exact Or.inl ⟨b, hb, rfl, rfl⟩
      · simp only [HoonMap.get_put, e, if_false] at hb'
        exact Or.inl ⟨b', hb', rfl, rfl⟩
  · unfold addOps at h
    simp only [hdr, if_true, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact Grow.refl g

/-- A computation that only allocates registers and puts ops in front of
blocks: it grows the state and makes no label. -/
def Quiet (g g' : Gen Map) : Prop := Grow g g' ∧ g'.bo = g.bo

theorem Quiet.refl (g : Gen Map) : Quiet g g := ⟨Grow.refl g, rfl⟩

theorem Quiet.trans {g0 g1 g2 : Gen Map} (a : Quiet g0 g1) (b : Quiet g1 g2) : Quiet g0 g2 :=
  ⟨a.1.trans b.1, b.2.trans a.2⟩

theorem quiet_reg (g : Gen Map) (k : Nat) : Quiet g { g with re := k } := ⟨grow_reg g k, rfl⟩

theorem quiet_re (g : Gen Map) : Quiet g { g with re := g.re + 1 } := quiet_reg g _

theorem quiet_addOps {o : Nat} {ops : List Pole} {g g' : Gen Map} {u : Unit}
    (h : addOps o ops g = some (u, g')) : Quiet g g' := by
  refine ⟨grow_addOps h, ?_⟩
  cases hdr : g.drop
  · obtain ⟨b, _, rfl⟩ := addOps_spec h hdr; rfl
  · unfold addOps at h
    simp only [hdr, if_true, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]

theorem quiet_sure {sur : Sure S} {ned : Need} {g g' : Gen Map} (h : sureRequireLook sur g = some (ned, g')) :
    Quiet g g' := by
  obtain ⟨k, rfl⟩ := (sureRequireLook_spec h).gen
  exact quiet_reg g k

theorem quiet_crashNeed {o : Nat} {atom : Sum Nat Nat} {ned : Need} {g g' : Gen Map} {u : Unit}
    (h : crashNeed o atom ned g = some (u, g')) : Quiet g g' := by
  cases atom with
  | inr p => exact quiet_addOps h
  | inl n =>
    simp only [crashNeed, bind_apply, re_apply, Option.bind_some] at h
    exact (quiet_re g).trans (quiet_addOps h)

theorem quiet_medeLoop {o : Nat} : ∀ (som : Noun) (ned : Need) (g g' : Gen Map) (u : Unit),
    medeLoop o som ned g = some (u, g') → Quiet g g'
  | _, Need.none, g, g', u, h => by
    simp only [medeLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact Quiet.refl g
  | _, Need.this r, g, g', u, h => by simp only [medeLoop] at h; exact quiet_addOps h
  | Noun.atom n, Need.pair p q, g, g', u, h => by simp only [medeLoop] at h; exact quiet_crashNeed h
  | Noun.cell a b, Need.pair p q, g, g', u, h => by
    simp only [medeLoop] at h
    obtain ⟨_, g1, h1, h2⟩ := bind_some h
    exact (quiet_medeLoop a p g g1 _ h1).trans (quiet_medeLoop b q g1 g' u h2)
  | Noun.atom n, Need.both r hh t, g, g', u, h => by simp only [medeLoop] at h; exact quiet_crashNeed h
  | Noun.cell a b, Need.both r hh t, g, g', u, h => by
    simp only [medeLoop] at h
    obtain ⟨_, g1, h1, h⟩ := bind_some h
    obtain ⟨_, g2, h2, h3⟩ := bind_some h
    exact (quiet_addOps h1).trans ((quiet_medeLoop a hh g1 g2 _ h2).trans (quiet_medeLoop b t g2 g' u h3))


/-! ## Fresh blocks and the jump `run` returns -/

/-- The jump goes to a block with no parameters. -/
def Fresh (g : Gen Map) (j : Jmp) : Prop := ∃ b, HoonMap.get g.blocks j.there = some b ∧ b.par = []

theorem Fresh.grow {g g' : Gen Map} {j : Jmp} (h : Fresh g j) (hl : j.there < g.bo) (hg : Grow g g') :
    Fresh g' j := by
  obtain ⟨b, hb, hp⟩ := h
  obtain ⟨b', hb', hp', _⟩ := hg.keep _ b hl hb
  exact ⟨b', hb', hp'.trans hp⟩

theorem fresh_emitted {g : Gen Map} {b : Blob} (hd : g.drop = false) (hp : b.par = []) {j : Jmp}
    (hj : j.there = g.bo) : Fresh (g.emitted b) j :=
  ⟨b, by rw [hj]; exact emitted_get g b hd, hp⟩

/-- The jumps of a goal go to labels in `[1, bo)`. -/
def GJ (bo : Nat) : CGoal S → Prop
  | CGoal.next _ th => 1 ≤ th.there ∧ th.there < bo
  | CGoal.pick z o => (1 ≤ z.there ∧ z.there < bo) ∧ (1 ≤ o.there ∧ o.there < bo)
  | CGoal.done => True

theorem GJ.mono {a b : Nat} {goal : CGoal S} (h : GJ a goal) (hab : a ≤ b) : GJ b goal := by
  cases goal with
  | next laz th => exact ⟨h.1, Nat.lt_of_lt_of_le h.2 hab⟩
  | pick z o => exact ⟨⟨h.1.1, Nat.lt_of_lt_of_le h.1.2 hab⟩, ⟨h.2.1, Nat.lt_of_lt_of_le h.2.2 hab⟩⟩
  | done => trivial

/-- A jump of the goal. -/
def GoalJ : CGoal S → Jmp → Prop
  | CGoal.next _ th, j => j = th
  | CGoal.pick z o, j => j = z ∨ j = o
  | CGoal.done, _ => False

/-- The jump that `run` returns goes to a block with no parameters, or is a
jump of its goal. -/
def Entry (g : Gen Map) (goal : CGoal S) (j : Jmp) : Prop := Fresh g j ∨ GoalJ goal j

theorem Entry.grow {g g' : Gen Map} {goal : CGoal S} {j : Jmp} (h : Entry g goal j) (hl : j.there < g.bo)
    (hg : Grow g g') : Entry g' goal j :=
  h.elim (fun f => Or.inl (f.grow hl hg)) Or.inr

/-- **What `run` does to the labels.** -/
structure DownR (goal : CGoal S) (g0 g1 : Gen Map) (nex : Next S) : Prop where
  grow : Grow g0 g1
  lo : 1 ≤ nex.th.there
  hi : nex.th.there < g1.bo
  entry : Entry g1 goal nex.th

/-- A run for a goal whose jump is a fresh block returns a fresh block. -/
theorem DownR.fresh {g g1 : Gen Map} {laz : Sure S} {j : Jmp} {nex : Next S}
    (h : DownR (CGoal.next laz j) g g1 nex) (hf : Fresh g j) (hl : j.there < g.bo) : Fresh g1 nex.th := by
  rcases h.entry with f | e
  · exact f
  · simp only [GoalJ] at e; rw [e]; exact hf.grow hl h.grow

/-- The end of a case whose last step is a run for a goal with a fresh jump. -/
theorem DownR.close {goal' : CGoal S} {g0 g g1 : Gen Map} {laz : Sure S} {j : Jmp} {nex : Next S}
    (h0 : Grow g0 g) (h : DownR (CGoal.next laz j) g g1 nex) (hf : Fresh g j) (hl : j.there < g.bo) :
    DownR goal' g0 g1 nex :=
  ⟨h0.trans h.grow, h.lo, h.hi, Or.inl (h.fresh hf hl)⟩

theorem jumpsBelow_nil {fin : Termin} (h : finJumps fin = []) (k : Nat) : JumpsBelow fin k := by
  intro j hj; rw [h] at hj; cases hj

/-! ## The helpers of `run` -/

theorem bomb_down {miss : Option Nat} {goal : CGoal S} {g g' : Gen Map} {nex : Next S}
    (h : bomb miss g = some (nex, g')) (hd : g.drop = false) (h1 : 1 ≤ g.bo) : DownR goal g g' nex := by
  rw [bomb_eq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨grow_emit (jumpsBelow_nil rfl _), h1, by simp [jmp0, emitted_bo],
    Or.inl (fresh_emitted hd rfl rfl)⟩

theorem simpleNext_down {goal : CGoal S} {g g' : Gen Map} {nex : Next S}
    (h : simpleNext goal g = some (nex, g')) (hj : GJ g.bo goal) (hd : g.drop = false) (h1 : 1 ≤ g.bo) :
    DownR goal g g' nex := by
  cases goal with
  | next laz th =>
    simp only [simpleNext, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Grow.refl g, hj.1, hj.2, Or.inr rfl⟩
  | done =>
    simp only [simpleNext, bind_apply, re_apply, emit_apply, Option.bind_some, pure_apply,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨(grow_re g).trans (grow_emit (jumpsBelow_nil rfl _)), h1, by simp [jmp0, emitted_bo],
      Or.inl (fresh_emitted hd rfl rfl)⟩
  | pick z o =>
    simp only [simpleNext, bind_apply, re_apply, emit_apply, Option.bind_some, pure_apply,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨(grow_re g).trans (grow_emit ?_), h1, by simp [jmp0, emitted_bo],
      Or.inl (fresh_emitted hd rfl rfl)⟩
    intro j hj'
    simp only [finJumps, List.mem_cons, List.not_mem_nil, or_false] at hj'
    rcases hj' with rfl | rfl
    · exact hj.1
    · exact hj.2

theorem quiet_copyNeed : ∀ (a b : Need) (ops : List Pole) (g g' : Gen Map) (x : Need × List Pole),
    copyNeed a b ops g = some (x, g') → Quiet g g' := by
  intro a
  induction a with
  | none =>
    intro b ops g g' x h
    simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact Quiet.refl g
  | this rl =>
    intro b ops g g' x h
    cases b <;> simp only [copyNeed, bind_apply, re_apply, Option.bind_some, pure_apply, Option.some.injEq,
      Prod.mk.injEq] at h <;> rw [← h.2]
    · exact quiet_re g
    · exact Quiet.refl g
    · exact Quiet.refl g
    · exact Quiet.refl g
  | pair pl ql ihp ihq =>
    intro b ops g g' x h
    cases b with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]; exact Quiet.refl g
    | this rr =>
      simp only [copyNeed, bind_apply, re_apply, Option.bind_some, pure_apply, Option.some.injEq,
        Prod.mk.injEq] at h
      rw [← h.2]; exact quiet_re g
    | pair pr qr =>
      simp only [copyNeed] at h
      obtain ⟨⟨a1, o1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨a2, o2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]; exact (ihp _ _ _ _ _ h1).trans (ihq _ _ _ _ _ h2)
    | both xr hr tr =>
      simp only [copyNeed] at h
      obtain ⟨⟨a1, o1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨a2, o2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]; exact (ihp _ _ _ _ _ h1).trans (ihq _ _ _ _ _ h2)
  | both rl hl tl ihh iht =>
    intro b ops g g' x h
    cases b with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]; exact Quiet.refl g
    | this rr =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]; exact Quiet.refl g
    | pair pr qr =>
      simp only [copyNeed] at h
      obtain ⟨xr, g0', h0, h⟩ := bind_some h
      simp only [re_apply, Option.some.injEq, Prod.mk.injEq] at h0
      obtain ⟨rfl, rfl⟩ := h0
      obtain ⟨⟨a1, o1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨a2, o2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]; exact (quiet_re g).trans ((ihh _ _ _ _ _ h1).trans (iht _ _ _ _ _ h2))
    | both xr hr tr =>
      simp only [copyNeed] at h
      obtain ⟨⟨a1, o1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨a2, o2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]; exact (ihh _ _ _ _ _ h1).trans (iht _ _ _ _ _ h2)

theorem copy_down {first : Next S} {second : Sure S} {goal : CGoal S} {g g' : Gen Map} {nex : Next S}
    (h : copy first second g = some (nex, g')) (hl : 1 ≤ first.th.there) (hh : first.th.there < g.bo)
    (hd : g.drop = false) (h1 : 1 ≤ g.bo) : DownR goal g g' nex := by
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
  have ge : Grow g (g.emitted ⟨[], [], Termin.hop first.th⟩) := grow_emit (by
    intro j hj; simp only [finJumps, List.mem_cons, List.not_mem_nil, or_false] at hj; subst hj; exact ⟨hl, hh⟩)
  have q := (quiet_copyNeed _ _ _ _ _ _ h2).trans (quiet_addOps h3)
  refine ⟨ge.trans q.1, h1, by simp [jmp0, q.2, emitted_bo], Or.inl ?_⟩
  exact (fresh_emitted hd rfl rfl).grow (by simp [jmp0, emitted_bo]) q.1

theorem quiet_must {ned : Need} {g g' : Gen Map} {x : Nat × Need} (h : must ned g = some (x, g')) :
    Quiet g g' := by
  cases ned <;> simp only [must, bind_apply, re_apply, Option.bind_some, pure_apply, Option.some.injEq,
    Prod.mk.injEq] at h <;> rw [← h.2]
  · exact quiet_re g
  · exact Quiet.refl g
  · exact Quiet.refl g
  · exact quiet_re g

theorem quiet_splitNeed {ned : Need} {o : Nat} {g g' : Gen Map} {x : Need × Need}
    (h : splitNeed ned o g = some (x, g')) : Quiet g g' := by
  cases ned with
  | pair p q =>
    simp only [splitNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact Quiet.refl g
  | none =>
    simp only [splitNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact Quiet.refl g
  | this r =>
    simp only [splitNeed, bind_apply, re_apply, Option.bind_some] at h
    obtain ⟨⟨_, g1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact (quiet_re _).trans ((quiet_re _).trans (quiet_addOps h1))
  | both r hh t =>
    simp only [splitNeed] at h
    obtain ⟨_, g1, h1, h⟩ := bind_some h
    obtain ⟨_, g2, h2, h⟩ := bind_some h
    obtain ⟨_, g3, h3, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact (quiet_must h1).trans ((quiet_must h2).trans (quiet_addOps h3))

theorem split_down {nex : Next S} {g g' : Gen Map} {x : Sure S × Sure S × Nat}
    (h : Comp.split nex g = some (x, g')) (hl : 1 ≤ nex.th.there) (hh : nex.th.there < g.bo)
    (hd : g.drop = false) :
    Grow g g' ∧ x.2.2 = g.bo ∧ g.bo < g'.bo ∧ Fresh g' (jmp0 x.2.2) := by
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
  have ge : Grow g (g.emitted ⟨[], [], Termin.hop nex.th⟩) := grow_emit (by
    intro j hj; simp only [finJumps, List.mem_cons, List.not_mem_nil, or_false] at hj; subst hj; exact ⟨hl, hh⟩)
  have q := quiet_splitNeed h3
  refine ⟨ge.trans q.1, rfl, by simp [q.2, emitted_bo], ?_⟩
  exact (fresh_emitted hd rfl rfl).grow (by simp [jmp0, emitted_bo]) q.1

theorem mede_down {th : Jmp} {som : Noun} {laz : Sure S} {goal : CGoal S} {g g' : Gen Map} {o : Nat}
    (h : mede th som laz g = some (o, g')) (hl : 1 ≤ th.there) (hh : th.there < g.bo)
    (hd : g.drop = false) (h1 : 1 ≤ g.bo) (x : Sure S) : DownR goal g g' ⟨x, jmp0 o⟩ := by
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
  have ge : Grow g (g.emitted ⟨[], [], Termin.hop th⟩) := grow_emit (by
    intro j hj; simp only [finJumps, List.mem_cons, List.not_mem_nil, or_false] at hj; subst hj; exact ⟨hl, hh⟩)
  have q := (quiet_sure h2).trans (quiet_medeLoop _ _ _ _ _ h3)
  refine ⟨ge.trans q.1, h1, by simp [jmp0, q.2, emitted_bo], Or.inl ?_⟩
  exact (fresh_emitted hd rfl rfl).grow (by simp [jmp0, emitted_bo]) q.1


theorem forl_down {r o : Nat} {g g' : Gen Map} {x : Nat × Nat} (h : forl r o g = some (x, g'))
    (hl : 1 ≤ o) (hh : o < g.bo) (h1 : 1 ≤ g.bo) :
    Grow g g' ∧ (1 ≤ x.1 ∧ x.1 < g'.bo) ∧ (1 ≤ x.2 ∧ x.2 < g'.bo) := by
  simp only [forl, bind_apply, re_apply, emit_apply, Option.bind_some, pure_apply, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨(grow_re _).trans ((grow_re _).trans ((grow_emit ?_).trans ((grow_emit ?_).trans (grow_emit ?_)))),
    ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  rotate_left 3
  all_goals try (simp only [Gen.emitted]; omega)
  all_goals
    intro j hj
    simp only [finJumps, List.mem_cons, List.not_mem_nil, or_false] at hj
    subst hj
    simp only [jmp0, emitted_bo]
    exact ⟨by omega, by omega⟩

theorem doneBlocks_down {g g' : Gen Map} {x : Nat × Nat} (h : (doneBlocks : CM Map (Nat × Nat)) g = some (x, g'))
    (h1 : 1 ≤ g.bo) : Grow g g' ∧ (1 ≤ x.1 ∧ x.1 < g'.bo) ∧ (1 ≤ x.2 ∧ x.2 < g'.bo) := by
  simp only [doneBlocks, bind_apply, re_apply, emit_apply, Option.bind_some, pure_apply, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨(grow_re _).trans ((grow_re _).trans ((grow_emit (jumpsBelow_nil rfl _)).trans
    (grow_emit (jumpsBelow_nil rfl _)))), ⟨h1, by simp only [Gen.emitted]; omega⟩,
    ⟨by simp only [Gen.emitted]; omega, by simp only [Gen.emitted]; omega⟩⟩

/-- The end of `+collapse-lazy-atom`, after the register and the block are
chosen. -/
theorem collapse_tail_quiet {lok : S} {r there : Nat} {g g' : Gen Map} {a : Option (Nat × Nat)}
    (h : (do
      let g ← get
      if g.drop then pure (some (r, there)) else do
        let ned' ← sureRequireLook (⟨Need.this r, lok⟩ : Sure S)
        match ned' with
        | Need.none => pure (some (r, there))
        | Need.this r' =>
            if r = r' then pure (some (r, there)) else do
              addOps there [Pole.mov r r']
              pure (some (r, there))
        | _ => do
            crashNeed there (Sum.inr r) ned'
            pure (some (r, there)) : CM Map (Option (Nat × Nat))) g = some (a, g')) :
    Quiet g g' ∧ a = some (r, there) := by
  obtain ⟨g1, g1', h1, h⟩ := bind_some h
  rw [get_apply] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  by_cases hd : g.drop = true
  · simp only [hd, if_true, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨Quiet.refl _, rfl⟩
  · simp only [hd, Bool.false_eq_true, if_false] at h
    obtain ⟨ned', g2, h2, h⟩ := bind_some h
    have q2 := quiet_sure h2
    cases ned' with
    | none =>
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨q2, rfl⟩
    | this r' =>
      simp only at h
      by_cases e : r = r'
      · simp only [e, if_true, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; exact ⟨q2, by rw [e]⟩
      · simp only [e, if_false] at h
        obtain ⟨_, g3, h3, h⟩ := bind_some h
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; exact ⟨q2.trans (quiet_addOps h3), rfl⟩
    | pair p q =>
      simp only at h
      obtain ⟨_, g3, h3, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨q2.trans (quiet_crashNeed h3), rfl⟩
    | both x p q =>
      simp only at h
      obtain ⟨_, g3, h3, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨q2.trans (quiet_crashNeed h3), rfl⟩

theorem collapse_down {nex : Next S} {g g' : Gen Map} {a : Option (Nat × Nat)}
    (h : collapseLazyAtom nex g = some (a, g')) (hl : 1 ≤ nex.th.there) (hh : nex.th.there < g.bo)
    (h1 : 1 ≤ g.bo) : Grow g g' ∧ ∀ r o, a = some (r, o) → 1 ≤ o ∧ o < g'.bo := by
  unfold collapseLazyAtom at h
  by_cases ea : nex.th.args ≠ []
  · rw [if_pos ea] at h; cases h
  rw [if_neg ea] at h
  by_cases en : noneEquivalent nex.laz = true
  · rw [if_pos en] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Grow.refl g, fun r o e => by cases e⟩
  rw [if_neg en] at h
  obtain ⟨ned, g1, h1', h⟩ := bind_some h
  have q1 := quiet_sure h1'
  obtain ⟨⟨r, there⟩, g2, h2, h⟩ := bind_some h
  have T : Grow g1 g2 ∧ 1 ≤ there ∧ there < g2.bo := by
    cases ned with
    | this x =>
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      exact ⟨Grow.refl _, hl, by rw [q1.2]; exact hh⟩
    | none =>
      simp only [bind_apply, re_apply, Option.bind_some, pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      exact ⟨grow_re _, hl, (by rw [q1.2]; exact hh : nex.th.there < g1.bo)⟩
    | pair p q =>
      simp only [bind_apply, re_apply, emit_apply, Option.bind_some, pure_apply, Option.some.injEq,
        Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      exact ⟨(grow_re _).trans (grow_emit (jumpsBelow_nil rfl _)), (by rw [q1.2]; exact h1 : 1 ≤ g1.bo),
        by simp [emitted_bo]⟩
    | both x p q =>
      simp only [bind_apply, emit_apply, Option.bind_some, pure_apply, Option.some.injEq,
        Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      exact ⟨grow_emit (jumpsBelow_nil rfl _), (by rw [q1.2]; exact h1 : 1 ≤ g1.bo), by simp [emitted_bo]⟩
  obtain ⟨q3, rfl⟩ := collapse_tail_quiet h
  exact ⟨q1.1.trans (T.1.trans q3.1), fun r' o' e => by
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨T.2.1, by rw [q3.2]; exact T.2.2⟩⟩

end Comp
end SkaModel
end Formalization
