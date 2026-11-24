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

/-! ## The arms, each with its footprint -/

/-- The registers of `ned` and those allocated from `g` to `g'`. -/
def NewOr (ned : Need) (g g' : Gen Map) (x : Nat) : Prop := NMem ned x ∨ (g.re ≤ x ∧ x < g'.re)

theorem newOr_mono {ned : Need} {g g' g2 : Gen Map} (hl : g'.re ≤ g2.re) {x : Nat} (h : NewOr ned g g' x) :
    NewOr ned g g2 x := h.imp id fun e => ⟨e.1, Nat.lt_of_lt_of_le e.2 hl⟩

theorem wr_must {ned n : Need} {r : Nat} {g g' : Gen Map} (Q : Nat → Prop) (h : must ned g = some ((r, n), g')) :
    WroteIn Q g g' := wroteIn_of_gen (must_spec h).1

theorem wr_sureRequireLook {sur : Sure S} {ned : Need} {g g' : Gen Map} (Q : Nat → Prop)
    (h : sureRequireLook sur g = some (ned, g')) : WroteIn Q g g' := by
  obtain ⟨k, e⟩ := (sureRequireLook_spec h).gen
  rw [e]; exact wroteIn_reg Q g k

/-- **`+split-need` writes only registers of the need it splits.** -/
theorem wr_splitNeed {ned : Need} {o : Nat} {g g' : Gen Map} {x : Need × Need}
    (h : splitNeed ned o g = some (x, g')) : WroteIn (NMem ned) g g' := by
  cases ned with
  | pair p q =>
    simp only [splitNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact WroteIn.refl _ _
  | none =>
    simp only [splitNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact WroteIn.refl _ _
  | this r =>
    simp only [splitNeed] at h
    obtain ⟨hh, g1, h1, h⟩ := bind_some h
    obtain ⟨t, g2, h2, h⟩ := bind_some h
    obtain ⟨u, g3, h3, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (wroteIn_re h1).trans ((wroteIn_re h2).trans (wroteIn_addOps (opsWr_one (p := Pole.con hh t r)
      (fun x hx => by simp only [poleWr, List.mem_cons, List.mem_nil_iff, or_false] at hx; rw [hx]; rfl)) h3))
  | both r hd tl =>
    simp only [splitNeed] at h
    obtain ⟨⟨r1, n1⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨⟨r2, n2⟩, g2, h2, h⟩ := bind_some h
    obtain ⟨u, g3, h3, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (wr_must _ h1).trans ((wr_must _ h2).trans (wroteIn_addOps (opsWr_one (p := Pole.con r1 r2 r)
      (fun x hx => by simp only [poleWr, List.mem_cons, List.mem_nil_iff, or_false] at hx; rw [hx]; exact Or.inl rfl)) h3))

/-- **`+crash-need` writes the registers of its need and the register of its
atom.** -/
theorem wr_crashNeed {o : Nat} {atom : Sum Nat Nat} {ned : Need} {g g' : Gen Map} {u : Unit}
    (h : crashNeed o atom ned g = some (u, g')) : WroteIn (NewOr ned g g') g g' := by
  cases atom with
  | inr p =>
    simp only [crashNeed] at h
    exact wroteIn_addOps (opsWr_cons (p := Pole.cel p) (fun x hx => by simp [poleWr] at hx)
      (opsWr_fill fun x hx => Or.inl hx)) h
  | inl n =>
    simp only [crashNeed, bind_apply, re_apply, Option.bind_some] at h
    have e := (addOps_re h).1
    exact (wroteIn_reg _ g _).trans (wroteIn_addOps (opsWr_cons (p := Pole.imm (A n) g.re) (fun x hx => by
      simp only [poleWr, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rw [hx]; exact Or.inr ⟨Nat.le_refl _, by rw [e]; exact Nat.lt_succ_self _⟩)
      (opsWr_cons (p := Pole.cel g.re) (fun x hx => by simp [poleWr] at hx)
        (opsWr_fill fun x hx => Or.inl hx))) h)

/-- **The loop of `+mede` writes the registers of its need and fresh ones.** -/
theorem wr_medeLoop {o : Nat} : ∀ (som : Noun) (ned : Need) (g g' : Gen Map) (u : Unit),
    NB g.re ned → medeLoop o som ned g = some (u, g') → WroteIn (NewOr ned g g') g g'
  | _, Need.none, g, g', u, _, h => by
    simp only [medeLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact WroteIn.refl _ g
  | som, Need.this r, g, g', u, hn, h => by
    simp only [medeLoop] at h
    exact wroteIn_addOps (opsWr_one (p := Pole.imm som r) (fun x hx => by
      simp only [poleWr, List.mem_cons, List.mem_nil_iff, or_false] at hx; exact Or.inl hx)) h
  | Noun.atom n, Need.pair p q, g, g', u, hn, h => by
    simp only [medeLoop] at h
    exact wr_crashNeed h
  | Noun.cell a b, Need.pair p q, g, g', u, hn, h => by
    simp only [medeLoop] at h
    obtain ⟨u1, g1, h1, h2⟩ := bind_some h
    have k1 := keeps_medeLoop a p g g1 u1 (fun y hy => hn y (Or.inl hy)) h1
    have k2 := keeps_medeLoop b q g1 g' u (NB.mono (n := g.re) (fun y hy => hn y (Or.inr hy)) k1.le) h2
    exact ((wr_medeLoop a p g g1 u1 (fun y hy => hn y (Or.inl hy)) h1).mono fun x hx =>
        hx.imp Or.inl fun e => ⟨e.1, Nat.lt_of_lt_of_le e.2 k2.le⟩).trans
      ((wr_medeLoop b q g1 g' u (NB.mono (n := g.re) (fun y hy => hn y (Or.inr hy)) k1.le) h2).mono fun x hx =>
        hx.imp Or.inr fun e => ⟨Nat.le_trans k1.le e.1, e.2⟩)
  | Noun.atom n, Need.both r hh t, g, g', u, hn, h => by
    simp only [medeLoop] at h
    exact wr_crashNeed h
  | Noun.cell a b, Need.both r hh t, g, g', u, hn, h => by
    simp only [medeLoop] at h
    obtain ⟨u0, g0, h0, h⟩ := bind_some h
    obtain ⟨k0, _⟩ := keeps_addOps (regsIn_single (p := Pole.imm (C a b) r) (fun x hx => by
      simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rw [hx]; exact hn r (Or.inl rfl)) _ (RegsIn.nil _)) h0
    obtain ⟨u1, g1, h1, h2⟩ := bind_some h
    have n1 : NB g0.re hh := NB.mono (n := g.re) (fun y hy => hn y (Or.inr (Or.inl hy))) k0.le
    have k1 := keeps_medeLoop a hh g0 g1 u1 n1 h1
    have n2 : NB g1.re t := NB.mono (n := g.re) (fun y hy => hn y (Or.inr (Or.inr hy))) (Nat.le_trans k0.le k1.le)
    have k2 := keeps_medeLoop b t g1 g' u n2 h2
    refine (wroteIn_addOps (Q := NewOr (Need.both r hh t) g g') (opsWr_one (p := Pole.imm (C a b) r) (fun x hx => by
      simp only [poleWr, List.mem_cons, List.mem_nil_iff, or_false] at hx; exact Or.inl (Or.inl hx))) h0).trans
      (((wr_medeLoop a hh g0 g1 u1 n1 h1).mono fun x hx => ?_).trans
        ((wr_medeLoop b t g1 g' u n2 h2).mono fun x hx => ?_))
    · rcases hx with e | e
      · exact Or.inl (Or.inr (Or.inl e))
      · exact Or.inr ⟨Nat.le_trans k0.le e.1, Nat.lt_of_lt_of_le e.2 k2.le⟩
    · rcases hx with e | e
      · exact Or.inl (Or.inr (Or.inr e))
      · exact Or.inr ⟨Nat.le_trans (Nat.le_trans k0.le k1.le) e.1, e.2⟩

/-- **`+mede` writes registers of the goal's need and fresh ones.** -/
theorem wr_mede {th : Jmp} {som : Noun} {laz : Sure S} {g g' : Gen Map} {o : Nat} (hd : g.drop = false)
    (hn : NB g.re laz.ned) (hj : JmpIn (· < g.re) th) (h : mede th som laz g = some (o, g')) :
    WroteIn (NewOr laz.ned g g') g g' := by
  have K := keeps_mede hd hn hj h
  unfold mede at h
  obtain ⟨o1, g1, h1, h⟩ := bind_some h
  obtain ⟨k1, _⟩ := keeps_emit hd (blobIn_fin (f := Termin.hop th) hj) h1
  obtain ⟨g2, g2', h2, h⟩ := bind_some h
  rw [get_apply] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl⟩ := h2
  rw [k1.dropF hd] at h
  simp only [Bool.false_eq_true, if_false] at h
  obtain ⟨ned, g3, h3, h⟩ := bind_some h
  obtain ⟨k3, n3⟩ := keeps_sureRequireLook (hn.mono k1.le) h3
  have L := sureRequireLook_spec h3
  obtain ⟨u4, g4, h4, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨_, rfl⟩ := h
  refine (wroteIn_emit (blobWr_fin _ _) h1).trans ((wr_sureRequireLook _ h3).trans
    ((wr_medeLoop _ _ _ _ _ n3 h4).mono fun x hx => ?_))
  rcases hx with e | e
  · rcases L.mem x e with e' | e'
    · exact Or.inl e'
    · exact Or.inr ⟨Nat.le_trans k1.le e'.1, Nat.lt_of_lt_of_le e'.2 (keeps_medeLoop _ _ _ _ _ n3 h4).le⟩
  · exact Or.inr ⟨Nat.le_trans (Nat.le_trans k1.le k3.le) e.1, e.2⟩

/-- **`+forl` writes its register (the parameter of the join) and two fresh
ones.** -/
theorem wr_forl {r o : Nat} {g g' : Gen Map} {x : Nat × Nat} (h : forl r o g = some (x, g')) :
    WroteIn (NewOr (Need.this r) g g') g g' := by
  unfold forl at h
  obtain ⟨r0, g1, h1, h⟩ := bind_some h
  obtain ⟨e1, q1, _⟩ := keeps_re h1
  obtain ⟨r1, g2, h2, h⟩ := bind_some h
  obtain ⟨e2, q2, _⟩ := keeps_re h2
  obtain ⟨barg, g3, h3, h⟩ := bind_some h
  have q3 : g3.re = g2.re := by
    rw [emit_apply] at h3; simp only [Option.some.injEq, Prod.mk.injEq] at h3; rw [← h3.2]; rfl
  obtain ⟨if0, g4, h4, h⟩ := bind_some h
  have q4 : g4.re = g3.re := by
    rw [emit_apply] at h4; simp only [Option.some.injEq, Prod.mk.injEq] at h4; rw [← h4.2]; rfl
  obtain ⟨if1, g5, h5, h⟩ := bind_some h
  have q5 : g5.re = g4.re := by
    rw [emit_apply] at h5; simp only [Option.some.injEq, Prod.mk.injEq] at h5; rw [← h5.2]; rfl
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨_, rfl⟩ := h
  refine (wroteIn_re h1).trans ((wroteIn_re h2).trans ((wroteIn_emit (b := ⟨[r], [], Termin.hop (jmp0 o)⟩)
    ⟨fun x hx => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx; exact Or.inl hx, opsWr_nil _⟩ h3).trans
    ((wroteIn_emit (blobWr_one (p := Pole.imm (A 0) r0) _ fun x hx => by
      simp only [poleWr, List.mem_cons, List.mem_nil_iff, or_false] at hx; rw [hx]; exact Or.inr ⟨by omega, by omega⟩) h4).trans
    (wroteIn_emit (blobWr_one (p := Pole.imm (A 1) r1) _ fun x hx => by
      simp only [poleWr, List.mem_cons, List.mem_nil_iff, or_false] at hx; rw [hx]; exact Or.inr ⟨by omega, by omega⟩) h5))))

/-- **The blocks of a `%done` loobean write two fresh registers.** -/
theorem wr_doneBlocks {g g' : Gen Map} {x : Nat × Nat} (h : (doneBlocks : CM Map (Nat × Nat)) g = some (x, g')) :
    WroteIn (NewOr Need.none g g') g g' := by
  unfold doneBlocks at h
  obtain ⟨r0, g1, h1, h⟩ := bind_some h
  obtain ⟨e1, q1, _⟩ := keeps_re h1
  obtain ⟨r1, g2, h2, h⟩ := bind_some h
  obtain ⟨e2, q2, _⟩ := keeps_re h2
  obtain ⟨o0, g3, h3, h⟩ := bind_some h
  have q3 : g3.re = g2.re := by
    rw [emit_apply] at h3; simp only [Option.some.injEq, Prod.mk.injEq] at h3; rw [← h3.2]; rfl
  obtain ⟨o1, g4, h4, h⟩ := bind_some h
  have q4 : g4.re = g3.re := by
    rw [emit_apply] at h4; simp only [Option.some.injEq, Prod.mk.injEq] at h4; rw [← h4.2]; rfl
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨_, rfl⟩ := h
  exact (wroteIn_re h1).trans ((wroteIn_re h2).trans ((wroteIn_emit (blobWr_one (p := Pole.imm (A 0) r0) _ fun x hx => by
      simp only [poleWr, List.mem_cons, List.mem_nil_iff, or_false] at hx; rw [hx]; exact Or.inr ⟨by omega, by omega⟩) h3).trans
    (wroteIn_emit (blobWr_one (p := Pole.imm (A 1) r1) _ fun x hx => by
      simp only [poleWr, List.mem_cons, List.mem_nil_iff, or_false] at hx; rw [hx]; exact Or.inr ⟨by omega, by omega⟩) h4)))

/-- **`+simple-next` writes nothing.** -/
theorem wr_simpleNext {goal : CGoal S} {g g' : Gen Map} {nex : Next S} (Q : Nat → Prop)
    (h : simpleNext goal g = some (nex, g')) : WroteIn Q g g' := by
  cases goal with
  | next laz th =>
    simp only [simpleNext, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact WroteIn.refl _ _
  | done =>
    simp only [simpleNext] at h
    obtain ⟨r, g1, h1, h⟩ := bind_some h
    obtain ⟨o, g2, h2, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (wroteIn_re h1).trans (wroteIn_emit (blobWr_fin _ _) h2)
  | pick z o =>
    simp only [simpleNext] at h
    obtain ⟨r, g1, h1, h⟩ := bind_some h
    obtain ⟨o', g2, h2, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (wroteIn_re h1).trans (wroteIn_emit (blobWr_fin _ _) h2)

theorem wr_bomb {miss : Option Nat} {g g' : Gen Map} {nex : Next S} (Q : Nat → Prop)
    (h : (bomb miss : CM Map (Next S)) g = some (nex, g')) : WroteIn Q g g' := by
  simp only [bomb] at h
  obtain ⟨o, g1, h1, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact wroteIn_emit (blobWr_fin _ _) h1

end Comp
end SkaModel
end Formalization
