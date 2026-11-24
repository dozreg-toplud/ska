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
      (fun q hq => opsWr_fill (fun x hx => Or.inl hx) q (crashFill_sub p ned hq))) h
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

/-! ## `+copy-need-make-ops` -/

/-- The writes of two sub-copies and of the move in front of them avoid the
copy `R` made of their results. -/
theorem wr_two {a b a1 b1 a2 b2 res1 res2 R : Need} {A1 A2 M : List Pole} {lo : Nat} {Top : Nat → Prop}
    (sa : ∀ y, NMem a1 y ∨ NMem a2 y → NMem a y) (sb : ∀ y, NMem b1 y ∨ NMem b2 y → NMem b y)
    (d12 : ∀ y, (NMem a1 y ∨ NMem b1 y) → ¬ (NMem a2 y ∨ NMem b2 y)) (hlo : ∀ y, NMem a y ∨ NMem b y → y < lo)
    (m1 : ∀ y, NMem res1 y → (NMem a1 y ∨ NMem b1 y) ∨ lo ≤ y) (m2 : ∀ y, NMem res2 y → (NMem a2 y ∨ NMem b2 y) ∨ lo ≤ y)
    (w1 : OpsWr (fun y => (NMem a1 y ∨ NMem b1 y) ∧ ¬ NMem res1 y) A1)
    (w2 : OpsWr (fun y => (NMem a2 y ∨ NMem b2 y) ∧ ¬ NMem res2 y) A2)
    (ht : ∀ y, Top y → ¬ (NMem a1 y ∨ NMem b1 y) ∧ ¬ (NMem a2 y ∨ NMem b2 y))
    (hR : ∀ y, NMem R y → Top y ∨ NMem res1 y ∨ NMem res2 y)
    (wM : OpsWr (fun y => (NMem a y ∨ NMem b y) ∧ ¬ Top y ∧ ¬ (NMem a1 y ∨ NMem b1 y) ∧ ¬ (NMem a2 y ∨ NMem b2 y)) M) :
    OpsWr (fun y => (NMem a y ∨ NMem b y) ∧ ¬ NMem R y) (A2 ++ A1 ++ M) := by
  have in1 : ∀ y, (NMem a1 y ∨ NMem b1 y) → NMem a y ∨ NMem b y := fun y h =>
    h.elim (fun e => Or.inl (sa y (Or.inl e))) (fun e => Or.inr (sb y (Or.inl e)))
  have in2 : ∀ y, (NMem a2 y ∨ NMem b2 y) → NMem a y ∨ NMem b y := fun y h =>
    h.elim (fun e => Or.inl (sa y (Or.inr e))) (fun e => Or.inr (sb y (Or.inr e)))
  refine OpsWr.append (OpsWr.append ?_ ?_) ?_
  · refine w2.mono fun y ⟨hy, hn⟩ => ⟨in2 y hy, fun hr => ?_⟩
    rcases hR y hr with e | e | e
    · exact (ht y e).2 hy
    · rcases m1 y e with e' | e'
      · exact d12 y e' hy
      · have := hlo y (in2 y hy); omega
    · exact hn e
  · refine w1.mono fun y ⟨hy, hn⟩ => ⟨in1 y hy, fun hr => ?_⟩
    rcases hR y hr with e | e | e
    · exact (ht y e).1 hy
    · exact hn e
    · rcases m2 y e with e' | e'
      · exact d12 y hy e'
      · have := hlo y (in1 y hy); omega
  · refine wM.mono fun y ⟨hy, h1, h2, h3⟩ => ⟨hy, fun hr => ?_⟩
    rcases hR y hr with e | e | e
    · exact h1 e
    · rcases m1 y e with e' | e'
      · exact h2 e'
      · have := hlo y hy; omega
    · rcases m2 y e with e' | e'
      · exact h3 e'
      · have := hlo y hy; omega

theorem copyNeed_mem {l r : Need} {ops : List Pole} {g g' : Gen Map} {x : Need × List Pole}
    (h : copyNeed l r ops g = some (x, g')) {lo : Nat} (hl : lo ≤ g.re) :
    g.re ≤ g'.re ∧ ∀ y, NMem x.1 y → (NMem l y ∨ NMem r y) ∨ lo ≤ y := by
  obtain ⟨_, _, c⟩ := copyNeed_spec _ _ _ _ _ _ h
  exact ⟨c.le, fun y hy => (c.mem y hy).imp id fun e => Nat.le_trans hl e.1⟩

theorem opsWr_mov {Q : Nat → Prop} {s d : Nat} (h : Q d) : OpsWr Q [Pole.mov s d] :=
  opsWr_one fun x hx => by simp only [poleWr, List.mem_cons, List.mem_nil_iff, or_false] at hx; rw [hx]; exact h

/-- **The ops of `+copy-need-make-ops` write registers of the two needs
copied, and none of the copy**, when the two needs are distinct and apart and
below `re`. -/
theorem wr_copyNeed : ∀ (a b : Need) (ops : List Pole) (g g' : Gen Map) (x : Need × List Pole),
    copyNeed a b ops g = some (x, g') → Distinct (Need.pair a b) → NB g.re a → NB g.re b →
    ∃ A, x.2 = A ++ ops ∧ OpsWr (fun y => (NMem a y ∨ NMem b y) ∧ ¬ NMem x.1 y) A := by
  intro a
  induction a with
  | none =>
    intro b ops g g' x h _ _ _
    simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl, opsWr_nil _⟩
  | this rl =>
    intro b ops g g' x h dab ha hb
    have hl : rl < g.re := ha rl rfl
    have ap : ∀ y, y = rl → ¬ NMem b y := fun y e => dab.2.2 y e
    cases b with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl, opsWr_nil _⟩
    | this rr =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[Pole.mov rl rr], rfl, opsWr_mov ⟨Or.inr rfl, fun e => ap rl rfl (show rl = rr from e.symm ▸ rfl) ⟩⟩
    | both xr hr tr =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[Pole.mov xr rl], rfl, opsWr_mov ⟨Or.inl rfl, ap rl rfl⟩⟩
    | pair p q =>
      simp only [copyNeed, bind_apply, re_apply, Option.bind_some, pure_apply, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨[Pole.mov g.re rl], rfl, opsWr_mov ⟨Or.inl rfl, fun e => ?_⟩⟩
      rcases e with e | e
      · omega
      · exact ap rl rfl e
  | pair pl ql ihp ihq =>
    intro b ops g g' x h dab ha hb
    obtain ⟨⟨dpl, dql, apq⟩, db, ab⟩ := dab
    cases b with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl, opsWr_nil _⟩
    | this rr =>
      simp only [copyNeed, bind_apply, re_apply, Option.bind_some, pure_apply, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hr : rr < g.re := hb rr rfl
      refine ⟨[Pole.mov g.re rr], rfl, opsWr_mov ⟨Or.inr rfl, fun e => ?_⟩⟩
      rcases e with e | e | e
      · omega
      · exact ab rr (Or.inl e) rfl
      · exact ab rr (Or.inr e) rfl
    | pair pr qr =>
      obtain ⟨dpr, dqr, apr⟩ := db
      simp only [copyNeed] at h
      obtain ⟨⟨a1, o1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨a2, o2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨l1, m1⟩ := copyNeed_mem h1 (Nat.le_refl _)
      obtain ⟨_, m2⟩ := copyNeed_mem h2 l1
      obtain ⟨A1, e1, w1⟩ := ihp _ _ _ _ _ h1 ⟨dpl, dpr, fun y hy => ab y (Or.inl hy) ∘ Or.inl⟩
        (fun y hy => ha y (Or.inl hy)) (fun y hy => hb y (Or.inl hy))
      obtain ⟨A2, e2, w2⟩ := ihq _ _ _ _ _ h2 ⟨dql, dqr, fun y hy => ab y (Or.inr hy) ∘ Or.inr⟩
        (fun y hy => Nat.lt_of_lt_of_le (ha y (Or.inr hy)) l1) (fun y hy => Nat.lt_of_lt_of_le (hb y (Or.inr hy)) l1)
      simp only at e1 e2 w1 w2 m1 m2
      refine ⟨A2 ++ A1 ++ [], by rw [e2, e1]; simp, wr_two (Top := fun _ => False) (lo := g.re)
        (fun y hy => hy) (fun y hy => hy) ?_ (fun y hy => hy.elim (ha y) (hb y)) m1 m2 w1 w2
        (fun _ e => e.elim) (fun y hy => Or.inr (nmem_consNeed hy)) (opsWr_nil _)⟩
      rintro y (e | e) (e' | e')
      · exact apq y e e'
      · exact ab y (Or.inl e) (Or.inr e')
      · exact ab y (Or.inr e') (Or.inl e)
      · exact apr y e e'
    | both xr hr tr =>
      obtain ⟨dhr, dtr, aht, nh, nt⟩ := db
      simp only [copyNeed] at h
      obtain ⟨⟨a1, o1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨a2, o2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨l1, m1⟩ := copyNeed_mem h1 (Nat.le_refl _)
      obtain ⟨_, m2⟩ := copyNeed_mem h2 l1
      obtain ⟨A1, e1, w1⟩ := ihp _ _ _ _ _ h1 ⟨dpl, dhr, fun y hy => ab y (Or.inl hy) ∘ Or.inr ∘ Or.inl⟩
        (fun y hy => ha y (Or.inl hy)) (fun y hy => hb y (Or.inr (Or.inl hy)))
      obtain ⟨A2, e2, w2⟩ := ihq _ _ _ _ _ h2 ⟨dql, dtr, fun y hy => ab y (Or.inr hy) ∘ Or.inr ∘ Or.inr⟩
        (fun y hy => Nat.lt_of_lt_of_le (ha y (Or.inr hy)) l1)
        (fun y hy => Nat.lt_of_lt_of_le (hb y (Or.inr (Or.inr hy))) l1)
      simp only at e1 e2 w1 w2 m1 m2
      refine ⟨A2 ++ A1 ++ [], by rw [e2, e1]; simp, wr_two (Top := fun y => y = xr) (lo := g.re)
        (fun y hy => hy) (fun y hy => hy.elim (Or.inr ∘ Or.inl) (Or.inr ∘ Or.inr)) ?_
        (fun y hy => hy.elim (ha y) (hb y)) m1 m2 w1 w2 ?_ (fun y hy => hy) (opsWr_nil _)⟩
      · rintro y (e | e) (e' | e')
        · exact apq y e e'
        · exact ab y (Or.inl e) (Or.inr (Or.inr e'))
        · exact ab y (Or.inr e') (Or.inr (Or.inl e))
        · exact aht y e e'
      · rintro y rfl
        exact ⟨fun e => e.elim (fun e => ab y (Or.inl e) (Or.inl rfl)) nh,
          fun e => e.elim (fun e => ab y (Or.inr e) (Or.inl rfl)) nt⟩
  | both rl hl tl ihh iht =>
    intro b ops g g' x h dab ha hb
    obtain ⟨⟨dhl, dtl, ahl, nhl, ntl⟩, db, ab⟩ := dab
    have hrl : rl < g.re := ha rl (Or.inl rfl)
    cases b with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨[], rfl, opsWr_nil _⟩
    | this rr =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[Pole.mov rl rr], rfl, opsWr_mov ⟨Or.inr rfl, fun e => ab rr e rfl⟩⟩
    | pair pr qr =>
      obtain ⟨dpr, dqr, apr⟩ := db
      simp only [copyNeed] at h
      obtain ⟨xr, g0', h0, h⟩ := bind_some h
      simp only [re_apply, Option.some.injEq, Prod.mk.injEq] at h0
      obtain ⟨rfl, rfl⟩ := h0
      obtain ⟨⟨a1, o1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨a2, o2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have s : ∀ y, y < g.re → y < g.re + 1 := fun _ e => Nat.lt_succ_of_lt e
      obtain ⟨l1, m1⟩ := copyNeed_mem h1 (lo := g.re) (Nat.le_succ _)
      obtain ⟨_, m2⟩ := copyNeed_mem h2 (lo := g.re) (Nat.le_trans (Nat.le_succ _) l1)
      obtain ⟨A1, e1, w1⟩ := ihh _ _ _ _ _ h1 ⟨dhl, dpr, fun y hy => ab y (Or.inr (Or.inl hy)) ∘ Or.inl⟩
        (fun y hy => s _ (ha y (Or.inr (Or.inl hy)))) (fun y hy => s _ (hb y (Or.inl hy)))
      obtain ⟨A2, e2, w2⟩ := iht _ _ _ _ _ h2 ⟨dtl, dqr, fun y hy => ab y (Or.inr (Or.inr hy)) ∘ Or.inr⟩
        (fun y hy => Nat.lt_of_lt_of_le (s _ (ha y (Or.inr (Or.inr hy)))) l1)
        (fun y hy => Nat.lt_of_lt_of_le (s _ (hb y (Or.inr hy))) l1)
      simp only at e1 e2 w1 w2 m1 m2
      refine ⟨A2 ++ A1 ++ [Pole.mov g.re rl], by rw [e2, e1]; simp, wr_two (Top := fun y => y = g.re) (lo := g.re)
        (fun y hy => hy.elim (Or.inr ∘ Or.inl) (Or.inr ∘ Or.inr)) (fun y hy => hy) ?_
        (fun y hy => hy.elim (ha y) (hb y)) m1 m2 w1 w2 ?_ (fun y hy => hy) (opsWr_mov ⟨Or.inl (Or.inl rfl), by omega,
          fun e => e.elim nhl (fun e => ab rl (Or.inl rfl) (Or.inl e)),
          fun e => e.elim ntl (fun e => ab rl (Or.inl rfl) (Or.inr e))⟩)⟩
      · rintro y (e | e) (e' | e')
        · exact ahl y e e'
        · exact ab y (Or.inr (Or.inl e)) (Or.inr e')
        · exact ab y (Or.inr (Or.inr e')) (Or.inl e)
        · exact apr y e e'
      · rintro y rfl
        refine ⟨fun e => ?_, fun e => ?_⟩
        · have := e.elim (fun e => ha _ (Or.inr (Or.inl e))) (fun e => hb _ (Or.inl e)); omega
        · have := e.elim (fun e => ha _ (Or.inr (Or.inr e))) (fun e => hb _ (Or.inr e)); omega
    | both xr hr tr =>
      obtain ⟨dhr, dtr, aht, nh, nt⟩ := db
      simp only [copyNeed] at h
      obtain ⟨⟨a1, o1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨a2, o2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨l1, m1⟩ := copyNeed_mem h1 (Nat.le_refl _)
      obtain ⟨_, m2⟩ := copyNeed_mem h2 l1
      obtain ⟨A1, e1, w1⟩ := ihh _ _ _ _ _ h1 ⟨dhl, dhr, fun y hy => ab y (Or.inr (Or.inl hy)) ∘ Or.inr ∘ Or.inl⟩
        (fun y hy => ha y (Or.inr (Or.inl hy))) (fun y hy => hb y (Or.inr (Or.inl hy)))
      obtain ⟨A2, e2, w2⟩ := iht _ _ _ _ _ h2 ⟨dtl, dtr, fun y hy => ab y (Or.inr (Or.inr hy)) ∘ Or.inr ∘ Or.inr⟩
        (fun y hy => Nat.lt_of_lt_of_le (ha y (Or.inr (Or.inr hy))) l1)
        (fun y hy => Nat.lt_of_lt_of_le (hb y (Or.inr (Or.inr hy))) l1)
      simp only at e1 e2 w1 w2 m1 m2
      refine ⟨A2 ++ A1 ++ [Pole.mov xr rl], by rw [e2, e1]; simp, wr_two (Top := fun y => y = xr) (lo := g.re)
        (fun y hy => hy.elim (Or.inr ∘ Or.inl) (Or.inr ∘ Or.inr)) (fun y hy => hy.elim (Or.inr ∘ Or.inl) (Or.inr ∘ Or.inr)) ?_
        (fun y hy => hy.elim (ha y) (hb y)) m1 m2 w1 w2 ?_ (fun y hy => hy) (opsWr_mov ⟨Or.inl (Or.inl rfl),
          fun e => ab rl (Or.inl rfl) (Or.inl e),
          fun e => e.elim nhl (fun e => ab rl (Or.inl rfl) (Or.inr (Or.inl e))),
          fun e => e.elim ntl (fun e => ab rl (Or.inl rfl) (Or.inr (Or.inr e)))⟩)⟩
      · rintro y (e | e) (e' | e')
        · exact ahl y e e'
        · exact ab y (Or.inr (Or.inl e)) (Or.inr (Or.inr e'))
        · exact ab y (Or.inr (Or.inr e')) (Or.inr (Or.inl e))
        · exact aht y e e'
      · rintro y rfl
        exact ⟨fun e => e.elim (fun e => ab y (Or.inr (Or.inl e)) (Or.inl rfl)) nh,
          fun e => e.elim (fun e => ab y (Or.inr (Or.inr e)) (Or.inl rfl)) nt⟩

/-! ## `+collapse-lazy-atom` -/

/-- **`+collapse-lazy-atom` writes registers of the goal's need and fresh
ones, and returns such a register.** -/
theorem wr_collapseLazyAtom {nex : Next S} {g g' : Gen Map} {a : Option (Nat × Nat)} (hd : g.drop = false)
    (hn : NB g.re nex.laz.ned) (h : collapseLazyAtom nex g = some (a, g')) :
    WroteIn (NewOr nex.laz.ned g g') g g' ∧ ∀ r o, a = some (r, o) → NewOr nex.laz.ned g g' r := by
  have K := (keeps_collapseLazyAtom hd hn h).1
  unfold collapseLazyAtom at h
  by_cases ha : nex.th.args ≠ []
  · rw [if_pos ha] at h; cases h
  rw [if_neg ha] at h
  by_cases hne : noneEquivalent nex.laz = true
  · rw [if_pos hne] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨WroteIn.refl _ _, fun _ _ e => by cases e⟩
  rw [if_neg hne] at h
  obtain ⟨ns, g1, h1, h⟩ := bind_some h
  obtain ⟨k1, n1⟩ := keeps_sureRequireLook hn h1
  have L1 := sureRequireLook_spec h1
  obtain ⟨⟨r, there⟩, g2, h2, h⟩ := bind_some h
  have hr : Keeps g1 g2 ∧ WroteIn (fun _ => False) g1 g2 ∧ (NMem ns r ∨ (g1.re ≤ r ∧ r < g2.re)) := by
    cases ns with
    | this r0 =>
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      exact ⟨Keeps.refl _, WroteIn.refl _ _, Or.inl rfl⟩
    | none =>
      obtain ⟨r0, g3, h3, h2⟩ := bind_some h2
      obtain ⟨e3, q3, k3⟩ := keeps_re h3
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      exact ⟨k3, wroteIn_re h3, Or.inr ⟨by omega, by omega⟩⟩
    | pair p q =>
      obtain ⟨r0, g3, h3, h2⟩ := bind_some h2
      obtain ⟨e3, q3, k3⟩ := keeps_re h3
      obtain ⟨o, g4, h4, h2⟩ := bind_some h2
      obtain ⟨k4, q4⟩ := keeps_emit ((k1.trans k3).dropF hd) (blobIn_fin (f := Termin.bom Option.none) trivial) h4
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      exact ⟨k3.trans k4, (wroteIn_re h3).trans (wroteIn_emit (blobWr_fin _ _) h4), Or.inr ⟨by omega, by omega⟩⟩
    | both r0 p q =>
      obtain ⟨o, g4, h4, h2⟩ := bind_some h2
      obtain ⟨k4, q4⟩ := keeps_emit (k1.dropF hd) (blobIn_fin (f := Termin.bom Option.none) trivial) h4
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      exact ⟨k4, wroteIn_emit (blobWr_fin _ _) h4, Or.inl (Or.inl rfl)⟩
  obtain ⟨k2, w2, r2⟩ := hr
  have d2 := (k1.trans k2).dropF hd
  have rlt : r < g2.re := by
    rcases r2 with e | e
    · exact Nat.lt_of_lt_of_le (n1 r e) k2.le
    · exact e.2
  obtain ⟨g3, g3', h3, h⟩ := bind_some h
  rw [get_apply] at h3
  simp only [Option.some.injEq, Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  rw [d2] at h
  simp only [Bool.false_eq_true, if_false] at h
  obtain ⟨ned', g4, h4, h⟩ := bind_some h
  obtain ⟨k4, n4⟩ := keeps_sureRequireLook (sur := ⟨Need.this r, nex.laz.lok⟩) (nb_this rlt) h4
  have L4 := sureRequireLook_spec h4
  have close : ∀ g5 : Gen Map, g4.re ≤ g5.re → WroteIn (NewOr ned' g4 g5) g4 g5 →
      (pure (some (r, there)) : CM Map (Option (Nat × Nat))) g5 = some (a, g') →
      WroteIn (NewOr nex.laz.ned g g') g g' ∧ ∀ r o, a = some (r, o) → NewOr nex.laz.ned g g' r := by
    intro g5 l5 w5 e5
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at e5
    obtain ⟨rfl, rfl⟩ := e5
    have hR : NewOr nex.laz.ned g g5 r := by
      rcases r2 with e | e
      · rcases L1.mem r e with e' | e'
        · exact Or.inl e'
        · exact Or.inr ⟨e'.1, by have := k2.le; have := k4.le; omega⟩
      · exact Or.inr ⟨Nat.le_trans k1.le e.1, by have := k4.le; omega⟩
    refine ⟨(wr_sureRequireLook _ h1).trans ((w2.mono fun _ e => e.elim).trans ((wr_sureRequireLook _ h4).trans
      (w5.mono fun x hx => ?_))), fun r' o' e => ?_⟩
    · rcases hx with e | e
      · rcases L4.mem x e with e' | e'
        · simp only [NMem] at e'; rw [e']; exact hR
        · exact Or.inr ⟨Nat.le_trans (Nat.le_trans k1.le k2.le) e'.1, by omega⟩
      · exact Or.inr ⟨Nat.le_trans (Nat.le_trans k1.le (Nat.le_trans k2.le k4.le)) e.1, e.2⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at e
      rw [← e.1]; exact hR
  cases ned' with
  | none => exact close g4 (Nat.le_refl _) (WroteIn.refl _ _) h
  | this r' =>
    simp only at h
    by_cases e : r = r'
    · rw [if_pos e] at h; exact close g4 (Nat.le_refl _) (WroteIn.refl _ _) h
    · rw [if_neg e] at h
      obtain ⟨u, g5, h5, h⟩ := bind_some h
      have q5 := (addOps_re h5).1
      exact close g5 (Nat.le_of_eq q5.symm) (wroteIn_addOps (opsWr_mov (s := r) (Or.inl rfl)) h5) h
  | pair p q =>
    simp only at h
    obtain ⟨u, g5, h5, h⟩ := bind_some h
    have k5 := keeps_crashNeed n4 (fun p e => by cases e; exact Nat.lt_of_lt_of_le rlt k4.le) h5
    exact close g5 k5.le (wr_crashNeed h5) h
  | both r0 p q =>
    simp only at h
    obtain ⟨u, g5, h5, h⟩ := bind_some h
    have k5 := keeps_crashNeed n4 (fun p e => by cases e; exact Nat.lt_of_lt_of_le rlt k4.le) h5
    exact close g5 k5.le (wr_crashNeed h5) h

/-! ## The relation of the induction over `run` -/

/-- The need of a goal `%next` is distinct. -/
def GDist : CGoal S → Prop
  | CGoal.next laz _ => Distinct laz.ned
  | _ => True

/-- **Fact (i) of one run, with what the induction carries**: the run writes
only registers below its end that it allocated or that its goal needs, and
none of its result's sure need (`wr`); the result's sure need lies in the
registers allocated in the run and those of the goal's need (`sure`), and is
distinct (`dist`). -/
structure Foot (g g' : Gen Map) (goal : CGoal S) (nex : Next S) : Prop where
  wr : WroteIn (fun x => x < g'.re ∧ (g.re ≤ x ∨ GMem goal x) ∧ ¬ NMem nex.laz.ned x) g g'
  sure : ∀ x, NMem nex.laz.ned x → g.re ≤ x ∨ GMem goal x
  dist : Distinct nex.laz.ned

/-- What the induction proves of one nomm. -/
def FootIH (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (p : Nomm) : Prop :=
  ∀ (goal : CGoal S) (g g' : Gen Map) (nex : Next S), g.drop = false → GoalIn g.re goal → GDist goal →
    run p goal g = some (nex, g') → Foot g g' goal nex

theorem nmem_fromSure {axe : Nat} {sur sur' : Sure S} (h : fromSure axe sur = some sur') {x : Nat}
    (hx : NMem sur'.ned x) : NMem sur.ned x := by
  unfold fromSure at h
  by_cases h0 : axe = 0
  · simp [h0] at h
  simp only [h0, if_false] at h
  by_cases hn : sur.ned = Need.none
  · simp only [hn, if_true] at h
    by_cases h1 : axe = 1
    · simp [h1] at h
    simp only [h1, if_false, Option.some.injEq] at h
    subst h; exact absurd hx (by simp [NMem])
  · simp only [hn, if_false, Option.some.injEq] at h
    subst h; exact nmem_fromPath _ _ _ hx

/-- A result whose sure need is empty. -/
theorem foot_none {g g' : Gen Map} {goal : CGoal S} {nex : Next S} (hn : nex.laz.ned = Need.none)
    (w : WroteIn (fun x => x < g'.re ∧ (g.re ≤ x ∨ GMem goal x)) g g') : Foot g g' goal nex :=
  ⟨w.mono fun x hx => ⟨hx.1, hx.2, by rw [hn]; simp [NMem]⟩, fun x hx => by rw [hn] at hx; exact hx.elim,
    by rw [hn]; trivial⟩

theorem foot_bomb {miss : Option Nat} {g g' : Gen Map} {goal : CGoal S} {nex : Next S}
    (h : (bomb miss : CM Map (Next S)) g = some (nex, g')) : Foot g g' goal nex := by
  have w := wr_bomb (fun x => x < g'.re ∧ (g.re ≤ x ∨ GMem goal x)) h
  simp only [bomb] at h
  obtain ⟨o, g1, h1, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact foot_none rfl w

/-- The block of a unary op that reads the fresh register `arg`, then the run
of the operand for `arg`: the writes before lie below `arg`. -/
theorem foot_tail {p : Nomm} (ihp : FootIH S Map p) {goal : CGoal S} {b : Blob} {arg : Nat} {g0 g g1 g2 : Gen Map}
    {o : Nat} {nex : Next S} (hd : g.drop = false) (hb : BlobIn (· < g.re) b) (ha : arg + 1 = g.re) (h0 : g0.re ≤ arg)
    (W : WroteIn (fun x => x < arg ∧ (g0.re ≤ x ∨ GMem goal x)) g0 g)
    (hbw : BlobWr (fun x => x < arg ∧ (g0.re ≤ x ∨ GMem goal x)) b) (h1 : (emit b : CM Map Nat) g = some (o, g1))
    (h : run p (CGoal.next (lazyReg arg) (jmp0 o)) g1 = some (nex, g2)) : Foot g0 g2 goal nex := by
  obtain ⟨k1, q1⟩ := keeps_emit hd hb h1
  have hg : GoalIn g1.re (CGoal.next (lazyReg arg : Sure S) (jmp0 o)) := ⟨nb_this (by omega), jmpIn_jmp0 _ _⟩
  have F := ihp _ _ _ _ (k1.dropF hd) hg trivial h
  have l2 := (run_keeps p _ _ _ _ (k1.dropF hd) hg h).1.le
  have sx : ∀ x, NMem nex.laz.ned x → g1.re ≤ x ∨ x = arg := fun x hx => by
    rcases F.sure x hx with e | e
    · exact Or.inl e
    · exact Or.inr e
  have a1 : ∀ x, x < arg → ¬ NMem nex.laz.ned x := fun x hx e => by
    rcases sx x e with e' | e' <;> omega
  have a2 : ∀ x, (g1.re ≤ x ∨ GMem (CGoal.next (lazyReg arg : Sure S) (jmp0 o)) x) → g0.re ≤ x ∨ GMem goal x :=
    fun x hx => by
      rcases hx with e | e
      · exact Or.inl (by omega)
      · exact Or.inl (by simp only [GMem, lazyReg, NMem] at e; omega)
  refine ⟨((W.trans (wroteIn_emit hbw h1)).mono fun x hx => ⟨by omega, hx.2, a1 x hx.1⟩).trans
    (F.wr.mono fun x hx => ⟨hx.1, a2 x hx.2.1, hx.2.2⟩), fun x hx => ?_, F.dist⟩
  rcases sx x hx with e | e
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)

/-! ## The cases of `run` -/

theorem foot_n0 (ax : Nat) : FootIH S Map (Nomm.n0 ax) := by
  intro goal g g' nex hd hg hD h
  simp only [run] at h
  by_cases h0 : ax = 0
  · rw [if_pos h0] at h; exact foot_bomb h
  rw [if_neg h0] at h
  obtain ⟨nex0, g1, h1, h⟩ := bind_some h
  have w1 := wr_simpleNext (fun x => x < g'.re ∧ (g.re ≤ x ∨ GMem goal x) ∧ ¬ NMem nex.laz.ned x) h1
  have F0 : (∀ x, NMem nex0.laz.ned x → g.re ≤ x ∨ GMem goal x) ∧ Distinct nex0.laz.ned := by
    cases goal with
    | next laz th =>
      simp only [simpleNext, pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      exact ⟨fun x hx => Or.inr hx, hD⟩
    | done =>
      simp only [simpleNext] at h1
      obtain ⟨r, g2, h2, h1⟩ := bind_some h1
      obtain ⟨e2, _, _⟩ := keeps_re h2
      obtain ⟨o, g3, h3, h1⟩ := bind_some h1
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      exact ⟨fun x hx => Or.inl (by simp only [lazyReg, NMem] at hx; omega), trivial⟩
    | pick z o =>
      simp only [simpleNext] at h1
      obtain ⟨r, g2, h2, h1⟩ := bind_some h1
      obtain ⟨e2, _, _⟩ := keeps_re h2
      obtain ⟨o', g3, h3, h1⟩ := bind_some h1
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      exact ⟨fun x hx => Or.inl (by simp only [lazyReg, NMem] at hx; omega), trivial⟩
  by_cases ha : ax = 1
  · rw [if_pos ha] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨w1, F0.1, F0.2⟩
  rw [if_neg ha] at h
  cases e : «from» ax nex0.laz with
  | none => rw [e] at h; cases h
  | some laz =>
    rw [e] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨w1, fun x hx => F0.1 x (nmem_fromSure e hx), fromSure_dist e F0.2⟩

theorem foot_n1 (k : Noun) : FootIH S Map (Nomm.n1 k) := by
  intro goal g g' nex hd hg hD h
  cases goal with
  | done =>
    simp only [run] at h
    obtain ⟨r, g1, h1, h⟩ := bind_some h
    obtain ⟨e1, q1, k1⟩ := keeps_re h1
    obtain ⟨o, g2, h2, h⟩ := bind_some h
    have q2 : g2.re = g1.re := by
      rw [emit_apply] at h2; simp only [Option.some.injEq, Prod.mk.injEq] at h2; rw [← h2.2]; rfl
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact foot_none rfl ((wroteIn_re h1).trans (wroteIn_emit (blobWr_one (p := Pole.imm k r) _ fun x hx => by
      simp only [poleWr, List.mem_cons, List.mem_nil_iff, or_false] at hx; rw [hx]; exact ⟨by omega, Or.inl (by omega)⟩) h2))
  | pick z o =>
    simp only [run] at h
    by_cases h0 : k = A 0
    · rw [if_pos h0] at h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact foot_none rfl (WroteIn.refl _ _)
    rw [if_neg h0] at h
    by_cases h1 : k = A 1
    · rw [if_pos h1] at h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact foot_none rfl (WroteIn.refl _ _)
    rw [if_neg h1] at h
    exact foot_bomb h
  | next laz th =>
    simp only [run] at h
    obtain ⟨o, g1, h1, h⟩ := bind_some h
    have w := wr_mede hd hg.1 hg.2 h1
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have l1 := (keeps_mede hd hg.1 hg.2 h1).le
    exact foot_none rfl (w.mono fun x hx => by
      rcases hx with e | e
      · exact ⟨Nat.lt_of_lt_of_le (hg.1 x e) l1, Or.inr e⟩
      · exact ⟨e.2, Or.inl e.1⟩)

theorem foot_n7 {p q : Nomm} (ihp : FootIH S Map p) (ihq : FootIH S Map q) : FootIH S Map (Nomm.n7 p q) := by
  intro goal g g' nex hd hg hD h
  simp only [run] at h
  obtain ⟨nexq, g1, h1, h⟩ := bind_some h
  obtain ⟨k1, n1⟩ := run_keeps q goal g g1 nexq hd hg h1
  have Fq := ihq goal g g1 nexq hd hg hD h1
  have l2 := (run_keeps p nexq.goal _ _ _ (k1.dropF hd) n1 h).1.le
  have Fp := ihp nexq.goal _ _ _ (k1.dropF hd) n1 Fq.dist h
  have sp : ∀ x, NMem nex.laz.ned x → g1.re ≤ x ∨ NMem nexq.laz.ned x := Fp.sure
  have a1 : ∀ x, x < g1.re → ¬ NMem nexq.laz.ned x → ¬ NMem nex.laz.ned x := fun x hx hn e => by
    rcases sp x e with e' | e'
    · omega
    · exact hn e'
  have a2 : ∀ x, (g1.re ≤ x ∨ NMem nexq.laz.ned x) → g.re ≤ x ∨ GMem goal x := fun x hx => by
    rcases hx with e | e
    · exact Or.inl (Nat.le_trans k1.le e)
    · exact Fq.sure x e
  exact ⟨(Fq.wr.mono fun x hx => ⟨by omega, hx.2.1, a1 x hx.1 hx.2.2⟩).trans
    (Fp.wr.mono fun x hx => ⟨hx.1, a2 x hx.2.1, hx.2.2⟩), fun x hx => a2 x (sp x hx), Fp.dist⟩

theorem blobWr_inc {Q : Nat → Prop} {s d : Nat} (f : Termin) (h : Q d) : BlobWr Q ⟨[], [Pole.inc s d], f⟩ :=
  blobWr_one f fun x hx => by simp only [poleWr, List.mem_cons, List.mem_nil_iff, or_false] at hx; rw [hx]; exact h

theorem foot_n4 {p : Nomm} (ih : FootIH S Map p) : FootIH S Map (Nomm.n4 p) := by
  intro goal g g' nex hd hg hD h
  cases goal with
  | done =>
    simp only [run] at h
    obtain ⟨pro, g1, h1, h⟩ := bind_some h
    obtain ⟨e1, q1, k1⟩ := keeps_re h1
    obtain ⟨arg, g2, h2, h⟩ := bind_some h
    obtain ⟨e2, q2, k2⟩ := keeps_re h2
    obtain ⟨o, g3, h3, h⟩ := bind_some h
    exact foot_tail ih ((k1.trans k2).dropF hd) (blobIn_one (p := Pole.inc arg pro) (f := Termin.don pro)
      (fun x hx => by simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; omega)
      (show pro < g2.re by omega)) (by omega) (by omega) ((wroteIn_re h1).trans (wroteIn_re h2))
      (blobWr_inc _ ⟨by omega, Or.inl (by omega)⟩) h3 h
  | pick z o =>
    simp only [run] at h
    obtain ⟨pro, g1, h1, h⟩ := bind_some h
    obtain ⟨e1, q1, k1⟩ := keeps_re h1
    obtain ⟨arg, g2, h2, h⟩ := bind_some h
    obtain ⟨e2, q2, k2⟩ := keeps_re h2
    obtain ⟨o', g3, h3, h⟩ := bind_some h
    have kk : ∀ x, x < g.re → x < g2.re := fun x hx => by omega
    exact foot_tail ih ((k1.trans k2).dropF hd) (blobIn_one (p := Pole.inc arg pro) (f := Termin.brn pro z o)
      (fun x hx => by simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; omega)
      ⟨show pro < g2.re by omega, hg.1.mono kk, hg.2.mono kk⟩) (by omega) (by omega)
      ((wroteIn_re h1).trans (wroteIn_re h2)) (blobWr_inc _ ⟨by omega, Or.inl (by omega)⟩) h3 h
  | next laz th =>
    simp only [run] at h
    obtain ⟨a, g1, h1, h⟩ := bind_some h
    obtain ⟨k1, r1⟩ := keeps_collapseLazyAtom (nex := ⟨laz, th⟩) hd hg.1 h1
    obtain ⟨w1, rr1⟩ := wr_collapseLazyAtom (nex := ⟨laz, th⟩) hd hg.1 h1
    obtain ⟨⟨pro, th'⟩, g2, h2, h⟩ := bind_some h
    have hp : Keeps g1 g2 ∧ pro < g2.re ∧ WroteIn (fun _ => False) g1 g2 ∧ (NewOr laz.ned g g1 pro ∨ g1.re ≤ pro) := by
      cases a with
      | some x =>
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        exact ⟨Keeps.refl _, r1 _ _ rfl, WroteIn.refl _ _, Or.inl (rr1 _ _ rfl)⟩
      | none =>
        simp only at h2
        obtain ⟨r, g3, h3, h2⟩ := bind_some h2
        obtain ⟨e3, q3, k3⟩ := keeps_re h3
        by_cases ht : th.args = []
        · rw [if_pos ht] at h2
          simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
          exact ⟨k3, by omega, wroteIn_re h3, Or.inr (by omega)⟩
        · rw [if_neg ht] at h2; cases h2
    obtain ⟨k2, p2, w2, pp⟩ := hp
    obtain ⟨arg, g3, h3, h⟩ := bind_some h
    obtain ⟨e3, q3, k3⟩ := keeps_re h3
    obtain ⟨o, g4, h4, h⟩ := bind_some h
    have l1 := k1.le
    have l2 := k2.le
    have bnd : ∀ x, NewOr laz.ned g g1 x → x < arg ∧ (g.re ≤ x ∨ GMem (CGoal.next laz th) x) := fun x hx => by
      rcases hx with e | e
      · exact ⟨by have := hg.1 x e; omega, Or.inr e⟩
      · exact ⟨by omega, Or.inl e.1⟩
    exact foot_tail ih ((k1.trans (k2.trans k3)).dropF hd)
      (blobIn_one (p := Pole.inc arg pro) (f := Termin.hop (jmp0 th'))
        (fun x hx => by simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; omega)
        (jmpIn_jmp0 _ _)) (by omega) (by omega)
      (((w1.mono bnd).trans (w2.mono fun _ e => e.elim)).trans (wroteIn_re h3))
      (blobWr_inc _ (by
        rcases pp with e | e
        · exact bnd pro e
        · exact ⟨by omega, Or.inl (by omega)⟩)) h4 h

theorem foot_n3 {p : Nomm} (ih : FootIH S Map p) : FootIH S Map (Nomm.n3 p) := by
  intro goal g g' nex hd hg hD h
  cases goal with
  | done =>
    simp only [run] at h
    obtain ⟨⟨o0, o1⟩, g1, h1, h⟩ := bind_some h
    have k1 := keeps_doneBlocks hd h1
    obtain ⟨r, g2, h2, h⟩ := bind_some h
    obtain ⟨e2, q2, k2⟩ := keeps_re h2
    obtain ⟨oc, g3, h3, h⟩ := bind_some h
    have l1 := k1.le
    exact foot_tail ih ((k1.trans k2).dropF hd)
      (blobIn_fin (f := Termin.clq r (jmp0 o0) (jmp0 o1)) ⟨show r < g2.re by omega, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩)
      (by omega) (by omega) (((wr_doneBlocks h1).mono fun x hx => by
        rcases hx with e | e
        · exact e.elim
        · exact ⟨by omega, Or.inl e.1⟩).trans (wroteIn_re h2)) (blobWr_fin _ _) h3 h
  | pick z o =>
    simp only [run] at h
    obtain ⟨r, g2, h2, h⟩ := bind_some h
    obtain ⟨e2, q2, k2⟩ := keeps_re h2
    obtain ⟨oc, g3, h3, h⟩ := bind_some h
    have kk : ∀ x, x < g.re → x < g2.re := fun x hx => by omega
    exact foot_tail ih (k2.dropF hd)
      (blobIn_fin (f := Termin.clq r z o) ⟨show r < g2.re by omega, hg.1.mono kk, hg.2.mono kk⟩) (by omega) (by omega)
      (wroteIn_re h2) (blobWr_fin _ _) h3 h
  | next laz th =>
    simp only [run] at h
    by_cases en : noneEquivalent laz = true
    · rw [if_pos en] at h; exact ih _ _ _ _ hd hg hD h
    rw [if_neg en] at h
    obtain ⟨a, g1, h1, h⟩ := bind_some h
    obtain ⟨k1, r1⟩ := keeps_collapseLazyAtom (nex := ⟨laz, th⟩) hd hg.1 h1
    obtain ⟨w1, rr1⟩ := wr_collapseLazyAtom (nex := ⟨laz, th⟩) hd hg.1 h1
    cases a with
    | none => cases h
    | some x =>
      obtain ⟨r, o⟩ := x
      simp only at h
      obtain ⟨⟨z, o'⟩, g2, h2, h⟩ := bind_some h
      have k2 := keeps_forl (k1.dropF hd) (r1 r o rfl) h2
      obtain ⟨r', g3, h3, h⟩ := bind_some h
      obtain ⟨e3, q3, k3⟩ := keeps_re h3
      obtain ⟨oc, g4, h4, h⟩ := bind_some h
      have l1 := k1.le
      have l2 := k2.le
      have bnd : ∀ x, NewOr laz.ned g g1 x → x < r' ∧ (g.re ≤ x ∨ GMem (CGoal.next laz th) x) := fun x hx => by
        rcases hx with e | e
        · exact ⟨by have := hg.1 x e; omega, Or.inr e⟩
        · exact ⟨by omega, Or.inl e.1⟩
      have bnd2 : ∀ x, NewOr (Need.this r) g1 g2 x → x < r' ∧ (g.re ≤ x ∨ GMem (CGoal.next laz th) x) :=
        fun x hx => by
          rcases hx with e | e
          · simp only [NMem] at e; rw [e]; exact bnd r (rr1 r o rfl)
          · exact ⟨by omega, Or.inl (by omega)⟩
      exact foot_tail ih ((k1.trans (k2.trans k3)).dropF hd)
        (blobIn_fin (f := Termin.clq r' (jmp0 z) (jmp0 o')) ⟨show r' < g3.re by omega, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩)
        (by omega) (by omega) (((w1.mono bnd).trans ((wr_forl h2).mono bnd2)).trans (wroteIn_re h3))
        (blobWr_fin _ _) h4 h

/-- **The induction over `run`**, given the cases that are still open (cons,
`%5`, `%10`) as hypotheses. -/
theorem run_foot_of
    (hc : ∀ p q, FootIH S Map p → FootIH S Map q → FootIH S Map (Nomm.cons p q))
    (h5 : ∀ p q, FootIH S Map p → FootIH S Map q → FootIH S Map (Nomm.n5 p q))
    (h10 : ∀ a v q, FootIH S Map v → FootIH S Map q → FootIH S Map (Nomm.n10 a v q)) :
    ∀ nm : Nomm, FootIH S Map nm := by
  intro nm
  induction nm with
  | n0 ax => exact foot_n0 ax
  | n1 k => exact foot_n1 k
  | n7 p q ihp ihq => exact foot_n7 ihp ihq
  | n4 p ih => exact foot_n4 ih
  | n3 p ih => exact foot_n3 ih
  | n5 p q ihp ihq => exact h5 p q ihp ihq
  | cons p q ihp ihq => exact hc p q ihp ihq
  | n10 a v q ihv ihq => exact h10 a v q ihv ihq
  | n2 => intro goal g0 g1 nex _ _ _ h; simp only [run] at h; cases h
  | n6 => intro goal g0 g1 nex _ _ _ h; simp only [run] at h; cases h
  | n11s => intro goal g0 g1 nex _ _ _ h; simp only [run] at h; cases h
  | n11d => intro goal g0 g1 nex _ _ _ h; simp only [run] at h; cases h
  | n12 => intro goal g0 g1 nex _ _ _ h; simp only [run] at h; cases h
  | mean => intro goal g0 g1 nex _ _ _ h; simp only [run] at h; cases h

end Comp
end SkaModel
end Formalization
