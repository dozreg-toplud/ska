import lemmas.Ska.CompUnproxyBelow

/-!
# Fact (i5) for `run`

Fact (i5) of README Gaps 12.2 (`BelowIn g0.bo g1`, `CompUnproxyBelow.lean`)
for every run of `run`, the model of `+comp` without forks, by induction on
the nomm as `run_clean` is.  The induction carries a stronger invariant than
(i5): a run keeps `BelowIn lo` for every `lo` (`Keeps`), because every block
it emits and every op it puts in front of a block mentions only registers
below the current `re`, when the registers of its goal are below `re` at the
start (`GoalIn`).  So a sub-run composes with what comes before it with no
condition on which blocks it changes, and (i5) of a run is `Keeps` applied to
`belowIn_start`.

* `NB n ned`: the registers of `ned` are below `n`.
* `Keeps g g'`: every `BelowIn lo` of `g` holds of `g'`, `re` grew, `drop`
  stayed.  The steps: `keeps_re`, `keeps_emit`, `keeps_addOps`.
* The arms: `keeps_must`, `keeps_splitNeed`, `keeps_copyNeed`,
  `keeps_sureRequireLook`, `keeps_medeLoop`, `keeps_crashNeed`,
  `keeps_intoLoop`, ...
* `run_keeps`: every run of `run` from a state that does not drop, for a
  goal whose registers are below `re`, keeps `BelowIn lo` for every `lo`, and
  returns a `next` whose registers are below the new `re`; `run_below`: fact
  (i5) of the run.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Needs and goals below a bound -/

/-- The registers of `ned` are below `n`. -/
def NB (n : Nat) (ned : Need) : Prop := ∀ r, NMem ned r → r < n

theorem NB.mono {n m : Nat} {ned : Need} (h : NB n ned) (hm : n ≤ m) : NB m ned :=
  fun r hr => Nat.lt_of_lt_of_le (h r hr) hm

theorem nb_none (n : Nat) : NB n Need.none := fun _ h => absurd h (by simp [NMem])

theorem nb_this {n r : Nat} (h : r < n) : NB n (Need.this r) := fun _ e => by
  simp only [NMem] at e; rw [e]; exact h

/-- The registers of a goal (its need and the arguments of its jumps) are
below `n`. -/
def GoalIn (n : Nat) : CGoal S → Prop
  | CGoal.next laz th => NB n laz.ned ∧ JmpIn (· < n) th
  | CGoal.pick z o => JmpIn (· < n) z ∧ JmpIn (· < n) o
  | CGoal.done => True

/-- The registers of a `next` are below `n`. -/
def NextIn (n : Nat) (nex : Next S) : Prop := NB n nex.laz.ned ∧ JmpIn (· < n) nex.th

theorem NextIn.mono {n m : Nat} {nex : Next S} (h : NextIn n nex) (hm : n ≤ m) : NextIn m nex :=
  ⟨h.1.mono hm, h.2.mono fun _ hx => Nat.lt_of_lt_of_le hx hm⟩

theorem GoalIn.mono {n m : Nat} {goal : CGoal S} (h : GoalIn n goal) (hm : n ≤ m) : GoalIn m goal := by
  have k : ∀ x, x < n → x < m := fun _ hx => Nat.lt_of_lt_of_le hx hm
  cases goal with
  | next laz th => exact ⟨h.1.mono hm, h.2.mono k⟩
  | pick z o => exact ⟨h.1.mono k, h.2.mono k⟩
  | done => trivial

/-! ## Runs that keep (i5) -/

/-- **`g'` keeps every `BelowIn lo` of `g`**, has at least its registers, and
the same mode. -/
structure Keeps (g g' : Gen Map) : Prop where
  bel : ∀ lo, BelowIn lo g → BelowIn lo g'
  le : g.re ≤ g'.re
  drop : g'.drop = g.drop

theorem Keeps.refl (g : Gen Map) : Keeps g g := ⟨fun _ h => h, Nat.le_refl _, rfl⟩

theorem Keeps.trans {g0 g1 g2 : Gen Map} (a : Keeps g0 g1) (b : Keeps g1 g2) : Keeps g0 g2 :=
  ⟨fun lo h => b.bel lo (a.bel lo h), Nat.le_trans a.le b.le, b.drop.trans a.drop⟩

theorem Keeps.dropF {g g' : Gen Map} (k : Keeps g g') (hd : g.drop = false) : g'.drop = false := k.drop.trans hd

theorem keeps_reg (g : Gen Map) (k : Nat) (hk : g.re ≤ k) : Keeps g { g with re := k } :=
  ⟨fun _ h => belowIn_re h k hk, hk, rfl⟩

theorem keeps_re {g g' : Gen Map} {r : Nat} (h : (re : CM Map Nat) g = some (r, g')) :
    r = g.re ∧ g'.re = g.re + 1 ∧ Keeps g g' := by
  rw [re_apply] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl, keeps_reg g _ (Nat.le_succ _)⟩

theorem keeps_emit {g g' : Gen Map} {b : Blob} {o : Nat} (hd : g.drop = false) (hb : BlobIn (· < g.re) b)
    (h : (emit b : CM Map Nat) g = some (o, g')) : Keeps g g' ∧ g'.re = g.re := by
  have e := h
  rw [emit_apply] at e
  simp only [Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨_, rfl⟩ := e
  exact ⟨⟨fun _ hl => belowIn_emit hl hd hb h, Nat.le_refl _, rfl⟩, rfl⟩

theorem addOps_re {g g' : Gen Map} {o : Nat} {ops : List Pole} {u : Unit} (h : addOps o ops g = some (u, g')) :
    g'.re = g.re ∧ g'.drop = g.drop := by
  unfold addOps at h
  by_cases hd : g.drop = true
  · rw [if_pos hd] at h; cases h; exact ⟨rfl, rfl⟩
  · rw [if_neg hd] at h
    obtain ⟨b, _, e⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at e
    rw [← e.2]; exact ⟨rfl, rfl⟩

theorem keeps_addOps {g g' : Gen Map} {o : Nat} {ops : List Pole} {u : Unit} (hA : RegsIn (· < g.re) ops)
    (h : addOps o ops g = some (u, g')) : Keeps g g' ∧ g'.re = g.re := by
  cases u
  obtain ⟨e1, e2⟩ := addOps_re h
  exact ⟨⟨fun _ hl => belowIn_addOps hl (Or.inr hA) h, Nat.le_of_eq e1.symm, e2⟩, e1⟩

/-- The registers of an op, by cases. -/
theorem regsIn_one {P : Nat → Prop} {p : Pole} (h : ∀ x ∈ poleRegs p, P x) : RegsIn P [p] :=
  RegsIn.cons (p := p) h (RegsIn.nil P)

/-- A block with no parameters and no body whose terminator mentions only
registers that satisfy `P`. -/
theorem blobIn_fin {P : Nat → Prop} {f : Termin} (h : FinIn P f) : BlobIn P ⟨[], [], f⟩ :=
  ⟨fun _ hx => absurd hx (List.not_mem_nil), RegsIn.nil P, h⟩

theorem keeps_of_gen {g g' : Gen Map} (e : g' = { g with re := g'.re }) (le : g.re ≤ g'.re) : Keeps g g' := by
  rw [e]; exact keeps_reg g _ le

theorem regsIn_mov {P : Nat → Prop} {s d : Nat} {ops : List Pole} (hs : P s) (hd : P d) (hA : RegsIn P ops) :
    RegsIn P (Pole.mov s d :: ops) :=
  RegsIn.cons (p := Pole.mov s d) (fun x hx => by
    simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with e | e <;> rw [e] <;> assumption) hA

theorem regsIn_con {P : Nat → Prop} {h t d : Nat} {ops : List Pole} (hh : P h) (ht : P t) (hd : P d)
    (hA : RegsIn P ops) : RegsIn P (Pole.con h t d :: ops) :=
  RegsIn.cons (p := Pole.con h t d) (fun x hx => by
    simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with e | e | e <;> rw [e] <;> assumption) hA

/-! ## The arms that take needs apart and copy them -/

theorem keeps_must {ned n : Need} {r : Nat} {g g' : Gen Map} (hn : NB g.re ned) (h : must ned g = some ((r, n), g')) :
    Keeps g g' ∧ NB g'.re n ∧ r < g'.re := by
  obtain ⟨e, le, m1, m2, _⟩ := must_spec h
  refine ⟨keeps_of_gen e le, fun y hy => ?_, ?_⟩
  · rcases m1 y hy with h1 | h1
    · exact Nat.lt_of_lt_of_le (hn y h1) le
    · exact h1.2
  · rcases m2 with h1 | h1
    · exact Nat.lt_of_lt_of_le (hn r h1) le
    · exact h1.2

theorem keeps_splitNeed {ned : Need} {o : Nat} {g g' : Gen Map} {x : Need × Need} (hn : NB g.re ned)
    (h : splitNeed ned o g = some (x, g')) : Keeps g g' ∧ NB g'.re x.1 ∧ NB g'.re x.2 := by
  cases ned with
  | pair p q =>
    simp only [splitNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Keeps.refl _, fun r hr => hn r (Or.inl hr), fun r hr => hn r (Or.inr hr)⟩
  | none =>
    simp only [splitNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Keeps.refl _, nb_none _, nb_none _⟩
  | this r =>
    simp only [splitNeed] at h
    obtain ⟨hh, g1, h1, h⟩ := bind_some h
    obtain ⟨t, g2, h2, h⟩ := bind_some h
    obtain ⟨u, g3, h3, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨e1, r1, k1⟩ := keeps_re h1
    obtain ⟨e2, r2, k2⟩ := keeps_re h2
    have hr : r < g.re := hn r rfl
    obtain ⟨k3, r3⟩ := keeps_addOps (regsIn_con (by omega) (by omega) (by omega) (RegsIn.nil _)) h3
    exact ⟨k1.trans (k2.trans k3), nb_this (by omega), nb_this (by omega)⟩
  | both r hd tl =>
    simp only [splitNeed] at h
    obtain ⟨⟨r1, n1⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨⟨r2, n2⟩, g2, h2, h⟩ := bind_some h
    obtain ⟨u, g3, h3, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hr : r < g.re := hn r (Or.inl rfl)
    obtain ⟨k1, n1b, r1b⟩ := keeps_must (fun y hy => hn y (Or.inr (Or.inl hy))) h1
    obtain ⟨k2, n2b, r2b⟩ := keeps_must (NB.mono (n := g.re) (fun y hy => hn y (Or.inr (Or.inr hy))) k1.le) h2
    have l1 := k1.le
    have l2 := k2.le
    obtain ⟨k3, r3⟩ := keeps_addOps (regsIn_con (by omega) (by omega) (by omega) (RegsIn.nil _)) h3
    exact ⟨k1.trans (k2.trans k3), (n1b.mono l2).mono (Nat.le_of_eq r3.symm), n2b.mono (Nat.le_of_eq r3.symm)⟩

/-- **The ops of `+copy-need-make-ops` mention registers of the two needs
or fresh ones.** -/
theorem copyNeed_regs : ∀ (a b : Need) (ops : List Pole) (g g' : Gen Map) (x : Need × List Pole),
    copyNeed a b ops g = some (x, g') → NB g.re a → NB g.re b → RegsIn (· < g.re) ops → RegsIn (· < g'.re) x.2 := by
  intro a
  induction a with
  | none =>
    intro b ops g g' x h _ _ hA
    simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact hA
  | this rl =>
    intro b ops g g' x h ha hb hA
    have hl : rl < g.re := ha rl rfl
    cases b with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact hA
    | this rr =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact regsIn_mov hl (hb rr rfl) hA
    | both xr hr tr =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact regsIn_mov (hb xr (Or.inl rfl)) hl hA
    | pair p q =>
      simp only [copyNeed, bind_apply, re_apply, Option.bind_some, pure_apply, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact regsIn_mov (Nat.lt_succ_self _) (Nat.lt_succ_of_lt hl) (hA.mono fun _ e => Nat.lt_succ_of_lt e)
  | pair pl ql ihp ihq =>
    intro b ops g g' x h ha hb hA
    cases b with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact hA
    | this rr =>
      simp only [copyNeed, bind_apply, re_apply, Option.bind_some, pure_apply, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact regsIn_mov (Nat.lt_succ_self _) (Nat.lt_succ_of_lt (hb rr rfl)) (hA.mono fun _ e => Nat.lt_succ_of_lt e)
    | pair pr qr =>
      simp only [copyNeed] at h
      obtain ⟨⟨a1, o1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨a2, o2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨_, _, c1⟩ := copyNeed_spec _ _ _ _ _ _ h1
      have l1 := c1.le
      exact ihq _ _ _ _ (a2, o2) h2 (fun y hy => Nat.lt_of_lt_of_le (ha y (Or.inr hy)) l1)
        (fun y hy => Nat.lt_of_lt_of_le (hb y (Or.inr hy)) l1)
        (ihp _ _ _ _ _ h1 (fun y hy => ha y (Or.inl hy)) (fun y hy => hb y (Or.inl hy)) hA)
    | both xr hr tr =>
      simp only [copyNeed] at h
      obtain ⟨⟨a1, o1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨a2, o2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨_, _, c1⟩ := copyNeed_spec _ _ _ _ _ _ h1
      have l1 := c1.le
      exact ihq _ _ _ _ (a2, o2) h2 (fun y hy => Nat.lt_of_lt_of_le (ha y (Or.inr hy)) l1)
        (fun y hy => Nat.lt_of_lt_of_le (hb y (Or.inr (Or.inr hy))) l1)
        (ihp _ _ _ _ _ h1 (fun y hy => ha y (Or.inl hy)) (fun y hy => hb y (Or.inr (Or.inl hy))) hA)
  | both rl hl tl ihh iht =>
    intro b ops g g' x h ha hb hA
    have hrl : rl < g.re := ha rl (Or.inl rfl)
    cases b with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact hA
    | this rr =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact regsIn_mov hrl (hb rr rfl) hA
    | pair pr qr =>
      simp only [copyNeed] at h
      obtain ⟨xr, g0', h0, h⟩ := bind_some h
      simp only [re_apply, Option.some.injEq, Prod.mk.injEq] at h0
      obtain ⟨rfl, rfl⟩ := h0
      obtain ⟨⟨a1, o1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨a2, o2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨_, _, c1⟩ := copyNeed_spec _ _ _ _ _ _ h1
      have l1 := c1.le
      have s : ∀ y, y < g.re → y < g.re + 1 := fun _ e => Nat.lt_succ_of_lt e
      exact iht _ _ _ _ (a2, o2) h2 (fun y hy => Nat.lt_of_lt_of_le (s _ (ha y (Or.inr (Or.inr hy)))) l1)
        (fun y hy => Nat.lt_of_lt_of_le (s _ (hb y (Or.inr hy))) l1)
        (ihh _ _ _ _ _ h1 (fun y hy => s _ (ha y (Or.inr (Or.inl hy)))) (fun y hy => s _ (hb y (Or.inl hy)))
          (regsIn_mov (Nat.lt_succ_self _) (s _ hrl) (hA.mono s)))
    | both xr hr tr =>
      simp only [copyNeed] at h
      obtain ⟨⟨a1, o1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨a2, o2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨_, _, c1⟩ := copyNeed_spec _ _ _ _ _ _ h1
      have l1 := c1.le
      exact iht _ _ _ _ (a2, o2) h2 (fun y hy => Nat.lt_of_lt_of_le (ha y (Or.inr (Or.inr hy))) l1)
        (fun y hy => Nat.lt_of_lt_of_le (hb y (Or.inr (Or.inr hy))) l1)
        (ihh _ _ _ _ _ h1 (fun y hy => ha y (Or.inr (Or.inl hy))) (fun y hy => hb y (Or.inr (Or.inl hy)))
          (regsIn_mov (hb xr (Or.inl rfl)) hrl hA))

theorem keeps_copyNeed {a b : Need} {g g' : Gen Map} {x : Need × List Pole} (h : copyNeed a b [] g = some (x, g'))
    (ha : NB g.re a) (hb : NB g.re b) : Keeps g g' ∧ NB g'.re x.1 ∧ RegsIn (· < g'.re) x.2 := by
  obtain ⟨_, _, c⟩ := copyNeed_spec _ _ _ _ _ _ h
  refine ⟨keeps_of_gen c.gen c.le, fun y hy => ?_, copyNeed_regs _ _ _ _ _ _ h ha hb (RegsIn.nil _)⟩
  rcases c.mem y hy with e | e
  · rcases e with e | e
    · exact Nat.lt_of_lt_of_le (ha y e) c.le
    · exact Nat.lt_of_lt_of_le (hb y e) c.le
  · exact e.2

theorem keeps_sureRequireLook {sur : Sure S} {ned : Need} {g g' : Gen Map} (hn : NB g.re sur.ned)
    (h : sureRequireLook sur g = some (ned, g')) : Keeps g g' ∧ NB g'.re ned := by
  have L := sureRequireLook_spec h
  obtain ⟨k, e⟩ := L.gen
  refine ⟨by rw [e]; exact keeps_reg g k (by have := L.le; rw [e] at this; exact this), fun y hy => ?_⟩
  rcases L.mem y hy with e' | e'
  · exact Nat.lt_of_lt_of_le (hn y e') L.le
  · exact e'.2

end Comp
end SkaModel
end Formalization
