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

theorem regsIn_single {P : Nat → Prop} {p : Pole} (h : ∀ x ∈ poleRegs p, P x) (A : List Pole) (hA : RegsIn P A) :
    RegsIn P (p :: A) := RegsIn.cons (p := p) h hA

theorem jmpIn_one {P : Nat → Prop} {r o : Nat} (h : P r) : JmpIn P ⟨[some r], o⟩ := fun x hx => by
  simp only [List.mem_cons, List.mem_nil_iff, or_false, Option.some.injEq] at hx
  rw [hx]; exact h

theorem fill_regs {n : Nat} {ned : Need} (hn : NB n ned) : RegsIn (· < n) ((flattenNeed ned).map fun x => Pole.imm (A 0) x) := by
  intro q hq x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hq
  simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rw [hx]; exact hn y ((mem_flatten ned y).mp hy)

/-! ## Constants and crashes -/

theorem keeps_crashNeed {o : Nat} {atom : Sum Nat Nat} {ned : Need} {g g' : Gen Map} {u : Unit}
    (hn : NB g.re ned) (ha : ∀ p, atom = Sum.inr p → p < g.re) (h : crashNeed o atom ned g = some (u, g')) :
    Keeps g g' := by
  cases atom with
  | inr p =>
    simp only [crashNeed] at h
    exact (keeps_addOps (regsIn_single (p := Pole.cel p) (fun x hx => by
      simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rw [hx]; exact ha p rfl) _ (fill_regs hn)) h).1
  | inl n =>
    simp only [crashNeed, bind_apply, re_apply, Option.bind_some] at h
    have s : g.re < g.re + 1 := Nat.lt_succ_self _
    refine (keeps_reg g _ (Nat.le_succ _)).trans (keeps_addOps (regsIn_single (p := Pole.imm (A n) g.re) (fun x hx => by
      simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rw [hx]; exact s) _ (regsIn_single (p := Pole.cel g.re) (fun x hx => by
      simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rw [hx]; exact s) _ (fill_regs (hn.mono (Nat.le_succ _))))) h).1

theorem keeps_medeLoop {o : Nat} : ∀ (som : Noun) (ned : Need) (g g' : Gen Map) (u : Unit),
    NB g.re ned → medeLoop o som ned g = some (u, g') → Keeps g g'
  | _, Need.none, g, g', u, _, h => by
    simp only [medeLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact Keeps.refl g
  | som, Need.this r, g, g', u, hn, h => by
    simp only [medeLoop] at h
    exact (keeps_addOps (regsIn_single (p := Pole.imm som r) (fun x hx => by
      simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rw [hx]; exact hn r rfl) _ (RegsIn.nil _)) h).1
  | Noun.atom n, Need.pair p q, g, g', u, hn, h => by
    simp only [medeLoop] at h
    exact keeps_crashNeed hn (fun _ e => by cases e) h
  | Noun.cell a b, Need.pair p q, g, g', u, hn, h => by
    simp only [medeLoop] at h
    obtain ⟨u1, g1, h1, h2⟩ := bind_some h
    have k1 := keeps_medeLoop a p g g1 u1 (fun y hy => hn y (Or.inl hy)) h1
    exact k1.trans (keeps_medeLoop b q g1 g' u (NB.mono (n := g.re) (fun y hy => hn y (Or.inr hy)) k1.le) h2)
  | Noun.atom n, Need.both r hh t, g, g', u, hn, h => by
    simp only [medeLoop] at h
    exact keeps_crashNeed hn (fun _ e => by cases e) h
  | Noun.cell a b, Need.both r hh t, g, g', u, hn, h => by
    simp only [medeLoop] at h
    obtain ⟨u0, g0, h0, h⟩ := bind_some h
    obtain ⟨k0, _⟩ := keeps_addOps (regsIn_single (p := Pole.imm (C a b) r) (fun x hx => by
      simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rw [hx]; exact hn r (Or.inl rfl)) _ (RegsIn.nil _)) h0
    obtain ⟨u1, g1, h1, h2⟩ := bind_some h
    have k1 := keeps_medeLoop a hh g0 g1 u1 (NB.mono (n := g.re) (fun y hy => hn y (Or.inr (Or.inl hy))) k0.le) h1
    exact k0.trans (k1.trans (keeps_medeLoop b t g1 g' u
      (NB.mono (n := g.re) (fun y hy => hn y (Or.inr (Or.inr hy))) (Nat.le_trans k0.le k1.le)) h2))

theorem keeps_mede {th : Jmp} {som : Noun} {laz : Sure S} {g g' : Gen Map} {o : Nat} (hd : g.drop = false)
    (hn : NB g.re laz.ned) (hj : JmpIn (· < g.re) th) (h : mede th som laz g = some (o, g')) : Keeps g g' := by
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
  obtain ⟨u4, g4, h4, h⟩ := bind_some h
  have k4 := keeps_medeLoop _ _ _ _ _ n3 h4
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.2]
  exact k1.trans (k3.trans k4)

/-! ## The blocks of `%3`, `%5` and `+simple-next` -/

theorem keeps_forl {r o : Nat} {g g' : Gen Map} {x : Nat × Nat} (hd : g.drop = false) (hr : r < g.re)
    (h : forl r o g = some (x, g')) : Keeps g g' := by
  unfold forl at h
  obtain ⟨r0, g1, h1, h⟩ := bind_some h
  obtain ⟨e1, q1, k1⟩ := keeps_re h1
  obtain ⟨r1, g2, h2, h⟩ := bind_some h
  obtain ⟨e2, q2, k2⟩ := keeps_re h2
  have d2 := (k1.trans k2).dropF hd
  obtain ⟨barg, g3, h3, h⟩ := bind_some h
  obtain ⟨k3, q3⟩ := keeps_emit (b := ⟨[r], [], Termin.hop (jmp0 o)⟩) d2 ⟨fun x hx => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx; rw [hx]; omega, RegsIn.nil _, jmpIn_jmp0 _ o⟩ h3
  obtain ⟨if0, g4, h4, h⟩ := bind_some h
  obtain ⟨k4, q4⟩ := keeps_emit (b := ⟨[], [Pole.imm (A 0) r0], Termin.hop ⟨[some r0], barg⟩⟩) (k3.dropF d2) ⟨fun x hx => absurd hx (List.not_mem_nil),
    regsIn_single (p := Pole.imm (A 0) r0) (fun x hx => by
      simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; rw [hx]; omega) _ (RegsIn.nil _),
    jmpIn_one (P := (· < g3.re)) (by omega)⟩ h4
  obtain ⟨if1, g5, h5, h⟩ := bind_some h
  obtain ⟨k5, q5⟩ := keeps_emit (b := ⟨[], [Pole.imm (A 1) r1], Termin.hop ⟨[some r1], barg⟩⟩) (k4.dropF (k3.dropF d2)) ⟨fun x hx => absurd hx (List.not_mem_nil),
    regsIn_single (p := Pole.imm (A 1) r1) (fun x hx => by
      simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; rw [hx]; omega) _ (RegsIn.nil _),
    jmpIn_one (P := (· < g4.re)) (by omega)⟩ h5
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.2]
  exact k1.trans (k2.trans (k3.trans (k4.trans k5)))

theorem keeps_doneBlocks {g g' : Gen Map} {x : Nat × Nat} (hd : g.drop = false)
    (h : (doneBlocks : CM Map (Nat × Nat)) g = some (x, g')) : Keeps g g' := by
  unfold doneBlocks at h
  obtain ⟨r0, g1, h1, h⟩ := bind_some h
  obtain ⟨e1, q1, k1⟩ := keeps_re h1
  obtain ⟨r1, g2, h2, h⟩ := bind_some h
  obtain ⟨e2, q2, k2⟩ := keeps_re h2
  have d2 := (k1.trans k2).dropF hd
  obtain ⟨o0, g3, h3, h⟩ := bind_some h
  obtain ⟨k3, q3⟩ := keeps_emit (b := ⟨[], [Pole.imm (A 0) r0], Termin.don r0⟩) d2 ⟨fun x hx => absurd hx (List.not_mem_nil),
    regsIn_single (p := Pole.imm (A 0) r0) (fun x hx => by
      simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; rw [hx]; omega) _ (RegsIn.nil _),
    show r0 < g2.re by omega⟩ h3
  obtain ⟨o1, g4, h4, h⟩ := bind_some h
  obtain ⟨k4, q4⟩ := keeps_emit (b := ⟨[], [Pole.imm (A 1) r1], Termin.don r1⟩) (k3.dropF d2) ⟨fun x hx => absurd hx (List.not_mem_nil),
    regsIn_single (p := Pole.imm (A 1) r1) (fun x hx => by
      simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; rw [hx]; omega) _ (RegsIn.nil _),
    show r1 < g3.re by omega⟩ h4
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.2]
  exact k1.trans (k2.trans (k3.trans k4))

theorem keeps_simpleNext {goal : CGoal S} {g g' : Gen Map} {nex : Next S} (hd : g.drop = false)
    (hg : GoalIn g.re goal) (h : simpleNext goal g = some (nex, g')) : Keeps g g' ∧ NextIn g'.re nex := by
  cases goal with
  | next laz th =>
    simp only [simpleNext, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Keeps.refl _, hg⟩
  | done =>
    simp only [simpleNext] at h
    obtain ⟨r, g1, h1, h⟩ := bind_some h
    obtain ⟨e1, q1, k1⟩ := keeps_re h1
    obtain ⟨o, g2, h2, h⟩ := bind_some h
    obtain ⟨k2, q2⟩ := keeps_emit (k1.dropF hd) (blobIn_fin (f := Termin.don r) (show r < g1.re by omega)) h2
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨k1.trans k2, nb_this (by omega), jmpIn_jmp0 _ _⟩
  | pick z o =>
    simp only [simpleNext] at h
    obtain ⟨r, g1, h1, h⟩ := bind_some h
    obtain ⟨e1, q1, k1⟩ := keeps_re h1
    obtain ⟨o', g2, h2, h⟩ := bind_some h
    have kk : ∀ x, x < g.re → x < g1.re := fun x hx => by omega
    obtain ⟨k2, q2⟩ := keeps_emit (k1.dropF hd)
      (blobIn_fin (f := Termin.brn r z o) ⟨show r < g1.re by omega, hg.1.mono kk, hg.2.mono kk⟩) h2
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨k1.trans k2, nb_this (by omega), jmpIn_jmp0 _ _⟩

theorem keeps_bomb {miss : Option Nat} {g g' : Gen Map} {nex : Next S} (hd : g.drop = false)
    (h : (bomb miss : CM Map (Next S)) g = some (nex, g')) : Keeps g g' ∧ NextIn g'.re nex := by
  simp only [bomb] at h
  obtain ⟨o, g1, h1, h⟩ := bind_some h
  obtain ⟨k1, _⟩ := keeps_emit hd (blobIn_fin (f := Termin.bom miss) trivial) h1
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨k1, nb_none _, jmpIn_jmp0 _ _⟩

end Comp
end SkaModel
end Formalization
