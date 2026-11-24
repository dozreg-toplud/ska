import lemmas.Ska.CompBelowRun

/-!
# The lower bound on the registers of a run's blocks, for `run`

The counterpart of `CompBelowRun.lean` with the bound turned around (README
Gaps 12.2, the general `AboveX`).  When every register of a goal is at least
`m` and `m ≤ re`, every block a run of `run` emits and every op it puts in
front of a block mentions only registers from `m` on, because each such
register is a register of the goal's need, an argument of the goal's jumps or
a fresh one.  The `%bom` block of `[0 0]` mentions no register, and the run
does not drop, so `emit` puts every block it counts.

* `NA m ned`: the registers of `ned` are at least `m`; `GoalA`, `NextA`.
* `AboveIn m lo g`: every block of `g` at a label in `[lo, g.bo)` mentions
  only registers from `m` on.
* `KeepsA m g g'`: every `AboveIn m lo` of `g` holds of `g'`, `re` and `bo`
  grew, `drop` stayed.  The steps `keepsA_re`, `keepsA_emit`,
  `keepsA_addOps`, and one lemma per arm, each the proof of its `keeps_`
  counterpart with the bound turned around.
* `run_keepsA`: every run of `run` from a state that does not drop, for a
  goal whose registers are at least `m`, with `m ≤ re`, keeps every
  `AboveIn m lo` and returns a `next` whose registers are at least `m`;
  `run_above`: the blocks the run emits mention only registers from `m` on.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Needs and goals above a bound -/

/-- The registers of `ned` are at least `m`. -/
def NA (m : Nat) (ned : Need) : Prop := ∀ r, NMem ned r → m ≤ r

theorem na_none (m : Nat) : NA m Need.none := fun _ h => absurd h (by simp [NMem])

theorem na_this {m r : Nat} (h : m ≤ r) : NA m (Need.this r) := fun _ e => by
  simp only [NMem] at e; rw [e]; exact h

/-- The registers of a goal (its need and the arguments of its jumps) are at
least `m`. -/
def GoalA (m : Nat) : CGoal S → Prop
  | CGoal.next laz th => NA m laz.ned ∧ JmpIn (m ≤ ·) th
  | CGoal.pick z o => JmpIn (m ≤ ·) z ∧ JmpIn (m ≤ ·) o
  | CGoal.done => True

/-- The registers of a `next` are at least `m`. -/
def NextA (m : Nat) (nex : Next S) : Prop := NA m nex.laz.ned ∧ JmpIn (m ≤ ·) nex.th

/-! ## The lower bound on blocks -/

/-- **Every block of `g` at a label in `[lo, g.bo)` mentions only registers
from `m` on.** -/
def AboveIn (m lo : Nat) (g : Gen Map) : Prop :=
  ∀ o b, lo ≤ o → o < g.bo → HoonMap.get g.blocks o = some b → BlobIn (m ≤ ·) b

theorem aboveIn_start (m : Nat) (g : Gen Map) : AboveIn m g.bo g := fun _ _ l u _ => absurd u (Nat.not_lt.mpr l)

theorem aboveIn_emitted {m lo : Nat} {g : Gen Map} {b : Blob} (h : AboveIn m lo g) (hd : g.drop = false)
    (hb : BlobIn (m ≤ ·) b) : AboveIn m lo (g.emitted b) := by
  intro o b' l u hb'
  simp only [Gen.emitted, hd, Bool.false_eq_true, if_false, HoonMap.get_put] at u hb'
  by_cases e : o = g.bo
  · rw [if_pos e] at hb'; cases hb'; exact hb
  · rw [if_neg e] at hb'
    exact h o b' l (by omega) hb'

theorem aboveIn_emit {m lo : Nat} {g g' : Gen Map} {b : Blob} {o : Nat} (h : AboveIn m lo g) (hd : g.drop = false)
    (hb : BlobIn (m ≤ ·) b) (he : (emit b : CM Map Nat) g = some (o, g')) : AboveIn m lo g' := by
  rw [emit_apply] at he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  rw [← he.2]; exact aboveIn_emitted h hd hb

/-- **Putting ops of registers from `m` on in front of a block keeps the
bound.** -/
theorem aboveIn_addOps {m lo o : Nat} {ops : List Pole} {g g' : Gen Map} (h : AboveIn m lo g)
    (hA : RegsIn (m ≤ ·) ops) (ha : addOps o ops g = some ((), g')) : AboveIn m lo g' := by
  unfold addOps at ha
  by_cases hd : g.drop = true
  · rw [if_pos hd] at ha; cases ha; exact h
  · rw [if_neg hd] at ha
    obtain ⟨b, hb, e⟩ := Option.map_eq_some_iff.mp ha
    simp only [Prod.mk.injEq] at e
    rw [← e.2]
    intro o' b' l u hb'
    simp only [HoonMap.get_put] at u hb'
    by_cases e' : o' = o
    · rw [if_pos e'] at hb'; cases hb'
      subst e'
      have hb0 := h o' b l u hb
      exact ⟨hb0.1, hA.append hb0.2.1, hb0.2.2⟩
    · rw [if_neg e'] at hb'
      exact h o' b' l u hb'

/-! ## Runs that keep the bound -/

/-- **`g'` keeps every `AboveIn m lo` of `g`**, has at least its registers,
and the same mode. -/
structure KeepsA (m : Nat) (g g' : Gen Map) : Prop where
  ab : ∀ lo, AboveIn m lo g → AboveIn m lo g'
  le : g.re ≤ g'.re
  drop : g'.drop = g.drop
  bo : g.bo ≤ g'.bo

theorem KeepsA.refl (m : Nat) (g : Gen Map) : KeepsA m g g := ⟨fun _ h => h, Nat.le_refl _, rfl, Nat.le_refl _⟩

theorem KeepsA.trans {m : Nat} {g0 g1 g2 : Gen Map} (a : KeepsA m g0 g1) (b : KeepsA m g1 g2) : KeepsA m g0 g2 :=
  ⟨fun lo h => b.ab lo (a.ab lo h), Nat.le_trans a.le b.le, b.drop.trans a.drop, Nat.le_trans a.bo b.bo⟩

theorem KeepsA.dropF {m : Nat} {g g' : Gen Map} (k : KeepsA m g g') (hd : g.drop = false) : g'.drop = false :=
  k.drop.trans hd

theorem keepsA_reg (m : Nat) (g : Gen Map) (k : Nat) (hk : g.re ≤ k) : KeepsA m g { g with re := k } :=
  ⟨fun _ h => h, hk, rfl, Nat.le_refl _⟩

theorem keepsA_re {m : Nat} {g g' : Gen Map} {r : Nat} (h : (re : CM Map Nat) g = some (r, g')) :
    r = g.re ∧ g'.re = g.re + 1 ∧ KeepsA m g g' := by
  rw [re_apply] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl, keepsA_reg m g _ (Nat.le_succ _)⟩

theorem keepsA_emit {m : Nat} {g g' : Gen Map} {b : Blob} {o : Nat} (hd : g.drop = false) (hb : BlobIn (m ≤ ·) b)
    (h : (emit b : CM Map Nat) g = some (o, g')) : KeepsA m g g' ∧ g'.re = g.re := by
  have e := h
  rw [emit_apply] at e
  simp only [Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨_, rfl⟩ := e
  exact ⟨⟨fun _ hl => aboveIn_emit hl hd hb h, Nat.le_refl _, rfl, Nat.le_succ _⟩, rfl⟩

theorem keepsA_addOps {m : Nat} {g g' : Gen Map} {o : Nat} {ops : List Pole} {u : Unit} (hA : RegsIn (m ≤ ·) ops)
    (h : addOps o ops g = some (u, g')) : KeepsA m g g' ∧ g'.re = g.re := by
  cases u
  obtain ⟨e1, e2, e3⟩ := addOps_re h
  exact ⟨⟨fun _ hl => aboveIn_addOps hl hA h, Nat.le_of_eq e1.symm, e2, Nat.le_of_eq e3.symm⟩, e1⟩

theorem keepsA_of_gen {m : Nat} {g g' : Gen Map} (e : g' = { g with re := g'.re }) (le : g.re ≤ g'.re) :
    KeepsA m g g' := by
  rw [e]; exact keepsA_reg m g _ le

/-! ## The arms that take needs apart and copy them -/

theorem keepsA_must {m : Nat} {ned n : Need} {r : Nat} {g g' : Gen Map} (hn : NA m ned) (hm : m ≤ g.re)
    (h : must ned g = some ((r, n), g')) : KeepsA m g g' ∧ NA m n ∧ m ≤ r := by
  obtain ⟨e, le, m1, m2, _⟩ := must_spec h
  refine ⟨keepsA_of_gen e le, fun y hy => ?_, ?_⟩
  · rcases m1 y hy with h1 | h1
    · exact hn y h1
    · exact Nat.le_trans hm h1.1
  · rcases m2 with h1 | h1
    · exact hn r h1
    · exact Nat.le_trans hm h1.1

theorem keepsA_splitNeed {m : Nat} {ned : Need} {o : Nat} {g g' : Gen Map} {x : Need × Need} (hn : NA m ned)
    (hm : m ≤ g.re) (h : splitNeed ned o g = some (x, g')) : KeepsA m g g' ∧ NA m x.1 ∧ NA m x.2 := by
  cases ned with
  | pair p q =>
    simp only [splitNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨KeepsA.refl _ _, fun r hr => hn r (Or.inl hr), fun r hr => hn r (Or.inr hr)⟩
  | none =>
    simp only [splitNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨KeepsA.refl _ _, na_none _, na_none _⟩
  | this r =>
    simp only [splitNeed] at h
    obtain ⟨hh, g1, h1, h⟩ := bind_some h
    obtain ⟨t, g2, h2, h⟩ := bind_some h
    obtain ⟨u, g3, h3, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨e1, r1, k1⟩ := keepsA_re (m := m) h1
    obtain ⟨e2, r2, k2⟩ := keepsA_re (m := m) h2
    have hr : m ≤ r := hn r rfl
    obtain ⟨k3, r3⟩ := keepsA_addOps (m := m) (regsIn_con (by omega) (by omega) (by omega) (RegsIn.nil _)) h3
    exact ⟨k1.trans (k2.trans k3), na_this (by omega), na_this (by omega)⟩
  | both r hd tl =>
    simp only [splitNeed] at h
    obtain ⟨⟨r1, n1⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨⟨r2, n2⟩, g2, h2, h⟩ := bind_some h
    obtain ⟨u, g3, h3, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hr : m ≤ r := hn r (Or.inl rfl)
    obtain ⟨k1, n1b, r1b⟩ := keepsA_must (fun y hy => hn y (Or.inr (Or.inl hy))) hm h1
    obtain ⟨k2, n2b, r2b⟩ := keepsA_must (fun y hy => hn y (Or.inr (Or.inr hy))) (Nat.le_trans hm k1.le) h2
    obtain ⟨k3, r3⟩ := keepsA_addOps (m := m) (regsIn_con r1b r2b hr (RegsIn.nil _)) h3
    exact ⟨k1.trans (k2.trans k3), n1b, n2b⟩

/-- **The ops of `+copy-need-make-ops` mention registers of the two needs
or fresh ones**, so registers from `m` on. -/
theorem copyNeed_regsA {m : Nat} : ∀ (a b : Need) (ops : List Pole) (g g' : Gen Map) (x : Need × List Pole),
    copyNeed a b ops g = some (x, g') → m ≤ g.re → NA m a → NA m b → RegsIn (m ≤ ·) ops →
    RegsIn (m ≤ ·) x.2 := by
  intro a
  induction a with
  | none =>
    intro b ops g g' x h _ _ _ hA
    simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact hA
  | this rl =>
    intro b ops g g' x h hm ha hb hA
    have hl : m ≤ rl := ha rl rfl
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
      exact regsIn_mov hm hl hA
  | pair pl ql ihp ihq =>
    intro b ops g g' x h hm ha hb hA
    cases b with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact hA
    | this rr =>
      simp only [copyNeed, bind_apply, re_apply, Option.bind_some, pure_apply, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact regsIn_mov hm (hb rr rfl) hA
    | pair pr qr =>
      simp only [copyNeed] at h
      obtain ⟨⟨a1, o1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨a2, o2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨_, _, c1⟩ := copyNeed_spec _ _ _ _ _ _ h1
      exact ihq _ _ _ _ (a2, o2) h2 (Nat.le_trans hm c1.le) (fun y hy => ha y (Or.inr hy))
        (fun y hy => hb y (Or.inr hy))
        (ihp _ _ _ _ _ h1 hm (fun y hy => ha y (Or.inl hy)) (fun y hy => hb y (Or.inl hy)) hA)
    | both xr hr tr =>
      simp only [copyNeed] at h
      obtain ⟨⟨a1, o1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨a2, o2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨_, _, c1⟩ := copyNeed_spec _ _ _ _ _ _ h1
      exact ihq _ _ _ _ (a2, o2) h2 (Nat.le_trans hm c1.le) (fun y hy => ha y (Or.inr hy))
        (fun y hy => hb y (Or.inr (Or.inr hy)))
        (ihp _ _ _ _ _ h1 hm (fun y hy => ha y (Or.inl hy)) (fun y hy => hb y (Or.inr (Or.inl hy))) hA)
  | both rl hl tl ihh iht =>
    intro b ops g g' x h hm ha hb hA
    have hrl : m ≤ rl := ha rl (Or.inl rfl)
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
      have hm1 : m ≤ g.re + 1 := Nat.le_succ_of_le hm
      exact iht _ _ _ _ (a2, o2) h2 (Nat.le_trans hm1 c1.le) (fun y hy => ha y (Or.inr (Or.inr hy)))
        (fun y hy => hb y (Or.inr hy))
        (ihh _ _ _ _ _ h1 hm1 (fun y hy => ha y (Or.inr (Or.inl hy))) (fun y hy => hb y (Or.inl hy))
          (regsIn_mov hm hrl hA))
    | both xr hr tr =>
      simp only [copyNeed] at h
      obtain ⟨⟨a1, o1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨a2, o2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨_, _, c1⟩ := copyNeed_spec _ _ _ _ _ _ h1
      exact iht _ _ _ _ (a2, o2) h2 (Nat.le_trans hm c1.le) (fun y hy => ha y (Or.inr (Or.inr hy)))
        (fun y hy => hb y (Or.inr (Or.inr hy)))
        (ihh _ _ _ _ _ h1 hm (fun y hy => ha y (Or.inr (Or.inl hy))) (fun y hy => hb y (Or.inr (Or.inl hy)))
          (regsIn_mov (hb xr (Or.inl rfl)) hrl hA))

theorem keepsA_copyNeed {m : Nat} {a b : Need} {g g' : Gen Map} {x : Need × List Pole}
    (h : copyNeed a b [] g = some (x, g')) (hm : m ≤ g.re) (ha : NA m a) (hb : NA m b) :
    KeepsA m g g' ∧ NA m x.1 ∧ RegsIn (m ≤ ·) x.2 := by
  obtain ⟨_, _, c⟩ := copyNeed_spec _ _ _ _ _ _ h
  refine ⟨keepsA_of_gen c.gen c.le, fun y hy => ?_, copyNeed_regsA _ _ _ _ _ _ h hm ha hb (RegsIn.nil _)⟩
  rcases c.mem y hy with e | e
  · rcases e with e | e
    · exact ha y e
    · exact hb y e
  · exact Nat.le_trans hm e.1

theorem keepsA_sureRequireLook {m : Nat} {sur : Sure S} {ned : Need} {g g' : Gen Map} (hn : NA m sur.ned)
    (hm : m ≤ g.re) (h : sureRequireLook sur g = some (ned, g')) : KeepsA m g g' ∧ NA m ned := by
  have L := sureRequireLook_spec h
  obtain ⟨k, e⟩ := L.gen
  refine ⟨by rw [e]; exact keepsA_reg m g k (by have := L.le; rw [e] at this; exact this), fun y hy => ?_⟩
  rcases L.mem y hy with e' | e'
  · exact hn y e'
  · exact Nat.le_trans hm e'.1

theorem fillA_regs {m : Nat} {ned : Need} (hn : NA m ned) :
    RegsIn (m ≤ ·) ((flattenNeed ned).map fun x => Pole.imm (A 0) x) := by
  intro q hq x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hq
  simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rw [hx]; exact hn y ((mem_flatten ned y).mp hy)

/-! ## Constants and crashes -/

theorem keepsA_crashNeed {m o : Nat} {atom : Sum Nat Nat} {ned : Need} {g g' : Gen Map} {u : Unit}
    (hn : NA m ned) (hm : m ≤ g.re) (ha : ∀ p, atom = Sum.inr p → m ≤ p) (h : crashNeed o atom ned g = some (u, g')) :
    KeepsA m g g' := by
  cases atom with
  | inr p =>
    simp only [crashNeed] at h
    exact (keepsA_addOps (regsIn_single (p := Pole.cel p) (fun x hx => by
      simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rw [hx]; exact ha p rfl) _ (fillA_regs hn)) h).1
  | inl n =>
    simp only [crashNeed, bind_apply, re_apply, Option.bind_some] at h
    refine (keepsA_reg m g _ (Nat.le_succ _)).trans (keepsA_addOps (regsIn_single (p := Pole.imm (A n) g.re) (fun x hx => by
      simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rw [hx]; exact hm) _ (regsIn_single (p := Pole.cel g.re) (fun x hx => by
      simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rw [hx]; exact hm) _ (fillA_regs hn))) h).1

theorem keepsA_medeLoop {m o : Nat} : ∀ (som : Noun) (ned : Need) (g g' : Gen Map) (u : Unit),
    NA m ned → m ≤ g.re → medeLoop o som ned g = some (u, g') → KeepsA m g g'
  | _, Need.none, g, g', u, _, _, h => by
    simp only [medeLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact KeepsA.refl m g
  | som, Need.this r, g, g', u, hn, _, h => by
    simp only [medeLoop] at h
    exact (keepsA_addOps (regsIn_single (p := Pole.imm som r) (fun x hx => by
      simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rw [hx]; exact hn r rfl) _ (RegsIn.nil _)) h).1
  | Noun.atom n, Need.pair p q, g, g', u, hn, hm, h => by
    simp only [medeLoop] at h
    exact keepsA_crashNeed hn hm (fun _ e => by cases e) h
  | Noun.cell a b, Need.pair p q, g, g', u, hn, hm, h => by
    simp only [medeLoop] at h
    obtain ⟨u1, g1, h1, h2⟩ := bind_some h
    have k1 := keepsA_medeLoop a p g g1 u1 (fun y hy => hn y (Or.inl hy)) hm h1
    exact k1.trans (keepsA_medeLoop b q g1 g' u (fun y hy => hn y (Or.inr hy)) (Nat.le_trans hm k1.le) h2)
  | Noun.atom n, Need.both r hh t, g, g', u, hn, hm, h => by
    simp only [medeLoop] at h
    exact keepsA_crashNeed hn hm (fun _ e => by cases e) h
  | Noun.cell a b, Need.both r hh t, g, g', u, hn, hm, h => by
    simp only [medeLoop] at h
    obtain ⟨u0, g0, h0, h⟩ := bind_some h
    obtain ⟨k0, _⟩ := keepsA_addOps (m := m) (regsIn_single (p := Pole.imm (C a b) r) (fun x hx => by
      simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rw [hx]; exact hn r (Or.inl rfl)) _ (RegsIn.nil _)) h0
    obtain ⟨u1, g1, h1, h2⟩ := bind_some h
    have k1 := keepsA_medeLoop a hh g0 g1 u1 (fun y hy => hn y (Or.inr (Or.inl hy))) (Nat.le_trans hm k0.le) h1
    exact k0.trans (k1.trans (keepsA_medeLoop b t g1 g' u
      (fun y hy => hn y (Or.inr (Or.inr hy))) (Nat.le_trans hm (Nat.le_trans k0.le k1.le)) h2))

theorem keepsA_mede {m : Nat} {th : Jmp} {som : Noun} {laz : Sure S} {g g' : Gen Map} {o : Nat}
    (hd : g.drop = false) (hn : NA m laz.ned) (hj : JmpIn (m ≤ ·) th) (hm : m ≤ g.re)
    (h : mede th som laz g = some (o, g')) : KeepsA m g g' := by
  unfold mede at h
  obtain ⟨o1, g1, h1, h⟩ := bind_some h
  obtain ⟨k1, _⟩ := keepsA_emit hd (blobIn_fin (f := Termin.hop th) hj) h1
  obtain ⟨g2, g2', h2, h⟩ := bind_some h
  rw [get_apply] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl⟩ := h2
  rw [k1.dropF hd] at h
  simp only [Bool.false_eq_true, if_false] at h
  obtain ⟨ned, g3, h3, h⟩ := bind_some h
  obtain ⟨k3, n3⟩ := keepsA_sureRequireLook hn (Nat.le_trans hm k1.le) h3
  obtain ⟨u4, g4, h4, h⟩ := bind_some h
  have k4 := keepsA_medeLoop _ _ _ _ _ n3 (Nat.le_trans hm (Nat.le_trans k1.le k3.le)) h4
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.2]
  exact k1.trans (k3.trans k4)

/-! ## The blocks of `%3`, `%5` and `+simple-next` -/

theorem keepsA_forl {m r o : Nat} {g g' : Gen Map} {x : Nat × Nat} (hd : g.drop = false) (hr : m ≤ r)
    (hm : m ≤ g.re) (h : forl r o g = some (x, g')) : KeepsA m g g' := by
  unfold forl at h
  obtain ⟨r0, g1, h1, h⟩ := bind_some h
  obtain ⟨e1, q1, k1⟩ := keepsA_re (m := m) h1
  obtain ⟨r1, g2, h2, h⟩ := bind_some h
  obtain ⟨e2, q2, k2⟩ := keepsA_re (m := m) h2
  have d2 := (k1.trans k2).dropF hd
  obtain ⟨barg, g3, h3, h⟩ := bind_some h
  obtain ⟨k3, q3⟩ := keepsA_emit (m := m) (b := ⟨[r], [], Termin.hop (jmp0 o)⟩) d2 ⟨fun x hx => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx; rw [hx]; exact hr, RegsIn.nil _, jmpIn_jmp0 _ o⟩ h3
  obtain ⟨if0, g4, h4, h⟩ := bind_some h
  obtain ⟨k4, q4⟩ := keepsA_emit (m := m) (b := ⟨[], [Pole.imm (A 0) r0], Termin.hop ⟨[some r0], barg⟩⟩)
    (k3.dropF d2) ⟨fun x hx => absurd hx (List.not_mem_nil),
    regsIn_single (p := Pole.imm (A 0) r0) (fun x hx => by
      simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; rw [hx]; omega) _ (RegsIn.nil _),
    jmpIn_one (P := (m ≤ ·)) (by omega)⟩ h4
  obtain ⟨if1, g5, h5, h⟩ := bind_some h
  obtain ⟨k5, q5⟩ := keepsA_emit (m := m) (b := ⟨[], [Pole.imm (A 1) r1], Termin.hop ⟨[some r1], barg⟩⟩)
    (k4.dropF (k3.dropF d2)) ⟨fun x hx => absurd hx (List.not_mem_nil),
    regsIn_single (p := Pole.imm (A 1) r1) (fun x hx => by
      simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; rw [hx]; omega) _ (RegsIn.nil _),
    jmpIn_one (P := (m ≤ ·)) (by omega)⟩ h5
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.2]
  exact k1.trans (k2.trans (k3.trans (k4.trans k5)))

theorem keepsA_doneBlocks {m : Nat} {g g' : Gen Map} {x : Nat × Nat} (hd : g.drop = false) (hm : m ≤ g.re)
    (h : (doneBlocks : CM Map (Nat × Nat)) g = some (x, g')) : KeepsA m g g' := by
  unfold doneBlocks at h
  obtain ⟨r0, g1, h1, h⟩ := bind_some h
  obtain ⟨e1, q1, k1⟩ := keepsA_re (m := m) h1
  obtain ⟨r1, g2, h2, h⟩ := bind_some h
  obtain ⟨e2, q2, k2⟩ := keepsA_re (m := m) h2
  have d2 := (k1.trans k2).dropF hd
  obtain ⟨o0, g3, h3, h⟩ := bind_some h
  obtain ⟨k3, q3⟩ := keepsA_emit (m := m) (b := ⟨[], [Pole.imm (A 0) r0], Termin.don r0⟩) d2
    ⟨fun x hx => absurd hx (List.not_mem_nil),
    regsIn_single (p := Pole.imm (A 0) r0) (fun x hx => by
      simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; rw [hx]; omega) _ (RegsIn.nil _),
    show m ≤ r0 by omega⟩ h3
  obtain ⟨o1, g4, h4, h⟩ := bind_some h
  obtain ⟨k4, q4⟩ := keepsA_emit (m := m) (b := ⟨[], [Pole.imm (A 1) r1], Termin.don r1⟩) (k3.dropF d2)
    ⟨fun x hx => absurd hx (List.not_mem_nil),
    regsIn_single (p := Pole.imm (A 1) r1) (fun x hx => by
      simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; rw [hx]; omega) _ (RegsIn.nil _),
    show m ≤ r1 by omega⟩ h4
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.2]
  exact k1.trans (k2.trans (k3.trans k4))

theorem keepsA_simpleNext {m : Nat} {goal : CGoal S} {g g' : Gen Map} {nex : Next S} (hd : g.drop = false)
    (hg : GoalA m goal) (hm : m ≤ g.re) (h : simpleNext goal g = some (nex, g')) : KeepsA m g g' ∧ NextA m nex := by
  cases goal with
  | next laz th =>
    simp only [simpleNext, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨KeepsA.refl _ _, hg⟩
  | done =>
    simp only [simpleNext] at h
    obtain ⟨r, g1, h1, h⟩ := bind_some h
    obtain ⟨e1, q1, k1⟩ := keepsA_re (m := m) h1
    obtain ⟨o, g2, h2, h⟩ := bind_some h
    obtain ⟨k2, q2⟩ := keepsA_emit (m := m) (k1.dropF hd) (blobIn_fin (f := Termin.don r) (show m ≤ r by omega)) h2
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨k1.trans k2, na_this (by omega), jmpIn_jmp0 _ _⟩
  | pick z o =>
    simp only [simpleNext] at h
    obtain ⟨r, g1, h1, h⟩ := bind_some h
    obtain ⟨e1, q1, k1⟩ := keepsA_re (m := m) h1
    obtain ⟨o', g2, h2, h⟩ := bind_some h
    obtain ⟨k2, q2⟩ := keepsA_emit (m := m) (k1.dropF hd)
      (blobIn_fin (f := Termin.brn r z o) ⟨show m ≤ r by omega, hg.1, hg.2⟩) h2
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨k1.trans k2, na_this (by omega), jmpIn_jmp0 _ _⟩

theorem keepsA_bomb {m : Nat} {miss : Option Nat} {g g' : Gen Map} {nex : Next S} (hd : g.drop = false)
    (h : (bomb miss : CM Map (Next S)) g = some (nex, g')) : KeepsA m g g' ∧ NextA m nex := by
  simp only [bomb] at h
  obtain ⟨o, g1, h1, h⟩ := bind_some h
  obtain ⟨k1, _⟩ := keepsA_emit (m := m) hd (blobIn_fin (f := Termin.bom miss) trivial) h1
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨k1, na_none _, jmpIn_jmp0 _ _⟩

/-! ## `+split`, `+into`, `+copy` -/

theorem na_rollTack {m : Nat} : ∀ (tack : List (Bool × Need)) (acc : Need), NA m acc → (∀ e ∈ tack, NA m e.2) →
    NA m (tack.foldl (fun acc e => side e.1 acc e.2) acc)
  | [], _, ha, _ => ha
  | e :: tack, _, ha, ht => na_rollTack tack _
      (fun y hy => ((nmem_side _ _ _ y).mp hy).elim (ha y) (ht e (List.mem_cons_self ..) y))
      (fun x hx => ht x (List.mem_cons_of_mem _ hx))

theorem keepsA_intoLoop {m o : Nat} : ∀ (axe : Nat) (ned : Need) (tack : List (Bool × Need)) (ops : List Pole)
    (g g' : Gen Map) (x : Need × Need), intoLoop o axe ned tack ops g = some (x, g') →
    NA m ned → (∀ e ∈ tack, NA m e.2) → RegsIn (m ≤ ·) ops → m ≤ g.re →
    KeepsA m g g' ∧ NA m x.1 ∧ NA m x.2 := by
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
  intro ned tack ops g g' x h hc ht hA hm
  rw [intoLoop] at h
  by_cases h1 : axe ≤ 1
  · rw [dif_pos h1] at h
    obtain ⟨u, g1, h2, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨k, e⟩ := keepsA_addOps hA h2
    exact ⟨k, hc, na_rollTack tack Need.none (na_none _) ht⟩
  rw [dif_neg h1] at h
  have lt := mas_lt axe (by omega)
  cases ned with
  | none =>
    exact ih _ lt _ _ _ _ _ _ h (na_none _) (by
      intro e he; rcases List.mem_cons.mp he with e' | he
      · rw [e']; exact na_none _
      · exact ht e he) hA hm
  | this r =>
    simp only at h
    obtain ⟨l, g1, h1', h⟩ := bind_some h
    obtain ⟨r', g2, h2, h⟩ := bind_some h
    obtain ⟨e1, q1, k1⟩ := keepsA_re (m := m) h1'
    obtain ⟨e2, q2, k2⟩ := keepsA_re (m := m) h2
    have hr : m ≤ r := hc r rfl
    obtain ⟨k, n1, n2⟩ := ih _ lt _ _ _ _ _ _ h (na_this (by split <;> omega)) (by
      intro e he; rcases List.mem_cons.mp he with e' | he
      · rw [e']; exact na_this (by split <;> omega)
      · exact ht e he) (regsIn_con (by omega) (by omega) (by omega) hA) (by omega)
    exact ⟨k1.trans (k2.trans k), n1, n2⟩
  | pair p q =>
    simp only at h
    exact ih _ lt _ _ _ _ _ _ h (by split <;> first | exact fun y hy => hc y (Or.inl hy) | exact fun y hy => hc y (Or.inr hy))
      (by
        intro e he; rcases List.mem_cons.mp he with e' | he
        · rw [e']; show NA _ (if _ then _ else _); split
          · exact fun y hy => hc y (Or.inr hy)
          · exact fun y hy => hc y (Or.inl hy)
        · exact ht e he) hA hm
  | both r hh t =>
    simp only at h
    obtain ⟨⟨lr, ln⟩, g1, h1', h⟩ := bind_some h
    obtain ⟨⟨rr, rn⟩, g2, h2, h⟩ := bind_some h
    have hr : m ≤ r := hc r (Or.inl rfl)
    obtain ⟨k1, nl, rl⟩ := keepsA_must (fun y hy => hc y (Or.inr (Or.inl hy))) hm h1'
    obtain ⟨k2, nr, rr2⟩ := keepsA_must (fun y hy => hc y (Or.inr (Or.inr hy))) (Nat.le_trans hm k1.le) h2
    have l1 := k1.le
    have l2 := k2.le
    obtain ⟨k, n1, n2⟩ := ih _ lt _ _ _ _ _ _ h (by split; exact nl; exact nr) (by
      intro e he; rcases List.mem_cons.mp he with e' | he
      · rw [e']; show NA _ (if _ then _ else _); split
        · exact nr
        · exact nl
      · exact ht e he) (regsIn_con (by omega) (by omega) (by omega) hA) (by omega)
    exact ⟨k1.trans (k2.trans k), n1, n2⟩

theorem keepsA_split {m : Nat} {laz : Sure S} {th : Jmp} {g g' : Gen Map} {x : Sure S × Sure S × Nat}
    (hd : g.drop = false) (hn : NA m laz.ned) (hj : JmpIn (m ≤ ·) th) (hm : m ≤ g.re)
    (h : Comp.split ⟨laz, th⟩ g = some (x, g')) : KeepsA m g g' ∧ NA m x.1.ned ∧ NA m x.2.1.ned := by
  simp only [Comp.split] at h
  obtain ⟨o, g0, h0, h⟩ := bind_some h
  obtain ⟨k0, _⟩ := keepsA_emit hd (blobIn_fin (f := Termin.hop th) hj) h0
  obtain ⟨⟨sh, st⟩, g1, h2, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [splitSure] at h2
  obtain ⟨⟨lh, lt⟩, _, h2⟩ := Option.bind_eq_some_iff.mp h2
  obtain ⟨⟨⟨nh, nt⟩, g2⟩, h3, h4⟩ := Option.map_eq_some_iff.mp h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
  obtain ⟨k3, n1, n2⟩ := keepsA_splitNeed hn (Nat.le_trans hm k0.le) h3
  exact ⟨k0.trans k3, n1, n2⟩

theorem keepsA_copy {m : Nat} {first : Next S} {second : Sure S} {g g' : Gen Map} {nex : Next S}
    (hd : g.drop = false) (h1 : NextA m first) (h2 : NA m second.ned) (hm : m ≤ g.re)
    (h : copy first second g = some (nex, g')) : KeepsA m g g' ∧ NextA m nex := by
  simp only [copy] at h
  obtain ⟨o, g0, h0, h⟩ := bind_some h
  obtain ⟨k0, _⟩ := keepsA_emit hd (blobIn_fin (f := Termin.hop first.th) h1.2) h0
  obtain ⟨laz, g1, h1', h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [copyLazy] at h1'
  obtain ⟨⟨n1, o1⟩, g2, h2', h1'⟩ := bind_some h1'
  obtain ⟨k2, nb2, rg2⟩ := keepsA_copyNeed h2' (Nat.le_trans hm k0.le) h1.1 h2
  obtain ⟨u, g3, h3, h1'⟩ := bind_some h1'
  obtain ⟨k3, e3⟩ := keepsA_addOps rg2 h3
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1'
  obtain ⟨rfl, rfl⟩ := h1'
  exact ⟨k0.trans (k2.trans k3), nb2, jmpIn_jmp0 _ _⟩

theorem keepsA_into {m : Nat} {nex : Next S} {axe : Nat} {g g' : Gen Map} {x : Sure S × Sure S × Nat}
    (hd : g.drop = false) (hn : NextA m nex) (hm : m ≤ g.re) (h : into nex axe g = some (x, g')) :
    KeepsA m g g' ∧ NA m x.1.ned ∧ NA m x.2.1.ned := by
  simp only [into] at h
  obtain ⟨o, g0, h0, h⟩ := bind_some h
  obtain ⟨k0, _⟩ := keepsA_emit hd (blobIn_fin (f := Termin.hop nex.th) hn.2) h0
  obtain ⟨⟨sd, sr⟩, g1, h2, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [intoSure] at h2
  obtain ⟨⟨ld, lr⟩, _, h2⟩ := Option.bind_eq_some_iff.mp h2
  obtain ⟨⟨⟨nd, nr⟩, g2⟩, h3, h4⟩ := Option.map_eq_some_iff.mp h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
  simp only [intoNeed] at h3
  by_cases a0 : axe = 0
  · simp [a0] at h3
  rw [if_neg a0] at h3
  by_cases a1 : axe = 1
  · rw [if_pos a1] at h3
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h3
    exact ⟨k0, hn.1, na_none _⟩
  rw [if_neg a1] at h3
  obtain ⟨k3, n1, n2⟩ := keepsA_intoLoop _ _ _ _ _ _ _ h3 hn.1 (fun e he => by simp at he) (RegsIn.nil _)
    (Nat.le_trans hm k0.le)
  exact ⟨k0.trans k3, n1, n2⟩

/-! ## `+collapse-lazy-atom` -/

theorem collapseA_end {m : Nat} {g g5 g' : Gen Map} {r there : Nat} {a : Option (Nat × Nat)} (k : KeepsA m g g5)
    (r5 : m ≤ r) (h : (pure (some (r, there)) : CM Map (Option (Nat × Nat))) g5 = some (a, g')) :
    KeepsA m g g' ∧ ∀ r' o', a = some (r', o') → m ≤ r' := by
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨k, fun r' o' e => by simp only [Option.some.injEq, Prod.mk.injEq] at e; rw [← e.1]; exact r5⟩

theorem keepsA_collapseLazyAtom {m : Nat} {nex : Next S} {g g' : Gen Map} {a : Option (Nat × Nat)}
    (hd : g.drop = false) (hn : NA m nex.laz.ned) (hm : m ≤ g.re) (h : collapseLazyAtom nex g = some (a, g')) :
    KeepsA m g g' ∧ ∀ r o, a = some (r, o) → m ≤ r := by
  unfold collapseLazyAtom at h
  by_cases ha : nex.th.args ≠ []
  · rw [if_pos ha] at h; cases h
  rw [if_neg ha] at h
  by_cases hne : noneEquivalent nex.laz = true
  · rw [if_pos hne] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨KeepsA.refl _ _, fun _ _ e => by cases e⟩
  rw [if_neg hne] at h
  obtain ⟨ns, g1, h1, h⟩ := bind_some h
  obtain ⟨k1, n1⟩ := keepsA_sureRequireLook hn hm h1
  obtain ⟨⟨r, there⟩, g2, h2, h⟩ := bind_some h
  have hr : KeepsA m g1 g2 ∧ m ≤ r := by
    cases ns with
    | this r0 =>
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      exact ⟨KeepsA.refl _ _, n1 _ rfl⟩
    | none =>
      obtain ⟨r0, g3, h3, h2⟩ := bind_some h2
      obtain ⟨e3, q3, k3⟩ := keepsA_re (m := m) h3
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      exact ⟨k3, by have := k1.le; omega⟩
    | pair p q =>
      obtain ⟨r0, g3, h3, h2⟩ := bind_some h2
      obtain ⟨e3, q3, k3⟩ := keepsA_re (m := m) h3
      obtain ⟨o, g4, h4, h2⟩ := bind_some h2
      obtain ⟨k4, q4⟩ := keepsA_emit (m := m) ((k1.trans k3).dropF hd)
        (blobIn_fin (f := Termin.bom Option.none) trivial) h4
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      exact ⟨k3.trans k4, by have := k1.le; omega⟩
    | both r0 p q =>
      obtain ⟨o, g4, h4, h2⟩ := bind_some h2
      obtain ⟨k4, q4⟩ := keepsA_emit (m := m) (k1.dropF hd) (blobIn_fin (f := Termin.bom Option.none) trivial) h4
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      exact ⟨k4, n1 _ (Or.inl rfl)⟩
  obtain ⟨k2, r2⟩ := hr
  have d2 := (k1.trans k2).dropF hd
  obtain ⟨g3, g3', h3, h⟩ := bind_some h
  rw [get_apply] at h3
  simp only [Option.some.injEq, Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  rw [d2] at h
  simp only [Bool.false_eq_true, if_false] at h
  obtain ⟨ned', g4, h4, h⟩ := bind_some h
  obtain ⟨k4, n4⟩ := keepsA_sureRequireLook (sur := ⟨Need.this r, nex.laz.lok⟩) (na_this r2)
    (Nat.le_trans hm (Nat.le_trans k1.le k2.le)) h4
  have k14 := k1.trans (k2.trans k4)
  have hm4 : m ≤ g4.re := Nat.le_trans hm k14.le
  cases ned' with
  | none => exact collapseA_end k14 r2 h
  | this r' =>
    simp only at h
    by_cases e : r = r'
    · rw [if_pos e] at h; exact collapseA_end k14 r2 h
    · rw [if_neg e] at h
      obtain ⟨u, g5, h5, h⟩ := bind_some h
      obtain ⟨k5, _⟩ := keepsA_addOps (m := m) (regsIn_mov r2 (n4 r' rfl) (RegsIn.nil _)) h5
      exact collapseA_end (k14.trans k5) r2 h
  | pair p q =>
    simp only at h
    obtain ⟨u, g5, h5, h⟩ := bind_some h
    have k5 := keepsA_crashNeed n4 hm4 (fun p e => by cases e; exact r2) h5
    exact collapseA_end (k14.trans k5) r2 h
  | both r0 p q =>
    simp only at h
    obtain ⟨u, g5, h5, h⟩ := bind_some h
    have k5 := keepsA_crashNeed n4 hm4 (fun p e => by cases e; exact r2) h5
    exact collapseA_end (k14.trans k5) r2 h

/-! ## `run` -/

theorem na_fromSure {m axe : Nat} {sur sur' : Sure S} (h : fromSure axe sur = some sur') (hc : NA m sur.ned) :
    NA m sur'.ned := by
  unfold fromSure at h
  by_cases h0 : axe = 0
  · simp [h0] at h
  simp only [h0, if_false] at h
  by_cases hn : sur.ned = Need.none
  · simp only [hn, if_true] at h
    by_cases h1 : axe = 1
    · simp [h1] at h
    simp only [h1, if_false, Option.some.injEq] at h
    subst h; exact na_none _
  · simp only [hn, if_false, Option.some.injEq] at h
    subst h; exact fun r hr => hc r (nmem_fromPath _ _ _ hr)

/-- What `run_keepsA` proves of one nomm. -/
def KeepAIH (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (m : Nat) (p : Nomm) : Prop :=
  ∀ (goal : CGoal S) (g g' : Gen Map) (nex : Next S), g.drop = false → GoalA m goal → m ≤ g.re →
    run p goal g = some (nex, g') → KeepsA m g g' ∧ NextA m nex

/-- The two runs and the copy of a cons, for a goal `%next`. -/
theorem cons_next_keepsA {m : Nat} {p q : Nomm} (ihp : KeepAIH S Map m p) (ihq : KeepAIH S Map m q)
    {laz : Sure S} {th : Jmp} {g0 g1 : Gen Map} {nex : Next S} (hd : g0.drop = false) (hg : NA m laz.ned)
    (hj : JmpIn (m ≤ ·) th) (hm : m ≤ g0.re)
    (h : (do
      let (hed, tel, o) ← Comp.split ⟨laz, th⟩
      let nexh ← past noCode ⟨hed, jmp0 o⟩ q
      let nex2 ← run q (CGoal.next tel nexh.th)
      let nex2 ← past noCode nex2 p
      let nex1 ← run p (CGoal.next nexh.laz nex2.th)
      copy nex1 nex2.laz : CM Map (Next S)) g0 = some (nex, g1)) : KeepsA m g0 g1 ∧ NextA m nex := by
  obtain ⟨⟨hed, tel, o⟩, g2, h2, h⟩ := bind_some h
  obtain ⟨k2, nh, nt⟩ := keepsA_split hd hg hj hm h2
  obtain ⟨nexh, g2', hph, h⟩ := bind_some h
  obtain ⟨rfl, rfl⟩ := past_some hph
  obtain ⟨nex2, g3, h3, h⟩ := bind_some h
  obtain ⟨k3, n3⟩ := ihq (CGoal.next _ _) g2 g3 nex2 (k2.dropF hd) ⟨nt, jmpIn_jmp0 _ _⟩
    (Nat.le_trans hm k2.le) h3
  obtain ⟨nex2', g3', hp2, h⟩ := bind_some h
  obtain ⟨rfl, rfl⟩ := past_some hp2
  obtain ⟨nex1, g4, h4, h⟩ := bind_some h
  obtain ⟨k4, n4⟩ := ihp (CGoal.next _ _) g3 g4 nex1 (k3.dropF (k2.dropF hd)) ⟨nh, n3.2⟩
    (Nat.le_trans hm (Nat.le_trans k2.le k3.le)) h4
  obtain ⟨k5, n5⟩ := keepsA_copy (k4.dropF (k3.dropF (k2.dropF hd))) n4 n3.1
    (Nat.le_trans hm (Nat.le_trans k2.le (Nat.le_trans k3.le k4.le))) h
  exact ⟨k2.trans (k3.trans (k4.trans k5)), n5⟩

/-- The block of a unary op whose register `arg` is fresh, then the run of
the operand for that register. -/
theorem unary_keepsA {m : Nat} {p : Nomm} (ihp : KeepAIH S Map m p) {b : Blob} {arg : Nat} {g g1 g2 : Gen Map}
    {o : Nat} {nex : Next S} (hd : g.drop = false) (hb : BlobIn (m ≤ ·) b) (ha : m ≤ arg) (hm : m ≤ g.re)
    (h1 : (emit b : CM Map Nat) g = some (o, g1))
    (h : run p (CGoal.next (lazyReg arg) (jmp0 o)) g1 = some (nex, g2)) : KeepsA m g g2 ∧ NextA m nex := by
  obtain ⟨k1, q1⟩ := keepsA_emit hd hb h1
  obtain ⟨k2, n2⟩ := ihp (CGoal.next _ _) _ _ _ (k1.dropF hd) ⟨na_this ha, jmpIn_jmp0 _ _⟩ (by rw [q1]; exact hm) h
  exact ⟨k1.trans k2, n2⟩

/-- **Every run of `run` keeps the lower bound `m` and returns a `next`
whose registers are at least `m`**, from a state that does not drop, for a
goal whose registers are at least `m`, when `m ≤ re`. -/
theorem run_keepsA (m : Nat) : ∀ (nm : Nomm), KeepAIH S Map m nm := by
  intro nm
  induction nm with
  | n0 ax =>
    intro goal g g' nex hd hg hm h
    simp only [run] at h
    by_cases h0 : ax = 0
    · rw [if_pos h0] at h; exact keepsA_bomb hd h
    rw [if_neg h0] at h
    obtain ⟨nex0, g1, h1, h⟩ := bind_some h
    obtain ⟨k1, n1⟩ := keepsA_simpleNext hd hg hm h1
    by_cases ha : ax = 1
    · rw [if_pos ha] at h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨k1, n1⟩
    rw [if_neg ha] at h
    cases e : «from» ax nex0.laz with
    | none => rw [e] at h; cases h
    | some laz =>
      rw [e] at h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨k1, na_fromSure e n1.1, n1.2⟩
  | n1 k =>
    intro goal g g' nex hd hg hm h
    cases goal with
    | done =>
      simp only [run] at h
      obtain ⟨r, g1, h1, h⟩ := bind_some h
      obtain ⟨e1, q1, k1⟩ := keepsA_re (m := m) h1
      obtain ⟨o, g2, h2, h⟩ := bind_some h
      obtain ⟨k2, _⟩ := keepsA_emit (m := m) (k1.dropF hd) (blobIn_one (p := Pole.imm k r) (f := Termin.don r)
        (fun x hx => by simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; omega)
        (show m ≤ r by omega)) h2
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨k1.trans k2, na_none _, jmpIn_jmp0 _ _⟩
    | pick z o =>
      simp only [run] at h
      by_cases h0 : k = A 0
      · rw [if_pos h0] at h
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨KeepsA.refl _ _, na_none _, hg.1⟩
      rw [if_neg h0] at h
      by_cases h1 : k = A 1
      · rw [if_pos h1] at h
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨KeepsA.refl _ _, na_none _, hg.2⟩
      rw [if_neg h1] at h
      exact keepsA_bomb hd h
    | next laz th =>
      simp only [run] at h
      obtain ⟨o, g1, h1, h⟩ := bind_some h
      have k1 := keepsA_mede hd hg.1 hg.2 hm h1
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨k1, na_none _, jmpIn_jmp0 _ _⟩
  | n7 p q ihp ihq =>
    intro goal g g' nex hd hg hm h
    simp only [run] at h
    obtain ⟨nexq, g1, h1, h⟩ := bind_some h
    obtain ⟨k1, n1⟩ := ihq goal g g1 nexq hd hg hm h1
    obtain ⟨k2, n2⟩ := ihp nexq.goal _ _ _ (k1.dropF hd) n1 (Nat.le_trans hm k1.le) h
    exact ⟨k1.trans k2, n2⟩
  | n4 p ih =>
    intro goal g g' nex hd hg hm h
    cases goal with
    | done =>
      simp only [run] at h
      obtain ⟨pro, g1, h1, h⟩ := bind_some h
      obtain ⟨e1, q1, k1⟩ := keepsA_re (m := m) h1
      obtain ⟨arg, g2, h2, h⟩ := bind_some h
      obtain ⟨e2, q2, k2⟩ := keepsA_re (m := m) h2
      obtain ⟨o, g3, h3, h⟩ := bind_some h
      obtain ⟨k3, n3⟩ := unary_keepsA ih ((k1.trans k2).dropF hd)
        (blobIn_one (p := Pole.inc arg pro) (f := Termin.don pro)
          (fun x hx => by simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; omega)
          (show m ≤ pro by omega)) (by omega) (by omega) h3 h
      exact ⟨k1.trans (k2.trans k3), n3⟩
    | pick z o =>
      simp only [run] at h
      obtain ⟨pro, g1, h1, h⟩ := bind_some h
      obtain ⟨e1, q1, k1⟩ := keepsA_re (m := m) h1
      obtain ⟨arg, g2, h2, h⟩ := bind_some h
      obtain ⟨e2, q2, k2⟩ := keepsA_re (m := m) h2
      obtain ⟨o', g3, h3, h⟩ := bind_some h
      obtain ⟨k3, n3⟩ := unary_keepsA ih ((k1.trans k2).dropF hd)
        (blobIn_one (p := Pole.inc arg pro) (f := Termin.brn pro z o)
          (fun x hx => by simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; omega)
          ⟨show m ≤ pro by omega, hg.1, hg.2⟩) (by omega) (by omega) h3 h
      exact ⟨k1.trans (k2.trans k3), n3⟩
    | next laz th =>
      simp only [run] at h
      obtain ⟨a, g1, h1, h⟩ := bind_some h
      obtain ⟨k1, r1⟩ := keepsA_collapseLazyAtom (nex := ⟨laz, th⟩) hd hg.1 hm h1
      obtain ⟨⟨pro, th'⟩, g2, h2, h⟩ := bind_some h
      have hp : KeepsA m g1 g2 ∧ m ≤ pro := by
        cases a with
        | some x =>
          simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
          obtain ⟨rfl, rfl⟩ := h2
          exact ⟨KeepsA.refl _ _, r1 _ _ rfl⟩
        | none =>
          simp only at h2
          obtain ⟨r, g3, h3, h2⟩ := bind_some h2
          obtain ⟨e3, q3, k3⟩ := keepsA_re (m := m) h3
          by_cases ht : th.args = []
          · rw [if_pos ht] at h2
            simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
            exact ⟨k3, by have := k1.le; omega⟩
          · rw [if_neg ht] at h2; cases h2
      obtain ⟨k2, p2⟩ := hp
      obtain ⟨arg, g3, h3, h⟩ := bind_some h
      obtain ⟨e3, q3, k3⟩ := keepsA_re (m := m) h3
      obtain ⟨o, g4, h4, h⟩ := bind_some h
      have l12 := (k1.trans k2).le
      obtain ⟨k4, n4⟩ := unary_keepsA ih ((k1.trans (k2.trans k3)).dropF hd)
        (blobIn_one (p := Pole.inc arg pro) (f := Termin.hop (jmp0 th'))
          (fun x hx => by simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; omega)
          (jmpIn_jmp0 _ _)) (by omega) (by omega) h4 h
      exact ⟨k1.trans (k2.trans (k3.trans k4)), n4⟩
  | n3 p ih =>
    intro goal g g' nex hd hg hm h
    cases goal with
    | done =>
      simp only [run] at h
      obtain ⟨⟨o0, o1⟩, g1, h1, h⟩ := bind_some h
      have k1 := keepsA_doneBlocks hd hm h1
      obtain ⟨r, g2, h2, h⟩ := bind_some h
      obtain ⟨e2, q2, k2⟩ := keepsA_re (m := m) h2
      obtain ⟨oc, g3, h3, h⟩ := bind_some h
      have l1 := k1.le
      obtain ⟨k3, n3⟩ := unary_keepsA ih ((k1.trans k2).dropF hd)
        (blobIn_fin (f := Termin.clq r (jmp0 o0) (jmp0 o1)) ⟨show m ≤ r by omega, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩)
        (by omega) (by omega) h3 h
      exact ⟨k1.trans (k2.trans k3), n3⟩
    | pick z o =>
      simp only [run] at h
      obtain ⟨r, g2, h2, h⟩ := bind_some h
      obtain ⟨e2, q2, k2⟩ := keepsA_re (m := m) h2
      obtain ⟨oc, g3, h3, h⟩ := bind_some h
      obtain ⟨k3, n3⟩ := unary_keepsA ih (k2.dropF hd)
        (blobIn_fin (f := Termin.clq r z o) ⟨show m ≤ r by omega, hg.1, hg.2⟩) (by omega) (by omega) h3 h
      exact ⟨k2.trans k3, n3⟩
    | next laz th =>
      simp only [run] at h
      by_cases en : noneEquivalent laz = true
      · rw [if_pos en] at h; exact ih _ _ _ _ hd hg hm h
      rw [if_neg en] at h
      obtain ⟨a, g1, h1, h⟩ := bind_some h
      obtain ⟨k1, r1⟩ := keepsA_collapseLazyAtom (nex := ⟨laz, th⟩) hd hg.1 hm h1
      cases a with
      | none => cases h
      | some x =>
        obtain ⟨r, o⟩ := x
        simp only at h
        obtain ⟨⟨z, o'⟩, g2, h2, h⟩ := bind_some h
        have k2 := keepsA_forl (k1.dropF hd) (r1 r o rfl) (Nat.le_trans hm k1.le) h2
        obtain ⟨r', g3, h3, h⟩ := bind_some h
        obtain ⟨e3, q3, k3⟩ := keepsA_re (m := m) h3
        obtain ⟨oc, g4, h4, h⟩ := bind_some h
        have l12 := (k1.trans k2).le
        obtain ⟨k4, n4⟩ := unary_keepsA ih ((k1.trans (k2.trans k3)).dropF hd)
          (blobIn_fin (f := Termin.clq r' (jmp0 z) (jmp0 o')) ⟨show m ≤ r' by omega, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩)
          (by omega) (by omega) h4 h
        exact ⟨k1.trans (k2.trans (k3.trans k4)), n4⟩
  | n5 p q ihp ihq =>
    intro goal g g' nex hd hg hm h
    simp only [run] at h
    obtain ⟨rp, g1, h1, h⟩ := bind_some h
    obtain ⟨e1, q1, k1⟩ := keepsA_re (m := m) h1
    obtain ⟨rq, g2, h2, h⟩ := bind_some h
    obtain ⟨e2, q2, k2⟩ := keepsA_re (m := m) h2
    have d2 := (k1.trans k2).dropF hd
    obtain ⟨o, g3, h3, h⟩ := bind_some h
    have k3 : KeepsA m g2 g3 := by
      cases goal with
      | pick z o =>
        exact (keepsA_emit d2 (blobIn_fin (f := Termin.eqq rp rq z o)
          ⟨show m ≤ rp by omega, show m ≤ rq by omega, hg.1, hg.2⟩) h3).1
      | done =>
        obtain ⟨⟨o0, o1⟩, g4, h4, h3⟩ := bind_some h3
        have k4 := keepsA_doneBlocks (m := m) d2 (show m ≤ g2.re by omega) h4
        exact k4.trans (keepsA_emit (k4.dropF d2) (blobIn_fin (f := Termin.eqq rp rq (jmp0 o0) (jmp0 o1))
          ⟨show m ≤ rp by omega, show m ≤ rq by omega, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩) h3).1
      | next laz th =>
        obtain ⟨a, g4, h4, h3⟩ := bind_some h3
        obtain ⟨k4, r4⟩ := keepsA_collapseLazyAtom (nex := ⟨laz, th⟩) d2 hg.1 (by omega) h4
        have l4 := k4.le
        cases a with
        | none =>
          simp only at h3
          by_cases ht : th.args = []
          · rw [if_pos ht] at h3
            exact k4.trans (keepsA_emit (k4.dropF d2) (blobIn_one (p := Pole.equ rp rq) (f := Termin.hop (jmp0 th.there))
              (fun x hx => by simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx; omega)
              (jmpIn_jmp0 _ _)) h3).1
          · rw [if_neg ht] at h3; cases h3
        | some x =>
          obtain ⟨r, o⟩ := x
          simp only at h3
          obtain ⟨⟨z, o'⟩, g5, h5, h3⟩ := bind_some h3
          have k5 := keepsA_forl (k4.dropF d2) (r4 r o rfl) (by omega) h5
          exact k4.trans (k5.trans (keepsA_emit ((k4.trans k5).dropF d2)
            (blobIn_fin (f := Termin.eqq rp rq (jmp0 z) (jmp0 o'))
            ⟨show m ≤ rp by omega, show m ≤ rq by omega, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩) h3).1)
    have d3 := k3.dropF d2
    obtain ⟨nexq, g4, h4, h⟩ := bind_some h
    have l3 := k3.le
    obtain ⟨k4, n4⟩ := ihq (CGoal.next _ _) _ _ _ d3 ⟨na_this (by omega), jmpIn_jmp0 _ _⟩ (by omega) h4
    obtain ⟨nexq', g4', hp, h⟩ := bind_some h
    obtain ⟨rfl, rfl⟩ := past_some hp
    obtain ⟨nexp, g5, h5, h⟩ := bind_some h
    have l4 := k4.le
    obtain ⟨k5, n5⟩ := ihp (CGoal.next _ _) _ _ _ (k4.dropF d3) ⟨na_this (by omega), n4.2⟩ (by omega) h5
    obtain ⟨k6, n6⟩ := keepsA_copy (k5.dropF (k4.dropF d3)) n5 n4.1 (by have := k5.le; omega) h
    exact ⟨k1.trans (k2.trans (k3.trans (k4.trans (k5.trans k6)))), n6⟩
  | cons p q ihp ihq =>
    intro goal g g' nex hd hg hm h
    cases goal with
    | done =>
      simp only [run] at h
      obtain ⟨gl, g1, h1, h⟩ := bind_some h
      obtain ⟨r, g2, h2, h1⟩ := bind_some h1
      obtain ⟨e2, q2, k2⟩ := keepsA_re (m := m) h2
      obtain ⟨o, g3, h3, h1⟩ := bind_some h1
      obtain ⟨k3, q3⟩ := keepsA_emit (m := m) (k2.dropF hd) (blobIn_fin (f := Termin.don r) (show m ≤ r by omega)) h3
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      simp only at h
      obtain ⟨k4, n4⟩ := cons_next_keepsA ihp ihq ((k2.trans k3).dropF hd) (na_this (by omega)) (jmpIn_jmp0 _ _)
        (by omega) h
      exact ⟨k2.trans (k3.trans k4), n4⟩
    | next laz th =>
      simp only [run, bind_apply, pure_apply, Option.bind_some] at h
      exact cons_next_keepsA ihp ihq hd hg.1 hg.2 hm h
    | pick z o =>
      simp only [run, bind_apply, pure_apply, Option.bind_some] at h
      obtain ⟨⟨o', g1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k1, _⟩ := keepsA_emit (m := m) hd (blobIn_fin (f := Termin.bom Option.none) trivial) h1
      have d1 := k1.dropF hd
      obtain ⟨⟨nex2, g3⟩, h3, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k3, n3⟩ := ihq (CGoal.next _ _) _ _ _ d1 ⟨na_none _, jmpIn_jmp0 _ _⟩ (Nat.le_trans hm k1.le) h3
      obtain ⟨⟨nex2', g3'⟩, hp, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨rfl, rfl⟩ := past_some hp
      obtain ⟨⟨nex1, g4⟩, h4, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k4, n4⟩ := ihp (CGoal.next _ _) _ _ _ (k3.dropF d1) ⟨na_none _, n3.2⟩
        (Nat.le_trans hm (Nat.le_trans k1.le k3.le)) h4
      obtain ⟨k5, n5⟩ := keepsA_copy (k4.dropF (k3.dropF d1)) n4 n3.1
        (Nat.le_trans hm (Nat.le_trans k1.le (Nat.le_trans k3.le k4.le))) h
      exact ⟨k1.trans (k3.trans (k4.trans k5)), n5⟩
  | n2 => intro goal g0 g1 nex _ _ _ h; simp only [run] at h; cases h
  | n6 => intro goal g0 g1 nex _ _ _ h; simp only [run] at h; cases h
  | n10 a v q ihv ihq =>
    intro goal g g' nex hd hg hm h
    simp only [run] at h
    obtain ⟨nex0, g2, h2, h⟩ := bind_some h
    obtain ⟨k2, n2⟩ := keepsA_simpleNext hd hg hm h2
    have d2 := k2.dropF hd
    obtain ⟨⟨don, rec, o⟩, g3, h3, h⟩ := bind_some h
    obtain ⟨k3, nd, nr⟩ := keepsA_into d2 n2 (Nat.le_trans hm k2.le) h3
    have d3 := k3.dropF d2
    simp only at h
    obtain ⟨nexR, g3', hpr, h⟩ := bind_some h
    obtain ⟨rfl, rfl⟩ := past_some hpr
    obtain ⟨nexDon, g4, h4, h⟩ := bind_some h
    have l23 := (k2.trans k3).le
    obtain ⟨k4, n4⟩ := ihv (CGoal.next _ _) _ _ _ d3 ⟨nd, jmpIn_jmp0 _ _⟩ (by omega) h4
    obtain ⟨nexDon', g4', hpd, h⟩ := bind_some h
    obtain ⟨rfl, rfl⟩ := past_some hpd
    obtain ⟨nexRec, g5, h5, h⟩ := bind_some h
    have l4 := k4.le
    obtain ⟨k5, n5⟩ := ihq (CGoal.next _ _) _ _ _ (k4.dropF d3) ⟨nr, n4.2⟩ (by omega) h5
    obtain ⟨k6, n6⟩ := keepsA_copy (k5.dropF (k4.dropF d3)) n5 n4.1 (by have := k5.le; omega) h
    exact ⟨k2.trans (k3.trans (k4.trans (k5.trans k6))), n6⟩
  | n11s => intro goal g0 g1 nex _ _ _ h; simp only [run] at h; cases h
  | n11d => intro goal g0 g1 nex _ _ _ h; simp only [run] at h; cases h
  | n12 => intro goal g0 g1 nex _ _ _ h; simp only [run] at h; cases h
  | mean => intro goal g0 g1 nex _ _ _ h; simp only [run] at h; cases h

/-- **The blocks a run of `run` emits mention only registers from `m` on**,
from a state that does not drop, for a goal whose registers are at least
`m`, when `m ≤ re`. -/
theorem run_above {m : Nat} {nm : Nomm} {goal : CGoal S} {g0 g1 : Gen Map} {nex : Next S} (hd : g0.drop = false)
    (hg : GoalA m goal) (hm : m ≤ g0.re) (h : run nm goal g0 = some (nex, g1)) : AboveIn m g0.bo g1 :=
  (run_keepsA m nm goal g0 g1 nex hd hg hm h).1.ab _ (aboveIn_start m g0)

end Comp
end SkaModel
end Formalization
