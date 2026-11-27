import lemmas.Ska.CompSixFuel
import lemmas.Ska.CompIntoLook

/-!
# `LeapTwice` holds

`+leap` of the rest that `+leap` returned is `~` (`leap_twice`), for any
lazy need and any branches whose passes have nonzero product axes (the
first axis of each pair of `passBoth q r`; `Bake.NoAx0` of the branches
gives it, `CompLeapTwiceRun.lean`).

**The invariant of one round** (`QuietL p s`): in every block of the lazy
need, the part of the sure need at the axis `p` is behind a register
(`+need-cut` gives `~`), or it is `%none` and every look under `p` goes to
`by` as the axis `1` (`QuietS`).  `QuietL p s laz` is exactly what makes
`+lazy-leap p s` give an empty `by` (`quiet_empty`, `empty_quiet`).

- After a pass at `p`, the rest is `QuietL p s` (`quiet_rest`): its parts at
  `p` are `%none` (`needCut_rec_quiet`) and its looks under `p` are gone.
- A pass at another `p'` keeps `QuietL p s` (`quiet_keep`).  On the need
  that is `needCut_keep`; when a part at `p` behind a register comes out
  `%none` (the pass took a part at or above the register), `p` is under
  `p'` (`needCut_open`), so no look under `p` is left either.
- So after the loop the rest is `QuietL` at every pass, whatever their
  order (`leapLoop_quiet`), and the second loop finds nothing
  (`leapLoop_none`).

`p ≠ 0` is used by `needCut_open` (an axis `0` is under no axis).  The
model needs no invariant of the lazy need: no `LInv`, no `LAll CrLok`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S]

/-! ## Axes: `b` at or under `a` is `b / 2 ^ k = a` -/

theorem div_pow_one (b : Nat) (hb : 1 ≤ b) : ∃ k, b / 2 ^ k = 1 := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    by_cases h1 : b = 1
    · exact ⟨0, by simp [h1]⟩
    · obtain ⟨k, hk⟩ := ih (b / 2) (by omega) (by omega)
      refine ⟨k + 1, ?_⟩
      rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
      exact hk

theorem div_pow_trans {a b c j k : Nat} (h1 : a / 2 ^ j = b) (h2 : b / 2 ^ k = c) :
    a / 2 ^ (j + k) = c := by
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, h1, h2]

/-- An answer `[~ r]` of `+gep`: `b` is under `a`. -/
theorem gep_some_div {a b r : Nat} (h : gep a b = some (some r)) : ∃ k, b / 2 ^ k = a := by
  unfold gep at h
  by_cases a0 : a = 0
  · simp [a0] at h
  by_cases b0 : b = 0
  · simp [b0] at h
  simp only [a0, b0, if_false] at h
  by_cases ab : a = b
  · exact ⟨0, by simp [ab]⟩
  rw [if_neg ab] at h
  by_cases ba : b < a
  · simp [ba] at h
  rw [if_neg ba] at h
  by_cases ht : b / 2 ^ (Hoon.metF 0 b - Hoon.metF 0 a) = a
  · exact ⟨_, ht⟩
  · simp [ht] at h

theorem cap_four {a : Nat} (h : 4 ≤ a) : cap a = cap (a / 2) := by
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 4 := ⟨a - 4, by omega⟩
  rw [cap]

theorem mas_four {a : Nat} (h : 4 ≤ a) : mas a = a % 2 + mas (a / 2) * 2 := by
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 4 := ⟨a - 4, by omega⟩
  rw [mas]

theorem cap_23 (a : Nat) (h : 2 ≤ a) : cap a = 2 ∨ cap a = 3 := by
  induction a using Nat.strongRecOn with
  | ind a ih =>
    rcases (by omega : a = 2 ∨ a = 3 ∨ 4 ≤ a) with rfl | rfl | h4
    · simp [cap]
    · simp [cap]
    · rw [cap_four h4]; exact ih (a / 2) (by omega) (by omega)

theorem mas_small {a : Nat} (h : a = 2 ∨ a = 3) : mas a = 1 := by
  rcases h with rfl | rfl <;> simp [mas]

theorem mas_ge2 {a : Nat} (h : 4 ≤ a) : 2 ≤ mas a := by
  rw [mas_four h]; have := mas_pos (a / 2) (by omega); omega

theorem cap_mas_inj : ∀ (a b : Nat), 2 ≤ a → 2 ≤ b → cap a = cap b → mas a = mas b → a = b := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro b ha hb hc hm
    by_cases h4 : 4 ≤ a
    · by_cases h4' : 4 ≤ b
      · rw [mas_four h4, mas_four h4'] at hm
        rw [cap_four h4, cap_four h4'] at hc
        have e2 : mas (a / 2) = mas (b / 2) := by omega
        have := ih (a / 2) (by omega) (b / 2) (by omega) (by omega) hc e2
        omega
      · have := mas_ge2 h4; rw [mas_small (by omega : b = 2 ∨ b = 3)] at hm; omega
    · by_cases h4' : 4 ≤ b
      · have := mas_ge2 h4'; rw [mas_small (by omega : a = 2 ∨ a = 3)] at hm; omega
      · rcases (by omega : a = 2 ∨ a = 3) with rfl | rfl <;>
          rcases (by omega : b = 2 ∨ b = 3) with rfl | rfl <;> first | rfl | simp [cap] at hc

/-- Under the same `+cap`, `b` under `a` follows from `+mas b` under `+mas a`. -/
theorem mas_div : ∀ (k a b : Nat), 2 ≤ a → 2 ≤ b → cap a = cap b → mas a / 2 ^ k = mas b →
    a / 2 ^ k = b := by
  intro k
  induction k with
  | zero => intro a b ha hb hc hm; simp at hm ⊢; exact cap_mas_inj a b ha hb hc hm
  | succ k ih =>
    intro a b ha hb hc hm
    have hmb := mas_pos b hb
    have h2 : 2 ≤ 2 ^ (k + 1) := by rw [Nat.pow_succ]; have := Nat.two_pow_pos k; omega
    have h4 : 4 ≤ a := by
      refine Decidable.byContradiction fun h => ?_
      rw [mas_small (by omega : a = 2 ∨ a = 3), Nat.div_eq_of_lt (by omega)] at hm
      omega
    have e : mas a / 2 = mas (a / 2) := by rw [mas_four h4]; omega
    rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul, e] at hm
    rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
    exact ih (a / 2) b (by omega) hb (by rw [← cap_four h4]; exact hc) hm

/-! ## Needs: the part at an axis is `%none` or behind a register -/

/-- A cut that gives `~` or a `%none` part. -/
def QCut (x : Option (Option (Need × Need))) : Prop :=
  x = some Option.none ∨ ∃ rec, x = some (some (Need.none, rec))

/-- The part of `ned` at `axe` is `%none`, or behind a register. -/
def QuietN (axe : Nat) (ned : Need) : Prop := QCut (needCut axe ned)

theorem needCut_none (axe : Nat) : needCut axe Need.none = some (some (Need.none, Need.none)) := by
  simp [needCut]

theorem quietN_none (axe : Nat) : QuietN axe Need.none := Or.inr ⟨_, needCut_none axe⟩

theorem needCut_pair {axe : Nat} (h : 2 ≤ axe) (a b : Need) :
    needCut axe (Need.pair a b) = if cap axe = 2 then
      (needCut (mas axe) a).map fun k => k.map fun e => (e.1, consNeed e.2 b)
    else (needCut (mas axe) b).map fun k => k.map fun e => (e.1, consNeed a e.2) := by
  rw [needCut, if_neg (by omega), if_neg (by omega)]

theorem needCut_pair_one (a b : Need) :
    needCut 1 (Need.pair a b) = some (some (Need.pair a b, Need.none)) := by
  simp [needCut]

theorem needCut_pair_zero (a b : Need) : needCut 0 (Need.pair a b) = Option.none := by
  simp [needCut]

theorem needCut_this {axe r : Nat} {don rec : Need} (h : needCut axe (Need.this r) = some (some (don, rec))) :
    rec = Need.none := by
  simp only [needCut] at h; split at h <;> simp_all

theorem needCut_both {axe r : Nat} {a b don rec : Need}
    (h : needCut axe (Need.both r a b) = some (some (don, rec))) : rec = Need.none := by
  simp only [needCut] at h; split at h <;> simp_all

theorem qcut_map (g : Need → Need) (x : Option (Option (Need × Need))) :
    QCut (x.map fun k => k.map fun e => (e.1, g e.2)) ↔ QCut x := by
  rcases x with _ | _ | ⟨d, c⟩ <;> simp [QCut]

theorem cut_map_none (g : Need → Need) (x : Option (Option (Need × Need))) :
    (x.map fun k => k.map fun e => (e.1, g e.2)) = some Option.none ↔ x = some Option.none := by
  rcases x with _ | _ | ⟨d, c⟩ <;> simp

theorem cut_map_some {g : Need → Need} {x : Option (Option (Need × Need))} {d c : Need}
    (h : (x.map fun k => k.map fun e => (e.1, g e.2)) = some (some (d, c))) :
    ∃ c0, x = some (some (d, c0)) ∧ c = g c0 := by
  rcases x with _ | _ | ⟨d0, c0⟩ <;> simp at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨c0, rfl, rfl⟩

theorem quietN_pair {axe : Nat} (h : 2 ≤ axe) (a b : Need) :
    QuietN axe (Need.pair a b) ↔ if cap axe = 2 then QuietN (mas axe) a else QuietN (mas axe) b := by
  unfold QuietN; rw [needCut_pair h]
  split
  · exact qcut_map (fun c => consNeed c b) _
  · exact qcut_map (fun c => consNeed a c) _

theorem quietN_cons {axe : Nat} (h : 2 ≤ axe) (a b : Need)
    (hc : if cap axe = 2 then QuietN (mas axe) a else QuietN (mas axe) b) : QuietN axe (consNeed a b) := by
  unfold consNeed; split
  · exact quietN_none axe
  · exact (quietN_pair h a b).2 hc

theorem quietN_ge2 {axe : Nat} {a b : Need} (h : QuietN axe (Need.pair a b)) : 2 ≤ axe := by
  rcases (by omega : axe = 0 ∨ axe = 1 ∨ 2 ≤ axe) with rfl | rfl | h2
  · rw [QuietN, needCut_pair_zero] at h; simp [QCut] at h
  · rw [QuietN, needCut_pair_one] at h; simp [QCut] at h
  · exact h2

/-- **After a cut at `axe`, the part at `axe` is `%none`.** -/
theorem needCut_rec_quiet : ∀ (ned : Need) (axe : Nat) (don rec : Need),
    needCut axe ned = some (some (don, rec)) → QuietN axe rec := by
  intro ned
  induction ned with
  | none =>
    intro axe don rec h
    rw [needCut_none] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; exact quietN_none _
  | this r => intro axe don rec h; rw [needCut_this h]; exact quietN_none _
  | both r a b _ _ => intro axe don rec h; rw [needCut_both h]; exact quietN_none _
  | pair a b iha ihb =>
    intro axe don rec h
    rcases (by omega : axe = 0 ∨ axe = 1 ∨ 2 ≤ axe) with rfl | rfl | h2
    · rw [needCut_pair_zero] at h; cases h
    · rw [needCut_pair_one] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h; exact quietN_none _
    · rw [needCut_pair h2] at h
      split at h
      · obtain ⟨c0, e, rfl⟩ := cut_map_some (g := fun c => consNeed c b) h
        exact quietN_cons h2 _ _ (by rw [if_pos ‹_›]; exact iha _ _ _ e)
      · obtain ⟨c0, e, rfl⟩ := cut_map_some (g := fun c => consNeed a c) h
        exact quietN_cons h2 _ _ (by rw [if_neg ‹_›]; exact ihb _ _ _ e)

/-- **A cut at `p2` keeps the part at `p1` `%none` or behind a register.** -/
theorem needCut_keep : ∀ (ned : Need) (p1 p2 : Nat) (don rec : Need), QuietN p1 ned →
    needCut p2 ned = some (some (don, rec)) → QuietN p1 rec := by
  intro ned
  induction ned with
  | none =>
    intro p1 p2 don rec _ h
    rw [needCut_none] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; exact quietN_none _
  | this r => intro p1 p2 don rec _ h; rw [needCut_this h]; exact quietN_none _
  | both r a b _ _ => intro p1 p2 don rec _ h; rw [needCut_both h]; exact quietN_none _
  | pair a b iha ihb =>
    intro p1 p2 don rec h1 h
    rcases (by omega : p2 = 0 ∨ p2 = 1 ∨ 2 ≤ p2) with rfl | rfl | h2
    · rw [needCut_pair_zero] at h; cases h
    · rw [needCut_pair_one] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h; exact quietN_none _
    · have hp1 := quietN_ge2 h1
      rw [quietN_pair hp1] at h1
      rw [needCut_pair h2] at h
      split at h
      · obtain ⟨c0, e, rfl⟩ := cut_map_some (g := fun c => consNeed c b) h
        refine quietN_cons hp1 _ _ ?_
        split
        · rw [if_pos ‹_›] at h1; exact iha _ _ _ _ h1 e
        · rw [if_neg ‹_›] at h1; exact h1
      · obtain ⟨c0, e, rfl⟩ := cut_map_some (g := fun c => consNeed a c) h
        refine quietN_cons hp1 _ _ ?_
        split
        · rw [if_pos ‹_›] at h1; exact h1
        · rw [if_neg ‹_›] at h1; exact ihb _ _ _ _ h1 e

/-- **A part at `p1` behind a register that a cut at `p2` makes `%none`
is under `p2`.** -/
theorem needCut_open : ∀ (ned : Need) (p1 p2 : Nat) (don rec : Need), p1 ≠ 0 →
    needCut p1 ned = some Option.none → needCut p2 ned = some (some (don, rec)) →
    needCut p1 rec ≠ some Option.none → ∃ k, p1 / 2 ^ k = p2 := by
  intro ned
  induction ned with
  | none => intro p1 p2 don rec _ h1; rw [needCut_none] at h1; simp at h1
  | this r =>
    intro p1 p2 don rec hp h1 h _
    simp only [needCut] at h; split at h
    · subst ‹p2 = 1›; exact div_pow_one p1 (by omega)
    · simp at h
  | both r a b _ _ =>
    intro p1 p2 don rec hp h1 h _
    simp only [needCut] at h; split at h
    · subst ‹p2 = 1›; exact div_pow_one p1 (by omega)
    · simp at h
  | pair a b iha ihb =>
    intro p1 p2 don rec hp h1 h h3
    rcases (by omega : p2 = 0 ∨ p2 = 1 ∨ 2 ≤ p2) with rfl | rfl | h2
    · rw [needCut_pair_zero] at h; cases h
    · exact div_pow_one p1 (by omega)
    · have hp1 : 2 ≤ p1 := by
        rcases (by omega : p1 = 1 ∨ 2 ≤ p1) with rfl | h
        · rw [needCut_pair_one] at h1; simp at h1
        · exact h
      have c1 := cap_23 p1 hp1
      have c2 := cap_23 p2 h2
      rw [needCut_pair hp1] at h1
      rw [needCut_pair h2] at h
      split at h
      · obtain ⟨c0, e, rfl⟩ := cut_map_some (g := fun c => consNeed c b) h
        split at h1
        · have h1' := (cut_map_none (fun c => consNeed c b) _).1 h1
          have h4 : needCut (mas p1) c0 ≠ some Option.none := by
            intro e4; apply h3
            unfold consNeed; split
            · rename_i hn; rw [hn.1, needCut_none] at e4; simp at e4
            · rw [needCut_pair hp1, if_pos ‹_›, e4]; rfl
          obtain ⟨k, hk⟩ := iha _ _ _ _ (by have := mas_pos p1 hp1; omega) h1' e h4
          exact ⟨k, mas_div k p1 p2 hp1 h2 (by omega) hk⟩
        · have h1' := (cut_map_none (fun c => consNeed a c) _).1 h1
          have hb : b ≠ Need.none := by intro hb; rw [hb, needCut_none] at h1'; simp at h1'
          exfalso; apply h3
          unfold consNeed; rw [if_neg (fun hh => hb hh.2), needCut_pair hp1, if_neg ‹_›, h1']; rfl
      · obtain ⟨c0, e, rfl⟩ := cut_map_some (g := fun c => consNeed a c) h
        split at h1
        · have h1' := (cut_map_none (fun c => consNeed c b) _).1 h1
          have ha : a ≠ Need.none := by intro ha; rw [ha, needCut_none] at h1'; simp at h1'
          exfalso; apply h3
          unfold consNeed; rw [if_neg (fun hh => ha hh.1), needCut_pair hp1, if_pos ‹_›, h1']; rfl
        · have h1' := (cut_map_none (fun c => consNeed a c) _).1 h1
          have h4 : needCut (mas p1) c0 ≠ some Option.none := by
            intro e4; apply h3
            unfold consNeed; split
            · rename_i hn; rw [hn.2, needCut_none] at e4; simp at e4
            · rw [needCut_pair hp1, if_neg ‹_›, e4]; rfl
          obtain ⟨k, hk⟩ := ihb _ _ _ _ (by have := mas_pos p1 hp1; omega) h1' e h4
          exact ⟨k, mas_div k p1 p2 hp1 h2 (by omega) hk⟩

/-! ## Looks: the fold of `leapLok` -/

/-- The step of the fold of `leapLok`. -/
def llF (p s : Nat) (acc : Option (S × S)) (a : Nat) : Option (S × S) :=
  acc.bind fun (lb, lr) => (gep p a).map fun d => match d with
    | Option.none => (lb, HoonSet.put lr a)
    | some d => (HoonSet.put lb (Hoon.pegF s d), lr)

theorem leapLok_fold (p s : Nat) (lok : S) :
    leapLok p s lok = (HoonSet.toList lok).foldl (llF p s) (some (HoonSet.empty, HoonSet.empty)) := rfl

theorem llF_some (p s : Nat) (b0 r0 : S) (a : Nat) :
    llF p s (some (b0, r0)) a = (gep p a).map fun d => match d with
      | Option.none => (b0, HoonSet.put r0 a)
      | some d => (HoonSet.put b0 (Hoon.pegF s d), r0) := rfl

theorem llF_fold_none (p s : Nat) : ∀ (l : List Nat), l.foldl (llF (S := S) p s) Option.none = Option.none
  | [] => rfl
  | _ :: l => llF_fold_none p s l

theorem llF_spec (p s : Nat) : ∀ (l : List Nat) (b0 r0 lb lr : S),
    l.foldl (llF p s) (some (b0, r0)) = some (lb, lr) →
    (∀ a ∈ l, gep p a ≠ Option.none) ∧
    (∀ y ∈ HoonSet.toList lr, y ∈ HoonSet.toList r0 ∨ (y ∈ l ∧ gep p y = some Option.none)) ∧
    (∀ y ∈ HoonSet.toList lb, y ∈ HoonSet.toList b0 ∨
      ∃ a ∈ l, ∃ d, gep p a = some (some d) ∧ y = Hoon.pegF s d) ∧
    (∀ y ∈ HoonSet.toList b0, y ∈ HoonSet.toList lb) ∧
    (∀ a ∈ l, ∀ d, gep p a = some (some d) → Hoon.pegF s d ∈ HoonSet.toList lb)
  | [], b0, r0, lb, lr, h => by
    simp only [List.foldl_nil, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp, fun y hy => Or.inl hy, fun y hy => Or.inl hy, fun y hy => hy, by simp⟩
  | a :: l, b0, r0, lb, lr, h => by
    rw [List.foldl_cons, llF_some] at h
    cases eg : gep p a with
    | none => rw [eg, Option.map_none, llF_fold_none] at h; cases h
    | some d =>
      rw [eg, Option.map_some] at h
      have ga : ∀ x ∈ a :: l, gep p x ≠ Option.none → True := fun _ _ _ => trivial
      clear ga
      cases d with
      | none =>
        obtain ⟨g1, r1, b1, m1, c1⟩ := llF_spec p s l b0 (HoonSet.put r0 a) lb lr h
        refine ⟨?_, ?_, ?_, m1, ?_⟩
        · intro x hx; rcases List.mem_cons.1 hx with rfl | hx
          · rw [eg]; simp
          · exact g1 x hx
        · intro y hy; rcases r1 y hy with h' | h'
          · rcases (HoonSet.mem_put _ _ _).1 h' with rfl | h'
            · exact Or.inr ⟨List.mem_cons_self, eg⟩
            · exact Or.inl h'
          · exact Or.inr ⟨List.mem_cons_of_mem _ h'.1, h'.2⟩
        · intro y hy; rcases b1 y hy with h' | ⟨a', ha', d', e', rfl⟩
          · exact Or.inl h'
          · exact Or.inr ⟨a', List.mem_cons_of_mem _ ha', d', e', rfl⟩
        · intro x hx d' e'; rcases List.mem_cons.1 hx with rfl | hx
          · rw [eg] at e'; cases e'
          · exact c1 x hx d' e'
      | some d =>
        obtain ⟨g1, r1, b1, m1, c1⟩ := llF_spec p s l (HoonSet.put b0 (Hoon.pegF s d)) r0 lb lr h
        refine ⟨?_, ?_, ?_, fun y hy => m1 y ((HoonSet.mem_put _ _ _).2 (Or.inr hy)), ?_⟩
        · intro x hx; rcases List.mem_cons.1 hx with rfl | hx
          · rw [eg]; simp
          · exact g1 x hx
        · intro y hy; rcases r1 y hy with h' | h'
          · exact Or.inl h'
          · exact Or.inr ⟨List.mem_cons_of_mem _ h'.1, h'.2⟩
        · intro y hy; rcases b1 y hy with h' | ⟨a', ha', d', e', rfl⟩
          · rcases (HoonSet.mem_put _ _ _).1 h' with rfl | h'
            · exact Or.inr ⟨a, List.mem_cons_self, d, eg, rfl⟩
            · exact Or.inl h'
          · exact Or.inr ⟨a', List.mem_cons_of_mem _ ha', d', e', rfl⟩
        · intro x hx d' e'; rcases List.mem_cons.1 hx with rfl | hx
          · rw [eg] at e'; cases e'; exact m1 _ ((HoonSet.mem_put _ _ _).2 (Or.inl rfl))
          · exact c1 x hx d' e'

theorem llF_ok (p s : Nat) : ∀ (l : List Nat) (b0 r0 : S), (∀ a ∈ l, gep p a ≠ Option.none) →
    ∃ lb lr, l.foldl (llF p s) (some (b0, r0)) = some (lb, lr)
  | [], b0, r0, _ => ⟨b0, r0, rfl⟩
  | a :: l, b0, r0, h => by
    rw [List.foldl_cons, llF_some]
    cases eg : gep p a with
    | none => exact absurd eg (h a List.mem_cons_self)
    | some d =>
      cases d with
      | none => exact llF_ok p s l _ _ (fun x hx => h x (List.mem_cons_of_mem _ hx))
      | some d => exact llF_ok p s l _ _ (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- What `leapLok` does: no crash on a look, the looks not under `p` stay,
the ones under `p` go to `by` as axes under `s`. -/
theorem leapLok_spec {p s : Nat} {lok lb lr : S} (h : leapLok p s lok = some (lb, lr)) :
    (∀ a ∈ HoonSet.toList lok, gep p a ≠ Option.none) ∧
    (∀ y ∈ HoonSet.toList lr, gep p y = some Option.none) ∧
    (∀ y ∈ HoonSet.toList lr, y ∈ HoonSet.toList lok) ∧
    (∀ y ∈ HoonSet.toList lb, ∃ a ∈ HoonSet.toList lok, ∃ d, gep p a = some (some d) ∧ y = Hoon.pegF s d) ∧
    (∀ a ∈ HoonSet.toList lok, ∀ d, gep p a = some (some d) → Hoon.pegF s d ∈ HoonSet.toList lb) := by
  rw [leapLok_fold] at h
  obtain ⟨g, r, b, -, c⟩ := llF_spec p s _ _ _ _ _ h
  refine ⟨g, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_, c⟩
  · rcases r y hy with h' | h'
    · exact absurd h' (HoonSet.mem_empty y)
    · exact h'.2
  · rcases r y hy with h' | h'
    · exact absurd h' (HoonSet.mem_empty y)
    · exact h'.1
  · rcases b y hy with h' | h'
    · exact absurd h' (HoonSet.mem_empty y)
    · exact h'

theorem leapLok_ok {p s : Nat} {lok : S} (h : ∀ a ∈ HoonSet.toList lok, gep p a ≠ Option.none) :
    ∃ lb lr, leapLok p s lok = some (lb, lr) := by
  rw [leapLok_fold]; exact llF_ok p s _ _ _ h

/-! ## Sure needs -/

/-- The sure needs of `by` and `rec` that `+lazy-leap` makes from the cut. -/
def lzS (p s : Nat) (sur : Sure S) : Option (Need × Need) → Option (Sure S × Sure S)
  | Option.none => some ((Sure.bunt : Sure S), sur)
  | some (don, rec) => (leapLok p s sur.lok).bind fun (lb, lr) =>
      (needFrom s don).map fun nf => ((⟨nf, lb⟩ : Sure S), (⟨rec, lr⟩ : Sure S))

theorem lazyLeap_mk (p s : Nat) (sur : Sure S) (fk : List ((Nat × Lazy S) × (Nat × Lazy S)))
    (bd : List (Nat × Lazy S)) :
    lazyLeap p s (mk sur fk bd) = (needCut p sur.ned).bind fun cut => (lzS p s sur cut).bind fun ss =>
      (leapForks p s fk).bind fun fs => (leapBonds p s bd).map fun bs =>
        (lazyPrune (mk ss.1 (fs.map Prod.fst) (bs.map Prod.fst)),
         lazyPrune (mk ss.2 (fs.map Prod.snd) (bs.map Prod.snd))) := by
  rw [lazyLeap]
  cases needCut p sur.ned with
  | none => rfl
  | some cut =>
    cases cut with
    | none => rfl
    | some dr =>
      obtain ⟨don, rec⟩ := dr
      simp only [Option.bind_some, lzS]

theorem lazyLeap_some {p s : Nat} {sur : Sure S} {fk : List ((Nat × Lazy S) × (Nat × Lazy S))}
    {bd : List (Nat × Lazy S)} {b r : Lazy S} (h : lazyLeap p s (mk sur fk bd) = some (b, r)) :
    ∃ cut sb sr fs bs, needCut p sur.ned = some cut ∧ lzS p s sur cut = some (sb, sr) ∧
      leapForks p s fk = some fs ∧ leapBonds p s bd = some bs ∧
      b = lazyPrune (mk sb (fs.map Prod.fst) (bs.map Prod.fst)) ∧
      r = lazyPrune (mk sr (fs.map Prod.snd) (bs.map Prod.snd)) := by
  rw [lazyLeap_mk] at h
  cases e1 : needCut p sur.ned with
  | none => simp [e1] at h
  | some cut =>
    cases e2 : lzS p s sur cut with
    | none => simp [e1, e2] at h
    | some ss =>
      obtain ⟨sb, sr⟩ := ss
      cases e3 : leapForks p s fk with
      | none => simp [e1, e3] at h
      | some fs =>
        cases e4 : leapBonds p s bd with
        | none => simp [e1, e3, e4] at h
        | some bs =>
          simp only [e1, e2, e3, e4, Option.bind_some, Option.map_some, Option.some.injEq,
            Prod.mk.injEq] at h
          refine ⟨cut, sb, sr, fs, bs, ?_, ?_, ?_, ?_, h.1.symm, h.2.symm⟩ <;> first | rfl | assumption

/-- **A sure need quiet at `p`**: its part at `p` is behind a register, or it
is `%none` and every look under `p` goes to `by` as the axis `1`. -/
def QuietS (p s : Nat) (sur : Sure S) : Prop :=
  needCut p sur.ned = some Option.none ∨
  ((∃ rec, needCut p sur.ned = some (some (Need.none, rec))) ∧
    ∀ a ∈ HoonSet.toList sur.lok, gep p a ≠ Option.none ∧
      ∀ d, gep p a = some (some d) → Hoon.pegF s d = 1)

theorem quietS_bunt (p s : Nat) : QuietS p s (Sure.bunt : Sure S) :=
  Or.inr ⟨⟨_, needCut_none p⟩, fun a ha => absurd ha (HoonSet.mem_empty a)⟩

theorem needFrom_none (s : Nat) : needFrom s Need.none = some Need.none := by simp [needFrom]

theorem fromPath_ne_none {ned : Need} (h : ned ≠ Need.none) (axe : Nat) : fromPath ned axe ≠ Need.none := by
  unfold fromPath
  split
  · exact h
  · split <;> simp

theorem needFrom_eq_none {s : Nat} {don : Need} (h : needFrom s don = some Need.none) : don = Need.none := by
  refine Decidable.byContradiction fun hd => ?_
  unfold needFrom at h
  rw [if_neg hd] at h
  split at h
  · cases h
  · simp only [Option.some.injEq] at h; exact fromPath_ne_none hd s h

theorem lzS_some {p s : Nat} {sur : Sure S} {don rec : Need} {sb sr : Sure S}
    (h : lzS p s sur (some (don, rec)) = some (sb, sr)) :
    ∃ lb lr nf, leapLok p s sur.lok = some (lb, lr) ∧ needFrom s don = some nf ∧
      sb = ⟨nf, lb⟩ ∧ sr = ⟨rec, lr⟩ := by
  simp only [lzS] at h
  cases el : leapLok p s sur.lok with
  | none => simp [el] at h
  | some lbr =>
    obtain ⟨lb, lr⟩ := lbr
    cases ef : needFrom s don with
    | none => simp [el, ef] at h
    | some nf =>
      simp only [el, ef, Option.bind_some, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨lb, lr, nf, rfl, rfl, h.1.symm, h.2.symm⟩

/-- A quiet sure need gives an empty sure need of `by`. -/
theorem quietS_empty {p s : Nat} {sur : Sure S} (h : QuietS p s sur) :
    ∃ cut sb sr, needCut p sur.ned = some cut ∧ lzS p s sur cut = some (sb, sr) ∧
      sb.ned = Need.none ∧ HoonSet.small sb.lok = true := by
  rcases h with h | ⟨⟨rec, h⟩, hl⟩
  · exact ⟨_, _, _, h, rfl, rfl, small_empty⟩
  · obtain ⟨lb, lr, el⟩ := leapLok_ok (s := s) (fun a ha => (hl a ha).1)
    refine ⟨_, ⟨Need.none, lb⟩, ⟨rec, lr⟩, h, ?_, rfl, ?_⟩
    · simp only [lzS, el, Option.bind_some, needFrom_none, Option.map_some]
    · obtain ⟨-, -, -, hb, -⟩ := leapLok_spec el
      refine (HoonSet.small_iff _).2 fun y hy => ?_
      obtain ⟨a, ha, d, e, rfl⟩ := hb y hy
      exact (hl a ha).2 d e

/-- An empty sure need of `by` comes from a quiet sure need. -/
theorem empty_quietS {p s : Nat} {sur : Sure S} {cut : Option (Need × Need)} {sb sr : Sure S}
    (h1 : needCut p sur.ned = some cut) (h2 : lzS p s sur cut = some (sb, sr)) (hn : sb.ned = Need.none)
    (hs : HoonSet.small sb.lok = true) : QuietS p s sur := by
  cases cut with
  | none => exact Or.inl h1
  | some dr =>
    obtain ⟨don, rec⟩ := dr
    obtain ⟨lb, lr, nf, el, ef, rfl, rfl⟩ := lzS_some h2
    simp only at hn hs
    subst hn
    have hd := needFrom_eq_none ef
    subst hd
    obtain ⟨hg, -, -, -, hc⟩ := leapLok_spec el
    exact Or.inr ⟨⟨rec, h1⟩, fun a ha => ⟨hg a ha, fun d e => (HoonSet.small_iff _).1 hs _ (hc a ha d e)⟩⟩

/-- **After a pass at `p`**, the sure need of the rest is quiet at `p`. -/
theorem quietS_rest {p s s' : Nat} {sur : Sure S} {cut : Option (Need × Need)} {sb sr : Sure S}
    (h1 : needCut p sur.ned = some cut) (h2 : lzS p s sur cut = some (sb, sr)) : QuietS p s' sr := by
  cases cut with
  | none =>
    simp only [lzS, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨-, rfl⟩ := h2; exact Or.inl h1
  | some dr =>
    obtain ⟨don, rec⟩ := dr
    obtain ⟨lb, lr, nf, el, -, -, rfl⟩ := lzS_some h2
    rcases needCut_rec_quiet _ _ _ _ h1 with hc | ⟨r', hc⟩
    · exact Or.inl hc
    · obtain ⟨-, hr, -, -, -⟩ := leapLok_spec el
      refine Or.inr ⟨⟨r', hc⟩, fun a ha => ?_⟩
      have e0 := hr a ha
      exact ⟨by rw [e0]; simp, fun d e => by rw [e0] at e; cases e⟩

/-- **A pass at `p2` keeps a sure need quiet at `p1`.** -/
theorem quietS_keep {p1 s1 p2 s2 : Nat} (hp : p1 ≠ 0) {sur : Sure S} {cut : Option (Need × Need)}
    {sb sr : Sure S} (hc : QuietS p1 s1 sur) (h1 : needCut p2 sur.ned = some cut)
    (h2 : lzS p2 s2 sur cut = some (sb, sr)) : QuietS p1 s1 sr := by
  cases cut with
  | none =>
    simp only [lzS, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨-, rfl⟩ := h2; exact hc
  | some dr =>
    obtain ⟨don, rec⟩ := dr
    obtain ⟨lb, lr, nf, el, -, -, rfl⟩ := lzS_some h2
    obtain ⟨-, hr, hsub, -, -⟩ := leapLok_spec el
    have hN : QuietN p1 sur.ned := by
      rcases hc with hc | ⟨⟨r, hc⟩, -⟩
      · exact Or.inl hc
      · exact Or.inr ⟨r, hc⟩
    rcases needCut_keep _ _ _ _ _ hN h1 with hk | ⟨r', hk⟩
    · exact Or.inl hk
    · refine Or.inr ⟨⟨r', hk⟩, ?_⟩
      rcases hc with hc | ⟨-, hl⟩
      · obtain ⟨k, hk'⟩ := needCut_open _ _ _ _ _ hp hc h1 (by rw [hk]; simp)
        intro a ha
        have hga := hr a ha
        have ha0 : a ≠ 0 := fun h0 => by
          have := gep_crash.2 (Or.inr h0 : p2 = 0 ∨ a = 0); rw [this] at hga; cases hga
        refine ⟨fun e => ?_, fun d e => ?_⟩
        · rcases gep_crash.1 e with h | h
          · exact hp h
          · exact ha0 h
        · obtain ⟨j, hj⟩ := gep_some_div e
          exact absurd (div_pow_trans hj hk') (gep_none hga (j + k))
      · intro a ha; exact hl a (hsub a ha)

/-! ## Lazy needs -/

mutual
/-- **The invariant of a round**: every block of the lazy need quiet at `p`. -/
def QuietL (p s : Nat) : Lazy S → Prop
  | mk sur fk bd => QuietS p s sur ∧ QuietF p s fk ∧ QuietB p s bd

def QuietF (p s : Nat) : List ((Nat × Lazy S) × (Nat × Lazy S)) → Prop
  | [] => True
  | ((_, y), (_, n)) :: rest => (QuietL p s y ∧ QuietL p s n) ∧ QuietF p s rest

def QuietB (p s : Nat) : List (Nat × Lazy S) → Prop
  | [] => True
  | (_, l) :: rest => QuietL p s l ∧ QuietB p s rest
end

theorem quietL_mk {p s : Nat} {sur : Sure S} {fk : List ((Nat × Lazy S) × (Nat × Lazy S))}
    {bd : List (Nat × Lazy S)} : QuietL p s (mk sur fk bd) ↔ QuietS p s sur ∧ QuietF p s fk ∧ QuietB p s bd := by
  rw [QuietL]

theorem quietF_iff (p s : Nat) : ∀ (fk : List ((Nat × Lazy S) × (Nat × Lazy S))),
    QuietF p s fk ↔ ∀ e ∈ fk, QuietL p s e.1.2 ∧ QuietL p s e.2.2
  | [] => by simp [QuietF]
  | ((oy, y), (on, n)) :: rest => by
    rw [QuietF, quietF_iff p s rest]
    simp

theorem quietB_iff (p s : Nat) : ∀ (bd : List (Nat × Lazy S)), QuietB p s bd ↔ ∀ e ∈ bd, QuietL p s e.2
  | [] => by simp [QuietB]
  | (o, l) :: rest => by
    rw [QuietB, quietB_iff p s rest]
    simp

theorem quietL_prune {p s : Nat} {sur : Sure S} {F : List ((Nat × Lazy S) × (Nat × Lazy S))}
    {B : List (Nat × Lazy S)} (hs : QuietS p s sur) (hf : QuietF p s F) (hb : QuietB p s B) :
    QuietL p s (lazyPrune (mk sur F B)) := by
  unfold lazyPrune
  refine quietL_mk.2 ⟨hs, (quietF_iff p s _).2 fun e he => (quietF_iff p s F).1 hf e (List.mem_filter.1 he).1,
    (quietB_iff p s _).2 fun e he => (quietB_iff p s B).1 hb e (List.mem_filter.1 he).1⟩

theorem lazyEmpty_prune {sb : Sure S} {F : List ((Nat × Lazy S) × (Nat × Lazy S))} {B : List (Nat × Lazy S)} :
    lazyEmpty (lazyPrune (mk sb F B)) = true ↔ sb.ned = Need.none ∧ HoonSet.small sb.lok = true ∧
      (∀ e ∈ F, lazyEmpty e.1.2 = true ∧ lazyEmpty e.2.2 = true) ∧ ∀ e ∈ B, lazyEmpty e.2 = true := by
  simp [lazyEmpty, lazyPrune, List.filter_eq_nil_iff, and_assoc]

theorem leapForks_cons {p s oy on : Nat} {y n : Lazy S} {rest : List ((Nat × Lazy S) × (Nat × Lazy S))}
    {fs} (h : leapForks p s (((oy, y), (on, n)) :: rest) = some fs) :
    ∃ yb yr nb nr rs, lazyLeap p s y = some (yb, yr) ∧ lazyLeap p s n = some (nb, nr) ∧
      leapForks p s rest = some rs ∧ fs = (((oy, yb), (on, nb)), ((oy, yr), (on, nr))) :: rs := by
  rw [leapForks] at h
  cases ey : lazyLeap p s y with
  | none => simp [ey] at h
  | some yy =>
    obtain ⟨yb, yr⟩ := yy
    cases en : lazyLeap p s n with
    | none => simp [ey, en] at h
    | some nn =>
      obtain ⟨nb, nr⟩ := nn
      cases er : leapForks p s rest with
      | none => simp [ey, en, er] at h
      | some rs =>
        simp only [ey, en, er, Option.bind_some, Option.map_some, Option.some.injEq] at h
        exact ⟨yb, yr, nb, nr, rs, rfl, rfl, rfl, h.symm⟩

theorem leapBonds_cons {p s o : Nat} {l : Lazy S} {rest : List (Nat × Lazy S)} {bs}
    (h : leapBonds p s ((o, l) :: rest) = some bs) :
    ∃ lb lr rs, lazyLeap p s l = some (lb, lr) ∧ leapBonds p s rest = some rs ∧
      bs = ((o, lb), (o, lr)) :: rs := by
  rw [leapBonds] at h
  cases el : lazyLeap p s l with
  | none => simp [el] at h
  | some ll =>
    obtain ⟨lb, lr⟩ := ll
    cases er : leapBonds p s rest with
    | none => simp [el, er] at h
    | some rs =>
      simp only [el, er, Option.bind_some, Option.map_some, Option.some.injEq] at h
      exact ⟨lb, lr, rs, rfl, rfl, h.symm⟩

theorem leapForks_nil {p s : Nat} {fs} (h : leapForks (S := S) p s [] = some fs) : fs = [] := by
  rw [leapForks] at h; cases h; rfl

theorem leapBonds_nil {p s : Nat} {bs} (h : leapBonds (S := S) p s [] = some bs) : bs = [] := by
  rw [leapBonds] at h; cases h; rfl

section
variable (p s : Nat)

mutual
/-- **Quiet means an empty `by`.** -/
theorem quiet_empty : ∀ (L : Lazy S), QuietL p s L → ∃ b r, lazyLeap p s L = some (b, r) ∧ lazyEmpty b = true
  | mk sur fk bd, h => by
    obtain ⟨hs, hf, hb⟩ := quietL_mk.1 h
    obtain ⟨cut, sb, sr, e1, e2, hn, hsm⟩ := quietS_empty hs
    obtain ⟨fs, ef, hfs⟩ := quiet_empty_forks fk hf
    obtain ⟨bs, eb, hbs⟩ := quiet_empty_bonds bd hb
    refine ⟨lazyPrune (mk sb (fs.map Prod.fst) (bs.map Prod.fst)),
      lazyPrune (mk sr (fs.map Prod.snd) (bs.map Prod.snd)), ?_, ?_⟩
    · rw [lazyLeap_mk, e1, Option.bind_some, e2, Option.bind_some, ef, Option.bind_some, eb, Option.map_some]
    · refine lazyEmpty_prune.2 ⟨hn, hsm, fun e he => ?_, fun e he => ?_⟩
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he; exact hfs x hx
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he; exact hbs x hx

theorem quiet_empty_forks : ∀ (fk : List ((Nat × Lazy S) × (Nat × Lazy S))), QuietF p s fk →
    ∃ fs, leapForks p s fk = some fs ∧ ∀ e ∈ fs, lazyEmpty e.1.1.2 = true ∧ lazyEmpty e.1.2.2 = true
  | [], _ => ⟨[], by rw [leapForks], by simp⟩
  | ((oy, y), (on, n)) :: rest, h => by
    rw [QuietF] at h
    obtain ⟨⟨hy, hn⟩, hr⟩ := h
    obtain ⟨yb, yr, ey, hyb⟩ := quiet_empty y hy
    obtain ⟨nb, nr, en, hnb⟩ := quiet_empty n hn
    obtain ⟨fs, ef, hfs⟩ := quiet_empty_forks rest hr
    refine ⟨(((oy, yb), (on, nb)), ((oy, yr), (on, nr))) :: fs, ?_, ?_⟩
    · simp only [leapForks, ey, en, ef, Option.bind_some, Option.map_some]
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact ⟨hyb, hnb⟩
      · exact hfs e he

theorem quiet_empty_bonds : ∀ (bd : List (Nat × Lazy S)), QuietB p s bd →
    ∃ bs, leapBonds p s bd = some bs ∧ ∀ e ∈ bs, lazyEmpty e.1.2 = true
  | [], _ => ⟨[], by rw [leapBonds], by simp⟩
  | (o, l) :: rest, h => by
    rw [QuietB] at h
    obtain ⟨hl, hr⟩ := h
    obtain ⟨lb, lr, el, hlb⟩ := quiet_empty l hl
    obtain ⟨bs, eb, hbs⟩ := quiet_empty_bonds rest hr
    refine ⟨((o, lb), (o, lr)) :: bs, ?_, ?_⟩
    · simp only [leapBonds, el, eb, Option.bind_some, Option.map_some]
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact hlb
      · exact hbs e he
end

mutual
/-- **An empty `by` means quiet.** -/
theorem empty_quiet : ∀ (L b r : Lazy S), lazyLeap p s L = some (b, r) → lazyEmpty b = true → QuietL p s L
  | mk sur fk bd, b, r, h, he => by
    obtain ⟨cut, sb, sr, fs, bs, e1, e2, ef, eb, rfl, -⟩ := lazyLeap_some h
    obtain ⟨hn, hsm, hF, hB⟩ := lazyEmpty_prune.1 he
    exact quietL_mk.2 ⟨empty_quietS e1 e2 hn hsm,
      empty_quiet_forks fk fs ef fun e he => hF _ (List.mem_map_of_mem he),
      empty_quiet_bonds bd bs eb fun e he => hB _ (List.mem_map_of_mem he)⟩

theorem empty_quiet_forks : ∀ (fk : List ((Nat × Lazy S) × (Nat × Lazy S))) fs, leapForks p s fk = some fs →
    (∀ e ∈ fs, lazyEmpty e.1.1.2 = true ∧ lazyEmpty e.1.2.2 = true) → QuietF p s fk
  | [], _, _, _ => by rw [QuietF]; trivial
  | ((oy, y), (on, n)) :: rest, fs, h, he => by
    obtain ⟨yb, yr, nb, nr, rs, ey, en, er, rfl⟩ := leapForks_cons h
    have h0 := he _ List.mem_cons_self
    rw [QuietF]
    exact ⟨⟨empty_quiet y yb yr ey h0.1, empty_quiet n nb nr en h0.2⟩,
      empty_quiet_forks rest rs er fun e h' => he e (List.mem_cons_of_mem _ h')⟩

theorem empty_quiet_bonds : ∀ (bd : List (Nat × Lazy S)) bs, leapBonds p s bd = some bs →
    (∀ e ∈ bs, lazyEmpty e.1.2 = true) → QuietB p s bd
  | [], _, _, _ => by rw [QuietB]; trivial
  | (o, l) :: rest, bs, h, he => by
    obtain ⟨lb, lr, rs, el, er, rfl⟩ := leapBonds_cons h
    rw [QuietB]
    exact ⟨empty_quiet l lb lr el (he _ List.mem_cons_self),
      empty_quiet_bonds rest rs er fun e h' => he e (List.mem_cons_of_mem _ h')⟩
end

mutual
/-- **After a pass at `p`, the rest is quiet at `p`.** -/
theorem quiet_rest : ∀ (L b r : Lazy S), lazyLeap p s L = some (b, r) → QuietL p s r
  | mk sur fk bd, b, r, h => by
    obtain ⟨cut, sb, sr, fs, bs, e1, e2, ef, eb, -, rfl⟩ := lazyLeap_some h
    exact quietL_prune (quietS_rest e1 e2) (quiet_rest_forks fk fs ef) (quiet_rest_bonds bd bs eb)

theorem quiet_rest_forks : ∀ (fk : List ((Nat × Lazy S) × (Nat × Lazy S))) fs, leapForks p s fk = some fs →
    QuietF p s (fs.map Prod.snd)
  | [], fs, h => by rw [leapForks_nil h, List.map_nil, QuietF]; trivial
  | ((oy, y), (on, n)) :: rest, fs, h => by
    obtain ⟨yb, yr, nb, nr, rs, ey, en, er, rfl⟩ := leapForks_cons h
    rw [List.map_cons, QuietF]
    exact ⟨⟨quiet_rest y yb yr ey, quiet_rest n nb nr en⟩, quiet_rest_forks rest rs er⟩

theorem quiet_rest_bonds : ∀ (bd : List (Nat × Lazy S)) bs, leapBonds p s bd = some bs →
    QuietB p s (bs.map Prod.snd)
  | [], bs, h => by rw [leapBonds_nil h, List.map_nil, QuietB]; trivial
  | (o, l) :: rest, bs, h => by
    obtain ⟨lb, lr, rs, el, er, rfl⟩ := leapBonds_cons h
    rw [List.map_cons, QuietB]
    exact ⟨quiet_rest l lb lr el, quiet_rest_bonds rest rs er⟩
end

end

section
variable (p1 s1 p2 s2 : Nat) (hp : p1 ≠ 0)
include hp

mutual
/-- **A pass at `p2` keeps a lazy need quiet at `p1`.** -/
theorem quiet_keep : ∀ (L b r : Lazy S), QuietL p1 s1 L → lazyLeap p2 s2 L = some (b, r) → QuietL p1 s1 r
  | mk sur fk bd, b, r, hc, h => by
    obtain ⟨hs, hf, hb⟩ := quietL_mk.1 hc
    obtain ⟨cut, sb, sr, fs, bs, e1, e2, ef, eb, -, rfl⟩ := lazyLeap_some h
    exact quietL_prune (quietS_keep hp hs e1 e2) (quiet_keep_forks fk fs hf ef) (quiet_keep_bonds bd bs hb eb)

theorem quiet_keep_forks : ∀ (fk : List ((Nat × Lazy S) × (Nat × Lazy S))) fs, QuietF p1 s1 fk →
    leapForks p2 s2 fk = some fs → QuietF p1 s1 (fs.map Prod.snd)
  | [], fs, _, h => by rw [leapForks_nil h, List.map_nil, QuietF]; trivial
  | ((oy, y), (on, n)) :: rest, fs, hc, h => by
    obtain ⟨yb, yr, nb, nr, rs, ey, en, er, rfl⟩ := leapForks_cons h
    rw [QuietF] at hc
    rw [List.map_cons, QuietF]
    exact ⟨⟨quiet_keep y yb yr hc.1.1 ey, quiet_keep n nb nr hc.1.2 en⟩, quiet_keep_forks rest rs hc.2 er⟩

theorem quiet_keep_bonds : ∀ (bd : List (Nat × Lazy S)) bs, QuietB p1 s1 bd →
    leapBonds p2 s2 bd = some bs → QuietB p1 s1 (bs.map Prod.snd)
  | [], bs, _, h => by rw [leapBonds_nil h, List.map_nil, QuietB]; trivial
  | (o, l) :: rest, bs, hc, h => by
    obtain ⟨lb, lr, rs, el, er, rfl⟩ := leapBonds_cons h
    rw [QuietB] at hc
    rw [List.map_cons, QuietB]
    exact ⟨quiet_keep l lb lr hc.1 el, quiet_keep_bonds rest rs hc.2 er⟩
end

end

/-! ## The loop and `+leap` -/

theorem mem_swap {x a : Nat × Nat} {pas done : List (Nat × Nat)} :
    x ∈ pas ++ a :: done ↔ x ∈ (a :: pas) ++ done := by
  simp only [List.mem_append, List.mem_cons]
  constructor
  · rintro (h | h | h)
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
  · rintro ((h | h) | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

/-- **The loop of `+leap` leaves the rest quiet at every pass**, the passes
already done (`done`) and the ones to do, in any order. -/
theorem leapLoop_quiet (sur : Sure S) : ∀ (pas : List (Nat × Nat)) (lab : Lazy S) (bys : List (Lazy S))
    (done : List (Nat × Nat)) (rest : Lazy S) (out : List (Lazy S)),
    (∀ e ∈ pas ++ done, e.1 ≠ 0) → (∀ e ∈ done, QuietL e.1 e.2 lab) →
    leapLoop sur pas lab bys = some (some (rest, out)) →
    ∃ labf : Lazy S, rest = mk sur labf.fork labf.bond ∧ ∀ e ∈ pas ++ done, QuietL e.1 e.2 labf
  | [], lab, bys, done, rest, out, _, hd, h => by
    simp only [leapLoop] at h
    split at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨lab, h.1.symm, by simpa using hd⟩
  | (p, s) :: pas, lab, bys, done, rest, out, hz, hd, h => by
    simp only [leapLoop] at h
    cases e : lazyLeap p s lab with
    | none => simp [e] at h
    | some br =>
      obtain ⟨b, r⟩ := br
      simp only [e, Option.bind_some] at h
      have hz' : ∀ x ∈ pas ++ (p, s) :: done, x.1 ≠ 0 := fun x hx => hz x (mem_swap.1 hx)
      split at h
      · rename_i hb
        obtain ⟨labf, h1, h2⟩ := leapLoop_quiet sur pas lab bys ((p, s) :: done) rest out hz'
          (fun x hx => by
            rcases List.mem_cons.1 hx with rfl | hx
            · exact empty_quiet p s lab b r e hb
            · exact hd x hx) h
        exact ⟨labf, h1, fun x hx => h2 x (mem_swap.2 hx)⟩
      · obtain ⟨labf, h1, h2⟩ := leapLoop_quiet sur pas r (b :: bys) ((p, s) :: done) rest out hz'
          (fun x hx => by
            rcases List.mem_cons.1 hx with rfl | hx
            · exact quiet_rest p s lab b r e
            · exact quiet_keep x.1 x.2 p s (hz x (List.mem_append_right _ hx)) lab b r (hd x hx) e) h
        exact ⟨labf, h1, fun x hx => h2 x (mem_swap.2 hx)⟩

/-- **A second loop on a lazy need quiet at every pass finds nothing.** -/
theorem leapLoop_none (sur : Sure S) : ∀ (pas : List (Nat × Nat)) (lab : Lazy S),
    (∀ e ∈ pas, QuietL e.1 e.2 lab) → leapLoop sur pas lab [] = some Option.none
  | [], lab, _ => by simp [leapLoop]
  | (p, s) :: pas, lab, h => by
    obtain ⟨b, r, e, he⟩ := quiet_empty p s lab (h (p, s) List.mem_cons_self)
    simp only [leapLoop, e, Option.bind_some, he, if_true]
    exact leapLoop_none sur pas lab (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- **`LeapTwice` holds** on any lazy need, when the passes of the branches
have nonzero product axes. -/
theorem leap_twice {laz : Lazy S} {q r : Nomm}
    (hpos : ∀ pas, passBoth q r = some pas → ∀ e ∈ pas, e.1 ≠ 0) : LeapTwice laz q r := by
  intro rest bys h
  unfold leap at h
  split at h
  · cases h
  cases ep : passBoth q r with
  | none => simp [ep] at h
  | some pas =>
    simp only [ep, Option.bind_some] at h
    obtain ⟨labf, rfl, hc⟩ := leapLoop_quiet laz.sure pas _ [] [] rest bys
      (by simpa using hpos pas ep) (by simp) h
    unfold leap
    split
    · rfl
    · rw [ep, Option.bind_some]
      refine leapLoop_none _ pas _ fun e he => ?_
      have := hc e (by simpa using he)
      obtain ⟨sf, fk, bd⟩ := labf
      exact quietL_mk.2 ⟨quietS_bunt _ _, (quietL_mk.1 this).2⟩

end Comp
end SkaModel
end Formalization
