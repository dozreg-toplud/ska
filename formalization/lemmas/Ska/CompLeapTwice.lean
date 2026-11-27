import lemmas.Ska.CompSixFuel
import lemmas.Ska.CompIntoLook

/-!
# `LeapTwice` holds

`+leap` of the rest that `+leap` returned is `~` (`leap_twice`), for any
lazy need and any branches whose passes have nonzero product axes (the
first axis of each pair of `passBoth q r`; `Bake.NoAx0` of the branches
gives it, `CompLeapTwiceRun.lean`).

**The invariant of one round** (`CleanL p s`): in every block of the lazy
need, the part of the sure need at the axis `p` is `%none`, or behind a
register (`+need-cut` gives `~`), and when it is `%none` every look under `p`
goes to `by` as the axis `1` (`CleanS`).  `CleanL p s laz` is exactly what
makes `+lazy-leap p s` give an empty `by` (`clean_quiet`, `quiet_clean`).

- After a pass at `p`, the rest is `CleanL p s` (`clean_rest`): its parts at
  `p` are `%none` (`needCut_rec_clean`) and its looks under `p` are gone.
- A pass at another `p'` keeps `CleanL p s` (`clean_keep`).  On the need
  that is `needCut_keep`; when a part at `p` behind a register comes out
  `%none` (the pass took a part at or above the register), `p` is under
  `p'` (`needCut_open`), so no look under `p` is left either.
- So after the loop the rest is `CleanL` at every pass, whatever their
  order (`leapLoop_clean`), and the second loop finds nothing
  (`leapLoop_quiet`).

`p ≠ 0` is used by `needCut_open` (an axis `0` is under no axis).
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
def CF (x : Option (Option (Need × Need))) : Prop :=
  x = some Option.none ∨ ∃ rec, x = some (some (Need.none, rec))

/-- The part of `ned` at `axe` is `%none`, or behind a register. -/
def CleanN (axe : Nat) (ned : Need) : Prop := CF (needCut axe ned)

theorem needCut_none (axe : Nat) : needCut axe Need.none = some (some (Need.none, Need.none)) := by
  simp [needCut]

theorem cleanN_none (axe : Nat) : CleanN axe Need.none := Or.inr ⟨_, needCut_none axe⟩

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

theorem cf_map (g : Need → Need) (x : Option (Option (Need × Need))) :
    CF (x.map fun k => k.map fun e => (e.1, g e.2)) ↔ CF x := by
  rcases x with _ | _ | ⟨d, c⟩ <;> simp [CF]

theorem map_none (g : Need → Need) (x : Option (Option (Need × Need))) :
    (x.map fun k => k.map fun e => (e.1, g e.2)) = some Option.none ↔ x = some Option.none := by
  rcases x with _ | _ | ⟨d, c⟩ <;> simp

theorem map_some {g : Need → Need} {x : Option (Option (Need × Need))} {d c : Need}
    (h : (x.map fun k => k.map fun e => (e.1, g e.2)) = some (some (d, c))) :
    ∃ c0, x = some (some (d, c0)) ∧ c = g c0 := by
  rcases x with _ | _ | ⟨d0, c0⟩ <;> simp at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨c0, rfl, rfl⟩

theorem cleanN_pair {axe : Nat} (h : 2 ≤ axe) (a b : Need) :
    CleanN axe (Need.pair a b) ↔ if cap axe = 2 then CleanN (mas axe) a else CleanN (mas axe) b := by
  unfold CleanN; rw [needCut_pair h]
  split
  · exact cf_map (fun c => consNeed c b) _
  · exact cf_map (fun c => consNeed a c) _

theorem cleanN_cons {axe : Nat} (h : 2 ≤ axe) (a b : Need)
    (hc : if cap axe = 2 then CleanN (mas axe) a else CleanN (mas axe) b) : CleanN axe (consNeed a b) := by
  unfold consNeed; split
  · exact cleanN_none axe
  · exact (cleanN_pair h a b).2 hc

theorem cleanN_ge2 {axe : Nat} {a b : Need} (h : CleanN axe (Need.pair a b)) : 2 ≤ axe := by
  rcases (by omega : axe = 0 ∨ axe = 1 ∨ 2 ≤ axe) with rfl | rfl | h2
  · rw [CleanN, needCut_pair_zero] at h; simp [CF] at h
  · rw [CleanN, needCut_pair_one] at h; simp [CF] at h
  · exact h2

/-- **After a cut at `axe`, the part at `axe` is `%none`.** -/
theorem needCut_rec_clean : ∀ (ned : Need) (axe : Nat) (don rec : Need),
    needCut axe ned = some (some (don, rec)) → CleanN axe rec := by
  intro ned
  induction ned with
  | none =>
    intro axe don rec h
    rw [needCut_none] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; exact cleanN_none _
  | this r => intro axe don rec h; rw [needCut_this h]; exact cleanN_none _
  | both r a b _ _ => intro axe don rec h; rw [needCut_both h]; exact cleanN_none _
  | pair a b iha ihb =>
    intro axe don rec h
    rcases (by omega : axe = 0 ∨ axe = 1 ∨ 2 ≤ axe) with rfl | rfl | h2
    · rw [needCut_pair_zero] at h; cases h
    · rw [needCut_pair_one] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h; exact cleanN_none _
    · rw [needCut_pair h2] at h
      split at h
      · obtain ⟨c0, e, rfl⟩ := map_some (g := fun c => consNeed c b) h
        exact cleanN_cons h2 _ _ (by rw [if_pos ‹_›]; exact iha _ _ _ e)
      · obtain ⟨c0, e, rfl⟩ := map_some (g := fun c => consNeed a c) h
        exact cleanN_cons h2 _ _ (by rw [if_neg ‹_›]; exact ihb _ _ _ e)

/-- **A cut at `p2` keeps the part at `p1` `%none` or behind a register.** -/
theorem needCut_keep : ∀ (ned : Need) (p1 p2 : Nat) (don rec : Need), CleanN p1 ned →
    needCut p2 ned = some (some (don, rec)) → CleanN p1 rec := by
  intro ned
  induction ned with
  | none =>
    intro p1 p2 don rec _ h
    rw [needCut_none] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; exact cleanN_none _
  | this r => intro p1 p2 don rec _ h; rw [needCut_this h]; exact cleanN_none _
  | both r a b _ _ => intro p1 p2 don rec _ h; rw [needCut_both h]; exact cleanN_none _
  | pair a b iha ihb =>
    intro p1 p2 don rec h1 h
    rcases (by omega : p2 = 0 ∨ p2 = 1 ∨ 2 ≤ p2) with rfl | rfl | h2
    · rw [needCut_pair_zero] at h; cases h
    · rw [needCut_pair_one] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h; exact cleanN_none _
    · have hp1 := cleanN_ge2 h1
      rw [cleanN_pair hp1] at h1
      rw [needCut_pair h2] at h
      split at h
      · obtain ⟨c0, e, rfl⟩ := map_some (g := fun c => consNeed c b) h
        refine cleanN_cons hp1 _ _ ?_
        split
        · rw [if_pos ‹_›] at h1; exact iha _ _ _ _ h1 e
        · rw [if_neg ‹_›] at h1; exact h1
      · obtain ⟨c0, e, rfl⟩ := map_some (g := fun c => consNeed a c) h
        refine cleanN_cons hp1 _ _ ?_
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
      · obtain ⟨c0, e, rfl⟩ := map_some (g := fun c => consNeed c b) h
        split at h1
        · have h1' := (map_none (fun c => consNeed c b) _).1 h1
          have h4 : needCut (mas p1) c0 ≠ some Option.none := by
            intro e4; apply h3
            unfold consNeed; split
            · rename_i hn; rw [hn.1, needCut_none] at e4; simp at e4
            · rw [needCut_pair hp1, if_pos ‹_›, e4]; rfl
          obtain ⟨k, hk⟩ := iha _ _ _ _ (by have := mas_pos p1 hp1; omega) h1' e h4
          exact ⟨k, mas_div k p1 p2 hp1 h2 (by omega) hk⟩
        · have h1' := (map_none (fun c => consNeed a c) _).1 h1
          have hb : b ≠ Need.none := by intro hb; rw [hb, needCut_none] at h1'; simp at h1'
          exfalso; apply h3
          unfold consNeed; rw [if_neg (fun hh => hb hh.2), needCut_pair hp1, if_neg ‹_›, h1']; rfl
      · obtain ⟨c0, e, rfl⟩ := map_some (g := fun c => consNeed a c) h
        split at h1
        · have h1' := (map_none (fun c => consNeed c b) _).1 h1
          have ha : a ≠ Need.none := by intro ha; rw [ha, needCut_none] at h1'; simp at h1'
          exfalso; apply h3
          unfold consNeed; rw [if_neg (fun hh => ha hh.1), needCut_pair hp1, if_pos ‹_›, h1']; rfl
        · have h1' := (map_none (fun c => consNeed a c) _).1 h1
          have h4 : needCut (mas p1) c0 ≠ some Option.none := by
            intro e4; apply h3
            unfold consNeed; split
            · rename_i hn; rw [hn.2, needCut_none] at e4; simp at e4
            · rw [needCut_pair hp1, if_neg ‹_›, e4]; rfl
          obtain ⟨k, hk⟩ := ihb _ _ _ _ (by have := mas_pos p1 hp1; omega) h1' e h4
          exact ⟨k, mas_div k p1 p2 hp1 h2 (by omega) hk⟩

end Comp
end SkaModel
end Formalization
