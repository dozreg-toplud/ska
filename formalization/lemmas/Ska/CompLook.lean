import lemmas.Ska.CompRun

/-!
# `+sure-require-look`

The need that `+sure-require-look` makes of a `sure`: the sure need with a
register for every looked-at axis it does not reach.  It holds a noun
exactly where the sure need does and the noun has the looked-at axes
(`sureRequireLook_spec`).
-/

set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- What one step of `+sure-require-look` does. -/
structure LookOK (ned : Need) (axe : Nat) (g0 g1 : Gen Map) (ned' : Need) : Prop where
  gen : ∃ k, g1 = { g0 with re := k }
  le : g0.re ≤ g1.re
  holds : ∀ (regs : Map Noun) n, HoldsN ned' regs n → HoldsN ned regs n
  fits : ∀ n, Fits ned' n ↔ Fits ned n ∧ (slot? axe n).isSome
  mem : ∀ r, NMem ned' r → NMem ned r ∨ (g0.re ≤ r ∧ r < g1.re)
  dist : Distinct ned → (∀ r, NMem ned r → r < g0.re) → Distinct ned'
  shape : 2 ≤ axe → (∃ p q, ned' = Need.pair p q) ∨ (∃ r p q, ned' = Need.both r p q)
  one : axe = 1 → ned' = ned ∨ (ned = Need.none ∧ ∃ r, ned' = Need.this r)

theorem lookPath_step (ned : Need) {axe : Nat} (h2 : 2 ≤ axe) :
    lookPath ned axe = (if cap axe = 2 then do
        let x ← lookPath (split3 ned).2.1 (mas axe)
        pure (wrapN (split3 ned).1 (consNeed x (split3 ned).2.2))
      else do
        let x ← lookPath (split3 ned).2.2 (mas axe)
        pure (wrapN (split3 ned).1 (consNeed (split3 ned).2.1 x)) : CM Map Need) := by
  rw [lookPath.eq_def]
  simp only [show ¬ axe ≤ 1 by omega, dif_neg, not_false_eq_true]

theorem consNeed_holds {a b : Need} (h : ¬ (a = Need.none ∧ b = Need.none)) (regs : Map Noun) (n : Noun) :
    HoldsN (consNeed a b) regs n ↔ HoldsN (Need.pair a b) regs n := by
  simp [consNeed, h]

theorem wrap_holds (here : Option Nat) {x : Need} (hx : ∃ p q, x = Need.pair p q) (regs : Map Noun) (n : Noun) :
    HoldsN (wrapN here x) regs n ↔ (∀ r, here = some r → SkaModel.read r regs = some n) ∧ HoldsN x regs n := by
  obtain ⟨p, q, rfl⟩ := hx
  cases here with
  | none => simp [wrapN]
  | some r => cases n <;> simp [wrapN, HoldsN]

theorem wrap_fits (here : Option Nat) {x : Need} (hx : ∃ p q, x = Need.pair p q) (n : Noun) :
    Fits (wrapN here x) n ↔ Fits x n := by
  obtain ⟨p, q, rfl⟩ := hx
  cases here with
  | none => simp [wrapN]
  | some r => cases n <;> simp [wrapN, Fits]

theorem wrap_mem (here : Option Nat) {x : Need} (hx : ∃ p q, x = Need.pair p q) (r : Nat) :
    NMem (wrapN here x) r ↔ here = some r ∨ NMem x r := by
  obtain ⟨p, q, rfl⟩ := hx
  cases here with
  | none => simp [wrapN]
  | some r' => simp [wrapN, NMem, eq_comm]

theorem split3_holds : ∀ (ned : Need) (regs : Map Noun) (a b : Noun),
    (∀ r, (split3 ned).1 = some r → SkaModel.read r regs = some (C a b)) →
    HoldsN (split3 ned).2.1 regs a → HoldsN (split3 ned).2.2 regs b → HoldsN ned regs (C a b)
  | Need.none, _, _, _, _, _, _ => trivial
  | Need.this r, _, _, _, h, _, _ => h r rfl
  | Need.pair p q, _, _, _, _, ha, hb => ⟨ha, hb⟩
  | Need.both r p q, _, _, _, h, ha, hb => ⟨h r rfl, ha, hb⟩

theorem split3_fits : ∀ (ned : Need) (a b : Noun),
    Fits ned (C a b) ↔ Fits (split3 ned).2.1 a ∧ Fits (split3 ned).2.2 b
  | Need.none, _, _ => by simp [Fits, split3]
  | Need.this r, _, _ => by simp [Fits, split3]
  | Need.pair p q, _, _ => by simp [Fits, split3]
  | Need.both r p q, _, _ => by simp [Fits, split3]

theorem split3_mem : ∀ (ned : Need) (r : Nat),
    NMem ned r ↔ (split3 ned).1 = some r ∨ NMem (split3 ned).2.1 r ∨ NMem (split3 ned).2.2 r
  | Need.none, _ => by simp [NMem, split3]
  | Need.this r, _ => by simp [NMem, split3, eq_comm]
  | Need.pair p q, _ => by simp [NMem, split3]
  | Need.both r p q, _ => by simp [NMem, split3, eq_comm]

theorem split3_dist : ∀ (ned : Need), Distinct ned →
    Distinct (split3 ned).2.1 ∧ Distinct (split3 ned).2.2 ∧
    (∀ x, NMem (split3 ned).2.1 x → ¬ NMem (split3 ned).2.2 x) ∧
    ∀ r, (split3 ned).1 = some r → ¬ NMem (split3 ned).2.1 r ∧ ¬ NMem (split3 ned).2.2 r
  | Need.none, _ => by simp [split3, Distinct, NMem]
  | Need.this r, _ => by simp [split3, Distinct, NMem]
  | Need.pair p q, h => by simp only [split3, Distinct] at h ⊢; exact ⟨h.1, h.2.1, h.2.2, by simp⟩
  | Need.both r p q, h => by
    simp only [split3, Distinct] at h ⊢
    exact ⟨h.1, h.2.1, h.2.2.1, fun r' e => by cases e; exact ⟨h.2.2.2.1, h.2.2.2.2⟩⟩

theorem lookPath_ne_none : ∀ (axe : Nat), 1 ≤ axe → ∀ (ned ned' : Need) (g0 g1 : Gen Map),
    lookPath ned axe g0 = some (ned', g1) → ned' ≠ Need.none := by
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
  intro ha ned ned' g0 g1 h
  by_cases h1 : axe ≤ 1
  · rw [lookPath.eq_def] at h
    simp only [h1, dif_pos] at h
    cases ned <;> simp [bind_apply, re_apply, pure_apply] at h <;> (obtain ⟨rfl, _⟩ := h) <;> simp
  · rw [lookPath_step ned (by omega)] at h
    have ihm := ih (mas axe) (mas_lt axe (by omega)) (mas_pos axe (by omega))
    have fin : ∀ (here : Option Nat) (a b : Need), (a ≠ Need.none ∨ b ≠ Need.none) →
        wrapN here (consNeed a b) ≠ Need.none := by
      intro here a b hab
      have : consNeed a b = Need.pair a b := by
        unfold consNeed; rw [if_neg]; rintro ⟨h1, h2⟩; rcases hab with h | h <;> contradiction
      rw [this]; cases here <;> simp [wrapN]
    split at h
    · obtain ⟨x, g, h5, h6⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h6
      rw [← h6.1]; exact fin _ _ _ (Or.inl (ihm _ x g0 g h5))
    · obtain ⟨x, g, h5, h6⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h6
      rw [← h6.1]; exact fin _ _ _ (Or.inr (ihm _ x g0 g h5))

end Comp
end SkaModel
end Formalization
