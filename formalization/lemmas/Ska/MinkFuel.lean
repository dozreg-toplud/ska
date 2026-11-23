import lemmas.Ska.FolLoopFacts

/-!
# What `+mink` returns, taken apart with its fuel

The lemmas `mink_inv_*` of `FolLoopFacts.lean` forget the fuel.  Here a run
of `+mink` with fuel `k + 1` that returns `%0` is taken apart into runs of its
parts with fuel `k`.  For Nock 2 this says that the callee runs with less fuel
than the call, which is what an induction on the runs of `+mink` needs: the
product soundness of the entries of a call graph is proved for runs with fuel
`k + 1` from the same for runs with fuel `k` (`ConvergeProd.lean`).
-/

namespace Formalization
namespace SkaModel

open Nock

section MinkFuel

variable {lib : Lib} {gul : Noun}

/-- A run with fuel `k` is a run with fuel `k + 1`. -/
theorem minkF_up {k : Nat} {x f : Noun} {r : Tone} (h : minkF lib gul k [] x f = some r) :
    minkF lib gul (k + 1) [] x f = some r :=
  minkF_lift (Nat.le_succ k) h

/-- A run that returns has some fuel. -/
theorem minkF_pos {k : Nat} {t : Trace} {x f : Noun} {r : Tone} (h : minkF lib gul k t x f = some r) :
    1 ≤ k := by
  cases k with
  | zero => simp [minkF] at h
  | succ k => omega

theorem minkF_inv_cons {k : Nat} {x a b q p : Noun}
    (h : minkF lib gul (k + 1) [] x (C (C a b) q) = some (Tone.zero p)) :
    ∃ p1 p2, p = C p1 p2 ∧ minkF lib gul k [] x (C a b) = some (Tone.zero p1) ∧
      minkF lib gul k [] x q = some (Tone.zero p2) := by
  rw [minkF_succ_eq] at h
  simp only [minkStep] at h
  obtain ⟨p1, h1, h⟩ := tbind_zero_inv h
  obtain ⟨p2, h2, h⟩ := tbind_zero_inv h
  cases h
  exact ⟨p1, p2, rfl, h1, h2⟩

theorem minkF_inv_n0 {k : Nat} {x p : Noun} {ax : Nat}
    (h : minkF lib gul (k + 1) [] x (C (A 0) (A ax)) = some (Tone.zero p)) : slot? ax x = some p :=
  mink_inv_n0 ⟨_, h⟩

theorem minkF_inv_n1 {k : Nat} {x q p : Noun}
    (h : minkF lib gul (k + 1) [] x (C (A 1) q) = some (Tone.zero p)) : p = q :=
  mink_inv_n1 ⟨_, h⟩

/-- **Nock 2 with fuel**: the subject and the formula with fuel `k`, and the
callee with fuel `k`, one less than the call. -/
theorem minkF_inv_n2 {k : Nat} {x b c p : Noun}
    (h : minkF lib gul (k + 1) [] x (n3 (A 2) b c) = some (Tone.zero p)) :
    ∃ y g, minkF lib gul k [] x b = some (Tone.zero y) ∧ minkF lib gul k [] x c = some (Tone.zero g) ∧
      minkF lib gul k [] y g = some (Tone.zero p) := by
  rw [minkF_succ_eq] at h
  simp only [minkStep] at h
  obtain ⟨y, h1, h⟩ := tbind_zero_inv h
  obtain ⟨g, h2, h⟩ := tbind_zero_inv h
  exact ⟨y, g, h1, h2, h⟩

theorem minkF_inv_n6 {k : Nat} {x b c d p : Noun}
    (h : minkF lib gul (k + 1) [] x (n4 (A 6) b c d) = some (Tone.zero p)) :
    minkF lib gul k [] x c = some (Tone.zero p) ∨ minkF lib gul k [] x d = some (Tone.zero p) := by
  rw [minkF_succ_eq] at h
  simp only [minkStep] at h
  obtain ⟨t, _, h⟩ := tbind_zero_inv h
  match t, h with
  | Noun.atom 0, h => exact Or.inl h
  | Noun.atom 1, h => exact Or.inr h
  | Noun.atom (_ + 2), h => simp at h
  | Noun.cell _ _, h => simp at h

theorem minkF_inv_n7 {k : Nat} {x b c p : Noun}
    (h : minkF lib gul (k + 1) [] x (n3 (A 7) b c) = some (Tone.zero p)) :
    ∃ y, minkF lib gul k [] x b = some (Tone.zero y) ∧ minkF lib gul k [] y c = some (Tone.zero p) := by
  rw [minkF_succ_eq] at h
  simp only [minkStep] at h
  obtain ⟨y, h1, h⟩ := tbind_zero_inv h
  exact ⟨y, h1, h⟩

theorem minkF_inv_n8 {k : Nat} {x b c p : Noun}
    (h : minkF lib gul (k + 1) [] x (n3 (A 8) b c) = some (Tone.zero p)) :
    ∃ y, minkF lib gul k [] x b = some (Tone.zero y) ∧ minkF lib gul k [] (C y x) c = some (Tone.zero p) := by
  rw [minkF_succ_eq] at h
  simp only [minkStep] at h
  obtain ⟨y, h1, h⟩ := tbind_zero_inv h
  exact ⟨y, h1, h⟩

theorem minkF_inv_n9 {k : Nat} {x c p : Noun} {ax : Nat}
    (h : minkF lib gul (k + 1) [] x (n3 (A 9) (A ax) c) = some (Tone.zero p)) :
    ∃ core arm, minkF lib gul k [] x c = some (Tone.zero core) ∧ slot? ax core = some arm ∧
      minkF lib gul k [] core arm = some (Tone.zero p) := by
  rw [minkF_succ_eq] at h
  simp only [minkStep] at h
  obtain ⟨core, h1, h⟩ := tbind_zero_inv h
  revert h
  cases hs : slot? ax core with
  | none => simp
  | some arm => intro h; exact ⟨core, arm, h1, hs, h⟩

theorem minkF_inv_n10 {k : Nat} {x v t p : Noun} {ax : Nat}
    (h : minkF lib gul (k + 1) [] x (n3 (A 10) (n2 (A ax) v) t) = some (Tone.zero p)) :
    ∃ tg vv, minkF lib gul k [] x t = some (Tone.zero tg) ∧ minkF lib gul k [] x v = some (Tone.zero vv) ∧
      edit? ax vv tg = some p := by
  rw [minkF_succ_eq] at h
  simp only [minkStep] at h
  split at h
  · simp at h
  · obtain ⟨tg, h1, h⟩ := tbind_zero_inv h
    obtain ⟨vv, h2, h⟩ := tbind_zero_inv h
    revert h
    cases he : edit? ax vv tg with
    | none => simp
    | some r =>
      simp only [Option.some.injEq, Tone.zero.injEq]
      intro hr; subst hr
      exact ⟨tg, vv, h1, h2, he⟩

theorem minkF_inv_n11s {k : Nat} {x q p : Noun} {tag : Nat}
    (h : minkF lib gul (k + 1) [] x (n3 (A 11) (A tag) q) = some (Tone.zero p)) :
    minkF lib gul k [] x q = some (Tone.zero p) := by
  rw [minkF_succ_eq] at h
  simp only [minkStep] at h
  obtain ⟨y, h1, h⟩ := tbind_zero_inv h
  cases h
  exact h1

theorem minkF_inv_n11d {k : Nat} {x h f p : Noun} {tag : Nat}
    (hm : minkF lib gul (k + 1) [] x (n3 (A 11) (C (A tag) h) f) = some (Tone.zero p)) :
    (∃ c, minkF lib gul k [] x h = some (Tone.zero c)) ∧ minkF lib gul k [] x f = some (Tone.zero p) := by
  rw [minkF_succ_eq] at hm
  simp only [minkStep] at hm
  obtain ⟨c, h1, hm⟩ := tbind_zero_inv hm
  obtain ⟨y, h2, hm⟩ := tbind_zero_inv hm
  cases hm
  exact ⟨⟨c, h1⟩, mink_nil_of_zero h2⟩

/-! ## Put together with its fuel -/

/-- `[2 [0 1] [0 ax]]` on a core runs its arm, with one more level. -/
theorem minkF_mk_arm {k : Nat} {core arm p : Noun} {ax : Nat} (hs : slot? ax core = some arm)
    (h : minkF lib gul k [] core arm = some (Tone.zero p)) :
    minkF lib gul (k + 1) [] core (n3 (A 2) (slot 1) (slot ax)) = some (Tone.zero p) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := minkF_pos h; omega⟩
  rw [minkF_succ_eq]
  simp only [minkStep]
  rw [show minkF lib gul (j + 1) [] core (slot 1) = some (Tone.zero core) by
        rw [minkF_succ_eq]; simp [minkStep, slot],
      tbind_zero,
      show minkF lib gul (j + 1) [] core (slot ax) = some (Tone.zero arm) by
        rw [minkF_succ_eq]; simp [minkStep, slot, hs],
      tbind_zero]
  exact h

/-- `[2 [0 1] [1 f]]` runs `f` on the same subject, with one more level. -/
theorem minkF_mk_self {k : Nat} {x f p : Noun} (h : minkF lib gul k [] x f = some (Tone.zero p)) :
    minkF lib gul (k + 1) [] x (n3 (A 2) (slot 1) (quote f)) = some (Tone.zero p) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := minkF_pos h; omega⟩
  rw [minkF_succ_eq]
  simp only [minkStep]
  rw [show minkF lib gul (j + 1) [] x (slot 1) = some (Tone.zero x) by
        rw [minkF_succ_eq]; simp [minkStep, slot],
      tbind_zero, show minkF lib gul (j + 1) [] x (quote f) = some (Tone.zero f) from rfl, tbind_zero]
  exact h

end MinkFuel

end SkaModel
end Formalization
