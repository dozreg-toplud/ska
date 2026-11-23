import lemmas.Ska.SockFacts

/-!
# What the operations on capes mean

A cape, read as a mask, is a set of paths: those that end inside a `&` leaf
(`Cape.Has`).  A cell of capes does not have the empty path, even `[& &]`:
the analysis keeps `[& &]` apart from `&`.  On that reading:

* `int_has`: `+int:ca` is the intersection.
* `uni_has`: `+uni:ca` is the union.
* `con_has`: `+con:ca` is the cons.
* `patLoop_has`: `+pat:ca` puts a cape under an axis.
* `lotLoop_has`: `+lot:ca` takes the cape under an axis.
-/

namespace Formalization
namespace SkaModel

open Nock

/-- The path `p` (from the root, `false` for the head) ends inside a `&`
leaf of the cape. -/
def Cape.Has : Cape → List Bool → Prop
  | Cape.yes, _ => True
  | Cape.no, _ => False
  | Cape.cell _ _, [] => False
  | Cape.cell h _, false :: p => h.Has p
  | Cape.cell _ t, true :: p => t.Has p

theorem con_has (h t : Cape) (p : List Bool) : (Ca.con h t).Has p ↔ (Cape.cell h t).Has p := by
  unfold Ca.con
  split
  · rename_i hn
    obtain ⟨rfl, rfl⟩ := hn
    cases p with
    | nil => simp [Cape.Has]
    | cons b q => cases b <;> simp [Cape.Has]
  · rfl

/-- **`+int:ca` is the intersection.** -/
theorem int_has : ∀ (a b : Cape) (p : List Bool), (Ca.int a b).Has p ↔ a.Has p ∧ b.Has p := by
  intro a
  induction a with
  | yes =>
    intro b p; unfold Ca.int; split
    · rename_i he; subst he; simp [Cape.Has]
    · simp [Cape.Has]
  | no => intro b p; unfold Ca.int; split <;> simp_all [Cape.Has]
  | cell ah aT ih1 ih2 =>
    intro b p
    unfold Ca.int
    split
    · rename_i he; subst he; simp
    · cases b with
      | yes => simp [Cape.Has]
      | no => simp [Cape.Has]
      | cell bh bT =>
        simp only
        rw [con_has]
        cases p with
        | nil => simp [Cape.Has]
        | cons x q => cases x <;> simp [Cape.Has, ih1, ih2]

/-- **`+uni:ca` is the union.** -/
theorem uni_has : ∀ (a b : Cape) (p : List Bool), (Ca.uni a b).Has p ↔ a.Has p ∨ b.Has p := by
  intro a
  induction a with
  | yes => intro b p; unfold Ca.uni; split <;> simp_all [Cape.Has]
  | no =>
    intro b p; unfold Ca.uni; split
    · rename_i he; subst he; simp [Cape.Has]
    · simp [Cape.Has]
  | cell ah aT ih1 ih2 =>
    intro b p
    unfold Ca.uni
    split
    · rename_i he; subst he; simp
    · cases b with
      | yes => simp [Cape.Has]
      | no => simp [Cape.Has]
      | cell bh bT =>
        simp only
        rw [con_has]
        cases p with
        | nil => simp [Cape.Has]
        | cons x q => cases x <;> simp [Cape.Has, ih1, ih2]

/-- **`+pat:ca` puts the cape `c` at the axis `a`**: the paths of the result
are the path of the axis followed by a path of `c`. -/
theorem patLoop_has : ∀ (a : Nat) (c : Cape) (q : List Bool), 1 ≤ a → axisPath a = some q →
    ∀ p, (Ca.patLoop c a).Has p ↔ ∃ r, p = q ++ r ∧ c.Has r := by
  intro a
  induction a using Nat.strongRecOn with
  | _ a ih =>
  intro c q h1 hq p
  rw [Ca.patLoop.eq_def]
  split
  · have : a = 1 := by omega
    subst this
    simp only [axisPath_one, Option.some.injEq] at hq
    subst hq
    simp
  · rename_i hax
    have h2 : 2 ≤ a := by omega
    rw [axisPath_cap a h2] at hq
    obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
    have ih' := ih (mas a) (mas_lt a h2) c q' (mas_pos a h2) hq'
    rcases cap_cases a h2 with hc | hc
    · rw [if_pos hc]
      simp only [hc]
      cases p with
      | nil => simp [Cape.Has]
      | cons x p =>
        cases x with
        | false => simp [Cape.Has, ih']
        | true => simp [Cape.Has]
    · rw [if_neg (by omega)]
      simp only [hc, decide_true]
      cases p with
      | nil => simp [Cape.Has]
      | cons x p =>
        cases x with
        | false => simp [Cape.Has]
        | true => simp [Cape.Has, ih']

/-- **`+lot:ca` takes the cape at the axis `a`.** -/
theorem lotLoop_has : ∀ (a : Nat) (c : Cape) (q : List Bool), 1 ≤ a → axisPath a = some q →
    ∀ r, (Ca.lot.lotLoop c a).Has r ↔ c.Has (q ++ r) := by
  intro a
  induction a using Nat.strongRecOn with
  | _ a ih =>
  intro c q h1 hq r
  rw [Ca.lot.lotLoop.eq_def]
  split
  · have : a = 1 := by omega
    subst this
    simp only [axisPath_one, Option.some.injEq] at hq
    subst hq
    simp
  · rename_i hax
    have h2 : 2 ≤ a := by omega
    rw [axisPath_cap a h2] at hq
    obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
    have ih' := fun c => ih (mas a) (mas_lt a h2) c q' (mas_pos a h2) hq'
    cases c with
    | yes => simp [Cape.Has]
    | no => simp [Cape.Has]
    | cell ch ct =>
      simp only
      rcases cap_cases a h2 with hc | hc
      · rw [if_pos hc, ih']; simp [hc, Cape.Has]
      · rw [if_neg (by omega), ih']; simp [hc, Cape.Has]

end SkaModel
end Formalization
