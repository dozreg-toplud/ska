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
* `dif_has`: `+dif:ca`, where it does not crash, is the difference.
* `lack_has`: `+lack:ca` keeps only paths of `a` that `b` lacks (it drops
  the root of a `&` split against a cell, so it is not the whole difference).
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

/-- **`+dif:ca` is the difference**, where it does not crash. -/
theorem dif_has : ∀ (a b c : Cape), Ca.dif a b = some c →
    ∀ p, c.Has p ↔ a.Has p ∧ ¬ b.Has p := by
  intro a
  induction a with
  | yes =>
    intro b c h p
    unfold Ca.dif at h
    split at h
    · rename_i he; subst he; simp only [Option.some.injEq] at h; subst h; simp [Cape.Has]
    · rename_i hne
      cases b with
      | yes => exact absurd rfl hne
      | no => simp only [Option.some.injEq] at h; subst h; simp [Cape.Has]
      | cell _ _ => simp at h
  | no =>
    intro b c h p
    unfold Ca.dif at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; simp [Cape.Has]
    · cases b <;> simp only [Option.some.injEq] at h <;> subst h <;> simp [Cape.Has]
  | cell ah aT ih1 ih2 =>
    intro b c h p
    unfold Ca.dif at h
    split at h
    · rename_i he; subst he; simp only [Option.some.injEq] at h; subst h; simp [Cape.Has]
    · cases b with
      | yes => simp only [Option.some.injEq] at h; subst h; simp [Cape.Has]
      | no => simp only [Option.some.injEq] at h; subst h; simp [Cape.Has]
      | cell bh bT =>
        simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
        obtain ⟨l, hl, r, hr, rfl⟩ := h
        rw [con_has]
        cases p with
        | nil => simp [Cape.Has]
        | cons x q => cases x <;> simp [Cape.Has, ih1 _ _ hl, ih2 _ _ hr]

theorem lack_has_yes : ∀ (b : Cape) (p : List Bool), (Ca.lack Cape.yes b).Has p → ¬ b.Has p := by
  intro b
  induction b with
  | yes => intro p h; simp [Ca.lack, Cape.Has] at h
  | no => intro p _; simp [Cape.Has]
  | cell bh bT ih1 ih2 =>
    intro p h
    simp only [Ca.lack, reduceCtorEq, if_false, Ca.hed, Ca.tel] at h
    rw [con_has] at h
    cases p with
    | nil => simp [Cape.Has] at h
    | cons x q => cases x <;> simp only [Cape.Has] at h ⊢ <;> first | exact ih1 _ h | exact ih2 _ h

/-- **`+lack:ca` keeps only paths of `a` that `b` lacks.** -/
theorem lack_has : ∀ (a b : Cape) (p : List Bool), (Ca.lack a b).Has p → a.Has p ∧ ¬ b.Has p := by
  intro a
  induction a with
  | yes =>
    intro b p h
    exact ⟨trivial, lack_has_yes b p h⟩
  | no => intro b p h; simp [Ca.lack, Cape.Has] at h
  | cell ah aT ih1 ih2 =>
    intro b p h
    cases b with
    | yes => simp [Ca.lack, Cape.Has] at h
    | no => simp only [Ca.lack] at h; exact ⟨h, by simp [Cape.Has]⟩
    | cell bh bT =>
      simp only [Ca.lack] at h
      split at h
      · simp [Cape.Has] at h
      · rw [con_has] at h
        simp only [Ca.hed, Ca.tel] at h
        cases p with
        | nil => simp [Cape.Has] at h
        | cons x q =>
          cases x
          · exact ih1 bh q h
          · exact ih2 bT q h

end SkaModel
end Formalization
