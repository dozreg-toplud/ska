import lemmas.Ska.CompCons

/-!
# The looks of `+into-sure`

`+into-sure` sorts the looked-at axes of the edited noun with `+gep`: an
axis under the edited axis `axe` becomes an axis of the donor, any other
stays an axis of the recipient, and `axe` itself is added to the recipient's
looks.  `intoLok_looks`: when the edit succeeds, the edited noun has the
looks exactly when the donor and the recipient have theirs.

* `gep_some`, `gep_none`: what `+gep` computes, as `+peg` and as "`b` is no
  axis under `a`" (`∀ k, b / 2 ^ k ≠ a`).
* `slot_edit_off`: an axis that is not under the edited one is there in the
  edited noun exactly when it is there in the recipient.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-! ## `+gep` -/

theorem metF_two (x : Nat) (h : 0 < x) : Hoon.metF 0 x = Hoon.metF 0 (x / 2) + 1 := by
  rw [Hoon.metF_pos 0 x h]

theorem metF_div_pow : ∀ (k x : Nat), 1 ≤ x / 2 ^ k → Hoon.metF 0 x = Hoon.metF 0 (x / 2 ^ k) + k := by
  intro k
  induction k with
  | zero => intro x _; simp
  | succ k ih =>
    intro x hx
    have e : x / 2 ^ (k + 1) = x / 2 / 2 ^ k := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]
    rw [e] at hx ⊢
    have h2 : 1 ≤ x / 2 := by
      rcases Nat.eq_zero_or_pos (x / 2) with h | h
      · rw [h, Nat.zero_div] at hx; omega
      · exact h
    rw [metF_two x (by omega), ih (x / 2) hx]
    omega

theorem pegF_pow : ∀ (a d m : Nat), m < 2 ^ d → Hoon.pegF a (2 ^ d + m) = a * 2 ^ d + m := by
  intro a d
  induction d with
  | zero => intro m hm; simp at hm; subst hm; rw [Hoon.pegF_eq]; simp
  | succ d ih =>
    intro m hm
    have p2 : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [Nat.pow_succ, Nat.mul_comm]
    have pp : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    rw [Hoon.pegF_eq]
    by_cases h2 : 2 ^ (d + 1) + m = 2
    · have d0 : d = 0 := by
        rcases Nat.eq_zero_or_pos d with h | h
        · exact h
        · have : 2 ≤ 2 ^ d := by
            have := Nat.pow_le_pow_right (show 0 < 2 by decide) h; simpa using this
          omega
      subst d0
      have : m = 0 := by simp at h2; omega
      subst this; simp
    by_cases h3 : 2 ^ (d + 1) + m = 3
    · have d0 : d = 0 := by
        rcases Nat.eq_zero_or_pos d with h | h
        · exact h
        · have : 2 ≤ 2 ^ d := by
            have := Nat.pow_le_pow_right (show 0 < 2 by decide) h; simpa using this
          omega
      subst d0
      have : m = 1 := by simp at h3; omega
      subst this; simp
    rw [if_neg (by omega), if_neg h2, if_neg h3, if_neg (by omega)]
    have e1 : (2 ^ (d + 1) + m) / 2 = 2 ^ d + m / 2 := by omega
    have e2 : (2 ^ (d + 1) + m) % 2 = m % 2 := by omega
    rw [e1, e2, ih (m / 2) (by omega), p2]
    have : a * (2 * 2 ^ d) = a * 2 ^ d * 2 := by rw [Nat.mul_comm 2, Nat.mul_assoc]
    rw [this]
    omega

theorem gep_crash {a b : Nat} : gep a b = Option.none ↔ a = 0 ∨ b = 0 := by
  unfold gep
  by_cases a0 : a = 0
  · simp [a0]
  by_cases b0 : b = 0
  · simp [b0]
  simp only [a0, b0, if_false, or_self, iff_false]
  split
  · simp
  split
  · simp
  split <;> simp

/-- An answer `[~ r]` of `+gep`: `b` is the axis `r` of the axis `a`. -/
theorem gep_some {a b r : Nat} (h : gep a b = some (some r)) :
    1 ≤ a ∧ 1 ≤ r ∧ b = Hoon.pegF a r ∧ (r = 1 → b = a) := by
  unfold gep at h
  by_cases a0 : a = 0
  · simp [a0] at h
  by_cases b0 : b = 0
  · simp [b0] at h
  simp only [a0, b0, if_false] at h
  by_cases ab : a = b
  · simp only [ab, if_true, Option.some.injEq] at h
    subst h; subst ab
    refine ⟨by omega, Nat.le_refl _, ?_, fun _ => rfl⟩
    rw [Hoon.pegF_eq]; simp
  rw [if_neg ab] at h
  by_cases ba : b < a
  · simp [ba] at h
  rw [if_neg ba] at h
  generalize hd : Hoon.metF 0 b - Hoon.metF 0 a = d at h
  by_cases ht : b / 2 ^ d ≠ a
  · simp [ht] at h
  simp only [ht, if_false, Option.some.injEq] at h
  simp only [ne_eq, Decidable.not_not] at ht
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.or_comm] at h
  have hm : b % 2 ^ d < 2 ^ d := Nat.mod_lt _ (Nat.two_pow_pos d)
  have e := Nat.two_pow_add_eq_or_of_lt hm 1
  rw [Nat.mul_one] at e
  rw [← e] at h
  subst h
  refine ⟨by omega, by have := Nat.two_pow_pos d; omega, ?_, fun h1 => ?_⟩
  · rw [pegF_pow a d _ hm, ← ht, Nat.mul_comm]
    exact (Nat.div_add_mod b (2 ^ d)).symm
  · have : 2 ^ d = 1 := by omega
    have d0 : d = 0 := by
      rcases Nat.eq_zero_or_pos d with h | h
      · exact h
      · have := Nat.pow_le_pow_right (show 0 < 2 by decide) h; simp at this; omega
    subst d0; simp at ht; exact ht

/-- An answer `~` of `+gep`: `b` is not under `a`. -/
theorem gep_none {a b : Nat} (h : gep a b = some Option.none) : ∀ k, b / 2 ^ k ≠ a := by
  unfold gep at h
  by_cases a0 : a = 0
  · simp [a0] at h
  by_cases b0 : b = 0
  · simp [b0] at h
  simp only [a0, b0, if_false] at h
  by_cases ab : a = b
  · simp [ab] at h
  rw [if_neg ab] at h
  intro k hk
  by_cases ba : b < a
  · have : b / 2 ^ k ≤ b := Nat.div_le_self _ _
    omega
  rw [if_neg ba] at h
  have hm := metF_div_pow k b (by omega)
  rw [hk] at hm
  have hd : Hoon.metF 0 b - Hoon.metF 0 a = k := by omega
  rw [hd, hk] at h
  simp at h

/-! ## Paths -/

theorem axisPath_two {x : Nat} (hx : 2 ≤ x) {p : List Bool} (h : axisPath x = some p) :
    ∃ p', axisPath (x / 2) = some p' ∧ p = p' ++ [decide (x % 2 = 1)] := by
  rw [axisPath_step x hx] at h
  obtain ⟨p', h1, h2⟩ := Option.map_eq_some_iff.mp h
  exact ⟨p', h1, h2.symm⟩

theorem axisPath_nil {x : Nat} (h : axisPath x = some []) : x = 1 := by
  rcases Nat.lt_or_ge x 2 with hx | hx
  · rcases (show x = 0 ∨ x = 1 by omega) with rfl | rfl
    · simp [axisPath_zero] at h
    · rfl
  · obtain ⟨p', _, e⟩ := axisPath_two hx h
    simp at e

theorem axisPath_inj : ∀ (l a : Nat) (p : List Bool), axisPath l = some p → axisPath a = some p → l = a := by
  intro l
  induction l using Nat.strongRecOn with
  | ind l ih =>
  intro a p hl ha
  rcases Nat.lt_or_ge l 2 with h | h
  · rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl
    · simp [axisPath_zero] at hl
    · rw [axisPath_one, Option.some.injEq] at hl; subst hl; exact (axisPath_nil ha).symm
  · obtain ⟨p', h1, rfl⟩ := axisPath_two h hl
    rcases Nat.lt_or_ge a 2 with h' | h'
    · rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl
      · simp [axisPath_zero] at ha
      · rw [axisPath_one] at ha; simp at ha
    · obtain ⟨q', h2, e⟩ := axisPath_two h' ha
      obtain ⟨e1, e2⟩ := List.append_inj' e rfl
      subst e1
      have := ih (l / 2) (by omega) (a / 2) p' h1 h2
      simp only [List.cons.injEq, and_true] at e2
      have : l % 2 = a % 2 := by
        by_cases x : l % 2 = 1 <;> by_cases y : a % 2 = 1 <;> simp [x, y] at e2 <;> omega
      omega

theorem axisPath_some : ∀ (l : Nat), 1 ≤ l → ∃ p, axisPath l = some p := by
  intro l
  induction l using Nat.strongRecOn with
  | ind l ih =>
  intro hl
  by_cases h1 : l = 1
  · subst h1; exact ⟨[], axisPath_one⟩
  · obtain ⟨q, hq⟩ := ih (l / 2) (by omega) (by omega)
    exact ⟨q ++ [decide (l % 2 = 1)], by rw [axisPath_step l (by omega), hq]; rfl⟩

/-- An axis whose path extends the path of `a` is under `a`. -/
theorem under_of_path : ∀ (l a : Nat) (pa ρ : List Bool), axisPath a = some pa → axisPath l = some (pa ++ ρ) →
    l / 2 ^ ρ.length = a := by
  intro l
  induction l using Nat.strongRecOn with
  | ind l ih =>
  intro a pa ρ ha hl
  rcases List.eq_nil_or_concat ρ with rfl | ⟨ρ', b, rfl⟩
  · simp only [List.append_nil] at hl
    simp only [List.length_nil, Nat.pow_zero, Nat.div_one]
    exact axisPath_inj l a pa hl ha
  · rw [List.concat_eq_append] at hl ⊢
    have l2 : 2 ≤ l := by
      rcases Nat.lt_or_ge l 2 with h | h
      · rcases (show l = 0 ∨ l = 1 by omega) with rfl | rfl
        · simp [axisPath_zero] at hl
        · rw [axisPath_one] at hl; simp at hl
      · exact h
    obtain ⟨p', h1, e⟩ := axisPath_two l2 hl
    rw [← List.append_assoc] at e
    obtain ⟨e1, _⟩ := List.append_inj' e rfl
    subst e1
    have := ih (l / 2) (by omega) a pa ρ' ha h1
    rw [List.length_append, List.length_singleton, Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
    exact this

theorem slotAtPath_edit : ∀ (pa : List Bool) (x t n : Noun), editAtPath pa x t = some n →
    slotAtPath n pa = some x ∧ (slotAtPath t pa).isSome
  | [], x, t, n, h => by simp only [editAtPath, Option.some.injEq] at h; subst h; simp [slotAtPath]
  | _ :: _, _, Noun.atom _, _, h => by simp [editAtPath] at h
  | false :: pa, x, Noun.cell th tt, n, h => by
    simp only [editAtPath] at h
    cases e : editAtPath pa x th with
    | none => rw [e] at h; cases h
    | some h' =>
      rw [e] at h; simp only [Option.some.injEq] at h; subst h
      exact slotAtPath_edit pa x th h' e
  | true :: pa, x, Noun.cell th tt, n, h => by
    simp only [editAtPath] at h
    cases e : editAtPath pa x tt with
    | none => rw [e] at h; cases h
    | some h' =>
      rw [e] at h; simp only [Option.some.injEq] at h; subst h
      exact slotAtPath_edit pa x tt h' e

theorem editAtPath_isSome : ∀ (pa : List Bool) (x t : Noun), (slotAtPath t pa).isSome →
    (editAtPath pa x t).isSome
  | [], _, _, _ => by simp [editAtPath]
  | _ :: _, _, Noun.atom _, h => by simp [slotAtPath] at h
  | false :: pa, x, Noun.cell th _, h => by
    simp only [slotAtPath] at h
    have := editAtPath_isSome pa x th h
    simp only [editAtPath]
    cases e : editAtPath pa x th with
    | none => rw [e] at this; cases this
    | some _ => rfl
  | true :: pa, x, Noun.cell _ tt, h => by
    simp only [slotAtPath] at h
    have := editAtPath_isSome pa x tt h
    simp only [editAtPath]
    cases e : editAtPath pa x tt with
    | none => rw [e] at this; cases this
    | some _ => rfl

/-- Off the edited path, the edited noun has the axes the recipient has. -/
theorem slotAtPath_edit_off : ∀ (pa pl : List Bool) (x t n : Noun), editAtPath pa x t = some n →
    (¬ ∃ ρ, pl = pa ++ ρ) → ((slotAtPath n pl).isSome ↔ (slotAtPath t pl).isSome)
  | [], pl, _, _, _, _, hn => absurd ⟨pl, rfl⟩ hn
  | _ :: _, _, _, Noun.atom _, _, h, _ => by simp [editAtPath] at h
  | b :: pa, [], x, Noun.cell th tt, n, h, _ => by
    cases b <;> simp only [editAtPath] at h <;> split at h <;> simp at h <;> subst h <;> simp [slotAtPath]
  | false :: pa, c :: pl, x, Noun.cell th tt, n, h, hn => by
    simp only [editAtPath] at h
    cases e : editAtPath pa x th with
    | none => rw [e] at h; cases h
    | some h' =>
      rw [e] at h; simp only [Option.some.injEq] at h; subst h
      cases c with
      | true => simp [slotAtPath]
      | false =>
        simp only [slotAtPath]
        exact slotAtPath_edit_off pa pl x th h' e (fun ⟨ρ, hρ⟩ => hn ⟨ρ, by simp [hρ]⟩)
  | true :: pa, c :: pl, x, Noun.cell th tt, n, h, hn => by
    simp only [editAtPath] at h
    cases e : editAtPath pa x tt with
    | none => rw [e] at h; cases h
    | some h' =>
      rw [e] at h; simp only [Option.some.injEq] at h; subst h
      cases c with
      | false => simp [slotAtPath]
      | true =>
        simp only [slotAtPath]
        exact slotAtPath_edit_off pa pl x tt h' e (fun ⟨ρ, hρ⟩ => hn ⟨ρ, by simp [hρ]⟩)

/-- What the edit does at the axes: the edited axis holds the donor, ... -/
theorem slot_edit {a : Nat} {x t n : Noun} (h : edit? a x t = some n) :
    slot? a n = some x ∧ (slot? a t).isSome := by
  unfold edit? at h
  unfold slot?
  cases e : axisPath a with
  | none => rw [e] at h; cases h
  | some pa => rw [e] at h; exact slotAtPath_edit pa x t n h

theorem edit_isSome {a : Nat} {x t : Noun} (h : (slot? a t).isSome) : (edit? a x t).isSome := by
  unfold slot? at h
  unfold edit?
  cases e : axisPath a with
  | none => rw [e] at h; cases h
  | some pa => rw [e] at h; exact editAtPath_isSome pa x t h

/-- ... and an axis not under the edited one is there exactly when it is
there in the recipient. -/
theorem slot_edit_off {a l : Nat} {x t n : Noun} (h : edit? a x t = some n) (hl : 1 ≤ l)
    (hu : ∀ k, l / 2 ^ k ≠ a) : (slot? l n).isSome ↔ (slot? l t).isSome := by
  unfold edit? at h
  unfold slot?
  cases e : axisPath a with
  | none => rw [e] at h; cases h
  | some pa =>
    rw [e] at h
    obtain ⟨pl, el⟩ := axisPath_some l hl
    rw [el]
    exact slotAtPath_edit_off pa pl x t n h fun ⟨ρ, hρ⟩ => hu ρ.length (under_of_path l a pa ρ e (hρ ▸ el))

/-! ## The fold of `+into-sure` -/

theorem foldl_intoStep_none (axe : Nat) (xs : List Nat) :
    xs.foldl (intoStep (S := S) axe) Option.none = Option.none := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [List.foldl, intoStep] using ih

theorem foldl_intoStep (axe : Nat) : ∀ (xs : List Nat) (d0 r0 ld lr : S),
    xs.foldl (intoStep axe) (some (d0, r0)) = some (ld, lr) →
    (∀ x ∈ xs, ∃ v, gep axe x = some v) ∧
    (∀ y, y ∈ HoonSet.toList ld ↔ y ∈ HoonSet.toList d0 ∨ ∃ x ∈ xs, gep axe x = some (some y) ∧ y ≠ 1) ∧
    (∀ y, y ∈ HoonSet.toList lr ↔ y ∈ HoonSet.toList r0 ∨ ∃ x ∈ xs, gep axe x = some Option.none ∧ y = x) := by
  intro xs
  induction xs with
  | nil =>
    intro d0 r0 ld lr h
    simp only [List.foldl, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | cons x xs ih =>
    intro d0 r0 ld lr h
    simp only [List.foldl] at h
    by_cases a0 : axe = 0
    · simp [intoStep, a0, foldl_intoStep_none] at h
    cases eg : gep axe x with
    | none => simp [intoStep, a0, eg, foldl_intoStep_none] at h
    | some v =>
      cases v with
      | none =>
        simp only [intoStep, Option.bind_some, a0, if_false, eg] at h
        obtain ⟨G, D, R⟩ := ih _ _ _ _ h
        refine ⟨fun z hz => ?_, fun y => ?_, fun y => ?_⟩
        · rcases List.mem_cons.mp hz with rfl | hz
          · exact ⟨_, eg⟩
          · exact G z hz
        · rw [D]; constructor
          · rintro (a | ⟨z, hz, a⟩)
            · exact Or.inl a
            · exact Or.inr ⟨z, List.mem_cons_of_mem _ hz, a⟩
          · rintro (a | ⟨z, hz, a⟩)
            · exact Or.inl a
            · rcases List.mem_cons.mp hz with rfl | hz
              · rw [eg] at a; cases a.1
              · exact Or.inr ⟨z, hz, a⟩
        · rw [R, HoonSet.mem_put]; constructor
          · rintro ((a | a) | ⟨z, hz, a⟩)
            · exact Or.inr ⟨x, List.mem_cons_self .., eg, a⟩
            · exact Or.inl a
            · exact Or.inr ⟨z, List.mem_cons_of_mem _ hz, a⟩
          · rintro (a | ⟨z, hz, a⟩)
            · exact Or.inl (Or.inr a)
            · rcases List.mem_cons.mp hz with rfl | hz
              · exact Or.inl (Or.inl a.2)
              · exact Or.inr ⟨z, hz, a⟩
      | some r =>
        by_cases r1 : r = 1
        · simp only [intoStep, Option.bind_some, a0, if_false, eg, r1, if_true] at h
          obtain ⟨G, D, R⟩ := ih _ _ _ _ h
          refine ⟨fun z hz => ?_, fun y => ?_, fun y => ?_⟩
          · rcases List.mem_cons.mp hz with rfl | hz
            · exact ⟨_, eg⟩
            · exact G z hz
          · rw [D]; constructor
            · rintro (a | ⟨z, hz, a⟩)
              · exact Or.inl a
              · exact Or.inr ⟨z, List.mem_cons_of_mem _ hz, a⟩
            · rintro (a | ⟨z, hz, a⟩)
              · exact Or.inl a
              · rcases List.mem_cons.mp hz with rfl | hz
                · rw [eg] at a; simp only [Option.some.injEq] at a; exact absurd (a.1 ▸ r1) a.2
                · exact Or.inr ⟨z, hz, a⟩
          · rw [R]; constructor
            · rintro (a | ⟨z, hz, a⟩)
              · exact Or.inl a
              · exact Or.inr ⟨z, List.mem_cons_of_mem _ hz, a⟩
            · rintro (a | ⟨z, hz, a⟩)
              · exact Or.inl a
              · rcases List.mem_cons.mp hz with rfl | hz
                · rw [eg] at a; simp at a
                · exact Or.inr ⟨z, hz, a⟩
        · simp only [intoStep, Option.bind_some, a0, if_false, eg, r1] at h
          obtain ⟨G, D, R⟩ := ih _ _ _ _ h
          refine ⟨fun z hz => ?_, fun y => ?_, fun y => ?_⟩
          · rcases List.mem_cons.mp hz with rfl | hz
            · exact ⟨_, eg⟩
            · exact G z hz
          · rw [D, HoonSet.mem_put]; constructor
            · rintro ((a | a) | ⟨z, hz, a⟩)
              · exact Or.inr ⟨x, List.mem_cons_self .., by rw [eg, a], by rw [a]; exact r1⟩
              · exact Or.inl a
              · exact Or.inr ⟨z, List.mem_cons_of_mem _ hz, a⟩
            · rintro (a | ⟨z, hz, a⟩)
              · exact Or.inl (Or.inr a)
              · rcases List.mem_cons.mp hz with rfl | hz
                · rw [eg] at a; simp only [Option.some.injEq] at a; exact Or.inl (Or.inl a.1.symm)
                · exact Or.inr ⟨z, hz, a⟩
          · rw [R]; constructor
            · rintro (a | ⟨z, hz, a⟩)
              · exact Or.inl a
              · exact Or.inr ⟨z, List.mem_cons_of_mem _ hz, a⟩
            · rintro (a | ⟨z, hz, a⟩)
              · exact Or.inl a
              · rcases List.mem_cons.mp hz with rfl | hz
                · rw [eg] at a; simp at a
                · exact Or.inr ⟨z, hz, a⟩

/-- **The looks of `+into-sure`.**  When the edit at `axe` succeeds, the
edited noun has the looks of `lok` exactly when the donor has those of
`ld` and the recipient those of `lr`. -/
theorem intoLok_looks {axe : Nat} {lok ld lr : S} (h : intoLok axe lok = some (ld, lr))
    {x t n : Noun} (he : edit? axe x t = some n) :
    Looks lok n ↔ Looks ld x ∧ Looks lr t := by
  obtain ⟨G, D, R⟩ := foldl_intoStep axe _ _ _ _ _ h
  obtain ⟨sa, _⟩ := slot_edit he
  constructor
  · intro hl
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · rcases (D y).mp hy with e | ⟨l, hl', eg, _⟩
      · exact absurd e (HoonSet.mem_empty _)
      · obtain ⟨a1, r1, rfl, _⟩ := gep_some eg
        have := hl _ hl'
        rw [Hoon.slot_pegF axe a1 n y r1, sa] at this
        exact this
    · rcases (R y).mp hy with e | ⟨l, hl', eg, rfl⟩
      · exact absurd e (HoonSet.mem_empty _)
      · have l1 : 1 ≤ y := by
          rcases Nat.eq_zero_or_pos y with e | e
          · subst e; rw [gep_crash.mpr (Or.inr rfl)] at eg; cases eg
          · exact e
        exact (slot_edit_off he l1 (gep_none eg)).mp (hl _ hl')
  · intro ⟨hx, ht⟩ l hl
    obtain ⟨v, eg⟩ := G l hl
    cases v with
    | none =>
      have l1 : 1 ≤ l := by
        rcases Nat.eq_zero_or_pos l with e | e
        · subst e; rw [gep_crash.mpr (Or.inr rfl)] at eg; cases eg
        · exact e
      exact (slot_edit_off he l1 (gep_none eg)).mpr (ht _ ((R l).mpr (Or.inr ⟨l, hl, eg, rfl⟩)))
    | some r =>
      obtain ⟨a1, r1, rfl, ra⟩ := gep_some eg
      rw [Hoon.slot_pegF axe a1 n r r1, sa]
      by_cases e : r = 1
      · subst e; simp
      · exact hx _ ((D r).mpr (Or.inr ⟨_, hl, eg, e⟩))

end Comp
end SkaModel
end Formalization
