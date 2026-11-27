module

public import lemmas.Run
/-!
The specification of `core/Nock.lean` and the form of it that the proofs use
(`lemmas/Spec.lean`) say the same:

* `fas_iff_slot`   `Fas (A n) s p ↔ Slot n s p`
* `hax_iff_edit`   `Hax (A n) r s o ↔ Edit n r s o`
* `nock_iff_eval`  `Nock s f p ↔ Eval s f p`

`Fas` and `Hax` hold only when the axis is an atom (`Fas.atom`, `Hax.atom`).
With `nock_eq_some_iff` of `Run.lean`, the executor `nock` is `Nock`
(`nock_eq_some_iff_spec`).
-/

@[expose] public section

namespace Formalization
namespace Nock

/-! ## Inversions of `Slot` and `Eval` -/

theorem Slot.two_inv {s p : Noun} (h : Slot 2 s p) : ∃ t, s = C p t := by
  generalize hk : 2 = k at h
  cases h with
  | one => omega
  | @left axis _ _ tail h' =>
    have : axis = 1 := by omega
    subst this
    exact ⟨tail, (Slot.deterministic h' Slot.one).symm⟩
  | right => omega

theorem Slot.three_inv {s p : Noun} (h : Slot 3 s p) : ∃ t, s = C t p := by
  generalize hk : 3 = k at h
  cases h with
  | one => omega
  | left => omega
  | @right axis _ head _ h' =>
    have : axis = 1 := by omega
    subst this
    exact ⟨head, (Slot.deterministic h' Slot.one).symm⟩

/-- The axes of a cell of two atoms. -/
theorem Slot.pair_atoms {x y m : Nat} {q : Noun} (h : Slot m (C (A x) (A y)) q) :
    (m = 1 ∧ q = C (A x) (A y)) ∨ (m = 2 ∧ q = A x) ∨ (m = 3 ∧ q = A y) := by
  generalize hs : C (A x) (A y) = s at h
  induction h with
  | one => exact Or.inl ⟨rfl, rfl⟩
  | left _ ih =>
    rcases ih hs with ⟨rfl, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inr (Or.inl ⟨rfl, (Noun.cell.inj (h.trans hs.symm)).1⟩)
    · cases h
    · cases h
  | right _ ih =>
    rcases ih hs with ⟨rfl, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inr (Or.inr ⟨rfl, (Noun.cell.inj (h.trans hs.symm)).2⟩)
    · cases h
    · cases h

theorem Eval.op0_inv {s x q : Noun} (h : Eval s (C (A 0) x) q) :
    ∃ axis, x = A axis ∧ Slot axis s q := by
  cases h with
  | op0 hs => exact ⟨_, rfl, hs⟩

theorem Eval.op4_inv {s b q : Noun} (h : Eval s (C (A 4) b) q) :
    ∃ n, Eval s b (A n) ∧ q = A (n + 1) := by
  cases h with
  | op4 hb => exact ⟨_, hb, rfl⟩

theorem Eval.op2_inv {s b c q : Noun} (h : Eval s (C (A 2) (C b c)) q) :
    ∃ s' f', Eval s b s' ∧ Eval s c f' ∧ Eval s' f' q := by
  cases h with
  | op2 h1 h2 h3 => exact ⟨_, _, h1, h2, h3⟩

/-! ## `/` and `#` -/

theorem Fas.atom {a s p : Noun} (h : Fas a s p) : ∃ n, a = A n ∧ Slot n s p := by
  induction h with
  | one => exact ⟨1, rfl, Slot.one⟩
  | two => exact ⟨2, rfl, Slot.left (axis := 1) Slot.one⟩
  | three => exact ⟨3, rfl, Slot.right (axis := 1) Slot.one⟩
  | @left a b p q _ _ ih1 ih2 =>
    obtain ⟨m, hm, h1⟩ := ih1
    obtain ⟨k, hk, h2⟩ := ih2
    cases hk
    cases hm
    obtain ⟨t, rfl⟩ := h2.two_inv
    exact ⟨2 * a, by rw [Nat.two_mul], Slot.left h1⟩
  | @right a b p q _ _ ih1 ih2 =>
    obtain ⟨m, hm, h1⟩ := ih1
    obtain ⟨k, hk, h2⟩ := ih2
    cases hk
    cases hm
    obtain ⟨t, rfl⟩ := h2.three_inv
    exact ⟨2 * a + 1, by rw [Nat.two_mul], Slot.right h1⟩

theorem fas_of_slot {n : Nat} {s p : Noun} (h : Slot n s p) : Fas (A n) s p := by
  induction h with
  | one => exact Fas.one
  | left _ ih => rw [Nat.two_mul]; exact Fas.left ih Fas.two
  | right _ ih => rw [Nat.two_mul]; exact Fas.right ih Fas.three

theorem fas_iff_slot {n : Nat} {s p : Noun} : Fas (A n) s p ↔ Slot n s p :=
  ⟨fun h => by obtain ⟨m, hm, hs⟩ := h.atom; cases hm; exact hs, fas_of_slot⟩

theorem Hax.atom {a r s o : Noun} (h : Hax a r s o) : ∃ n, a = A n ∧ Edit n r s o := by
  induction h with
  | one => exact ⟨1, rfl, Edit.one⟩
  | @left a b c p q hf _ ih =>
    obtain ⟨m, hm, he⟩ := ih
    cases hm
    have hs : Slot (2 * a + 1) c p := by rw [Nat.two_mul]; exact fas_iff_slot.mp hf
    exact ⟨2 * a, by rw [Nat.two_mul], Edit.left hs he⟩
  | @right a b c p q hf _ ih =>
    obtain ⟨m, hm, he⟩ := ih
    cases hm
    have hs : Slot (2 * a) c p := by rw [Nat.two_mul]; exact fas_iff_slot.mp hf
    exact ⟨2 * a + 1, by rw [Nat.two_mul], Edit.right hs he⟩

theorem hax_of_edit {n : Nat} {r s o : Noun} (h : Edit n r s o) : Hax (A n) r s o := by
  induction h with
  | one => exact Hax.one
  | left hs _ ih =>
    have hf := fas_of_slot hs
    rw [Nat.two_mul] at hf ⊢
    exact Hax.left hf ih
  | right hs _ ih =>
    have hf := fas_of_slot hs
    rw [Nat.two_mul] at hf ⊢
    exact Hax.right hf ih

theorem hax_iff_edit {n : Nat} {r s o : Noun} : Hax (A n) r s o ↔ Edit n r s o :=
  ⟨fun h => by obtain ⟨m, hm, he⟩ := h.atom; cases hm; exact he, hax_of_edit⟩

/-! ## `*` -/

theorem Wut_eq_wut (p : Noun) : Wut p = wut p := by cases p <;> rfl

theorem nock_of_eval_spec {s f p : Noun} (h : Eval s f p) : Nock s f p := by
  induction h with
  | cell _ _ ih1 ih2 => exact Nock.cons ih1 ih2
  | op0 hs => exact Nock.op0 (fas_of_slot hs)
  | op1 => exact Nock.op1
  | op2 _ _ _ ih1 ih2 ih3 => exact Nock.op2 ih1 ih2 ih3
  | op3 _ ih => exact Nock.op3 ih (Wut_eq_wut _).symm
  | @op4 _ _ n _ ih => exact Nock.op4 ih (show A (n + 1) = A (1 + n) by rw [Nat.add_comm])
  | op5 _ _ ih1 ih2 => exact Nock.op5 ih1 ih2 rfl
  | op6_zero _ _ ih1 ih2 =>
    exact Nock.op6
      (Nock.op4 (Nock.op4 ih1 (show A 1 = A (1 + 0) from rfl)) (show A 2 = A (1 + 1) from rfl))
      (Nock.op0 Fas.two) (Nock.op0 Fas.two) ih2
  | op6_one _ _ ih1 ih2 =>
    exact Nock.op6
      (Nock.op4 (Nock.op4 ih1 (show A 2 = A (1 + 1) from rfl)) (show A 3 = A (1 + 2) from rfl))
      (Nock.op0 Fas.three) (Nock.op0 Fas.three) ih2
  | op7 _ _ ih1 ih2 => exact Nock.op7 ih1 ih2
  | op8 _ _ ih1 ih2 => exact Nock.op8 ih1 ih2
  | op9 _ _ ih1 ih2 => exact Nock.op9 ih1 ih2
  | op10 _ _ he ih1 ih2 => exact Nock.op10 ih1 ih2 (hax_of_edit he)
  | op11_cell _ _ _ ih1 ih2 ih3 => exact Nock.op11cell ih1 ih2 ih3
  | op11_atom _ ih => exact Nock.op11atom ih

theorem eval_of_nock_spec {s f p : Noun} (h : Nock s f p) : Eval s f p := by
  induction h with
  | cons _ _ ih1 ih2 => exact Eval.cell ih1 ih2
  | op0 hf =>
    obtain ⟨n, rfl, hs⟩ := hf.atom
    exact Eval.op0 hs
  | op1 => exact Eval.op1
  | op2 _ _ _ ih1 ih2 ih3 => exact Eval.op2 ih1 ih2 ih3
  | op3 _ hq ih => subst hq; rw [Wut_eq_wut]; exact Eval.op3 ih
  | @op4 a b p q _ hl ih =>
    cases p with
    | atom n =>
      have hq : q = A (n + 1) := by rw [Nat.add_comm]; exact hl
      subst hq; exact Eval.op4 ih
    | cell x y => exact False.elim hl
  | op5 _ _ hr ih1 ih2 => subst hr; exact Eval.op5 ih1 ih2
  | @op6 a b c d p q r s _ _ _ _ ih1 ih2 ih3 ih4 =>
    obtain ⟨m, hm, rfl⟩ := ih1.op4_inv
    obtain ⟨n, hb, hmn⟩ := hm.op4_inv
    cases hmn
    obtain ⟨k, hk, hs2⟩ := ih2.op0_inv
    cases hk
    obtain ⟨k', hk', hs3⟩ := ih3.op0_inv
    rcases hs2.pair_atoms with ⟨h1, _⟩ | ⟨h2, rfl⟩ | ⟨h3, rfl⟩
    · omega
    · cases hk'
      have hn : n = 0 := by omega
      subst hn
      obtain ⟨t, ht⟩ := hs3.two_inv
      cases ht
      exact Eval.op6_zero hb ih4
    · cases hk'
      have hn : n = 1 := by omega
      subst hn
      obtain ⟨t, ht⟩ := hs3.three_inv
      cases ht
      exact Eval.op6_one hb ih4
  | op7 _ _ ih1 ih2 => exact Eval.op7 ih1 ih2
  | op8 _ _ ih1 ih2 => exact Eval.op8 ih1 ih2
  | op9 _ _ ih1 ih2 =>
    obtain ⟨s', f', _, hf, _⟩ := ih2.op2_inv
    obtain ⟨axis, rfl, _⟩ := hf.op0_inv
    exact Eval.op9 ih1 ih2
  | op10 _ _ hh ih1 ih2 =>
    obtain ⟨n, rfl, he⟩ := hh.atom
    exact Eval.op10 ih1 ih2 he
  | op11cell _ _ _ ih1 ih2 ih3 => exact Eval.op11_cell ih1 ih2 ih3
  | op11atom _ ih => exact Eval.op11_atom ih

/-- The specification and the form the proofs use are the same relation. -/
theorem nock_iff_eval {s f p : Noun} : Nock s f p ↔ Eval s f p :=
  ⟨eval_of_nock_spec, nock_of_eval_spec⟩

/-- The executor is the specification. -/
theorem nock_eq_some_iff_spec {s f p : Noun} : nock s f = some p ↔ Nock s f p :=
  nock_eq_some_iff.trans nock_iff_eval.symm

end Nock
end Formalization
