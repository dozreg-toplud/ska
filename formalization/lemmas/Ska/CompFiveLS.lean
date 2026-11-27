import lemmas.Ska.CompFourTop

/-!
# The equality test `[5 p q]`: the `+mink` side

README Gaps 12.29 (next).  `[5 p q]` compiles as the indirect call does:
the inner pair `[p q]` under `%next (pairReg rp)` and a block behind it, here
`[eqq rp rq z o']` (with `+forl` in front, as `[3 p]`'s `[clq arg z o']`), or
`[equ rp rq] hop th` under a goal that asks nothing.  This file has the
`+mink` side.

* `MinkC5`: `+mink` on `f` is the equality test of `+mink` on `fb` and `fc`
  (`MinkC2` with `eqCode` in place of the run of the products).
* `minkC5_five`: `[5 b c]` itself.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

/-- **`+mink` on `f` is the equality test of `+mink` on `fb` and `fc`**:
`fb` runs, then `fc`, with less fuel, and the product is `eqCode` of theirs
(`fwd`); backward, runs of the parts give one of `f` (`bwd`). -/
structure MinkC5 (lib : Lib) (P : Noun → Prop) (f fb fc : Noun) : Prop where
  fwd : ∀ {s gul : Noun} {n : Nat} {tm : Trace} {r : Tone}, P s → minkF lib gul n tm s f = some r →
    ∃ n', n' < n ∧ ∃ rb, minkF lib gul n' tm s fb = some rb ∧
      (((∀ q, rb ≠ Tone.zero q) ∧ r = rb) ∨ ∃ x, rb = Tone.zero x ∧ ∃ rc, minkF lib gul n' tm s fc = some rc ∧
        (((∀ q, rc ≠ Tone.zero q) ∧ r = rc) ∨ ∃ y, rc = Tone.zero y ∧ r = Tone.zero (eqCode x y)))
  bwd : ∀ {s gul : Noun} {tm : Trace} {rb : Tone}, P s → Mink lib gul tm s fb rb →
    ((∀ q, rb ≠ Tone.zero q) → Mink lib gul tm s f rb) ∧
    ∀ x rc, rb = Tone.zero x → Mink lib gul tm s fc rc →
      ((∀ q, rc ≠ Tone.zero q) → Mink lib gul tm s f rc) ∧
      ∀ y, rc = Tone.zero y → Mink lib gul tm s f (Tone.zero (eqCode x y))

/-- `[5 b c]` itself. -/
theorem minkC5_five (lib : Lib) (P : Noun → Prop) (b c : Noun) : MinkC5 lib P (n3 (A 5) b c) b c where
  fwd := fun {s gul n tm r} _ h => by
    cases n with
    | zero => simp [minkF] at h
    | succ n' =>
      rw [minkF_succ_eq] at h
      simp only [n3, minkStep] at h
      refine ⟨n', Nat.lt_succ_self n', ?_⟩
      cases eb : minkF lib gul n' tm s b with
      | none => rw [eb] at h; simp [tbind] at h
      | some rb =>
        rw [eb] at h
        refine ⟨rb, rfl, ?_⟩
        cases rb with
        | one q => simp only [tbind, Option.some.injEq] at h; exact Or.inl ⟨(fun _ e => by cases e), h.symm⟩
        | two t' => simp only [tbind, Option.some.injEq] at h; exact Or.inl ⟨(fun _ e => by cases e), h.symm⟩
        | zero x =>
          refine Or.inr ⟨x, rfl, ?_⟩
          simp only [tbind_zero] at h
          cases ec : minkF lib gul n' tm s c with
          | none => rw [ec] at h; simp [tbind] at h
          | some rc =>
            rw [ec] at h
            refine ⟨rc, rfl, ?_⟩
            cases rc with
            | one q => simp only [tbind, Option.some.injEq] at h; exact Or.inl ⟨(fun _ e => by cases e), h.symm⟩
            | two t' => simp only [tbind, Option.some.injEq] at h; exact Or.inl ⟨(fun _ e => by cases e), h.symm⟩
            | zero y =>
              simp only [tbind_zero, Option.some.injEq] at h
              exact Or.inr ⟨y, rfl, h.symm⟩
  bwd := fun {s gul tm rb} _ hb => by
    obtain ⟨n1, e1⟩ := hb
    refine ⟨fun hn => ⟨n1 + 1, ?_⟩, fun x rc ex hc => ?_⟩
    · rw [minkF_succ_eq]; simp only [n3, minkStep]; rw [e1]
      cases rb with
      | zero q => exact absurd rfl (hn q)
      | one _ => rfl
      | two _ => rfl
    · subst ex
      obtain ⟨n2, e2⟩ := hc
      have e1' := minkF_le lib gul (Nat.le_max_left n1 n2) tm s b _ e1
      have e2' := minkF_le lib gul (Nat.le_max_right n1 n2) tm s c _ e2
      refine ⟨fun hn => ⟨max n1 n2 + 1, ?_⟩, fun y ey => ?_⟩
      · rw [minkF_succ_eq]; simp only [n3, minkStep]; rw [e1', tbind_zero, e2']
        cases rc with
        | zero q => exact absurd rfl (hn q)
        | one _ => rfl
        | two _ => rfl
      · subst ey
        exact ⟨max n1 n2 + 1, by rw [minkF_succ_eq]; simp only [n3, minkStep]; rw [e1', tbind_zero, e2',
          tbind_zero]⟩

end Comp
end SkaModel
end Formalization
