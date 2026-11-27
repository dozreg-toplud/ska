import lemmas.Compiler.OptLinkAlNouns

/-!
# `+alias`: `old.gen` and `rn` (phase 1 of the plan, README Gaps 13)

```hoon
  ++  rn  |=(r=@uvre ^-(@uvre (~(gut by old.gen) r r)))
```

* `OldRel N f`: the map `old.gen` is the renaming `f` of the model (`AGen.old`,
  `ABody.old`): every entry an atom to its alias, an absent register its own.
  `oldRel_nil`: the bunt is `id`; `old_put`: `(~(put by old.gen) d x)` is
  `updA f d x`.
* `al_rn`: **`rn` is `f`**, in any core whose `gen` has `old.gen` at axis `6`
  and `optC` where the `|^` core of `+alias` has it.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- `old.gen` is the map of the renaming `f`. -/
def OldRel (N : Noun) (f : Nat → Nat) : Prop :=
  IsMap mugF N ∧ (∀ kn v, look N kn = some v → ∃ r, kn = A r ∧ v = A (f r)) ∧
    ∀ r, look N (A r) = none → f r = r

theorem oldRel_nil : OldRel (A 0) id := by
  refine ⟨IsMap.nil, fun kn v h => ?_, fun r _ => rfl⟩
  rw [look_nil] at h
  cases h

/-- `(~(gut by old.gen) r r)` is `f r`. -/
theorem old_gut {N : Noun} {f : Nat → Nat} (h : OldRel N f) (r : Nat) :
    nock (C by.gut.battery (C (C (A r) (A r)) (C by.battery (C N layer2)))) by.gut.battery
      = some (A (f r)) := by
  cases hl : look N (A r) with
  | none =>
    have hg := getF_none h.1 (fun v hv => by rw [← look_get h.1] at hv; rw [hl] at hv; cases hv)
    rw [gut_gate (mug := mugF) layer2 gutIn_layer2 _ _ _ _ hg (Or.inl rfl)]
    simp [h.2.2 r hl]
  | some v =>
    obtain ⟨r', e, rfl⟩ := h.2.1 _ _ hl
    have e' : r = r' := Noun.atom.inj e
    subst e'
    have hg := getF_some h.1 ((look_get h.1 _ _).1 hl)
    rw [gut_gate (mug := mugF) layer2 gutIn_layer2 _ _ _ _ hg (Or.inr ⟨_, rfl⟩)]
    simp

/-- `(~(put by old.gen) d x)`: the alias of `d` is `x`. -/
theorem old_put {N : Noun} {f : Nat → Nat} (h : OldRel N f) (d x : Nat) :
    ∃ N', nock (C by.put.battery (C (C (A d) (A x)) (C by.battery (C N layer2)))) by.put.battery
      = some N' ∧ OldRel N' (Opt.updA f d x) := by
  obtain ⟨out, hp, ho, hg⟩ := putF_spec mugF N (A d) (A x) h.1
  refine ⟨out, put_gate (mug := mugF) layer2 gorIn_morIn_layer2 _ _ _ _ hp, ho, ?_, ?_⟩
  · intro kn v hv
    rw [look_put ho h.1 hg] at hv
    by_cases e : kn = A d
    · subst e
      rw [if_pos rfl] at hv
      cases hv
      exact ⟨d, rfl, by simp [Opt.updA]⟩
    · rw [if_neg e] at hv
      obtain ⟨r, rfl, rfl⟩ := h.2.1 _ _ hv
      have hr : r ≠ d := fun hr => e (by rw [hr])
      exact ⟨r, rfl, by simp [Opt.updA, hr]⟩
  · intro r hr
    rw [look_put ho h.1 hg] at hr
    by_cases e : r = d
    · subst e; simp at hr
    · have e' : A r ≠ A d := fun h' => e (Noun.atom.inj h')
      rw [if_neg e'] at hr
      simp [Opt.updA, e, h.2.2 r hr]

/-- **`rn`**: `(rn r)` is `f r`, where `old.gen` is the map of `f`. -/
theorem al_rn (X Y Z NEW OLD REST : Noun) (f : Nat → Nat) (h : OldRel OLD f) (r : Nat) :
    nock (C alRnB (C (A r) (C X (C (C NEW (C OLD REST)) (C Y (C Z optC)))))) alRnB = some (A (f r)) := by
  have hg := old_gut h r
  have hL := optC_layer2
  generalize optC = OC at hL
  simp [nock_exec, alRnB, hL, by.arm_at, by_arm, by.gut.arm_at, gut_arm, hg]

end Compiler
end Formalization
