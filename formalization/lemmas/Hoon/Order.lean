module

public import lemmas.Hoon.Arith
public import lemmas.Hoon.MapModel
public import lemmas.Pill.Arm.Dor
public import lemmas.Pill.Arm.Gor
public import lemmas.Pill.Arm.Mor
public import lemmas.Hoon.MugSpec
import all lemmas.Pill.Arm.Dor
import all lemmas.Pill.Arm.Gor
import all lemmas.Pill.Arm.Mor
/-!
The noun orders of the pill's `hoon.hoon` compute their Lean models: `+dor`
is `dorF`, and, given what `+mug` computes, `+gor` is `gorF` and `+mor` is
`morF`.

The three arms live in the library's second layer and reach `+lth` in the
first layer, which is the tail of their context (`Below LthIn c`).
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

/-! ## What the gates read from their context -/

abbrev DorIn (c : Noun) : Prop := slot? dor.axis c = some dor.arm ∧ Below LthIn c

abbrev GorIn (mug : Noun → Nat) (c : Noun) : Prop :=
  slot? gor.axis c = some gor.arm ∧ MugIn mug c ∧ DorIn c

abbrev MorIn (mug : Noun → Nat) (c : Noun) : Prop :=
  slot? mor.axis c = some mor.arm ∧ MugIn mug c ∧ DorIn c

/-! ## The arms build their gates -/

@[nock_exec] theorem dor_arm (c : Noun) :
    nock c dor.arm = some (C dor.battery (C (C (A 0) (A 0)) c)) := by
  nock_open dor.arm; simp only [nock_exec]

@[nock_exec] theorem gor_arm (c : Noun) :
    nock c gor.arm = some (C gor.battery (C (C (A 0) (A 0)) c)) := by
  nock_open gor.arm; simp only [nock_exec]

@[nock_exec] theorem mor_arm (c : Noun) :
    nock c mor.arm = some (C mor.battery (C (C (A 0) (A 0)) c)) := by
  nock_open mor.arm; simp only [nock_exec]

/-! ## `+dor` -/

theorem dorF_self (a : Noun) : dorF a a = true := by
  induction a with
  | atom a => simp [dorF]
  | cell h t _ iht => simp [dorF, iht]

/-- Slamming the `+dor` gate on two nouns. -/
theorem dor_gate (c : Noun) (hc : Below LthIn c) : ∀ (a b : Noun),
    nock (C dor.battery (C (C a b) c)) dor.battery = some (loob (dorF a b)) := by
  obtain ⟨bat, t, rfl, ht⟩ := hc.elim
  intro a
  induction a with
  | atom x =>
    intro b
    cases b with
    | atom y =>
      nock_open dor.battery
      by_cases hxy : x = y
      · simp [nock_exec, hxy, dorF, loob]
      · simp only [nock_exec, Noun.atom.injEq, hxy, ↓reduceIte, ht, lth_arm, lth_gate t ht.2]
        have : decide (x < y) = decide (x ≤ y) := by
          by_cases h : x < y
          · have : x ≤ y := by omega
            simp [*]
          · have : ¬ x ≤ y := by omega
            simp [*]
        simp [dorF, this]
    | cell h' t' =>
      nock_open dor.battery
      simp [nock_exec, dorF, loob]
  | cell h t ihh iht =>
    intro b
    cases b with
    | atom y =>
      nock_open dor.battery
      simp [nock_exec, dorF, loob]
    | cell h' t' =>
      nock_open dor.battery
      by_cases heq : h = h'
      · by_cases teq : t = t'
        · simp [nock_exec, heq, teq, dorF_self, loob]
        · simp only [nock_exec, Noun.cell.injEq, heq, teq, and_false, ↓reduceIte,
            iht t']
          simp [dorF]
      · simp only [nock_exec, Noun.cell.injEq, heq, false_and, ↓reduceIte, ihh h']
        simp [dorF, heq]

/-! ## `+gor` and `+mor`, given `+mug` -/

/-- Slamming the `+gor` gate on two nouns. -/
theorem gor_gate {mug : Noun → Nat} (c : Noun) (hc : MugIn mug c ∧ DorIn c) (a b : Noun) :
    nock (C gor.battery (C (C a b) c)) gor.battery = some (loob (gorF mug a b)) := by
  have hdor := dor_gate c hc.2.2
  obtain ⟨hm, hd, hb⟩ := hc
  obtain ⟨bat, t, rfl, ht⟩ := hb.elim
  nock_open gor.battery
  simp only [nock_exec, hm, mug_arm, Noun.atom.injEq]
  by_cases h : mug a = mug b
  · simp [nock_exec, h, gorF, hd, dor_arm, hdor]
  · simp [nock_exec, h, gorF, ht, lth_gate t ht.2]

/-- Slamming the `+mor` gate on two nouns. -/
theorem mor_gate {mug : Noun → Nat} (c : Noun) (hc : MugIn mug c ∧ DorIn c) (a b : Noun) :
    nock (C mor.battery (C (C a b) c)) mor.battery = some (loob (morF mug a b)) := by
  have hdor := dor_gate c hc.2.2
  obtain ⟨hm, hd, hb⟩ := hc
  obtain ⟨bat, t, rfl, ht⟩ := hb.elim
  nock_open mor.battery
  simp only [nock_exec, hm, mug_arm, Noun.atom.injEq]
  by_cases h : mug (A (mug a)) = mug (A (mug b))
  · simp [nock_exec, h, morF, hd, dor_arm, hdor]
  · simp [nock_exec, h, morF, ht, lth_gate t ht.2]

end Hoon
end Formalization

end
