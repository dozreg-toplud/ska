import lemmas.Hoon.Dec
import lemmas.Hoon.MapModel

/-!
The comparison arms of the pill's `hoon.hoon` compute their Lean models:
`+lth` is `<` on atoms, `+dor` is `dorF`, and, given what `+mug` computes,
`+gor` is `gorF` and `+mor` is `morF`.
-/

namespace Formalization
namespace Hoon

open Nock Pill

/-- A Hoon flag: `&` is `0` and `|` is `1`. -/
def loob (b : Bool) : Noun := if b then A 0 else A 1

@[nock_exec] theorem loob_true : loob true = A 0 := rfl

@[nock_exec] theorem loob_false : loob false = A 1 := rfl

@[nock_exec] theorem pick_loob (b : Bool) (yes no : Noun) :
    pick (loob b) yes no = some (if b then yes else no) := by
  cases b <;> rfl

/-! ## `+lth` -/

theorem lth_loop : ∀ (a b : Nat),
    nock (C lth.loop (C lth.battery (C (C (A a) (A b)) layer1))) lth.loop
      = some (loob (decide (a ≤ b))) := by
  intro a
  induction a with
  | zero =>
    intro b
    nock_open lth.loop
    simp [nock_exec, loob]
  | succ a ih =>
    intro b
    cases b with
    | zero =>
      have h1 : ¬ (0 = a + 1) := by omega
      nock_open lth.loop
      simp [nock_exec, loob]
    | succ b =>
      have h1 : ¬ (0 = a + 1) := by omega
      have h2 : ¬ (0 = b + 1) := by omega
      nock_open lth.loop
      simp only [nock_exec, Noun.atom.injEq, h1, h2, ↓reduceIte, dec_arm,
        dec_gate (a + 1) (by omega), dec_gate (b + 1) (by omega), Nat.add_sub_cancel, ih b]
      by_cases hab : a ≤ b <;> simp [nock_exec, hab, loob]

/-- Slamming the `+lth` gate on two atoms. -/
theorem lth_gate (a b : Nat) :
    nock (C lth.battery (C (C (A a) (A b)) layer1)) lth.battery
      = some (loob (decide (a < b))) := by
  nock_open lth.battery
  by_cases hab : a = b
  · simp [nock_exec, hab, loob]
  · simp only [nock_exec, Noun.atom.injEq, hab, ↓reduceIte, lth_loop]
    by_cases hle : a ≤ b
    · have : a < b := by omega
      simp [nock_exec, hle, this, loob]
    · have : ¬ a < b := by omega
      simp [nock_exec, hle, this, loob]

@[nock_exec] theorem lth_arm :
    nock layer1 lth.arm = some (C lth.battery (C (C (A 0) (A 0)) layer1)) := by
  nock_open lth.arm
  simp only [nock_exec]

/-! ## `+dor` -/

theorem dorF_self (a : Noun) : dorF a a = true := by
  induction a with
  | atom a => simp [dorF]
  | cell h t _ iht => simp [dorF, iht]

@[nock_exec] theorem dor_arm :
    nock layer2 dor.arm = some (C dor.battery (C (C (A 0) (A 0)) layer2)) := by
  nock_open dor.arm
  simp only [nock_exec]

/-- Slamming the `+dor` gate on two nouns. -/
theorem dor_gate : ∀ (a b : Noun),
    nock (C dor.battery (C (C a b) layer2)) dor.battery = some (loob (dorF a b)) := by
  intro a
  induction a with
  | atom x =>
    intro b
    cases b with
    | atom y =>
      nock_open dor.battery
      by_cases hxy : x = y
      · simp [nock_exec, hxy, dorF, loob]
      · simp only [nock_exec, Noun.atom.injEq, hxy, ↓reduceIte, lth_arm, lth_gate]
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

/-- What the proofs need from `+mug`: slamming its gate on any noun ends, with
an atom.  `mug a` is that atom. -/
def MugSpec (mug : Noun → Nat) : Prop :=
  ∀ a : Noun, nock (C Pill.mug.battery (C a layer2)) Pill.mug.battery = some (A (mug a))

@[nock_exec] theorem mug_arm :
    nock layer2 mug.arm = some (C mug.battery (C (A 0) layer2)) := by
  nock_open mug.arm
  simp only [nock_exec]

@[nock_exec] theorem gor_arm :
    nock layer2 gor.arm = some (C gor.battery (C (C (A 0) (A 0)) layer2)) := by
  nock_open gor.arm
  simp only [nock_exec]

@[nock_exec] theorem mor_arm :
    nock layer2 mor.arm = some (C mor.battery (C (C (A 0) (A 0)) layer2)) := by
  nock_open mor.arm
  simp only [nock_exec]

/-- Slamming the `+gor` gate on two nouns. -/
theorem gor_gate {mug : Noun → Nat} (hmug : MugSpec mug) (a b : Noun) :
    nock (C gor.battery (C (C a b) layer2)) gor.battery = some (loob (gorF mug a b)) := by
  nock_open gor.battery
  simp only [nock_exec, hmug a, hmug b, Noun.atom.injEq]
  by_cases h : mug a = mug b
  · simp [nock_exec, h, gorF, dor_gate]
  · simp [nock_exec, h, gorF, lth_gate]

/-- Slamming the `+mor` gate on two nouns. -/
theorem mor_gate {mug : Noun → Nat} (hmug : MugSpec mug) (a b : Noun) :
    nock (C mor.battery (C (C a b) layer2)) mor.battery = some (loob (morF mug a b)) := by
  nock_open mor.battery
  simp only [nock_exec, hmug a, hmug b, hmug (A (mug a)), hmug (A (mug b)), Noun.atom.injEq]
  by_cases h : mug (A (mug a)) = mug (A (mug b))
  · simp [nock_exec, h, morF, dor_gate]
  · simp [nock_exec, h, morF, lth_gate]

end Hoon
end Formalization
