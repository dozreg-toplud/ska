module

public import lemmas.Hoon.Dec
public import lemmas.Pill.Arm.Add
public import lemmas.Pill.Arm.Sub
public import lemmas.Pill.Arm.Mul
public import lemmas.Pill.Arm.Lth
public import lemmas.Pill.Arm.Lte
public import lemmas.Pill.Arm.Gte
public import lemmas.Pill.Arm.Gth
public import lemmas.Pill.Arm.Max
public import lemmas.Pill.Arm.Min
public import lemmas.Pill.Arm.Dvr
public import lemmas.Pill.Arm.Div
public import lemmas.Pill.Arm.Mod
import all lemmas.Pill.Arm.Add
import all lemmas.Pill.Arm.Sub
import all lemmas.Pill.Arm.Mul
import all lemmas.Pill.Arm.Lth
import all lemmas.Pill.Arm.Lte
import all lemmas.Pill.Arm.Gte
import all lemmas.Pill.Arm.Gth
import all lemmas.Pill.Arm.Max
import all lemmas.Pill.Arm.Min
import all lemmas.Pill.Arm.Dvr
import all lemmas.Pill.Arm.Div
import all lemmas.Pill.Arm.Mod
/-!
The unsigned arithmetic and comparison arms of the pill's `hoon.hoon`, against
`Nat`:

| arm | model | reads from the context |
| --- | --- | --- |
| `+add` | `a + b` | `+dec` |
| `+sub` | `a - b`, a crash when `a < b` | `+dec` |
| `+mul` | `a * b` | `+dec`, `+add` |
| `+lth` | `a < b` | `+dec` |
| `+lte` | `a ≤ b` | `+lth` |
| `+gte` | `b ≤ a` | `+lth` |
| `+gth` | `b < a` | `+lte` |
| `+max`, `+min` | `max a b`, `min a b` | `+gth`, `+lth` |
| `+dvr` | `[a / b a % b]`, a crash when `b = 0` | `+lth`, `+sub` |
| `+div`, `+mod` | `a / b`, `a % b`, a crash when `b = 0` | `+dvr` |

Each gate theorem holds for every context `c` that satisfies the predicate
of what the gate reads (`AddIn`, `LthIn`, ...).  All the arms live in the
library's first layer, and `layer1` satisfies every predicate
(`arith_layer1` in `Layer1.lean`).
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

/-! ## What the gates read from their context -/

abbrev AddIn (c : Noun) : Prop := slot? add.axis c = some add.arm ∧ DecIn c
abbrev SubIn (c : Noun) : Prop := slot? sub.axis c = some sub.arm ∧ DecIn c
abbrev MulIn (c : Noun) : Prop := slot? mul.axis c = some mul.arm ∧ AddIn c
abbrev LthIn (c : Noun) : Prop := slot? lth.axis c = some lth.arm ∧ DecIn c
abbrev LteIn (c : Noun) : Prop := slot? lte.axis c = some lte.arm ∧ LthIn c
abbrev GteIn (c : Noun) : Prop := slot? gte.axis c = some gte.arm ∧ LthIn c
abbrev GthIn (c : Noun) : Prop := slot? gth.axis c = some gth.arm ∧ LteIn c
abbrev MaxIn (c : Noun) : Prop := slot? max.axis c = some max.arm ∧ GthIn c
abbrev MinIn (c : Noun) : Prop := slot? min.axis c = some min.arm ∧ LthIn c
abbrev DvrIn (c : Noun) : Prop := slot? dvr.axis c = some dvr.arm ∧ LthIn c ∧ SubIn c
abbrev DivIn (c : Noun) : Prop := slot? div.axis c = some div.arm ∧ DvrIn c
abbrev ModIn (c : Noun) : Prop := slot? mod.axis c = some mod.arm ∧ DvrIn c

/-! ## The arms build their gates -/

@[nock_exec] theorem add_arm (c : Noun) :
    nock c add.arm = some (C add.battery (C (C (A 0) (A 0)) c)) := by
  nock_open add.arm; simp only [nock_exec]

@[nock_exec] theorem sub_arm (c : Noun) :
    nock c sub.arm = some (C sub.battery (C (C (A 0) (A 0)) c)) := by
  nock_open sub.arm; simp only [nock_exec]

@[nock_exec] theorem mul_arm (c : Noun) :
    nock c mul.arm = some (C mul.battery (C (C (A 1) (A 1)) c)) := by
  nock_open mul.arm; simp only [nock_exec]

@[nock_exec] theorem lth_arm (c : Noun) :
    nock c lth.arm = some (C lth.battery (C (C (A 0) (A 0)) c)) := by
  nock_open lth.arm; simp only [nock_exec]

@[nock_exec] theorem lte_arm (c : Noun) :
    nock c lte.arm = some (C lte.battery (C (C (A 0) (A 0)) c)) := by
  nock_open lte.arm; simp only [nock_exec]

@[nock_exec] theorem gte_arm (c : Noun) :
    nock c gte.arm = some (C gte.battery (C (C (A 0) (A 0)) c)) := by
  nock_open gte.arm; simp only [nock_exec]

@[nock_exec] theorem gth_arm (c : Noun) :
    nock c gth.arm = some (C gth.battery (C (C (A 0) (A 0)) c)) := by
  nock_open gth.arm; simp only [nock_exec]

@[nock_exec] theorem max_arm (c : Noun) :
    nock c max.arm = some (C max.battery (C (C (A 0) (A 0)) c)) := by
  nock_open max.arm; simp only [nock_exec]

@[nock_exec] theorem min_arm (c : Noun) :
    nock c min.arm = some (C min.battery (C (C (A 0) (A 0)) c)) := by
  nock_open min.arm; simp only [nock_exec]

@[nock_exec] theorem dvr_arm (c : Noun) :
    nock c dvr.arm = some (C dvr.battery (C (C (A 1) (A 1)) c)) := by
  nock_open dvr.arm; simp only [nock_exec]

@[nock_exec] theorem div_arm (c : Noun) :
    nock c div.arm = some (C div.battery (C (C (A 1) (A 1)) c)) := by
  nock_open div.arm; simp only [nock_exec]

@[nock_exec] theorem mod_arm (c : Noun) :
    nock c mod.arm = some (C mod.battery (C (C (A 1) (A 1)) c)) := by
  nock_open mod.arm; simp only [nock_exec]

/-! ## `+add` -/

/-- Slamming the `+add` gate on two atoms. -/
theorem add_gate (c : Noun) (hc : DecIn c) : ∀ (a b : Nat),
    nock (C add.battery (C (C (A a) (A b)) c)) add.battery = some (A (a + b)) := by
  intro a
  induction a with
  | zero =>
    intro b
    nock_open add.battery
    simp [nock_exec]
  | succ a ih =>
    intro b
    have h1 : ¬ (0 = a + 1) := by omega
    nock_open add.battery
    simp only [nock_exec, Noun.atom.injEq, h1, ↓reduceIte, hc, dec_arm,
      dec_gate c (a + 1) (by omega), Nat.add_sub_cancel, ih (b + 1)]
    congr 2
    omega

/-! ## `+sub` -/

/-- Slamming the `+sub` gate on `a` and `b ≤ a`. -/
theorem sub_gate (c : Noun) (hc : DecIn c) : ∀ (b a : Nat), b ≤ a →
    nock (C sub.battery (C (C (A a) (A b)) c)) sub.battery = some (A (a - b)) := by
  intro b
  induction b with
  | zero =>
    intro a _
    nock_open sub.battery
    simp [nock_exec]
  | succ b ih =>
    intro a h
    have h1 : ¬ (0 = b + 1) := by omega
    nock_open sub.battery
    simp only [nock_exec, Noun.atom.injEq, h1, ↓reduceIte, hc, dec_arm,
      dec_gate c a (by omega), dec_gate c (b + 1) (by omega), Nat.add_sub_cancel,
      ih (a - 1) (by omega)]
    congr 2
    omega

/-- `(sub a b)` crashes when `a < b`. -/
theorem sub_gate_lt (c : Noun) (hc : DecIn c) : ∀ (a b : Nat), a < b →
    nock (C sub.battery (C (C (A a) (A b)) c)) sub.battery = none := by
  intro a
  induction a with
  | zero =>
    intro b h
    have h1 : ¬ (0 = b) := by omega
    nock_open sub.battery
    simp only [nock_exec, Noun.atom.injEq, h1, ↓reduceIte, hc, dec_arm, dec_gate_zero]
  | succ a ih =>
    intro b h
    have h1 : ¬ (0 = b) := by omega
    nock_open sub.battery
    simp only [nock_exec, Noun.atom.injEq, h1, ↓reduceIte, hc, dec_arm,
      dec_gate c (a + 1) (by omega), dec_gate c b (by omega), Nat.add_sub_cancel,
      ih (b - 1) (by omega)]

/-! ## `+mul` -/

theorem mul_loop (c : Noun) (hc : AddIn c) (b : Nat) : ∀ (a k : Nat),
    nock (C mul.loop (C (A k) (C mul.battery (C (C (A a) (A b)) c)))) mul.loop
      = some (A (k + a * b)) := by
  intro a
  induction a with
  | zero =>
    intro k
    nock_open mul.loop
    simp [nock_exec]
  | succ a ih =>
    intro k
    have h1 : ¬ (0 = a + 1) := by omega
    nock_open mul.loop
    simp only [nock_exec, Noun.atom.injEq, h1, ↓reduceIte, hc, dec_arm, add_arm,
      dec_gate c (a + 1) (by omega), add_gate c hc.2, Nat.add_sub_cancel, ih (b + k)]
    congr 2
    rw [Nat.succ_mul]
    omega

/-- Slamming the `+mul` gate on two atoms. -/
theorem mul_gate (c : Noun) (hc : AddIn c) (a b : Nat) :
    nock (C mul.battery (C (C (A a) (A b)) c)) mul.battery = some (A (a * b)) := by
  nock_open mul.battery
  simp only [nock_exec, mul_loop c hc b a 0, Nat.zero_add]

/-! ## `+lth` -/

theorem lth_loop (c : Noun) (hc : DecIn c) : ∀ (a b : Nat),
    nock (C lth.loop (C lth.battery (C (C (A a) (A b)) c))) lth.loop
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
      nock_open lth.loop
      simp [nock_exec, loob]
    | succ b =>
      have h1 : ¬ (0 = a + 1) := by omega
      have h2 : ¬ (0 = b + 1) := by omega
      nock_open lth.loop
      simp only [nock_exec, Noun.atom.injEq, h1, h2, ↓reduceIte, hc, dec_arm,
        dec_gate c (a + 1) (by omega), dec_gate c (b + 1) (by omega), Nat.add_sub_cancel,
        ih b]
      by_cases hab : a ≤ b <;> simp [nock_exec, hab, loob]

/-- Slamming the `+lth` gate on two atoms. -/
theorem lth_gate (c : Noun) (hc : DecIn c) (a b : Nat) :
    nock (C lth.battery (C (C (A a) (A b)) c)) lth.battery = some (loob (decide (a < b))) := by
  nock_open lth.battery
  by_cases hab : a = b
  · simp [nock_exec, hab, loob]
  · simp only [nock_exec, Noun.atom.injEq, hab, ↓reduceIte, lth_loop c hc]
    by_cases hle : a ≤ b
    · have : a < b := by omega
      simp [nock_exec, hle, this, loob]
    · have : ¬ a < b := by omega
      simp [nock_exec, hle, this, loob]

/-! ## `+lte`, `+gte`, `+gth` -/

/-- Slamming the `+lte` gate on two atoms. -/
theorem lte_gate (c : Noun) (hc : LthIn c) (a b : Nat) :
    nock (C lte.battery (C (C (A a) (A b)) c)) lte.battery = some (loob (decide (a ≤ b))) := by
  nock_open lte.battery
  by_cases hab : a = b
  · simp [nock_exec, hab, loob]
  · simp only [nock_exec, Noun.atom.injEq, hab, ↓reduceIte, hc, lth_arm, lth_gate c hc.2]
    by_cases hlt : a < b
    · have : a ≤ b := by omega
      simp [nock_exec, hlt, this, loob]
    · have : ¬ a ≤ b := by omega
      simp [nock_exec, hlt, this, loob]

/-- Slamming the `+gte` gate on two atoms. -/
theorem gte_gate (c : Noun) (hc : LthIn c) (a b : Nat) :
    nock (C gte.battery (C (C (A a) (A b)) c)) gte.battery = some (loob (decide (b ≤ a))) := by
  nock_open gte.battery
  simp only [nock_exec, hc, lth_arm, lth_gate c hc.2]
  by_cases hlt : a < b
  · have : ¬ b ≤ a := by omega
    simp [nock_exec, hlt, this, loob]
  · have : b ≤ a := by omega
    simp [nock_exec, hlt, this, loob]

/-- Slamming the `+gth` gate on two atoms. -/
theorem gth_gate (c : Noun) (hc : LteIn c) (a b : Nat) :
    nock (C gth.battery (C (C (A a) (A b)) c)) gth.battery = some (loob (decide (b < a))) := by
  nock_open gth.battery
  simp only [nock_exec, hc, lte_arm, lte_gate c hc.2]
  by_cases hle : a ≤ b
  · have : ¬ b < a := by omega
    simp [nock_exec, hle, this, loob]
  · have : b < a := by omega
    simp [nock_exec, hle, this, loob]

/-! ## `+max`, `+min` -/

/-- Slamming the `+max` gate on two atoms. -/
theorem max_gate (c : Noun) (hc : GthIn c) (a b : Nat) :
    nock (C max.battery (C (C (A a) (A b)) c)) max.battery = some (A (max a b)) := by
  nock_open max.battery
  simp only [nock_exec, hc, gth_arm, gth_gate c hc.2]
  by_cases hlt : b < a
  · rw [Nat.max_eq_left (by omega)]
    simp [nock_exec, hlt]
  · rw [Nat.max_eq_right (by omega)]
    simp [nock_exec, hlt]

/-- Slamming the `+min` gate on two atoms. -/
theorem min_gate (c : Noun) (hc : LthIn c) (a b : Nat) :
    nock (C min.battery (C (C (A a) (A b)) c)) min.battery = some (A (min a b)) := by
  nock_open min.battery
  simp only [nock_exec, hc, lth_arm, lth_gate c hc.2]
  by_cases hlt : a < b
  · rw [Nat.min_eq_left (by omega)]
    simp [nock_exec, hlt]
  · rw [Nat.min_eq_right (by omega)]
    simp [nock_exec, hlt]

/-! ## `+dvr`, `+div`, `+mod` -/

theorem dvr_loop (c : Noun) (hc : LthIn c ∧ SubIn c) (b : Nat) (hb : 0 < b) : ∀ (a k : Nat),
    nock (C dvr.loop (C (A k) (C dvr.battery (C (C (A a) (A b)) c)))) dvr.loop
      = some (C (A (k + a / b)) (A (a % b))) := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro k
    nock_open dvr.loop
    by_cases hab : a < b
    · simp only [nock_exec, hc, lth_arm, lth_gate c hc.1.2, decide_eq_true hab,
        Nat.div_eq_of_lt hab, Nat.mod_eq_of_lt hab, Nat.add_zero]
    · have hle : b ≤ a := by omega
      simp only [nock_exec, hc, lth_arm, sub_arm, lth_gate c hc.1.2, decide_eq_false hab,
        sub_gate c hc.2.2 b a hle,
        ih (a - b) (by omega) (k + 1)]
      rw [Nat.div_eq_sub_div hb hle, Nat.mod_eq_sub_mod hle]
      congr 3
      omega

/-- Slamming the `+dvr` gate on `a` and a positive `b`. -/
theorem dvr_gate (c : Noun) (hc : LthIn c ∧ SubIn c) (a b : Nat) (hb : 0 < b) :
    nock (C dvr.battery (C (C (A a) (A b)) c)) dvr.battery
      = some (C (A (a / b)) (A (a % b))) := by
  have h1 : ¬ (0 = b) := by omega
  nock_open dvr.battery
  simp only [nock_exec, Noun.atom.injEq, h1, ↓reduceIte, dvr_loop c hc b hb a 0, Nat.zero_add]

/-- `(dvr a 0)` crashes. -/
theorem dvr_gate_zero (c : Noun) (a : Nat) :
    nock (C dvr.battery (C (C (A a) (A 0)) c)) dvr.battery = none := by
  nock_open dvr.battery
  simp only [nock_exec, ↓reduceIte]

/-- Slamming the `+div` gate on `a` and a positive `b`. -/
theorem div_gate (c : Noun) (hc : DvrIn c) (a b : Nat) (hb : 0 < b) :
    nock (C div.battery (C (C (A a) (A b)) c)) div.battery = some (A (a / b)) := by
  nock_open div.battery
  simp only [nock_exec, hc, dvr_arm, dvr_gate c hc.2 a b hb]

/-- Slamming the `+mod` gate on `a` and a positive `b`. -/
theorem mod_gate (c : Noun) (hc : DvrIn c) (a b : Nat) (hb : 0 < b) :
    nock (C mod.battery (C (C (A a) (A b)) c)) mod.battery = some (A (a % b)) := by
  nock_open mod.battery
  simp only [nock_exec, hc, dvr_arm, dvr_gate c hc.2 a b hb]

/-- `(div a 0)` crashes. -/
theorem div_gate_zero (c : Noun) (hc : DvrIn c) (a : Nat) :
    nock (C div.battery (C (C (A a) (A 0)) c)) div.battery = none := by
  nock_open div.battery
  simp only [nock_exec, hc, dvr_arm, dvr_gate_zero]

/-- `(mod a 0)` crashes. -/
theorem mod_gate_zero (c : Noun) (hc : DvrIn c) (a : Nat) :
    nock (C mod.battery (C (C (A a) (A 0)) c)) mod.battery = none := by
  nock_open mod.battery
  simp only [nock_exec, hc, dvr_arm, dvr_gate_zero]

end Hoon
end Formalization

end
