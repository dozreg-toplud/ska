module

public import lemmas.Hoon.Axis
public import lemmas.Pill.Arm.Mink
import all lemmas.Pill.Arm.Mink
/-!
The gates `frag` and `edit` of the `|^` core of `+mink`: `frag` is `slot?`
and `edit` is `edit?`, as units.

```hoon
++  frag
  |=  [axis=@ noun=*]
  ^-  (unit)
  ?:  =(0 axis)  ~
  |-  ^-  (unit)
  ?:  =(1 axis)  `noun
  ?@  noun  ~
  =/  pick  (cap axis)
  %=  $
    axis  (mas axis)
    noun  ?-(pick %2 -.noun, %3 +.noun)
  ==
::
++  edit
  |=  [axis=@ target=* value=*]
  ^-  (unit)
  ?:  =(1 axis)  `value
  ?@  target  ~
  =/  pick  (cap axis)
  =/  mutant
    %=  $
      axis    (mas axis)
      target  ?-(pick %2 -.target, %3 +.target)
    ==
  ?~  mutant  ~
  ?-  pick
    %2  `[u.mutant +.target]
    %3  `[-.target u.mutant]
  ==
```

Both read `+cap` and `+mas` of layer 1 deep in the context of `+mink`
(`MinkIn`).  Their own context is the `|^` core of `+mink`, `minkCore`.
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

/-- The context of the gate `+mink` holds layer 1 of `hoon.hoon`, with `+cap`
and `+mas`, at `mink.layer1.axis`. -/
abbrev MinkIn (ctx : Noun) : Prop :=
  ∃ l1, slot? mink.layer1.axis ctx = some l1 ∧ CapIn l1 ∧ MasIn l1

/-- The `|^` core of `+mink`: the trace `tr` pushed on the gate whose sample is
`smp` and whose context is `ctx`. -/
abbrev minkCore (tr smp ctx : Noun) : Noun := C mink.core (C tr (C mink.battery (C smp ctx)))

/-! ## `+cap` and `+mas` walk an axis from the top -/

theorem capF_cases (a : Nat) (h : 2 ≤ a) : capF a = 2 ∨ capF a = 3 := by
  induction a using Nat.strongRecOn with
  | ind a ih =>
    rw [capF_eq]
    by_cases a2 : a = 2
    · simp [a2]
    by_cases a3 : a = 3
    · simp [a3]
    rw [if_neg a2, if_neg a3, if_neg (by omega)]
    exact ih (a / 2) (by omega) (by omega)

theorem masF_lt : ∀ (a : Nat), 2 ≤ a → masF a < a := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro ha
    rw [masF_eq]
    by_cases h : a = 2 ∨ a = 3
    · simp only [h, if_true]; omega
    rw [if_neg h, if_neg (show ¬ a < 2 by omega)]
    by_cases h' : a / 2 = 2 ∨ a / 2 = 3
    · rw [masF_eq, if_pos h']; omega
    have := ih (a / 2) (by omega) (by omega)
    omega

theorem axisPath_cap_mas : ∀ (a : Nat), 2 ≤ a →
    axisPath a = (axisPath (masF a)).map (decide (capF a = 3) :: ·) := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro ha
    rw [capF_eq, masF_eq]
    by_cases a2 : a = 2
    · subst a2; rfl
    by_cases a3 : a = 3
    · subst a3; rfl
    have hm := masF_pos (a / 2) (by omega)
    have h1 : (2 * masF (a / 2) + a % 2) / 2 = masF (a / 2) := by omega
    have h2 : (2 * masF (a / 2) + a % 2) % 2 = a % 2 := by omega
    have e1 : axisPath (a % 2 + masF (a / 2) * 2) =
        (axisPath (masF (a / 2))).map (· ++ [decide (a % 2 = 1)]) := by
      rw [show a % 2 + masF (a / 2) * 2 = 2 * masF (a / 2) + a % 2 by omega,
        axisPath_step _ (by omega), h1, h2]
    rw [if_neg (show ¬ (a = 2 ∨ a = 3) by omega), if_neg (show ¬ a < 2 by omega), if_neg a2,
      if_neg a3, if_neg (show ¬ a < 2 by omega), axisPath_step a ha,
      ih (a / 2) (by omega) (by omega), e1]
    cases axisPath (masF (a / 2)) <;> rfl

/-- `#` from the top: the edit at an axis `a ≥ 2` is the edit at `masF a` of
the head or the tail. -/
theorem edit_cap_mas (r : Noun) (a : Nat) (ha : 2 ≤ a) (h t : Noun) :
    edit? a r (C h t) =
      if capF a = 2 then (edit? (masF a) r h).map (fun m => C m t)
      else (edit? (masF a) r t).map (C h) := by
  unfold edit?
  rw [axisPath_cap_mas a ha]
  rcases capF_cases a ha with hc | hc
  · rw [hc]
    cases axisPath (masF a) with
    | none => simp
    | some p => cases he : editAtPath p r h <;> simp [editAtPath, he]
  · rw [hc]
    cases axisPath (masF a) with
    | none => simp
    | some p => cases he : editAtPath p r t <;> simp [editAtPath, he]

theorem edit_atom (r : Noun) (a : Nat) (ha : 2 ≤ a) (k : Nat) : edit? a r (A k) = none := by
  unfold edit?
  rw [axisPath_cap_mas a ha]
  cases axisPath (masF a) <;> rfl

/-! ## `frag` -/

@[nock_exec] theorem mink_frag_arm (S : Noun) :
    nock S mink.frag.arm = some (C mink.frag.battery (C (C (A 0) (A 0)) S)) := by
  nock_open mink.frag.arm; simp only [nock_exec]

theorem mink_frag_loop (tr smp ctx : Noun) (hc : MinkIn ctx) : ∀ (ax : Nat), 1 ≤ ax → ∀ (n : Noun),
    nock (C mink.frag.loop (C mink.frag.battery (C (C (A ax) n) (minkCore tr smp ctx))))
        mink.frag.loop
      = some (unitN (slot? ax n)) := by
  obtain ⟨l1, hl, ⟨hcap, hdiv⟩, ⟨hmas, hadd, hmod, hmul, hdiv'⟩⟩ := hc
  intro ax
  induction ax using Nat.strongRecOn with
  | ind ax ih =>
    intro h1 n
    nock_open mink.frag.loop
    by_cases a1 : ax = 1
    · subst a1; simp [nock_exec, unitN]
    have h2 : 2 ≤ ax := by omega
    have hne : ¬ (1 = ax) := by omega
    have hcap' := cap_gate l1 hdiv ax h2
    have hmas' := mas_gate l1 ⟨hadd, hmod, hmul, hdiv'⟩ ax h2
    have ih' := ih (masF ax) (masF_lt ax h2) (masF_pos ax h2)
    rw [slot_cap_mas n ax h2]
    rcases n with k | ⟨x, y⟩
    · have hk : slot? (capF ax) (A k) = none := by
        rcases capF_cases ax h2 with h | h <;> rw [h] <;> rfl
      simp [nock_exec, hne, unitN, hk]
    rcases capF_cases ax h2 with hc2 | hc3
    · simp [nock_exec, hne, hl, hcap, hmas, cap_arm, mas_arm, hcap', hmas', hc2, ih', slot_two,
        child]
    · simp [nock_exec, hne, hl, hcap, hmas, cap_arm, mas_arm, hcap', hmas', hc3, ih', slot_three,
        child]

/-- Slamming `frag` on an axis and a noun: the noun at the axis, as a unit. -/
theorem mink_frag_gate (tr smp ctx : Noun) (hc : MinkIn ctx) (ax : Nat) (n : Noun) :
    nock (C mink.frag.battery (C (C (A ax) n) (minkCore tr smp ctx))) mink.frag.battery
      = some (unitN (slot? ax n)) := by
  nock_open mink.frag.battery
  by_cases a0 : ax = 0
  · subst a0; simp [nock_exec, unitN, slot?_zero]
  have hne : ¬ (0 = ax) := by omega
  simp [nock_exec, hne, mink_frag_loop tr smp ctx hc ax (by omega) n]

/-! ## `edit` -/

@[nock_exec] theorem mink_edit_arm (S : Noun) :
    nock S mink.edit.arm = some (C mink.edit.battery (C (C (A 0) (C (A 0) (A 0))) S)) := by
  nock_open mink.edit.arm; simp only [nock_exec]

/-- Slamming `edit` on an axis `ax ≥ 1`, a target and a value: the target
edited at the axis, as a unit. -/
theorem mink_edit_gate (tr smp ctx : Noun) (hc : MinkIn ctx) : ∀ (ax : Nat), 1 ≤ ax →
    ∀ (tgt v : Noun),
    nock (C mink.edit.battery (C (C (A ax) (C tgt v)) (minkCore tr smp ctx))) mink.edit.battery
      = some (unitN (edit? ax v tgt)) := by
  obtain ⟨l1, hl, ⟨hcap, hdiv⟩, ⟨hmas, hadd, hmod, hmul, hdiv'⟩⟩ := hc
  intro ax
  induction ax using Nat.strongRecOn with
  | ind ax ih =>
    intro h1 tgt v
    nock_open mink.edit.battery
    by_cases a1 : ax = 1
    · subst a1; simp [nock_exec, unitN]
    have h2 : 2 ≤ ax := by omega
    have hne : ¬ (1 = ax) := by omega
    have hcap' := cap_gate l1 hdiv ax h2
    have hmas' := mas_gate l1 ⟨hadd, hmod, hmul, hdiv'⟩ ax h2
    have hpos := masF_pos ax h2
    have hlt := masF_lt ax h2
    rcases tgt with k | ⟨x, y⟩
    · simp [nock_exec, hne, unitN, edit_atom v ax h2]
    rw [edit_cap_mas v ax h2]
    rcases capF_cases ax h2 with hc2 | hc3
    · have ih' := ih (masF ax) hlt hpos x v
      cases he : edit? (masF ax) v x <;> rw [he] at ih' <;>
        simp [nock_exec, hne, hl, hcap, hmas, cap_arm, mas_arm, hcap', hmas', hc2, ih', unitN]
    · have ih' := ih (masF ax) hlt hpos y v
      cases he : edit? (masF ax) v y <;> rw [he] at ih' <;>
        simp [nock_exec, hne, hl, hcap, hmas, cap_arm, mas_arm, hcap', hmas', hc3, ih', unitN]

end Hoon
end Formalization

end
