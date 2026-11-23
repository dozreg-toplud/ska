module

public import lemmas.Hoon.Arith
public import lemmas.Pill.Arm.Cap
public import lemmas.Pill.Arm.Mas
public import lemmas.Pill.Arm.Peg
import all lemmas.Pill.Arm.Cap
import all lemmas.Pill.Arm.Mas
import all lemmas.Pill.Arm.Peg

/-!
The tree-addressing arms of the pill's `hoon.hoon`.

```hoon
++  cap                                                 ::  tree head
  ~/  %cap
  |=  a=@
  ^-  ?(%2 %3)
  ?-  a
    %2        %2
    %3        %3
    ?(%0 %1)  !!
    *         $(a (div a 2))
  ==
::
++  mas                                                 ::  axis within head/tail
  ~/  %mas
  |=  a=@
  ^-  @
  ?-  a
    ?(%2 %3)  1
    ?(%0 %1)  !!
    *         (add (mod a 2) (mul $(a (div a 2)) 2))
  ==
::
++  peg                                                 ::  axis within axis
  ~/  %peg
  |=  [a=@ b=@]
  ?<  =(0 a)
  ?<  =(0 b)
  ^-  @
  ?-  b
    %1  a
    %2  (mul a 2)
    %3  +((mul a 2))
    *   (add (mod b 2) (mul $(b (div b 2)) 2))
  ==
```

The models `capF`, `masF`, `pegF` follow the Hoon.  What they mean is
`slot_pegF`: the noun at axis `pegF a b` is the noun at axis `b` of the noun
at axis `a`, and `slot_cap_mas`: the noun at axis `a ≥ 2` is the noun at
axis `masF a` of the head or the tail, as `capF a` is `2` or `3`.
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

/-! ## The models -/

/-- `+cap`: `2` or `3`, as the axis `a ≥ 2` lies in the head or the tail. -/
def capF (a : Nat) : Nat :=
  if a = 2 then 2 else if a = 3 then 3 else if a < 2 then 0 else capF (a / 2)
termination_by a
decreasing_by omega

/-- `+mas`: the axis of `a ≥ 2` within the head or the tail. -/
def masF (a : Nat) : Nat :=
  if a = 2 ∨ a = 3 then 1 else if a < 2 then 0 else a % 2 + masF (a / 2) * 2
termination_by a
decreasing_by omega

/-- `+peg`: the axis of `b` within the axis `a`. -/
def pegF (a b : Nat) : Nat :=
  if b = 1 then a else if b = 2 then a * 2 else if b = 3 then a * 2 + 1
  else if b < 1 then 0 else b % 2 + pegF a (b / 2) * 2
termination_by b
decreasing_by omega

theorem capF_eq (a : Nat) :
    capF a = if a = 2 then 2 else if a = 3 then 3 else if a < 2 then 0 else capF (a / 2) := by
  rw [capF]

theorem masF_eq (a : Nat) :
    masF a = if a = 2 ∨ a = 3 then 1 else if a < 2 then 0 else a % 2 + masF (a / 2) * 2 := by
  rw [masF]

theorem pegF_eq (a b : Nat) :
    pegF a b = if b = 1 then a else if b = 2 then a * 2 else if b = 3 then a * 2 + 1
      else if b < 1 then 0 else b % 2 + pegF a (b / 2) * 2 := by
  rw [pegF]

/-! ## What the models mean -/

theorem slot_bit (m : Nat) (hm : 1 ≤ m) (bit : Nat) (hb : bit < 2) (s : Noun) :
    slot? (2 * m + bit) s = (slot? m s).bind (child (decide (bit = 1))) := by
  rw [slot?_step _ (by omega)]
  have h1 : (2 * m + bit) / 2 = m := by omega
  have h2 : (2 * m + bit) % 2 = bit := by omega
  rw [h1, h2]

theorem Option.bind_assoc' {α β γ : Type} (x : Option α) (f : α → Option β) (g : β → Option γ) :
    (x.bind f).bind g = x.bind fun a => (f a).bind g := by
  cases x <;> rfl

theorem pegF_pos (a : Nat) (ha : 1 ≤ a) : ∀ (b : Nat), 1 ≤ b → 1 ≤ pegF a b := by
  intro b
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro hb
    rw [pegF_eq]
    by_cases b1 : b = 1
    · simp [b1]; omega
    by_cases b2 : b = 2
    · simp [b2]; omega
    by_cases b3 : b = 3
    · simp [b3]
    rw [if_neg b1, if_neg b2, if_neg b3, if_neg (by omega)]
    have := ih (b / 2) (by omega) (by omega)
    omega

theorem masF_pos : ∀ (a : Nat), 2 ≤ a → 1 ≤ masF a := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro ha
    rw [masF_eq]
    by_cases h : a = 2 ∨ a = 3
    · simp [h]
    rw [if_neg h, if_neg (by omega)]
    have := ih (a / 2) (by omega) (by omega)
    omega

theorem slot_two (t : Noun) : slot? 2 t = child false t := by
  rw [slot?_step 2 (by decide)]; simp

theorem slot_three (t : Noun) : slot? 3 t = child true t := by
  rw [slot?_step 3 (by decide)]; simp

/-- The noun at axis `pegF a b` is the noun at axis `b` of the noun at axis `a`. -/
theorem slot_pegF (a : Nat) (ha : 1 ≤ a) (s : Noun) : ∀ (b : Nat), 1 ≤ b →
    slot? (pegF a b) s = (slot? a s).bind (slot? b) := by
  intro b
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro hb
    rw [pegF_eq]
    by_cases b1 : b = 1
    · subst b1
      cases h : slot? a s <;> simp [h]
    by_cases b2 : b = 2
    · subst b2
      rw [if_neg (by decide), if_pos rfl, show a * 2 = 2 * a + 0 by omega,
        slot_bit a ha 0 (by decide)]
      congr 1; funext t; rw [slot_two]; rfl
    by_cases b3 : b = 3
    · subst b3
      rw [if_neg (by decide), if_neg (by decide), if_pos rfl, show a * 2 + 1 = 2 * a + 1 by omega,
        slot_bit a ha 1 (by decide)]
      congr 1; funext t; rw [slot_three]; rfl
    rw [if_neg b1, if_neg b2, if_neg b3, if_neg (by omega)]
    have hm := pegF_pos a ha (b / 2) (by omega)
    have hb' : slot? b = fun t => (slot? (b / 2) t).bind (child (decide (b % 2 = 1))) := by
      funext t; exact slot?_step b (by omega) t
    rw [show b % 2 + pegF a (b / 2) * 2 = 2 * pegF a (b / 2) + b % 2 by omega,
      slot_bit _ hm (b % 2) (by omega), ih (b / 2) (by omega) (by omega), Option.bind_assoc', hb']

/-- The noun at axis `a ≥ 2` is the noun at axis `masF a` of the head or the
tail, as `capF a` is `2` or `3`. -/
theorem slot_cap_mas (s : Noun) : ∀ (a : Nat), 2 ≤ a →
    slot? a s = (slot? (capF a) s).bind (slot? (masF a)) := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro ha
    rw [capF_eq, masF_eq]
    by_cases a2 : a = 2
    · subst a2; cases h : slot? 2 s <;> simp [h]
    by_cases a3 : a = 3
    · subst a3; cases h : slot? 3 s <;> simp [h]
    rw [if_neg a2, if_neg a3, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have hm := masF_pos (a / 2) (by omega)
    have hs : slot? (a % 2 + masF (a / 2) * 2) =
        fun t => (slot? (masF (a / 2)) t).bind (child (decide (a % 2 = 1))) := by
      funext t
      rw [show a % 2 + masF (a / 2) * 2 = 2 * masF (a / 2) + a % 2 by omega,
        slot_bit _ hm (a % 2) (by omega)]
    rw [hs, ← Option.bind_assoc', ← ih (a / 2) (by omega) (by omega), slot?_step a (by omega)]

/-! ## The Nock -/

abbrev CapIn (c : Noun) : Prop := slot? cap.axis c = some cap.arm ∧ DivIn c
abbrev MasIn (c : Noun) : Prop :=
  slot? mas.axis c = some mas.arm ∧ AddIn c ∧ ModIn c ∧ MulIn c ∧ DivIn c
abbrev PegIn (c : Noun) : Prop :=
  slot? peg.axis c = some peg.arm ∧ AddIn c ∧ ModIn c ∧ MulIn c ∧ DivIn c

@[nock_exec] theorem cap_arm (c : Noun) :
    nock c cap.arm = some (C cap.battery (C (A 0) c)) := by
  nock_open cap.arm; simp only [nock_exec]

@[nock_exec] theorem mas_arm (c : Noun) :
    nock c mas.arm = some (C mas.battery (C (A 0) c)) := by
  nock_open mas.arm; simp only [nock_exec]

@[nock_exec] theorem peg_arm (c : Noun) :
    nock c peg.arm = some (C peg.battery (C (C (A 0) (A 0)) c)) := by
  nock_open peg.arm; simp only [nock_exec]

/-- Slamming the `+cap` gate on an axis `a ≥ 2`. -/
theorem cap_gate (c : Noun) (hc : DivIn c) : ∀ (a : Nat), 2 ≤ a →
    nock (C cap.battery (C (A a) c)) cap.battery = some (A (capF a)) := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro ha
    nock_open cap.battery
    rw [capF_eq]
    by_cases a2 : a = 2
    · subst a2; simp [nock_exec]
    by_cases a3 : a = 3
    · subst a3; simp [nock_exec]
    have h2 : ¬ (2 = a) := by omega
    have h3 : ¬ (3 = a) := by omega
    have h1 : ¬ (1 = a) := by omega
    have h0 : ¬ (0 = a) := by omega
    simp only [nock_exec, Noun.atom.injEq, h2, h3, h1, h0, ↓reduceIte, hc, div_arm,
      div_gate c hc.2 a 2 (by decide), ih (a / 2) (by omega) (by omega), a2, a3,
      show ¬ a < 2 by omega]

/-- `(cap 0)` and `(cap 1)` crash. -/
theorem cap_gate_lt (c : Noun) (a : Nat) (ha : a < 2) :
    nock (C cap.battery (C (A a) c)) cap.battery = none := by
  nock_open cap.battery
  obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
  all_goals simp [nock_exec]

/-- Slamming the `+mas` gate on an axis `a ≥ 2`. -/
theorem mas_gate (c : Noun) (hc : AddIn c ∧ ModIn c ∧ MulIn c ∧ DivIn c) : ∀ (a : Nat), 2 ≤ a →
    nock (C mas.battery (C (A a) c)) mas.battery = some (A (masF a)) := by
  obtain ⟨ha', hm, hu, hd⟩ := hc
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro ha
    nock_open mas.battery
    rw [masF_eq]
    by_cases a3 : a = 3
    · subst a3; simp [nock_exec]
    by_cases a2 : a = 2
    · subst a2; simp [nock_exec]
    have h2 : ¬ (2 = a) := by omega
    have h3 : ¬ (3 = a) := by omega
    have h1 : ¬ (1 = a) := by omega
    have h0 : ¬ (0 = a) := by omega
    simp only [nock_exec, Noun.atom.injEq, h2, h3, h1, h0, ↓reduceIte, ha', hm, hu, hd,
      add_arm, mod_arm, mul_arm, div_arm, div_gate c hd.2 a 2 (by decide),
      mod_gate c hm.2 a 2 (by decide), ih (a / 2) (by omega) (by omega), mul_gate c hu.2,
      add_gate c ha'.2, a2, a3, or_self, show ¬ a < 2 by omega]

/-- Slamming the `+peg` gate on two positive axes. -/
theorem peg_gate (c : Noun) (hc : AddIn c ∧ ModIn c ∧ MulIn c ∧ DivIn c) (a : Nat) (ha : 1 ≤ a) :
    ∀ (b : Nat), 1 ≤ b →
      nock (C peg.battery (C (C (A a) (A b)) c)) peg.battery = some (A (pegF a b)) := by
  obtain ⟨ha', hm, hu, hd⟩ := hc
  have ha0 : ¬ (0 = a) := by omega
  intro b
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro hb
    nock_open peg.battery
    rw [pegF_eq]
    have hb0 : ¬ (0 = b) := by omega
    by_cases b1 : b = 1
    · subst b1; simp [nock_exec, ha0]
    by_cases b2 : b = 2
    · subst b2; simp [nock_exec, ha0, hu, mul_arm, mul_gate c hu.2]
    by_cases b3 : b = 3
    · subst b3; simp [nock_exec, ha0, hu, mul_arm, mul_gate c hu.2]
    have h1 : ¬ (1 = b) := by omega
    have h2 : ¬ (2 = b) := by omega
    have h3 : ¬ (3 = b) := by omega
    simp only [nock_exec, Noun.atom.injEq, ha0, hb0, h1, h2, h3, ↓reduceIte, ha', hm, hu, hd,
      add_arm, mod_arm, mul_arm, div_arm, div_gate c hd.2 b 2 (by decide),
      mod_gate c hm.2 b 2 (by decide), ih (b / 2) (by omega) (by omega), mul_gate c hu.2,
      add_gate c ha'.2, b1, b2, b3, show ¬ b < 1 by omega]

end Hoon
end Formalization

end
