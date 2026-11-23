import lemmas.Compiler.Anno
import lemmas.Hoon.Layer1
import lemmas.Pill.Arm.Cape_size

/-!
`+cape-size` of the analysis core `ana` against `capeSize`, which follows the
Hoon line by line.  It is the first callee of `+he-sock`.

```hoon
++  cape-size
  |=  c=cape
  ^-  @
  ?@  c  1
  ~+((add $(c -.c) $(c +.c)))
```

The gate counts the leaves of any noun (`leafCount`), a cape or not.  It
reads `+add` of the library's first layer, at axis `16383` of its context
(`CapeSizeIn`).
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon

/-- `+cape-size` on any noun: `1` on an atom, the sum on a cell. -/
def leafCount : Noun → Nat
  | Noun.atom _ => 1
  | Noun.cell a b => leafCount a + leafCount b

/-- `+cape-size` on a cape, as the Hoon reads it. -/
def capeSize : Cape → Nat
  | Cape.yes => 1
  | Cape.no => 1
  | Cape.cell a b => capeSize a + capeSize b

theorem capeSize_eq (c : Cape) : capeSize c = leafCount c.toNoun := by
  induction c with
  | yes => rfl
  | no => rfl
  | cell a b iha ihb => simp [capeSize, leafCount, Cape.toNoun, iha, ihb]

/-- The axis of the library's first layer in the context of `+cape-size`. -/
abbrev capeSize.layer1.axis : Nat := 16383

/-- What `+cape-size` reads from its context: `+add` and `+dec`. -/
abbrev CapeSizeIn (c : Noun) : Prop :=
  ∃ l, slot? capeSize.layer1.axis c = some l ∧ AddIn l

@[nock_exec] theorem cape_size_arm (c : Noun) :
    nock c cape_size.arm = some (C cape_size.battery (C (A 1) c)) := by
  nock_open cape_size.arm; simp only [nock_exec]

/-- Slamming `+cape-size` on any noun. -/
theorem cape_size_gate (ctx : Noun) (hc : CapeSizeIn ctx) : ∀ n : Noun,
    nock (C cape_size.battery (C n ctx)) cape_size.battery = some (A (leafCount n)) := by
  obtain ⟨l, hl, ha, hd⟩ := hc
  intro n
  induction n with
  | atom a => nock_open cape_size.battery; simp [nock_exec, leafCount]
  | cell a b iha ihb =>
    nock_open cape_size.battery
    simp [nock_exec, leafCount, hl, ha, add_arm, iha, ihb, add_gate l hd]

theorem cape_size_cape (ctx : Noun) (hc : CapeSizeIn ctx) (c : Cape) :
    nock (C cape_size.battery (C c.toNoun ctx)) cape_size.battery = some (A (capeSize c)) := by
  rw [cape_size_gate ctx hc, capeSize_eq]

/-! ## On the pill's analysis core -/

/-- A run of tail steps: from `slot? k s = slot? r v`, the same `n` tail
steps further down on both sides. -/
theorem slot_spine {s v : Noun} {k r : Nat} (hk : 0 < k) (hr : 0 < r)
    (h : slot? k s = slot? r v) : ∀ n,
    slot? (2 ^ n * (k + 1) - 1) s = slot? (2 ^ n * (r + 1) - 1) v
  | 0 => by simpa using h
  | n + 1 => by
    have hp : 0 < 2 ^ n := Nat.two_pow_pos n
    have h1 : 0 < 2 ^ n * (k + 1) - 1 := by
      have : 2 ≤ 2 ^ n * (k + 1) := by
        calc 2 ≤ 1 * (k + 1) := by omega
          _ ≤ 2 ^ n * (k + 1) := Nat.mul_le_mul_right _ hp
      omega
    have h2 : 0 < 2 ^ n * (r + 1) - 1 := by
      have : 2 ≤ 2 ^ n * (r + 1) := by
        calc 2 ≤ 1 * (r + 1) := by omega
          _ ≤ 2 ^ n * (r + 1) := Nat.mul_le_mul_right _ hp
      omega
    have := slot?_sub_right h1 h2 (slot_spine hk hr h n)
    have e1 : 2 * (2 ^ n * (k + 1) - 1) + 1 = 2 ^ (n + 1) * (k + 1) - 1 := by
      rw [Nat.pow_succ]
      have : 1 ≤ 2 ^ n * (k + 1) := by omega
      rw [Nat.mul_comm (2 ^ n) 2, Nat.mul_assoc]; omega
    have e2 : 2 * (2 ^ n * (r + 1) - 1) + 1 = 2 ^ (n + 1) * (r + 1) - 1 := by
      rw [Nat.pow_succ]
      have : 1 ≤ 2 ^ n * (r + 1) := by omega
      rw [Nat.mul_comm (2 ^ n) 2, Nat.mul_assoc]; omega
    rwa [e1, e2] at this

/-- `ana` holds the library's first layer at axis `16383`: through `lib`. -/
theorem ana_layer1 : slot? capeSize.layer1.axis ana = some layer1 := by
  have h : slot? 7 ana = slot? 1 lib := by
    rw [show (7 : Nat) = knit_anno.lib.axis from rfl, knit_anno.lib.arm_at]; rfl
  have := slot_spine (by omega) (by omega) h 11
  simp only [show 2 ^ 11 * (7 + 1) - 1 = 16383 from rfl,
    show 2 ^ 11 * (1 + 1) - 1 = 4095 from rfl] at this
  rw [this]
  exact ca.lib.layer1.arm_at

theorem capeSizeIn_ana : CapeSizeIn ana := ⟨layer1, ana_layer1, arith_layer1.1⟩

theorem cape_size_pill (n : Noun) :
    nock (C cape_size.battery (C n ana)) cape_size.battery = some (A (leafCount n)) :=
  cape_size_gate ana capeSizeIn_ana n

end Compiler
end Formalization
