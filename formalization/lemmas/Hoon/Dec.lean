module

public import lemmas.Hoon.Basic
public import lemmas.Pill.Arm.Dec
import all lemmas.Pill.Arm.Dec
/-!
`+dec` of the pill's `hoon.hoon`, proved against `Nat` subtraction.

```hoon
++  dec
  ~/  %dec
  |=  a=@
  ~_  leaf+"decrement-underflow"
  ?<  =(0 a)
  =+  b=0
  |-  ^-  @
  ?:  =(a +(b))  b
  $(b +(b))
```

The gate reads nothing from its context, so the theorems hold for every
context `c`.  The nouns `dec.arm`, `dec.battery` and `dec.loop` are the ones
in the pill (`Pill/Nouns.lean`).
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

/-- The context `c` holds the arm `+dec` at its axis. -/
abbrev DecIn (c : Noun) : Prop := slot? dec.axis c = some dec.arm

/-- The loop of `+dec` with counter `b`, in the gate whose sample is `n`. -/
theorem dec_loop (c : Noun) (n : Nat) : ∀ (k b : Nat), b + k + 1 = n →
    nock (C dec.loop (C (A b) (C dec.battery (C (A n) c)))) dec.loop = some (A (n - 1)) := by
  intro k
  induction k with
  | zero =>
    intro b h
    obtain rfl : n = b + 1 := by omega
    nock_open dec.loop
    simp only [nock_exec, ↓reduceIte, Nat.add_sub_cancel]
  | succ k ih =>
    intro b h
    have hne : n ≠ b + 1 := by omega
    nock_open dec.loop
    simp only [nock_exec, Noun.atom.injEq, hne, ↓reduceIte, ih (b + 1) (by omega)]

/-- Slamming the `+dec` gate on a positive atom `n` gives `n - 1`. -/
@[nock_exec] theorem dec_gate (c : Noun) (n : Nat) (h : 0 < n) :
    nock (C dec.battery (C (A n) c)) dec.battery = some (A (n - 1)) := by
  have hne : ¬ (0 = n) := by omega
  nock_open dec.battery
  simp only [nock_exec, Noun.atom.injEq, hne, ↓reduceIte, dec_loop c n (n - 1) 0 (by omega)]

/-- `(dec 0)` crashes. -/
theorem dec_gate_zero (c : Noun) : nock (C dec.battery (C (A 0) c)) dec.battery = none := by
  nock_open dec.battery
  simp only [nock_exec, ↓reduceIte]

/-- The arm `dec` builds the gate, with a bunted sample. -/
@[nock_exec] theorem dec_arm (c : Noun) : nock c dec.arm = some (C dec.battery (C (A 0) c)) := by
  nock_open dec.arm
  simp only [nock_exec]

/-- `(dec n)` as a caller compiles it: pull the arm out of the context, replace
the sample, and kick. -/
theorem dec_call (c : Noun) (hc : DecIn c) (n : Nat) (h : 0 < n) :
    nock (C (A n) c)
        (C (A 8) (C (C (A 9) (C (A dec.axis) (C (A 0) (A 3))))
          (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2))))))))
      = some (A (n - 1)) := by
  simp only [nock_exec, hc, dec_arm, dec_gate c n h]

/-- The same statement about the relation of the Nock specification. -/
theorem dec_gate_eval (c : Noun) (n : Nat) (h : 0 < n) :
    Eval (C dec.battery (C (A n) c)) dec.battery (A (n - 1)) :=
  eval_of_nock (dec_gate c n h)

/-- No derivation of the specification evaluates `(dec 0)`. -/
theorem dec_gate_zero_eval (c : Noun) (p : Noun) :
    ¬ Eval (C dec.battery (C (A 0) c)) dec.battery p := by
  intro h
  have := nock_of_eval h
  rw [dec_gate_zero] at this
  cases this

end Hoon
end Formalization

end
