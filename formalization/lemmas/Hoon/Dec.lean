import lemmas.Exec
import lemmas.Pill.Facts

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

The nouns `dec.arm`, `dec.battery`, `dec.loop` and `layer1` are the ones in the
pill (`Pill/Nouns.lean`).
-/

namespace Formalization
namespace Hoon

open Nock Pill

/-- The loop of `+dec` with counter `b`, in the gate whose sample is `n`. -/
theorem dec_loop (n : Nat) : ∀ (k b : Nat), b + k + 1 = n →
    nock (C dec.loop (C (A b) (C dec.battery (C (A n) layer1)))) dec.loop = some (A (n - 1)) := by
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
@[nock_exec] theorem dec_gate (n : Nat) (h : 0 < n) :
    nock (C dec.battery (C (A n) layer1)) dec.battery = some (A (n - 1)) := by
  have hne : ¬ (0 = n) := by omega
  nock_open dec.battery
  simp only [nock_exec, Noun.atom.injEq, hne, ↓reduceIte, dec_loop n (n - 1) 0 (by omega)]

/-- The arm `dec` of layer 1 builds the gate, with a bunted sample. -/
@[nock_exec] theorem dec_arm : nock layer1 dec.arm = some (C dec.battery (C (A 0) layer1)) := by
  nock_open dec.arm
  simp only [nock_exec]

/-- `(dec n)` as a caller compiles it: pull the arm out of layer 1, replace the
sample, and kick. -/
theorem dec_call (n : Nat) (h : 0 < n) :
    nock (C (A n) layer1)
        (C (A 8) (C (C (A 9) (C (A 2398) (C (A 0) (A 3))))
          (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2))))))))
      = some (A (n - 1)) := by
  simp only [nock_exec, dec_arm, dec_gate n h]

/-- The same statement about the relation of the Nock specification. -/
theorem dec_gate_eval (n : Nat) (h : 0 < n) :
    Eval (C dec.battery (C (A n) layer1)) dec.battery (A (n - 1)) :=
  eval_of_nock (dec_gate n h)

end Hoon
end Formalization
