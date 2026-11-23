module

public import lemmas.Hoon.Bits
public import lemmas.Pill.Arm.Rip
import all lemmas.Pill.Arm.Rip
/-!
`+rip` of the pill's `hoon.hoon`:

```hoon
++  rip
  ~/  %rip
  |=  [a=bite b=@]
  ^-  (list @)
  ?:  =(0 b)  ~
  [(end a b) $(b (rsh a b))]
```

On a bite of bloq `bl` and step `st ≥ 1`, the blocks of `k = 2 ^ bl * st`
bits, least significant first (`ripF k b`).  With the step `0` the gate does
not end on a nonzero atom.
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

/-- The blocks of `k` bits of `b`, least significant first. -/
def ripF (k : Nat) (b : Nat) : List Nat :=
  if h : b = 0 ∨ k = 0 then [] else (b % 2 ^ k) :: ripF k (b / 2 ^ k)
termination_by b
decreasing_by
  have hk : 1 < 2 ^ k := Nat.one_lt_two_pow (by omega)
  exact Nat.div_lt_self (by omega) hk

theorem ripF_zero (k : Nat) : ripF k 0 = [] := by
  rw [ripF]; simp

theorem ripF_pos (k b : Nat) (hk : 0 < k) (hb : 0 < b) :
    ripF k b = (b % 2 ^ k) :: ripF k (b / 2 ^ k) := by
  rw [ripF, dif_neg (by omega)]

/-- What `+rip` reads from its context: `+end` and `+rsh`. -/
abbrev RipIn (c : Noun) : Prop := slot? rip.axis c = some rip.arm ∧ EndIn c ∧ RshIn c

@[nock_exec] theorem rip_arm (c : Noun) :
    nock c rip.arm = some (C rip.battery (C (C (A 0) (A 0)) c)) := by
  nock_open rip.arm; simp only [nock_exec]

/-- Slamming the `+rip` gate on a bite of bloq `bl` and step `st ≥ 1` and an
atom `b`: the list of its blocks. -/
theorem rip_gate (c : Noun) (hc : EndIn c ∧ RshIn c) (x : Noun) (bl st : Nat)
    (hx : BiteIs x bl st) (hst : 0 < st) : ∀ (b : Nat),
    nock (C rip.battery (C (C x (A b)) c)) rip.battery
      = some (listN ((ripF (2 ^ bl * st) b).map A)) := by
  have hk : 0 < 2 ^ bl * st := Nat.mul_pos (Nat.two_pow_pos _) hst
  have hlt : 1 < 2 ^ (2 ^ bl * st) := Nat.one_lt_two_pow (by omega)
  intro b
  induction b using Nat.strongRecOn with
  | ind b ih =>
    nock_open rip.battery
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp [nock_exec, ripF_zero]
    · have hne : ¬ (0 = b) := by omega
      have hrec := ih (b / 2 ^ (2 ^ bl * st)) (Nat.div_lt_self hb hlt)
      simp [nock_exec, hne, hc.1, hc.2, end_arm, rsh_arm, end_gate c hc.1 x bl st b hx,
        rsh_gate c hc.2 x bl st b hx, hrec, ripF_pos _ b hk hb]

end Hoon
end Formalization

end
