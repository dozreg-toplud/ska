import lemmas.Hoon.Bits

/-!
`+muk` of the pill's `hoon.hoon` (murmur3, as `+mug` uses it), and the arms
`sit`, `sum`, `rol` of the door `+fe` that it builds with `~(. fe 5)`.

```hoon
++  fe                                                  ::  modulo bloq
  |_  a=bloq
  ++  rol  |=  [b=bloq c=@ d=@]  ^-  @                  ::  roll left
           =+  e=(sit d)
           =+  f=(bex (sub a b))
           =+  g=(mod c f)
           (sit (con (lsh [b g] e) (rsh [b (sub f g)] e)))
  ++  sum  |=([b=@ c=@] (sit (add b c)))                ::  wrapping add
  ++  sit  |=(b=@ (end a b))                            ::  enforce modulo
  --
```

The models are the Hoon read as Lean functions on `Nat`; nothing here claims
that they are murmur3.
-/

namespace Formalization
namespace Hoon

open Nock Pill

/-! ## The door `+fe` -/

/-- What the arms `sit`, `sum`, `rol` of a `+fe` door with context `c` read
from `c`. -/
abbrev FeNeeds (c : Noun) : Prop := ConIn c ∧ Below SubIn c ∧ Below ModIn c

/-- `+rol` of `+fe` with bloq `a`: roll the low `2 ^ a` bits of `d` left by
`c` blocks of `2 ^ b` bits. -/
def rolF (a b c d : Nat) : Nat :=
  let e := d % 2 ^ (2 ^ a)
  let f := 2 ^ (a - b)
  let g := c % f
  (e * 2 ^ (2 ^ b * g) ||| e / 2 ^ (2 ^ b * (f - g))) % 2 ^ (2 ^ a)

@[nock_exec] theorem fe_arm (c : Noun) : nock c fe.arm = some (C fe.battery (C (A 0) c)) := by
  nock_open fe.arm; simp only [nock_exec]

@[nock_exec] theorem sit_arm (d : Noun) :
    nock d fe.sit.arm = some (C fe.sit.battery (C (A 0) d)) := by
  nock_open fe.sit.arm; simp only [nock_exec]

@[nock_exec] theorem sum_arm (d : Noun) :
    nock d fe.sum.arm = some (C fe.sum.battery (C (C (A 0) (A 0)) d)) := by
  nock_open fe.sum.arm; simp only [nock_exec]

@[nock_exec] theorem rol_arm (d : Noun) :
    nock d fe.rol.arm = some (C fe.rol.battery (C (C (A 0) (C (A 0) (A 0))) d)) := by
  nock_open fe.rol.arm; simp only [nock_exec]

/-- Slamming `sit` of the door `+fe` with bloq `a` on `b`. -/
theorem sit_gate (c : Noun) (hc : EndIn c) (a b : Nat) :
    nock (C fe.sit.battery (C (A b) (C fe.battery (C (A a) c)))) fe.sit.battery
      = some (A (b % 2 ^ (2 ^ a))) := by
  nock_open fe.sit.battery
  simp [nock_exec, hc, end_arm, end_gate c hc (A a) a 1 b (BiteIs.atom a)]

/-- Slamming `sum` of the door `+fe` with bloq `a` on `[b c']`. -/
theorem sum_gate (c : Noun) (hc : EndIn c ∧ Below AddIn c) (a b b' : Nat) :
    nock (C fe.sum.battery (C (C (A b) (A b')) (C fe.battery (C (A a) c)))) fe.sum.battery
      = some (A ((b + b') % 2 ^ (2 ^ a))) := by
  have hsit := sit_gate c hc.1 a
  obtain ⟨he, ha⟩ := hc
  obtain ⟨bat, t, rfl, ht⟩ := ha.elim
  nock_open fe.sum.battery
  simp [nock_exec, ht, add_arm, add_gate t ht.2, hsit]

/-- Slamming `rol` of the door `+fe` with bloq `a` on `[b c d]`, for `b ≤ a`. -/
theorem rol_gate (ctx : Noun) (hc : FeNeeds ctx) (a b c d : Nat) (hb : b ≤ a) :
    nock (C fe.rol.battery (C (C (A b) (C (A c) (A d))) (C fe.battery (C (A a) ctx))))
      fe.rol.battery = some (A (rolF a b c d)) := by
  obtain ⟨⟨hcn, hr, hl, he, hadd⟩, hs, hm⟩ := hc
  have hsit := sit_gate ctx he a
  have hbex := bex_gate ctx hr.2.1.2
  have hcon := con_gate ctx ⟨hr, hl, he, hadd⟩
  have hlsh := lsh_gate ctx hl.2
  have hrsh := rsh_gate ctx hr
  obtain ⟨bat, t, rfl, ht⟩ := hs.elim
  have hm : ModIn t := hm
  have hf : 0 < 2 ^ (a - b) := Nat.two_pow_pos _
  have hg : c % 2 ^ (a - b) ≤ 2 ^ (a - b) := Nat.le_of_lt (Nat.mod_lt _ hf)
  nock_open fe.rol.battery
  simp [nock_exec, hcn, hr, hl, ht, hm, hsit, hbex, hcon, sub_arm, mod_arm, bex_arm,
    con_arm, lsh_arm, rsh_arm, sub_gate t ht.2 b a hb, mod_gate t hm.2 _ _ hf,
    sub_gate t ht.2 _ _ hg, hlsh _ b _ _ (BiteIs.cell b _), hrsh _ b _ _ (BiteIs.cell b _),
    rolF]

/-! ## `+muk` -/

/-- What the gate `+muk` reads from its context `c`. -/
abbrev MukNeeds (c : Noun) : Prop :=
  slot? fe.axis c = some fe.arm ∧ FeNeeds c ∧ CutIn c ∧ MixIn c ∧ DisIn c ∧
  Below DivIn c ∧ Below MulIn c

/-- One block of the loop of `+muk`: mix the 32-bit word `nb - i` of `key`
into `hi`. -/
def mukBlock (key nb i hi : Nat) : Nat :=
  let k1 := key / 2 ^ (2 ^ 5 * (nb - i)) % 2 ^ (2 ^ 5 * 1)
  let k1 := k1 * 0xcc9e2d51 % 2 ^ (2 ^ 5)
  let k1 := rolF 5 0 15 k1
  let k1 := k1 * 0x1b873593 % 2 ^ (2 ^ 5)
  let hi := hi ^^^ k1
  let hi := rolF 5 0 13 hi
  (hi * 5 % 2 ^ (2 ^ 5) + 0xe6546b64) % 2 ^ (2 ^ 5)

/-- `f i`, then `f (i - 1)`, ..., then `f 1`, applied to `x`. -/
def iterDown (f : Nat → Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | i + 1, x => iterDown f i (f (i + 1) x)

theorem iterDown_zero (f : Nat → Nat → Nat) (x : Nat) : iterDown f 0 x = x := rfl

theorem iterDown_succ (f : Nat → Nat → Nat) (i x : Nat) :
    iterDown f (i + 1) x = iterDown f i (f (i + 1) x) := rfl

/-- The loop of `+muk`, from block counter `i` down to `0`. -/
def mukLoop (key nb : Nat) : Nat → Nat → Nat := iterDown (mukBlock key nb)

@[nock_exec] theorem muk_arm (c : Noun) :
    nock c muk.arm = some (C muk.battery (C (C (A 0) (C (A 0) (A 0))) c)) := by
  nock_open muk.arm; simp only [nock_exec]

/-- `mukBlock` written out, as the Nock of the loop computes it. -/
theorem mukBlock_eq (key nb j hi : Nat) :
    mukBlock key nb j hi =
      (rolF 5 0 13 (hi ^^^ rolF 5 0 15 (key / 2 ^ (2 ^ 5 * (nb - j)) % 2 ^ (2 ^ 5 * 1) *
        0xcc9e2d51 % 2 ^ 2 ^ 5) * 0x1b873593 % 2 ^ 2 ^ 5) * 5 % 2 ^ 2 ^ 5 + 0xe6546b64) %
        2 ^ 2 ^ 5 := by
  delta mukBlock
  exact Eq.refl _

theorem mukLoop_zero (key nb hi : Nat) : mukLoop key nb 0 hi = hi := iterDown_zero _ _

theorem mukLoop_succ (key nb i hi : Nat) :
    mukLoop key nb (i + 1) hi = mukLoop key nb i (mukBlock key nb (i + 1) hi) :=
  iterDown_succ _ _ _

theorem muk_loop (c : Noun) (hc : MukNeeds c) (key nb h1 syd len : Nat) : ∀ (i hi : Nat), i ≤ nb →
    nock (C muk.loop (C (A hi) (C (A i) (C (C (A 0xcc9e2d51) (A 0x1b873593)) (C (A h1)
      (C (A nb) (C (C fe.battery (C (A 5) c))
        (C muk.battery (C (C (A syd) (C (A len) (A key))) c)))))))))
      muk.loop = some (A (mukLoop key nb i hi)) := by
  obtain ⟨hfe, hf, hcut, hmix, hdis, hdiv, hmul⟩ := hc
  have hsit := sit_gate c hf.1.2.2.2.1 5
  have hsum := sum_gate c ⟨hf.1.2.2.2.1, hf.1.2.2.2.2⟩ 5
  have hrol := rol_gate c hf 5
  have hcutg := cut_gate c hcut.2
  have hmixg := mix_gate c hmix.2
  obtain ⟨bat, t, rfl, ht⟩ := hmul.elim
  have hs : SubIn t := hf.2.1
  intro i
  induction i with
  | zero =>
    intro hi _
    nock_open muk.loop
    simp only [nock_op6, nock_op5, nock_op1, nock_op0, Option.bind_some, slotLit, pick_eqCode,
      if_true, mukLoop_zero]
  | succ i ih =>
    intro hi hle
    have h1 : ¬ (0 = i + 1) := by omega
    nock_open muk.loop
    simp only [nock_exec, Noun.atom.injEq, h1, ↓reduceIte, hcut, hmix, ht, hs, sit_arm, sum_arm,
      rol_arm, cut_arm, mix_arm, sub_arm, mul_arm, dec_arm, hsit, hsum, hrol _ _ _ (Nat.zero_le 5),
      hcutg, hmixg, sub_gate t hs.2 _ _ hle, mul_gate t ht.2, dec_gate t (i + 1) (by omega),
      Nat.add_sub_cancel, ih _ (by omega : i ≤ nb)]
    rw [mukLoop_succ, mukBlock_eq]

end Hoon
end Formalization
