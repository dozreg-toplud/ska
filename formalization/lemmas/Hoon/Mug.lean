module

public import lemmas.Hoon.Muk
public import lemmas.Hoon.Order
public import lemmas.Pill.Arm.Mug
import all lemmas.Pill.Arm.Mug
/-!
`+mug` of the pill's `hoon.hoon` computes the Lean model `mugF`, which
discharges the assumption `MugSpec` of `+gor`, `+mor`, `+put:by` and the map
and set theorems.

```hoon
++  mug                                                 ::  mug with murmur3
  ~/  %mug
  |=  a=*
  |^  ?@  a  (mum 0xcafe.babe 0x7fff a)
      =/  b  (cat 5 $(a -.a) $(a +.a))
      (mum 0xdead.beef 0xfffe b)
  ::
  ++  mum
    |=  [syd=@uxF fal=@F key=@]
    =/  wyd  (met 3 key)
    =|  i=@ud
    |-  ^-  @F
    ?:  =(8 i)  fal
    =/  haz=@F  (muk syd wyd key)
    =/  ham=@F  (mix (rsh [0 31] haz) (end [0 31] haz))
    ?.(=(0 ham) ham $(i +(i), syd +(syd)))
  --
```

The gate is the core `[[buc mum] gate]` of the `|^`, where `buc` is the arm
`$` (`mug.buc`) and `mum` the gate builder `mug.mum.arm`.

As in `Muk.lean`, the recursions of the models go through generic combinators
(`retry`, `foldNoun`), so that no equation lemma of a recursive definition
sees the hash constants.
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

/-! ## The models -/

/-- Try `f s`, `f (s + 1)`, ... at most `n` times until one is not `0`; `fal`
if all are. -/
def retry (f : Nat → Nat) (fal : Nat) : Nat → Nat → Nat
  | 0, _ => fal
  | n + 1, s => if f s = 0 then retry f fal n (s + 1) else f s

theorem retry_zero (f : Nat → Nat) (fal s : Nat) : retry f fal 0 s = fal := rfl

theorem retry_succ (f : Nat → Nat) (fal n s : Nat) :
    retry f fal (n + 1) s = if f s = 0 then retry f fal n (s + 1) else f s := rfl

/-- The fold of a noun: `fa` at the atoms, `fc` at the cells. -/
def foldNoun (fa : Nat → Nat) (fc : Nat → Nat → Nat) : Noun → Nat
  | Noun.atom a => fa a
  | Noun.cell h t => fc (foldNoun fa fc h) (foldNoun fa fc t)

theorem foldNoun_atom (fa : Nat → Nat) (fc : Nat → Nat → Nat) (a : Nat) :
    foldNoun fa fc (A a) = fa a := rfl

theorem foldNoun_cell (fa : Nat → Nat) (fc : Nat → Nat → Nat) (h t : Noun) :
    foldNoun fa fc (C h t) = fc (foldNoun fa fc h) (foldNoun fa fc t) := rfl

/-- The 31-bit hash that `mum` tries with seed `s`. -/
def mumHam (key s : Nat) : Nat :=
  mukF s (metF 3 key) key / 2 ^ (2 ^ 0 * 31) ^^^ mukF s (metF 3 key) key % 2 ^ (2 ^ 0 * 31)

/-- The arm `mum` of `+mug`. -/
def mumF (syd fal key : Nat) : Nat := retry (mumHam key) fal 8 syd

/-- `+mug`. -/
def mugF : Noun → Nat :=
  foldNoun (fun a => mumF 0xcafebabe 0x7fff a)
    (fun x y => mumF 0xdeadbeef 0xfffe (y * 2 ^ (2 ^ 5 * metF 5 x) + x))

theorem mumHam_eq (key s : Nat) :
    mumHam key s =
      mukF s (metF 3 key) key / 2 ^ (2 ^ 0 * 31) ^^^ mukF s (metF 3 key) key % 2 ^ (2 ^ 0 * 31) := by
  delta mumHam; exact Eq.refl _

theorem mumF_eq (syd fal key : Nat) : mumF syd fal key = retry (mumHam key) fal 8 syd := by
  delta mumF; exact Eq.refl _

theorem mugF_atom (a : Nat) : mugF (A a) = mumF 0xcafebabe 0x7fff a :=
  foldNoun_atom _ _ a

theorem mugF_cell (h t : Noun) :
    mugF (C h t) = mumF 0xdeadbeef 0xfffe (mugF t * 2 ^ (2 ^ 5 * metF 5 (mugF h)) + mugF h) :=
  foldNoun_cell _ _ h t

/-! ## The Nock -/

/-- What the gate `+mug` reads from its context `c`. -/
abbrev MugNeeds (c : Noun) : Prop :=
  slot? muk.axis c = some muk.arm ∧ MukNeeds c ∧ MetIn c ∧ CatIn c

theorem mum_loop (c : Noun) (hc : MugNeeds c) (k1 k2 k3 : Noun) (fal key : Nat) :
    ∀ (n i syd : Nat), i + n = 8 →
      nock (C mug.loop (C (A i) (C (A (metF 3 key)) (C mug.mum.battery
        (C (C (A syd) (C (A fal) (A key))) (C k1 (C k2 (C k3 c)))))))) mug.loop
        = some (A (retry (mumHam key) fal n syd)) := by
  obtain ⟨hmk, hmuk, _, _⟩ := hc
  have hmukg := muk_gate c hmuk
  have hmixg := mix_gate c hmuk.2.2.2.1.2
  have hrsh := rsh_gate c hmuk.2.1.1.2.1
  have hend := end_gate c hmuk.2.1.1.2.2.2.1
  have hmix := hmuk.2.2.2.1.1
  have hr := hmuk.2.1.1.2.1.1
  have he := hmuk.2.1.1.2.2.2.1.1
  intro n
  induction n with
  | zero =>
    intro i syd h
    obtain rfl : i = 8 := by omega
    nock_open mug.loop
    simp only [nock_exec, ↓reduceIte, retry_zero]
  | succ n ih =>
    intro i syd h
    have h8 : ¬ (8 = i) := by omega
    rw [retry_succ, mumHam_eq]
    nock_open mug.loop
    by_cases hz : mukF syd (metF 3 key) key / 2 ^ (2 ^ 0 * 31) ^^^
        mukF syd (metF 3 key) key % 2 ^ (2 ^ 0 * 31) = 0
    · rw [if_pos hz]
      simp only [nock_exec, Noun.atom.injEq, h8, ↓reduceIte, hmk, hmix, hr, he, muk_arm,
        mix_arm, rsh_arm, end_arm, hmukg, hmixg, hrsh _ 0 _ _ (BiteIs.cell 0 _),
        hend _ 0 _ _ (BiteIs.cell 0 _), hz, ih (i + 1) (syd + 1) (by omega)]
    · rw [if_neg hz]
      simp only [nock_exec, Noun.atom.injEq, h8, ↓reduceIte, hmk, hmix, hr, he, muk_arm,
        mix_arm, rsh_arm, end_arm, hmukg, hmixg, hrsh _ 0 _ _ (BiteIs.cell 0 _),
        hend _ 0 _ _ (BiteIs.cell 0 _), Ne.symm hz]

/-- Slamming the gate `mum` on `[syd fal key]`, in a core whose context is
`c` at the depth where `+mug` puts it. -/
theorem mum_gate (c : Noun) (hc : MugNeeds c) (k1 k2 k3 : Noun) (syd fal key : Nat) :
    nock (C mug.mum.battery (C (C (A syd) (C (A fal) (A key))) (C k1 (C k2 (C k3 c)))))
      mug.mum.battery = some (A (mumF syd fal key)) := by
  have hmet := met_gate c hc.2.2.1.2
  have hm := hc.2.2.1.1
  rw [mumF_eq]
  nock_open mug.mum.battery
  simp only [nock_exec, hm, met_arm, hmet, mum_loop c hc k1 k2 k3 fal key 8 0 syd (by omega)]

@[nock_exec] theorem mum_arm (k : Noun) :
    nock k mug.mum.arm = some (C mug.mum.battery (C (C (A 0) (C (A 0) (A 0))) k)) := by
  nock_open mug.mum.arm; simp only [nock_exec]

theorem mug_buc (c : Noun) (hc : MugNeeds c) : ∀ (a : Noun),
    nock (C (C mug.buc mug.mum.arm) (C Pill.mug.battery (C a c))) mug.buc
      = some (A (mugF a)) := by
  have hmum := mum_gate c hc
  have hcat := cat_gate c hc.2.2.2.2
  have hct := hc.2.2.2.1
  intro a
  induction a with
  | atom x =>
    rw [mugF_atom]
    nock_open mug.buc
    simp only [nock_exec, mum_arm, hmum]
  | cell h t ihh iht =>
    rw [mugF_cell]
    nock_open mug.buc
    simp only [nock_exec, mum_arm, hmum, hct, cat_arm, hcat, ihh, iht]

/-- Slamming the `+mug` gate on any noun gives `mugF` of it: the assumption
`MugSpec` holds for `mugF`. -/
theorem mug_spec (c : Noun) (hc : MugNeeds c) : MugSpec mugF c := by
  intro a
  nock_open Pill.mug.battery
  simp only [nock_exec, mug_buc c hc a]

end Hoon
end Formalization

end
