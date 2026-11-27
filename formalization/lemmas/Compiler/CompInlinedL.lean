import lemmas.Compiler.CompInlined
import lemmas.Glue.Inline

/-!
# `+nomm-size`, linked (track Q)

```hoon
++  nomm-size
  |=  =nomm
  ^-  @ud
  =|  n=@ud
  |-  ^-  @ud
  ?:  (gth n inline-max)  n
  =.  n  +(n)
  ?-  nomm  ...  ==
```

The arm is `0x5ddd5` of `K` (`ns_at`), `inline-max` is arm `0x5ddc`, the
constant `48` (`imax_at`).  The nouns are cut by `tools/gen/inlinedsize.py`.
`ns_go`: the trap from the count `n` is `nommSize n` of `Glue/Inline.lean`
(one induction on the nomm, every count).  `ns_gate`: the gate is
`nommSize 0`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.Glue

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The nouns -/

/-- The trap of `+nomm-size`. -/
def nsTrap : Noun :=
  (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 75) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 0x5ddc) (C (A 0) (A 31)))))))) (C (A 0) (A 2)))))))) (C (C (A 0) (A 6)) (C (A 7) (C (C (A 10) (C (C (A 6) (C (A 4) (C (A 0) (A 6)))) (C (A 0) (A 1)))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 30))) (C (C (A 3) (C (A 0) (A 60))) (C (A 1) (A 1))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 61))) (C (A 10) (C (C (A 6) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 60))) (C (A 0) (A 1))))))) (C (A 0) (A 1)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 30))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 60)))) (C (A 1) (A 1))))) (C (C (A 0) (A 6)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 30))) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 60)))) (C (A 1) (A 1))))) (C (C (A 0) (A 6)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 30))) (C (C (A 5) (C (C (A 1) (A 2)) (C (A 0) (A 60)))) (C (A 1) (A 1))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 246))) (C (A 10) (C (C (A 6) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 122))) (C (A 0) (A 1))))))) (C (A 0) (A 1)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 30))) (C (C (A 5) (C (C (A 1) (A 3)) (C (A 0) (A 60)))) (C (A 1) (A 1))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 61))) (C (A 0) (A 1)))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 30))) (C (C (A 5) (C (C (A 1) (A 4)) (C (A 0) (A 60)))) (C (A 1) (A 1))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 61))) (C (A 0) (A 1)))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 30))) (C (C (A 5) (C (C (A 1) (A 5)) (C (A 0) (A 60)))) (C (A 1) (A 1))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 123))) (C (A 10) (C (C (A 6) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 122))) (C (A 0) (A 1))))))) (C (A 0) (A 1)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 30))) (C (C (A 5) (C (C (A 1) (A 6)) (C (A 0) (A 60)))) (C (A 1) (A 1))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 247))) (C (A 10) (C (C (A 6) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 246))) (C (A 10) (C (C (A 6) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 122))) (C (A 0) (A 1))))))) (C (A 0) (A 1))))))))) (C (A 0) (A 1)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 30))) (C (C (A 5) (C (C (A 1) (A 7)) (C (A 0) (A 60)))) (C (A 1) (A 1))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 123))) (C (A 10) (C (C (A 6) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 122))) (C (A 0) (A 1))))))) (C (A 0) (A 1)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 30))) (C (C (A 5) (C (C (A 1) (A 10)) (C (A 0) (A 60)))) (C (A 1) (A 1))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 123))) (C (A 10) (C (C (A 6) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 245))) (C (A 0) (A 1))))))) (C (A 0) (A 1)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 30))) (C (C (A 5) (C (C (A 1) (A 11)) (C (A 0) (A 60)))) (C (A 1) (A 1))))) (C (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 122))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 246))) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 246))) (C (A 10) (C (C (A 6) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 245))) (C (A 0) (A 1))))))) (C (A 0) (A 1))))))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 30))) (C (C (A 5) (C (C (A 1) (A 12)) (C (A 0) (A 60)))) (C (A 1) (A 1))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 123))) (C (A 10) (C (C (A 6) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 122))) (C (A 0) (A 1))))))) (C (A 0) (A 1)))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 6) (C (C (A 3) (C (A 0) (A 30))) (C (C (A 5) (C (C (A 1) (A 0x6e61656d)) (C (A 0) (A 60)))) (C (A 1) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 494))) (C (A 10) (C (C (A 6) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 122))) (C (A 0) (A 1))))))) (C (A 0) (A 1)))))))))))))))))))))))))))))))))))))))))))))))))))

/-- The gate body of `+nomm-size`. -/
def nsBody : Noun :=
  (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 1) nsTrap) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))

/-- The arm `+nomm-size`: the gate with the bunt `[0 0]`. -/
def nsArm : Noun := C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (C (A 1) nsBody) (C (A 0) (A 1))))

theorem ns_at : slot? 0x5ddd5 compK = some nsArm := by kernel_rfl

theorem ns_arm (d : Noun) : nock d nsArm = some (C nsBody (C (C (A 0) (A 0)) d)) := by
  unfold nsArm; simp only [nock_exec]

/-- `inline-max` is arm `0x5ddc` of `K`: the constant `48`. -/
theorem imax_at : slot? 0x5ddc compK = some (C (A 1) (A 48)) := by kernel_rfl

theorem inlK_layer1 : slot? 0x1ffff compK = some layer1 := by kernel_rfl

/-! ## The trap -/

/-- **The trap of `+nomm-size`** from the count `n` is `nommSize n`. -/
theorem ns_go : ∀ (nm : Nomm) (n : Nat),
    nock (C nsTrap (C (A n) (C nsBody (C nm.toNoun compK)))) nsTrap = some (A (nommSize n nm)) := by
  intro nm
  induction nm with
  | cons p q ihp ihq =>
    obtain ⟨a, b, hab⟩ := nomm_cell p
    simp only [hab] at ihp
    intro n
    have hg := gth_gate layer1 arith_layer1.2.2.2.2.1 n 48
    by_cases h : inlineMax < n
    · have h' : 48 < n := h
      simp only [nommSize, h, if_true]
      conv => { lhs; arg 2; unfold nsTrap }
      simp [nock_exec, inlK_layer1, gth.arm_at, gth_arm, hg, imax_at, h', loob]
    · have h' : ¬ 48 < n := h
      simp only [nommSize, h, if_false]
      conv => { lhs; arg 2; unfold nsTrap }
      simp [nock_exec, inlK_layer1, gth.arm_at, gth_arm, hg, imax_at, h', loob, Nomm.toNoun, Tag.mean, hab, ihp, ihq]
  | n0 a =>
    intro n
    have hg := gth_gate layer1 arith_layer1.2.2.2.2.1 n 48
    by_cases h : inlineMax < n
    · have h' : 48 < n := h
      simp only [nommSize, h, if_true]
      conv => { lhs; arg 2; unfold nsTrap }
      simp [nock_exec, inlK_layer1, gth.arm_at, gth_arm, hg, imax_at, h', loob]
    · have h' : ¬ 48 < n := h
      simp only [nommSize, h, if_false]
      conv => { lhs; arg 2; unfold nsTrap }
      simp [nock_exec, inlK_layer1, gth.arm_at, gth_arm, hg, imax_at, h', loob, Nomm.toNoun, Tag.mean]
  | n1 k =>
    intro n
    have hg := gth_gate layer1 arith_layer1.2.2.2.2.1 n 48
    by_cases h : inlineMax < n
    · have h' : 48 < n := h
      simp only [nommSize, h, if_true]
      conv => { lhs; arg 2; unfold nsTrap }
      simp [nock_exec, inlK_layer1, gth.arm_at, gth_arm, hg, imax_at, h', loob]
    · have h' : ¬ 48 < n := h
      simp only [nommSize, h, if_false]
      conv => { lhs; arg 2; unfold nsTrap }
      simp [nock_exec, inlK_layer1, gth.arm_at, gth_arm, hg, imax_at, h', loob, Nomm.toNoun, Tag.mean]
  | n2 p q info ihp ihq =>
    intro n
    have hg := gth_gate layer1 arith_layer1.2.2.2.2.1 n 48
    by_cases h : inlineMax < n
    · have h' : 48 < n := h
      simp only [nommSize, h, if_true]
      conv => { lhs; arg 2; unfold nsTrap }
      simp [nock_exec, inlK_layer1, gth.arm_at, gth_arm, hg, imax_at, h', loob]
    · have h' : ¬ 48 < n := h
      simp only [nommSize, h, if_false]
      conv => { lhs; arg 2; unfold nsTrap }
      simp [nock_exec, inlK_layer1, gth.arm_at, gth_arm, hg, imax_at, h', loob, Nomm.toNoun, Tag.mean, ihp, ihq]
  | n3 p ihp =>
    intro n
    have hg := gth_gate layer1 arith_layer1.2.2.2.2.1 n 48
    by_cases h : inlineMax < n
    · have h' : 48 < n := h
      simp only [nommSize, h, if_true]
      conv => { lhs; arg 2; unfold nsTrap }
      simp [nock_exec, inlK_layer1, gth.arm_at, gth_arm, hg, imax_at, h', loob]
    · have h' : ¬ 48 < n := h
      simp only [nommSize, h, if_false]
      conv => { lhs; arg 2; unfold nsTrap }
      simp [nock_exec, inlK_layer1, gth.arm_at, gth_arm, hg, imax_at, h', loob, Nomm.toNoun, Tag.mean, ihp]
  | n4 p ihp =>
    intro n
    have hg := gth_gate layer1 arith_layer1.2.2.2.2.1 n 48
    by_cases h : inlineMax < n
    · have h' : 48 < n := h
      simp only [nommSize, h, if_true]
      conv => { lhs; arg 2; unfold nsTrap }
      simp [nock_exec, inlK_layer1, gth.arm_at, gth_arm, hg, imax_at, h', loob]
    · have h' : ¬ 48 < n := h
      simp only [nommSize, h, if_false]
      conv => { lhs; arg 2; unfold nsTrap }
      simp [nock_exec, inlK_layer1, gth.arm_at, gth_arm, hg, imax_at, h', loob, Nomm.toNoun, Tag.mean, ihp]
  | n5 p q ihp ihq =>
    intro n
    have hg := gth_gate layer1 arith_layer1.2.2.2.2.1 n 48
    by_cases h : inlineMax < n
    · have h' : 48 < n := h
      simp only [nommSize, h, if_true]
      conv => { lhs; arg 2; unfold nsTrap }
      simp [nock_exec, inlK_layer1, gth.arm_at, gth_arm, hg, imax_at, h', loob]
    · have h' : ¬ 48 < n := h
      simp only [nommSize, h, if_false]
      conv => { lhs; arg 2; unfold nsTrap }
      simp [nock_exec, inlK_layer1, gth.arm_at, gth_arm, hg, imax_at, h', loob, Nomm.toNoun, Tag.mean, ihp, ihq]
  | n6 p q r ihp ihq ihr =>
    intro n
    have hg := gth_gate layer1 arith_layer1.2.2.2.2.1 n 48
    by_cases h : inlineMax < n
    · have h' : 48 < n := h
      simp only [nommSize, h, if_true]
      conv => { lhs; arg 2; unfold nsTrap }
      simp [nock_exec, inlK_layer1, gth.arm_at, gth_arm, hg, imax_at, h', loob]
    · have h' : ¬ 48 < n := h
      simp only [nommSize, h, if_false]
      conv => { lhs; arg 2; unfold nsTrap }
      simp [nock_exec, inlK_layer1, gth.arm_at, gth_arm, hg, imax_at, h', loob, Nomm.toNoun, Tag.mean, ihp, ihq, ihr]
  | n7 p q ihp ihq =>
    intro n
    have hg := gth_gate layer1 arith_layer1.2.2.2.2.1 n 48
    by_cases h : inlineMax < n
    · have h' : 48 < n := h
      simp only [nommSize, h, if_true]
      conv => { lhs; arg 2; unfold nsTrap }
      simp [nock_exec, inlK_layer1, gth.arm_at, gth_arm, hg, imax_at, h', loob]
    · have h' : ¬ 48 < n := h
      simp only [nommSize, h, if_false]
      conv => { lhs; arg 2; unfold nsTrap }
      simp [nock_exec, inlK_layer1, gth.arm_at, gth_arm, hg, imax_at, h', loob, Nomm.toNoun, Tag.mean, ihp, ihq]
  | n10 a v q ihv ihq =>
    intro n
    have hg := gth_gate layer1 arith_layer1.2.2.2.2.1 n 48
    by_cases h : inlineMax < n
    · have h' : 48 < n := h
      simp only [nommSize, h, if_true]
      conv => { lhs; arg 2; unfold nsTrap }
      simp [nock_exec, inlK_layer1, gth.arm_at, gth_arm, hg, imax_at, h', loob]
    · have h' : ¬ 48 < n := h
      simp only [nommSize, h, if_false]
      conv => { lhs; arg 2; unfold nsTrap }
      simp [nock_exec, inlK_layer1, gth.arm_at, gth_arm, hg, imax_at, h', loob, Nomm.toNoun, Tag.mean, ihv, ihq]
  | n11s t q body ihq =>
    intro n
    have hg := gth_gate layer1 arith_layer1.2.2.2.2.1 n 48
    by_cases h : inlineMax < n
    · have h' : 48 < n := h
      simp only [nommSize, h, if_true]
      conv => { lhs; arg 2; unfold nsTrap }
      simp [nock_exec, inlK_layer1, gth.arm_at, gth_arm, hg, imax_at, h', loob]
    · have h' : ¬ 48 < n := h
      simp only [nommSize, h, if_false]
      conv => { lhs; arg 2; unfold nsTrap }
      simp [nock_exec, inlK_layer1, gth.arm_at, gth_arm, hg, imax_at, h', loob, Nomm.toNoun, Tag.mean, ihq]
  | n11d t h q body ihh ihq =>
    intro n
    have hg := gth_gate layer1 arith_layer1.2.2.2.2.1 n 48
    by_cases h : inlineMax < n
    · have h' : 48 < n := h
      simp only [nommSize, h, if_true]
      conv => { lhs; arg 2; unfold nsTrap }
      simp [nock_exec, inlK_layer1, gth.arm_at, gth_arm, hg, imax_at, h', loob]
    · have h' : ¬ 48 < n := h
      simp only [nommSize, h, if_false]
      conv => { lhs; arg 2; unfold nsTrap }
      simp [nock_exec, inlK_layer1, gth.arm_at, gth_arm, hg, imax_at, h', loob, Nomm.toNoun, Tag.mean, ihh, ihq]
  | n12 p q ihp ihq =>
    intro n
    have hg := gth_gate layer1 arith_layer1.2.2.2.2.1 n 48
    by_cases h : inlineMax < n
    · have h' : 48 < n := h
      simp only [nommSize, h, if_true]
      conv => { lhs; arg 2; unfold nsTrap }
      simp [nock_exec, inlK_layer1, gth.arm_at, gth_arm, hg, imax_at, h', loob]
    · have h' : ¬ 48 < n := h
      simp only [nommSize, h, if_false]
      conv => { lhs; arg 2; unfold nsTrap }
      simp [nock_exec, inlK_layer1, gth.arm_at, gth_arm, hg, imax_at, h', loob, Nomm.toNoun, Tag.mean, ihp, ihq]
  | mean p b q body k ihp ihq =>
    intro n
    have hg := gth_gate layer1 arith_layer1.2.2.2.2.1 n 48
    by_cases h : inlineMax < n
    · have h' : 48 < n := h
      simp only [nommSize, h, if_true]
      conv => { lhs; arg 2; unfold nsTrap }
      simp [nock_exec, inlK_layer1, gth.arm_at, gth_arm, hg, imax_at, h', loob]
    · have h' : ¬ 48 < n := h
      simp only [nommSize, h, if_false]
      conv => { lhs; arg 2; unfold nsTrap }
      simp [nock_exec, inlK_layer1, gth.arm_at, gth_arm, hg, imax_at, h', loob, Nomm.toNoun, Tag.mean, ihp, ihq]

/-- **`+nomm-size`** (`K` arm `0x5ddd5`) is `nommSize 0`. -/
theorem ns_gate (nm : Nomm) :
    nock (C nsBody (C nm.toNoun compK)) nsBody = some (A (nommSize 0 nm)) := by
  have h := ns_go nm 0
  conv => { lhs; arg 2; unfold nsBody }
  simp only [nock_exec]
  exact h

/-! ## The trap on any nomm

The statement of the trap on one nomm: on every cache `CA` with the
invariant `I`, when the walk `walk` of the model returns `nm'`, the trap
returns `nm'` and a cache with `I`.  `inl_trap` proves it on every nomm from
the one case that is not a rebuild, the `%2` with an `info` (`h2`, which may
use the statement on both children). -/

/-- The trap of `+inlined` on the nomm `nm` returns the walk of it and a
cache with `I`. -/
def TrapP (I : Noun → Prop) (walk : Nomm → Option Nomm) (HOT N BAT B LONG JH KK : Noun) (nm : Nomm) : Prop :=
  ∀ CA nm', I CA → walk nm = some nm' → ∃ CA', I CA' ∧
    nock (C inlTrap (C nm.toNoun (inlR HOT N BAT B LONG JH CA KK))) inlTrap = some (C nm'.toNoun CA')

/-- **The trap of `+inlined` on any nomm** is `inlWalk`, threading the
cache, given the `%2` case with an `info`. -/
theorem inl_trap (calls : Bell → Bell → Bool) (hot single : Bell → Bool) (go : Bell → Option Nomm)
    (I : Noun → Prop) (HOT N BAT B LONG JH KK : Noun)
    (h2 : ∀ p q c k, TrapP I (inlWalk calls hot single go) HOT N BAT B LONG JH KK p →
      TrapP I (inlWalk calls hot single go) HOT N BAT B LONG JH KK q →
      TrapP I (inlWalk calls hot single go) HOT N BAT B LONG JH KK (Nomm.n2 p q (some (c, k)))) :
    ∀ nm, TrapP I (inlWalk calls hot single go) HOT N BAT B LONG JH KK nm := by
  intro nm
  induction nm with
  | cons p q ihp ihq =>
    intro CA nm' hI hw
    simp only [inlWalk, Option.bind_eq_some_iff, Option.some.injEq] at hw
    obtain ⟨r1, w1, r2, w2, rfl⟩ := hw
    obtain ⟨CA1, hI1, e1⟩ := ihp CA r1 hI w1
    obtain ⟨CA2, hI2, e2⟩ := ihq CA1 r2 hI1 w2
    refine ⟨CA2, hI2, ?_⟩
    obtain ⟨x, y, hxy⟩ := nomm_cell p
    rw [hxy] at e1
    conv => { lhs; arg 2; unfold inlTrap }
    unfold inlR at e1 e2 ⊢
    simp [nock_exec, Nomm.toNoun, Tag.mean, inlBCons, hxy, e1, e2]
  | n0 a =>
    intro CA nm' hI hw
    simp only [inlWalk, Option.some.injEq] at hw
    subst hw
    refine ⟨CA, hI, ?_⟩
    conv => { lhs; arg 2; unfold inlTrap }
    unfold inlR
    simp [nock_exec, Nomm.toNoun]
  | n1 k =>
    intro CA nm' hI hw
    simp only [inlWalk, Option.some.injEq] at hw
    subst hw
    refine ⟨CA, hI, ?_⟩
    conv => { lhs; arg 2; unfold inlTrap }
    unfold inlR
    simp [nock_exec, Nomm.toNoun]
  | n2 p q info ihp ihq =>
    cases info with
    | none =>
      intro CA nm' hI hw
      simp only [inlWalk, Option.bind_eq_some_iff, Option.some.injEq] at hw
      obtain ⟨r1, w1, r2, w2, rfl⟩ := hw
      obtain ⟨CA1, hI1, e1⟩ := ihp CA r1 hI w1
      obtain ⟨CA2, hI2, e2⟩ := ihq CA1 r2 hI1 w2
      refine ⟨CA2, hI2, ?_⟩
      conv => { lhs; arg 2; unfold inlTrap }
      unfold inlR at e1 e2 ⊢
      simp [nock_exec, Nomm.toNoun, Tag.mean, unitNoun, inlB2, e1, e2]
    | some ck =>
      obtain ⟨c, k⟩ := ck
      exact h2 p q c k ihp ihq
  | n3 p ihp =>
    intro CA nm' hI hw
    simp only [inlWalk, Option.bind_eq_some_iff, Option.some.injEq] at hw
    obtain ⟨r1, w1, rfl⟩ := hw
    obtain ⟨CA1, hI1, e1⟩ := ihp CA r1 hI w1
    refine ⟨CA1, hI1, ?_⟩
    conv => { lhs; arg 2; unfold inlTrap }
    unfold inlR at e1 ⊢
    simp [nock_exec, Nomm.toNoun, Tag.mean, inlB3, e1]
  | n4 p ihp =>
    intro CA nm' hI hw
    simp only [inlWalk, Option.bind_eq_some_iff, Option.some.injEq] at hw
    obtain ⟨r1, w1, rfl⟩ := hw
    obtain ⟨CA1, hI1, e1⟩ := ihp CA r1 hI w1
    refine ⟨CA1, hI1, ?_⟩
    conv => { lhs; arg 2; unfold inlTrap }
    unfold inlR at e1 ⊢
    simp [nock_exec, Nomm.toNoun, Tag.mean, inlB4, e1]
  | n5 p q ihp ihq =>
    intro CA nm' hI hw
    simp only [inlWalk, Option.bind_eq_some_iff, Option.some.injEq] at hw
    obtain ⟨r1, w1, r2, w2, rfl⟩ := hw
    obtain ⟨CA1, hI1, e1⟩ := ihp CA r1 hI w1
    obtain ⟨CA2, hI2, e2⟩ := ihq CA1 r2 hI1 w2
    refine ⟨CA2, hI2, ?_⟩
    conv => { lhs; arg 2; unfold inlTrap }
    unfold inlR at e1 e2 ⊢
    simp [nock_exec, Nomm.toNoun, Tag.mean, inlB5, e1, e2]
  | n6 p q r ihp ihq ihr =>
    intro CA nm' hI hw
    simp only [inlWalk, Option.bind_eq_some_iff, Option.some.injEq] at hw
    obtain ⟨r1, w1, r2, w2, r3, w3, rfl⟩ := hw
    obtain ⟨CA1, hI1, e1⟩ := ihp CA r1 hI w1
    obtain ⟨CA2, hI2, e2⟩ := ihq CA1 r2 hI1 w2
    obtain ⟨CA3, hI3, e3⟩ := ihr CA2 r3 hI2 w3
    refine ⟨CA3, hI3, ?_⟩
    conv => { lhs; arg 2; unfold inlTrap }
    unfold inlR at e1 e2 e3 ⊢
    simp [nock_exec, Nomm.toNoun, Tag.mean, inlB6, e1, e2, e3]
  | n7 p q ihp ihq =>
    intro CA nm' hI hw
    simp only [inlWalk, Option.bind_eq_some_iff, Option.some.injEq] at hw
    obtain ⟨r1, w1, r2, w2, rfl⟩ := hw
    obtain ⟨CA1, hI1, e1⟩ := ihp CA r1 hI w1
    obtain ⟨CA2, hI2, e2⟩ := ihq CA1 r2 hI1 w2
    refine ⟨CA2, hI2, ?_⟩
    conv => { lhs; arg 2; unfold inlTrap }
    unfold inlR at e1 e2 ⊢
    simp [nock_exec, Nomm.toNoun, Tag.mean, inlB7, e1, e2]
  | n10 a v q ihv ihq =>
    intro CA nm' hI hw
    simp only [inlWalk, Option.bind_eq_some_iff, Option.some.injEq] at hw
    obtain ⟨r1, w1, r2, w2, rfl⟩ := hw
    obtain ⟨CA1, hI1, e1⟩ := ihv CA r1 hI w1
    obtain ⟨CA2, hI2, e2⟩ := ihq CA1 r2 hI1 w2
    refine ⟨CA2, hI2, ?_⟩
    conv => { lhs; arg 2; unfold inlTrap }
    unfold inlR at e1 e2 ⊢
    simp [nock_exec, Nomm.toNoun, Tag.mean, inlB10, e1, e2]
  | n11s t q body ihq =>
    intro CA nm' hI hw
    simp only [inlWalk, Option.bind_eq_some_iff, Option.some.injEq] at hw
    obtain ⟨r1, w1, rfl⟩ := hw
    obtain ⟨CA1, hI1, e1⟩ := ihq CA r1 hI w1
    refine ⟨CA1, hI1, ?_⟩
    conv => { lhs; arg 2; unfold inlTrap }
    unfold inlR at e1 ⊢
    simp [nock_exec, Nomm.toNoun, Tag.mean, inlB11, e1]
  | n11d t h q body ihh ihq =>
    intro CA nm' hI hw
    simp only [inlWalk, Option.bind_eq_some_iff, Option.some.injEq] at hw
    obtain ⟨r1, w1, r2, w2, rfl⟩ := hw
    obtain ⟨CA1, hI1, e1⟩ := ihh CA r1 hI w1
    obtain ⟨CA2, hI2, e2⟩ := ihq CA1 r2 hI1 w2
    refine ⟨CA2, hI2, ?_⟩
    conv => { lhs; arg 2; unfold inlTrap }
    unfold inlR at e1 e2 ⊢
    simp [nock_exec, Nomm.toNoun, Tag.mean, inlB11, e1, e2]
  | n12 p q ihp ihq =>
    intro CA nm' hI hw
    simp only [inlWalk, Option.bind_eq_some_iff, Option.some.injEq] at hw
    obtain ⟨r1, w1, r2, w2, rfl⟩ := hw
    obtain ⟨CA1, hI1, e1⟩ := ihp CA r1 hI w1
    obtain ⟨CA2, hI2, e2⟩ := ihq CA1 r2 hI1 w2
    refine ⟨CA2, hI2, ?_⟩
    conv => { lhs; arg 2; unfold inlTrap }
    unfold inlR at e1 e2 ⊢
    simp [nock_exec, Nomm.toNoun, Tag.mean, inlB12, e1, e2]
  | mean p b q body k ihp ihq =>
    intro CA nm' hI hw
    simp only [inlWalk, Option.bind_eq_some_iff, Option.some.injEq] at hw
    obtain ⟨r1, w1, r2, w2, rfl⟩ := hw
    obtain ⟨CA1, hI1, e1⟩ := ihp CA r1 hI w1
    obtain ⟨CA2, hI2, e2⟩ := ihq CA1 r2 hI1 w2
    refine ⟨CA2, hI2, ?_⟩
    conv => { lhs; arg 2; unfold inlTrap }
    unfold inlR at e1 e2 ⊢
    simp [nock_exec, Nomm.toNoun, Tag.mean, inlBMean, e1, e2]

end Compiler
end Formalization
