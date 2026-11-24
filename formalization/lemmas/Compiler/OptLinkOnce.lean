import lemmas.Compiler.OptLinkRub
import lemmas.Compiler.OptLinkDead
import lemmas.Compiler.OptLinkRev
import lemmas.Compiler.OptLinkTopo
import lemmas.Compiler.OptLinkHops
import lemmas.Compiler.OptLinkMiddleRd
import lemmas.Compiler.OptLinkNoLti
import lemmas.Compiler.OptLinkSy

/-!
# `+optimize-once`: the structural loop

```hoon
  =/  topo  (bb-topo blocks.s)
  =/  rev  (rev-cfg blocks.s (sy topo))
  =^  [topo=(list @uwoo) rev=(jar @uwoo @uwoo)]  blocks.s
    |-  ^-  [[(list @uwoo) (jar @uwoo @uwoo)] (map @uwoo blob)]
    =^  c-hops=?  blocks.s  (remove-hops blocks.s rev topo)
    =^  c-branch=?  blocks.s  (remove-useless-branching blocks.s)
    =^  c-middle=?  blocks.s  (remove-empty-middle blocks.s)
    ?.  |(c-hops c-branch c-middle)  [[topo rev] blocks.s]
    =.  topo  (bb-topo blocks.s)
    =.  rev  (rev-cfg blocks.s (sy topo))
    $
```

`+optimize-once` is arm `180` of `optC` (`oo_at`, nouns by
`tools/gen/optlink.py oo`): its body computes `topo` and `rev`, runs the
structural loop `ooLoop` and then `ooAfter` (`+alias`, `+trim-trace-hints`,
`+remove-dead-code`, the three passes once more).

* `oo_loop`: **where `structLoop fuel n` returns `(topo, rev, blocks)` on
  blocks with no `%lti`, the loop returns `[[topo rev] blocks]`**, by
  induction on `n`, from `rh_gate`, `rub_gate`, `rem_gate`, `bb_gate`,
  `rev_gate` with the set of `si_gate`, and `NoLti` kept by the passes.

* `structLoop_noLti`: the loop keeps `NoLti`.
* `AliasLink P`, `TrimLink P`: what the link of the whole gate is to assume
  of `+alias` (arm `725`, `alias_at`) and `+trim-trace-hints` (arm `23`,
  `trim_at`), their bodies read from the pill: where the field of `P`
  returns on blocks with no `%lti`, the gate returns the noun of the result,
  which has no `%lti`.
* `skim_has`: `(skim topo ~(has by blocks))` is the model's `filter`.

`ooAfter` is linked step by step in `OptLinkOnceAfter.lean` (one `simp`
over all of it went past the 3 GB cap) and the whole gate in
`OptLinkOnceGate.lean` (`oo_gate`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The nouns -/

/-- The `%fast` hint of `+alias`. -/
def ooAliasHint : Noun :=
  (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x7361696c61) (C (C (A 0) (A 0xffff)) (A 0))))) (C (A 0) (A 1))))

/-- The `%fast` hint of `+trim-trace-hints`. -/
def ooTrimHint : Noun :=
  (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x73746e69682d65636172742d6d697274) (C (C (A 0) (A 0xffff)) (A 0))))) (C (A 0) (A 1))))

/-- The structural loop of `+optimize-once`: the three passes, and `+bb-topo` and `+rev-cfg` again after a change. -/
def ooLoop : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 4) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 507)) (C (C (A 0) (A 14)) (C (A 0) (A 30))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 507) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 363) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 1019))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 1019) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 2940) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 2043))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 2043) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 6) (C (C (A 6) (C (C (A 0) (A 14)) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 0) (A 6)) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 0) (A 2)) (C (C (A 1) (A 0)) (C (A 1) (A 1))))))))))) (C (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 8) (C (C (A 9) (C (A 2942) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 4091))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 62) (C (A 8) (C (C (A 9) (C (A 732) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 4091)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 42) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 254))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 9) (C (A 2) (C (A 0) (A 15)))))))) (C (C (C (A 0) (A 126)) (C (A 0) (A 62))) (C (A 0) (A 2043))))))))))))))))))))))))))))))

/-- `+alias`, `+trim-trace-hints`, `+remove-dead-code` and the three passes once more. -/
def ooAfter : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 251) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 725) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 506)) (C (C (A 0) (A 507)) (C (C (A 0) (A 13)) (C (A 0) (A 12)))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 507) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 10) (C (C (A 12) (C (A 8) (C (C (A 9) (C (A 0x5f7bb) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 3061) (C (A 10) (C (C (A 6) (C (A 0) (A 1019))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 13) (C (A 8) (C (C (A 9) (C (A 732) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1019)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 42) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 507) (C (A 8) (C (C (A 9) (C (A 23) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1019)) (C (C (A 0) (A 28)) (C (A 0) (A 29))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 507) (C (A 8) (C (C (A 9) (C (A 724) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1019)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0x2fbd7f) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 4) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1019)) (C (C (A 0) (A 29)) (C (A 0) (A 28))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 1019) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 363) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 2043))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 2043) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 2940) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 4091))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 4091) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (A 6) (C (C (A 0) (A 30)) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 0) (A 14)) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 0) (A 6)) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 0) (A 2)) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))))))))) (C (A 0) (A 1022)))))))))))))))))))))))))))))))))))))))))))))))

/-- The gate body of `+optimize-once`. -/
def ooBody : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 2942) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 732) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 123)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 42) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2)))))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 1) ooLoop) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))) ooAfter))))))))

/-- Its sample bunt. -/
def ooBunt : Noun :=
  (C (C (A 0x656e6f6e) (A 0)) (C (A 0) (A 0)))

/-- Its `%fast` hint. -/
def ooHint : Noun :=
  (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x65636e6f2d657a696d6974706f) (C (C (A 0) (A 0xffff)) (A 0))))) (C (A 0) (A 1))))

/-- The arm `+optimize-once`. -/
def ooArm : Noun := C (A 7) (C (C (A 8) (C (C (A 1) ooBunt) (C (C (A 1) ooBody) (C (A 0) (A 1))))) ooHint)

/-- `+optimize-once` is arm `180` of `optC`. -/
theorem oo_at : slot? 180 optC = some ooArm := by kernel_rfl

/-! ## The structural loop -/

/-- The subject of the loop: `[ooLoop [rev [topo [ooBody [s optC]]]]]`, `s`
the straight `[need n-args blocks]`. -/
def ooL (rev : TreapMap mugF (List Nat)) (topo : List Nat) (NEED : Noun) (nargs : Nat) (bl : TreapMap mugF Blob) :
    Noun :=
  C ooLoop (C (jarN rev) (C (listNoun A topo) (C ooBody (C (C NEED (C (A nargs) (HoonMap.toNoun Blob.toNoun bl)))
    optC))))

theorem flag_true : flag true = A 0 := rfl
theorem flag_false : flag false = A 1 := rfl

/-- **The structural loop of `+optimize-once`**: where `structLoop fuel n`
returns, the loop returns `[[topo rev] blocks]`. -/
theorem oo_loop (fuel : Nat) (NEED : Noun) (nargs : Nat) :
    ∀ (n : Nat) (bl : TreapMap mugF Blob) (topo : List Nat) (rev : TreapMap mugF (List Nat))
      (r : List Nat × TreapMap mugF (List Nat) × TreapMap mugF Blob), NoLti bl →
    Opt.structLoop fuel n bl topo rev = some r →
    nock (ooL rev topo NEED nargs bl) ooLoop
      = some (C (C (listNoun A r.1) (jarN r.2.1)) (HoonMap.toNoun Blob.toNoun r.2.2)) := by
  intro n
  induction n with
  | zero => intro bl topo rev r hl h; simp [Opt.structLoop] at h
  | succ n ih =>
    intro bl topo rev r hl h
    simp only [Opt.structLoop] at h
    obtain ⟨r1, hr1, h1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r2, hr2, h2⟩ := Option.bind_eq_some_iff.mp h1
    obtain ⟨r3, hr3, h3⟩ := Option.bind_eq_some_iff.mp h2
    have hl1 : NoLti r1.2 := noLti_hops (bl' := r1.2) (ch := r1.1) hr1 hl
    have hl2 : NoLti r2.2 := noLti_rub (bl' := r2.2) (ch := r2.1) hr2 hl1
    have hl3 : NoLti r3.2 := noLti_mid (bl' := r3.2) (ch := r3.1) hr3 hl2
    have hrh := rh_gate bl rev topo fuel r1 hr1
    have hrub := rub_gate r1.2
    rw [hr2] at hrub
    have hrem := rem_gate r2.2 hl2 fuel r3 hr3
    have hL := optC_layer2
    have h1a := rh_at
    have h2a := rub_at
    have h3a := rem_at
    unfold ooL
    conv => lhs; arg 2; unfold ooLoop
    by_cases hc : (r1.1 || r2.1 || r3.1) = true
    · simp only [hc, Bool.not_true, Bool.false_eq_true, if_false] at h3
      obtain ⟨topo', ht', h4⟩ := Option.bind_eq_some_iff.mp h3
      have hn := ih r3.2 topo' (Opt.revCfg r3.2 topo') r hl3 h4
      have hbb := bb_gate r3.2 hl3 fuel topo' ht'
      obtain ⟨TS, hsi, hTS⟩ := si_gate topo'
      have hrev := rev_gate r3.2 hl3 topo' TS hTS
      have h4a := bb_at
      have h5a := rev_at
      have hsy := sy_at
      have hsya := sy_arm
      unfold ooL at hn
      generalize optC = OC at hL hn hrh hrub hrem hbb hrev h1a h2a h3a h4a h5a
      obtain ⟨c1, b1⟩ := r1
      obtain ⟨c2, b2⟩ := r2
      obtain ⟨c3, b3⟩ := r3
      simp only at hc hrh hrub hrem hbb hrev hn hl1 hl2 hl3
      cases c1 <;> cases c2 <;> cases c3 <;> simp at hc <;>
        simp [nock_exec, hL, h1a, rh_arm, hrh, h2a, rub_arm, hrub, rubN, h3a, rem_arm, hrem, remN, flag,
          h4a, bb_arm, hbb, h5a, rev_arm, hsy, hsya, hsi, hrev, hn]
    · simp only [Bool.not_eq_true] at hc
      simp only [hc, Bool.not_false, if_true, Option.some.injEq] at h3
      subst h3
      generalize optC = OC at hL hrh hrub hrem h1a h2a h3a
      obtain ⟨c1, b1⟩ := r1
      obtain ⟨c2, b2⟩ := r2
      obtain ⟨c3, b3⟩ := r3
      simp only at hc hrh hrub hrem
      cases c1 <;> cases c2 <;> cases c3 <;> simp at hc <;>
        simp [nock_exec, hL, h1a, rh_arm, hrh, h2a, rub_arm, hrub, rubN, h3a, rem_arm, hrem, remN, flag]

theorem structLoop_noLti (fuel : Nat) : ∀ (n : Nat) (bl : TreapMap mugF Blob) (topo : List Nat)
    (rev : TreapMap mugF (List Nat)) (r : List Nat × TreapMap mugF (List Nat) × TreapMap mugF Blob),
    NoLti bl → Opt.structLoop fuel n bl topo rev = some r → NoLti r.2.2 := by
  intro n
  induction n with
  | zero => intro bl topo rev r hl h; simp [Opt.structLoop] at h
  | succ n ih =>
    intro bl topo rev r hl h
    simp only [Opt.structLoop] at h
    obtain ⟨r1, hr1, h1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r2, hr2, h2⟩ := Option.bind_eq_some_iff.mp h1
    obtain ⟨r3, hr3, h3⟩ := Option.bind_eq_some_iff.mp h2
    have hl3 : NoLti r3.2 := noLti_mid (bl' := r3.2) (ch := r3.1) hr3
      (noLti_rub (bl' := r2.2) (ch := r2.1) hr2 (noLti_hops (bl' := r1.2) (ch := r1.1) hr1 hl))
    split at h3
    · simp only [Option.some.injEq] at h3; subst h3; exact hl3
    · obtain ⟨topo', -, h4⟩ := Option.bind_eq_some_iff.mp h3
      exact ih _ _ _ _ hl3 h4

/-! ## `+alias` and `+trim-trace-hints`, as hypotheses -/

/-- The arm `+alias` (axis `725` of `optC`), its body and bunt read from the
pill. -/
noncomputable def aliasArm : Noun := (slot? 725 optC).getD (A 0)
noncomputable def aliasBody : Noun := (slot? 109 aliasArm).getD (A 0)
noncomputable def aliasBunt : Noun := (slot? 53 aliasArm).getD (A 0)
theorem alias_at : slot? 725 optC
    = some (C (A 7) (C (C (A 8) (C (C (A 1) aliasBunt) (C (C (A 1) aliasBody) (C (A 0) (A 1))))) ooAliasHint)) := by
  kernel_rfl

/-- The arm `+trim-trace-hints` (axis `23` of `optC`). -/
noncomputable def trimArm : Noun := (slot? 23 optC).getD (A 0)
noncomputable def trimBody : Noun := (slot? 109 trimArm).getD (A 0)
noncomputable def trimBunt : Noun := (slot? 53 trimArm).getD (A 0)
theorem trim_at : slot? 23 optC
    = some (C (A 7) (C (C (A 8) (C (C (A 1) trimBunt) (C (C (A 1) trimBody) (C (A 0) (A 1))))) ooTrimHint)) := by
  kernel_rfl

/-- **What the link of `+optimize-once` assumes of `+alias`**: where
`P.alias` returns on blocks with no `%lti`, the gate on the nouns of its
arguments returns the noun of the result, which has no `%lti`. -/
def AliasLink (P : Opt.Passes (TreapMap mugF)) : Prop :=
  ∀ (nargs : Nat) (bl : TreapMap mugF Blob) (rev : TreapMap mugF (List Nat)) (topo : List Nat)
    (ra : Bool × TreapMap mugF Blob), NoLti bl → P.alias nargs bl rev topo = some ra →
    NoLti ra.2 ∧ nock (C aliasBody (C (C (A nargs) (C (HoonMap.toNoun Blob.toNoun bl) (C (jarN rev)
      (listNoun A topo)))) optC)) aliasBody = some (C (flag ra.1) (HoonMap.toNoun Blob.toNoun ra.2))

/-- **What the link of `+optimize-once` assumes of `+trim-trace-hints`**. -/
def TrimLink (P : Opt.Passes (TreapMap mugF)) : Prop :=
  ∀ (bl : TreapMap mugF Blob) (topo : List Nat) (rev : TreapMap mugF (List Nat)) (bt : TreapMap mugF Blob),
    NoLti bl → P.trim bl topo rev = some bt →
    NoLti bt ∧ nock (C trimBody (C (C (HoonMap.toNoun Blob.toNoun bl) (C (listNoun A topo) (jarN rev))) optC))
      trimBody = some (HoonMap.toNoun Blob.toNoun bt)

/-- `~(has by blocks)` as the gate of `+skim`. -/
theorem skim_has (bl : TreapMap mugF Blob) (topo : List Nat) :
    nock (C skim.battery (C (C (listNoun A topo) (C by.has.battery (C (A 0) (C by.battery
      (C (HoonMap.toNoun Blob.toNoun bl) layer2))))) layer2)) skim.battery
      = some (listNoun A (topo.filter fun o => (HoonMap.get bl o).isSome)) := by
  have h := skim_gate layer2 by.has.battery (A 0) (C by.battery (C (HoonMap.toNoun Blob.toNoun bl) layer2))
    (fun x => (HoonMap.get bl (OptDec.atomOf x)).isSome) (topo.map A) (fun x hx => by
      obtain ⟨o, -, rfl⟩ := List.mem_map.1 hx
      rw [has_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ (A o) _ _
        (getF_hoonMap Blob.toNoun bl o)]
      cases e : HoonMap.get bl o <;> simp [unitNoun, OptDec.atomOf, e, loob])
  rw [listNoun_map_listN, listNoun_map_listN, h, List.filter_map]
  rfl

end Compiler
end Formalization
