import lemmas.Compiler.OptLinkOnce

/-!
# `+optimize-once` after the structural loop, step by step

```hoon
  =^  f-alias=?  blocks.s  (alias n-args.s blocks.s rev topo)
  =.  topo  (skim topo ~(has by blocks.s))
  =.  rev  (rev-cfg blocks.s (sy topo))
  =.  blocks.s  (trim-trace-hints blocks.s topo rev)
  =.  blocks.s  (remove-dead-code blocks.s (flop topo))
  =^  c-hops=?  blocks.s  (remove-hops blocks.s rev topo)
  =^  c-branch=?  blocks.s  (remove-useless-branching blocks.s)
  =^  c-middle=?  blocks.s  (remove-empty-middle blocks.s)
  [|(f-alias c-hops c-branch c-middle) s]
```

`ooAfter` (`OptLinkOnce.lean`) is a chain of `[7 ...]`; `ooAfterCut` is the
same noun with each rest named (`ooR1` to `ooR12`, `ooFin`, by
`tools/gen/optlink.py ooa`), `ooAfter_cut`.  Each step is stated as the
subject it leaves: `ooX TP RV R0 T0 NEED nargs BL` is the subject after the
`=^` of the loop, `[[topo rev] [rev0 [topo0 [ooBody [[need [n-args blocks]]
optC]]]]]` (`rev0` and `topo0`, the values before the loop, are never read
again), with the flags of the passes run so far pushed in front.

* `oo_s0`: the loop's product `[[topo rev] blocks]` goes into the subject.
* `oo_alias`: `+alias`, from `AliasLink`.
* `oo_skimrev`: `+skim` with `~(has by blocks)` (`skim_has`) and `+rev-cfg`
  with `(sy topo)` (`si_gate`, `rev_gate`).
* `oo_trimdead`: `+trim-trace-hints` from `TrimLink`, `+remove-dead-code` on
  `(flop topo)` (`rdc_gate`).
* `oo_hops`, `oo_rub`, `oo_rem`: the three passes (`rh_gate`, `rub_gate`,
  `rem_gate`).
* `oo_fin`: the product, the flag `|(f-alias c-hops c-branch c-middle)` with
  the four booleans split.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The pieces of `ooAfter` -/

/-- `[|(f-alias c-hops c-branch c-middle) s]`. -/
def ooFin : Noun :=
  (C (C (A 6) (C (C (A 0) (A 30)) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 0) (A 14)) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 0) (A 6)) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 0) (A 2)) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))))))))) (C (A 0) (A 1022)))

/-- The edit of `blocks.s` by the product of `+remove-empty-middle`, then the rest. -/
def ooR12 : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 4091) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) ooFin))))

/-- `=^  c-middle=?  blocks.s  (remove-empty-middle blocks.s)` and the rest. -/
def ooR11 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 2940) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 4091))) (C (A 0) (A 2)))))))))) ooR12))))

/-- The edit of `blocks.s` by the product of `+remove-useless-branching`, then the rest. -/
def ooR10 : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 2043) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) ooR11))))

/-- `=^  c-branch=?  blocks.s  (remove-useless-branching blocks.s)` and the rest. -/
def ooR9 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 363) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 2043))) (C (A 0) (A 2)))))))))) ooR10))))

/-- The edit of `blocks.s` by the product of `+remove-hops`, then the rest. -/
def ooR8 : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 1019) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) ooR9))))

/-- `=^  c-hops=?  blocks.s  (remove-hops blocks.s rev topo)` and the rest. -/
def ooR7 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 4) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1019)) (C (C (A 0) (A 29)) (C (A 0) (A 28))))) (C (A 0) (A 2)))))))))) ooR8))))

/-- `=.  blocks.s  (remove-dead-code blocks.s (flop topo))` and the rest. -/
def ooR6 : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 507) (C (A 8) (C (C (A 9) (C (A 724) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1019)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0x2fbd7f) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) ooR7))

/-- `=.  blocks.s  (trim-trace-hints blocks.s topo rev)` and the rest. -/
def ooR5 : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 507) (C (A 8) (C (C (A 9) (C (A 23) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1019)) (C (C (A 0) (A 28)) (C (A 0) (A 29))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) ooR6))

/-- `=.  rev  (rev-cfg blocks.s (sy topo))` and the rest. -/
def ooR4 : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 13) (C (A 8) (C (C (A 9) (C (A 732) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1019)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 42) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) ooR5))

/-- `=.  topo  (skim topo ~(has by blocks.s))` and the rest. -/
def ooR3 : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 12) (C (A 8) (C (C (A 9) (C (A 0x5f7bb) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 3061) (C (A 10) (C (C (A 6) (C (A 0) (A 1019))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) ooR4))

/-- The edit of `blocks.s` by the product of `+alias`, then the rest. -/
def ooR2 : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 507) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) ooR3))))

/-- `=^  f-alias=?  blocks.s  (alias n-args.s blocks.s rev topo)` and the rest. -/
def ooR1 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 725) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 506)) (C (C (A 0) (A 507)) (C (C (A 0) (A 13)) (C (A 0) (A 12)))))) (C (A 0) (A 2)))))))))) ooR2))))

/-- `ooAfter` with its pieces named. -/
def ooAfterCut : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 251) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) ooR1))))

theorem ooAfter_cut : ooAfter = ooAfterCut := by
  unfold ooAfter ooAfterCut ooR1 ooR2 ooR3 ooR4 ooR5 ooR6 ooR7 ooR8 ooR9 ooR10 ooR11 ooR12 ooFin
  rfl

/-! ## The arms called -/

/-- The arm `+alias` as `alias_at` reads it. -/
noncomputable def aliasArmN : Noun :=
  C (A 7) (C (C (A 8) (C (C (A 1) aliasBunt) (C (C (A 1) aliasBody) (C (A 0) (A 1))))) ooAliasHint)

theorem alias_at' : slot? 725 optC = some aliasArmN := alias_at

@[nock_exec] theorem alias_arm (d : Noun) : nock d aliasArmN = some (C aliasBody (C aliasBunt d)) := by
  unfold aliasArmN ooAliasHint; generalize aliasBody = B; generalize aliasBunt = U; simp [nock_exec]

/-- The arm `+trim-trace-hints` as `trim_at` reads it. -/
noncomputable def trimArmN : Noun :=
  C (A 7) (C (C (A 8) (C (C (A 1) trimBunt) (C (C (A 1) trimBody) (C (A 0) (A 1))))) ooTrimHint)

theorem trim_at' : slot? 23 optC = some trimArmN := trim_at

@[nock_exec] theorem trim_arm (d : Noun) : nock d trimArmN = some (C trimBody (C trimBunt d)) := by
  unfold trimArmN ooTrimHint; generalize trimBody = B; generalize trimBunt = U; simp [nock_exec]

/-- The arm `+skim` of `layer2`, its hint and bunt. -/
def skimHint : Noun :=
  C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x6d696b73) (C (C (A 0) (A 7)) (A 0))))) (C (A 0) (A 1)))

def skimBunt : Noun := C (A 0) (C (C (A 0) (A 15)) (C (A 0) (C (A 0) (A 0))))

theorem skim_arm_eq : skim.arm
    = C (A 7) (C (C (A 8) (C (C (A 1) skimBunt) (C (C (A 1) skim.battery) (C (A 0) (A 1))))) skimHint) := by
  kernel_rfl

@[nock_exec] theorem skim_arm (d : Noun) : nock d skim.arm = some (C skim.battery (C skimBunt d)) := by
  rw [skim_arm_eq]; unfold skimHint; generalize skim.battery = B; generalize skimBunt = U; simp [nock_exec]

/-! ## The subject -/

/-- The noun of a treap of blocks. -/
abbrev blN (bl : TreapMap mugF Blob) : Noun := HoonMap.toNoun Blob.toNoun bl

/-- The subject after the `=^` of the loop: `[[topo rev] [rev0 [topo0 [ooBody
[[need [n-args blocks]] optC]]]]]`. -/
def ooX (TP RV R0 T0 NEED : Noun) (nargs : Nat) (BL : Noun) : Noun :=
  C (C TP RV) (C R0 (C T0 (C ooBody (C (C NEED (C (A nargs) BL)) optC))))

/-! ## The steps -/

/-- The loop's product `[[topo rev] blocks]` goes into the subject. -/
theorem oo_s0 (TP RV BL' R0 T0 NEED : Noun) (nargs : Nat) (BL : Noun) :
    nock (C (C (C TP RV) BL') (C R0 (C T0 (C ooBody (C (C NEED (C (A nargs) BL)) optC))))) ooAfter
      = nock (ooX TP RV R0 T0 NEED nargs BL') ooR1 := by
  rw [ooAfter_cut]
  unfold ooX
  conv => lhs; arg 2; unfold ooAfterCut
  generalize optC = OC
  simp [nock_exec]

/-- **`+alias`**, from `AliasLink`. -/
theorem oo_alias (P : Opt.Passes (TreapMap mugF)) (hA : AliasLink P) (R0 T0 NEED : Noun) (nargs : Nat)
    (bl : TreapMap mugF Blob) (rev : TreapMap mugF (List Nat)) (topo : List Nat) (ra : Bool × TreapMap mugF Blob)
    (hl : NoLti bl) (h : P.alias nargs bl rev topo = some ra) :
    nock (ooX (listNoun A topo) (jarN rev) R0 T0 NEED nargs (blN bl)) ooR1
      = nock (C (flag ra.1) (ooX (listNoun A topo) (jarN rev) R0 T0 NEED nargs (blN ra.2))) ooR3 := by
  have ha := (hA nargs bl rev topo ra hl h).2
  have h1 := alias_at'
  unfold ooX blN
  conv => lhs; arg 2; unfold ooR1
  conv => lhs; arg 2; arg 2; arg 2; arg 2; unfold ooR2
  generalize optC = OC at ha h1
  generalize blN bl = BL at ha ⊢
  generalize blN ra.2 = BL' at ha ⊢
  generalize flag ra.1 = F at ha ⊢
  simp [nock_exec, h1, ha]

/-- **`+skim` and `+rev-cfg`**: `topo` filtered by the blocks, `rev` made
again from it. -/
theorem oo_skimrev (FA RV R0 T0 NEED : Noun) (nargs : Nat) (bl : TreapMap mugF Blob) (hl : NoLti bl)
    (topo : List Nat) :
    nock (C FA (ooX (listNoun A topo) RV R0 T0 NEED nargs (blN bl))) ooR3
      = nock (C FA (ooX (listNoun A (topo.filter fun o => (HoonMap.get bl o).isSome))
          (jarN (Opt.revCfg bl (topo.filter fun o => (HoonMap.get bl o).isSome))) R0 T0 NEED nargs (blN bl)))
          ooR5 := by
  have hs := skim_has bl topo
  obtain ⟨TS, hsi, hTS⟩ := si_gate (topo.filter fun o => (HoonMap.get bl o).isSome)
  have hrev := rev_gate bl hl _ TS hTS
  have hL := optC_layer2
  have h5a := rev_at
  have hsy := sy_at
  have hsya := sy_arm
  have hsk := skim.arm_at
  unfold ooX blN
  conv => lhs; arg 2; unfold ooR3 ooR4
  generalize optC = OC at hL hrev h5a
  generalize HoonMap.toNoun Blob.toNoun bl = BL at hs hrev ⊢
  generalize jarN (Opt.revCfg bl (topo.filter fun o => (HoonMap.get bl o).isSome)) = RV' at hrev ⊢
  simp [nock_exec, hL, hsk, skim_arm, by.arm_at, by_arm, by.has.arm_at, has_arm, hs, h5a, rev_arm, hsy, hsya,
    hsi, hrev]

theorem flop_atoms (l : List Nat) :
    nock (C flop.battery (C (listNoun A l) layer2)) flop.battery = some (listNoun A l.reverse) := by
  rw [listNoun_map_listN, listNoun_map_listN, flop_gate layer2 homoIn_layer2, List.map_reverse]

/-- **`+trim-trace-hints` and `+remove-dead-code`**, from `TrimLink`. -/
theorem oo_trimdead (P : Opt.Passes (TreapMap mugF)) (hT : TrimLink P) (FA R0 T0 NEED : Noun) (nargs : Nat)
    (bl bt bd : TreapMap mugF Blob) (topo : List Nat) (rev : TreapMap mugF (List Nat)) (hl : NoLti bl)
    (h1 : P.trim bl topo rev = some bt) (h2 : Opt.removeDeadCode bt topo.reverse = some bd) :
    nock (C FA (ooX (listNoun A topo) (jarN rev) R0 T0 NEED nargs (blN bl))) ooR5
      = nock (C FA (ooX (listNoun A topo) (jarN rev) R0 T0 NEED nargs (blN bd))) ooR7 := by
  obtain ⟨hlt, ht⟩ := hT bl topo rev bt hl h1
  have hd := rdc_gate bt hlt topo.reverse
  rw [h2, Option.map_some] at hd
  have hL := optC_layer2
  have h1a := trim_at'
  have h2a := rdc_at
  have hfl := flop.arm_at
  have hf := flop_atoms topo
  unfold ooX blN
  conv => lhs; arg 2; unfold ooR5 ooR6
  generalize optC = OC at hL ht hd h1a h2a
  generalize HoonMap.toNoun Blob.toNoun bl = BL at ht ⊢
  generalize HoonMap.toNoun Blob.toNoun bt = BT at ht hd ⊢
  generalize HoonMap.toNoun Blob.toNoun bd = BD at hd ⊢
  simp [nock_exec, hL, h1a, trim_arm, ht, h2a, rdc_arm, hd, hfl, flop_arm, hf]

/-- **`+remove-hops`**. -/
theorem oo_hops (fuel : Nat) (FA R0 T0 NEED : Noun) (nargs : Nat) (bl : TreapMap mugF Blob)
    (rev : TreapMap mugF (List Nat)) (topo : List Nat) (r1 : Bool × TreapMap mugF Blob)
    (h : Opt.removeHops fuel bl rev topo = some r1) :
    nock (C FA (ooX (listNoun A topo) (jarN rev) R0 T0 NEED nargs (blN bl))) ooR7
      = nock (C (flag r1.1) (C FA (ooX (listNoun A topo) (jarN rev) R0 T0 NEED nargs (blN r1.2)))) ooR9 := by
  have hrh := rh_gate bl rev topo fuel r1 h
  have h1a := rh_at
  unfold ooX blN
  conv => lhs; arg 2; unfold ooR7 ooR8
  generalize optC = OC at hrh h1a
  generalize HoonMap.toNoun Blob.toNoun bl = BL at hrh ⊢
  generalize HoonMap.toNoun Blob.toNoun r1.2 = B1 at hrh ⊢
  generalize flag r1.1 = F at hrh ⊢
  simp [nock_exec, h1a, rh_arm, hrh]

/-- **`+remove-useless-branching`**. -/
theorem oo_rub (CH FA TP RV R0 T0 NEED : Noun) (nargs : Nat) (bl : TreapMap mugF Blob)
    (r2 : Bool × TreapMap mugF Blob) (h : Opt.removeUselessBranching bl = some r2) :
    nock (C CH (C FA (ooX TP RV R0 T0 NEED nargs (blN bl)))) ooR9
      = nock (C (flag r2.1) (C CH (C FA (ooX TP RV R0 T0 NEED nargs (blN r2.2))))) ooR11 := by
  have hrub := rub_gate bl
  rw [h, Option.map_some] at hrub
  have h1a := rub_at
  unfold ooX blN
  conv => lhs; arg 2; unfold ooR9 ooR10
  unfold rubN at hrub
  generalize optC = OC at hrub h1a
  generalize HoonMap.toNoun Blob.toNoun bl = BL at hrub ⊢
  generalize HoonMap.toNoun Blob.toNoun r2.2 = B1 at hrub ⊢
  generalize flag r2.1 = F at hrub ⊢
  simp [nock_exec, h1a, rub_arm, hrub]

/-- **`+remove-empty-middle`**. -/
theorem oo_rem (fuel : Nat) (CB CH FA TP RV R0 T0 NEED : Noun) (nargs : Nat) (bl : TreapMap mugF Blob)
    (hl : NoLti bl) (r3 : Bool × TreapMap mugF Blob) (h : Opt.removeEmptyMiddle fuel bl = some r3) :
    nock (C CB (C CH (C FA (ooX TP RV R0 T0 NEED nargs (blN bl))))) ooR11
      = nock (C (flag r3.1) (C CB (C CH (C FA (ooX TP RV R0 T0 NEED nargs (blN r3.2)))))) ooFin := by
  have hrem := rem_gate bl hl fuel r3 h
  have h1a := rem_at
  unfold ooX blN
  conv => lhs; arg 2; unfold ooR11 ooR12
  unfold remN at hrem
  generalize optC = OC at hrem h1a
  generalize HoonMap.toNoun Blob.toNoun bl = BL at hrem ⊢
  generalize HoonMap.toNoun Blob.toNoun r3.2 = B1 at hrem ⊢
  generalize flag r3.1 = F at hrem ⊢
  simp [nock_exec, h1a, rem_arm, hrem]

/-- **The product**: `[|(f-alias c-hops c-branch c-middle) s]`. -/
theorem oo_fin (fa c1 c2 c3 : Bool) (TP RV R0 T0 NEED : Noun) (nargs : Nat) (BL : Noun) :
    nock (C (flag c3) (C (flag c2) (C (flag c1) (C (flag fa) (ooX TP RV R0 T0 NEED nargs BL))))) ooFin
      = some (C (flag (fa || c1 || c2 || c3)) (C NEED (C (A nargs) BL))) := by
  unfold ooX ooFin
  generalize optC = OC
  cases fa <;> cases c1 <;> cases c2 <;> cases c3 <;> simp [nock_exec, flag]

end Compiler
end Formalization
