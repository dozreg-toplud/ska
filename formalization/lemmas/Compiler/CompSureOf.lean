import lemmas.Compiler.CompFinish

/-!
# `+sure-of` and `+inter1-to-inter2` on a fork-free input

```hoon
++  sure-of
  |=  [sur=sure-ordered less=cape]
  ^-  need-ordered
  sure:(inter1-to-inter2 [sur ~] less)
```

`+sure-of` (arm `0x2bae` of `K`, no `%fast` hint, its gate body `soBody`)
slams `+inter1-to-inter2` (arm `0xbbbb` of `K`, `%inter1-to-inter2`, its gate
body `i2Body`) on `[[sur ~] less]` and takes the head.  The gate body of
`+inter1-to-inter2` is the pair of `i2Rep`, a `+rep:in` over `lok.sure.intr`
from `ned.sure.intr` with the gate `i2Gate`, and `i2Turn`, a `+turn` over
`fork.intr`, here `~`.  The gate keeps `new` at axis `1` and at an axis
inside the known part of `less` (`+axe-in-less-cape`, `aic_gate`), and
otherwise runs the trap `i2Trap`, which walks `new` down to the axis,
splitting a `%none` or `%this` into two `%none`, puts `%this` at the axis
where `new` has `%none`, and rebuilds the cells with `+cons-need` (arm
`350` of `K`), a former `%this` or `%both` as a `%both`.

## The model

No model of `+sure-of` was in `lemmas/Ska`: it is written here.
`sureLook axe new` is the trap, `sureOfStep` the gate, and `sureOf ned lok
less` the fold of `sureOfStep` over `lok` in the order of `+rep:in`
(`HoonSet.toList`, preorder).  It is `none` exactly where the Nock crashes:
on the axis `0` in `lok` (`+axe-in-less-cape` asserts `!=(0 axe)`).

## The links

* `cn_gate_ord`: `+cons-need` on shapes is `consOrd`.
* `i2_trap`: the trap is `sureLook` from every axis `≥ 1`.
* `i2_gate_step`: the gate is `sureOfStep`.
* `i2_gate`: the gate of `+inter1-to-inter2` on `[[[ned lok] ~] less]` is
  `[sure ~]` with `sure` the noun of `sureOf ned lok less`.
* `so_gate`: the gate of `+sure-of` on `[[ned lok] less]` is `sureOf`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The model -/

/-- `+cons-need` on shapes. -/
def consOrd (a b : NeedOrd) : NeedOrd :=
  if a = NeedOrd.none ∧ b = NeedOrd.none then NeedOrd.none else NeedOrd.pair a b

/-- The halves the trap walks into: those of a cell or a `%both`, two
`%none` for a `%none` or a `%this`. -/
def ordHalves : NeedOrd → NeedOrd × NeedOrd
  | NeedOrd.pair p q => (p, q)
  | NeedOrd.both h t => (h, t)
  | _ => (NeedOrd.none, NeedOrd.none)

/-- The rebuild of the trap: the cell `x` of `+cons-need` itself under a
`%none` or a cell, and under a `%this` or a `%both` a `%both` of it, or
`%this` when it is `%none` (`?@  -.x  [%this ~]  [%both x]`). -/
def ordRebuild (new x : NeedOrd) : NeedOrd :=
  match new with
  | NeedOrd.none => x
  | NeedOrd.pair _ _ => x
  | _ => match x with
    | NeedOrd.pair a b => NeedOrd.both a b
    | _ => NeedOrd.this

/-- **The trap of `+inter1-to-inter2`**: the look at `axe` made sure in
`new`. -/
def sureLook (axe : Nat) (new : NeedOrd) : NeedOrd :=
  if _h : axe ≤ 1 then (if new = NeedOrd.none then NeedOrd.this else new) else
  ordRebuild new (if cap axe = 2 then consOrd (sureLook (mas axe) (ordHalves new).1) (ordHalves new).2
    else consOrd (ordHalves new).1 (sureLook (mas axe) (ordHalves new).2))
termination_by axe
decreasing_by all_goals exact mas_lt axe (by omega)

/-- **The gate of the `+rep:in`**: `new` at axis `1` and inside the known
part of `less`, `sureLook` otherwise, a crash at axis `0`. -/
noncomputable def sureOfStep (less : Cape) (new : NeedOrd) (axe : Nat) : Option NeedOrd :=
  if axe = 1 then some new else
  (axeInLessCape axe less).map fun inLess => if inLess then new else sureLook axe new

/-- **`+sure-of`** of `[ned lok]` under `less`: the fold of `sureOfStep`
over `lok` in the order of `+rep:in`. -/
noncomputable def sureOf (ned : NeedOrd) (lok : CSet) (less : Cape) : Option NeedOrd :=
  (HoonSet.toList lok).foldlM (fun new axe => sureOfStep less new axe) ned

/-! ## The nouns -/

/-- The trap of the gate of the `+rep:in`: the look at `axe` made sure in `new`. -/
def i2Trap : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 28)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 58)))) (C (C (A 1) (C (A 0x73696874) (A 0))) (C (A 0) (A 29))))) (C (A 8) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 58)))) (C (C (A 1) (A 0)) (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 58))))))) (C (C (A 7) (C (C (A 1) (C (A 0x656e6f6e) (A 0))) (C (C (A 0) (A 1)) (C (A 0) (A 1))))) (C (A 6) (C (C (A 3) (C (A 0) (A 58))) (C (C (A 0) (A 29)) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 58))))) (C (A 7) (C (C (A 0) (A 29)) (C (C (A 0) (A 6)) (C (A 0) (A 7))))))))))))) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 22) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 124))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 2)) (C (A 0) (A 2)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (C (A 8) (C (C (A 9) (C (A 47) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 124))) (C (A 0) (A 2)))))))) (C (A 0) (A 4)))) (C (A 0) (A 3)))))) (C (A 0) (A 5))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 3)) (C (A 0) (A 2))))) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 0) (A 4)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (C (A 8) (C (C (A 9) (C (A 47) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 124))) (C (A 0) (A 2)))))))) (C (A 0) (A 5)))) (C (A 0) (A 3)))))))))))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 350) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 12)) (C (A 0) (A 13)))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 506)))) (C (C (A 1) (A 0)) (C (A 3) (C (A 0) (A 506)))))) (C (C (A 0) (A 2)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 4))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (C (A 0x73696874) (A 0))) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 2))))))))))))))))))

/-- The gate of the `+rep:in` over `lok.sure.intr`. -/
def i2Gate : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 12)))) (C (C (A 0) (A 13)) (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 95) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 0) (A 125)))) (C (A 0) (A 2)))))))) (C (C (A 0) (A 13)) (C (A 8) (C (C (A 1) i2Trap) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))))))

/-- The `+rep:in` over `lok.sure.intr`. -/
def i2Rep : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 383) (C (A 10) (C (C (A 6) (C (A 0) (A 113))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (A 1) (A 0)) (C (A 0) (A 48))) (C (C (A 1) i2Gate) (C (A 0) (A 1)))))))) (C (A 0) (A 2))))))))

/-- The `+turn` over `fork.intr`. -/
def i2Turn : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 57)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (A 0)) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (A 0)))) (C (C (A 1) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 12))) (C (A 0) (A 7)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 13))) (C (A 0) (A 7)))))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))

/-- The gate body of `+inter1-to-inter2`. -/
def i2Body : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C i2Rep i2Turn)))

/-- Its sample bunt. -/
def i2Bunt : Noun :=
  (C (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (A 0)) (A 1))

/-- Its `%fast` hint. -/
def i2Hint : Noun :=
  (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x327265746e692d6f742d317265746e69) (C (C (A 0) (A 0x7fff)) (A 0))))) (C (A 0) (A 1))))

/-- The gate body of `+sure-of`. -/
def soBody : Noun :=
  (C (A 7) (C (C (A 8) (C (C (A 9) (C (A 0xbbbb) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (A 0) (A 12)) (C (A 1) (A 0))))) (C (A 0) (A 29)))) (C (A 0) (A 2)))))))) (C (A 0) (A 2))))

/-- Its sample bunt. -/
def soBunt : Noun :=
  (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (A 1))


/-- The arm `+inter1-to-inter2`. -/
def i2Arm : Noun := C (A 7) (C (C (A 8) (C (C (A 1) i2Bunt) (C (C (A 1) i2Body) (C (A 0) (A 1))))) i2Hint)

/-- `+inter1-to-inter2` is arm `0xbbbb` of `K`. -/
theorem i2_at : slot? 0xbbbb compK = some i2Arm := by kernel_rfl

/-- The arm `+sure-of`. -/
def soArm : Noun := C (A 8) (C (C (A 1) soBunt) (C (C (A 1) soBody) (C (A 0) (A 1))))

/-- `+sure-of` is arm `0x2bae` of `K`. -/
theorem so_at : slot? 0x2bae compK = some soArm := by kernel_rfl

theorem i2_arm (d : Noun) : nock d i2Arm = some (C i2Body (C i2Bunt d)) := by
  unfold i2Arm i2Hint; generalize i2Body = B; generalize i2Bunt = U; simp [nock_exec]

theorem so_arm (d : Noun) : nock d soArm = some (C soBody (C soBunt d)) := by
  unfold soArm; generalize soBody = B; generalize soBunt = U; simp [nock_exec]

/-! ## `+cons-need` on shapes -/

theorem ord_eqCode (n : Nat) (o : NeedOrd) : eqCode (A n) o.toNoun = A 1 := by
  obtain ⟨u, v, h⟩ := nord_cell o
  rw [h]; simp [eqCode]

theorem wut_ord (o : NeedOrd) : wut o.toNoun = A 0 := by
  obtain ⟨u, v, h⟩ := nord_cell o
  rw [h]; rfl

/-- **`+cons-need` on shapes** is `consOrd`. -/
theorem cn_gate_ord (K : Noun) (a b : NeedOrd) :
    nock (C cnBat (C (C a.toNoun b.toNoun) K)) cnBat = some (consOrd a b).toNoun := by
  unfold cnBat
  cases a <;> cases b <;> simp [nock_exec, NeedOrd.toNoun, consOrd, eqCode_atom, eqCode_self, Tag.none,
    Tag.both, Tag.this, ord_eqCode]

/-! ## The trap -/

/-- The core of the trap: `[i2Trap [i2Gate [[axe new] R]]]`. -/
def i2TC (axe : Nat) (new : NeedOrd) (R : Noun) : Noun := C i2Trap (C i2Gate (C (C (A axe) new.toNoun) R))

theorem i2_trap_one (R : Noun) (new : NeedOrd) :
    nock (i2TC 1 new R) i2Trap = some (sureLook 1 new).toNoun := by
  rw [sureLook.eq_def]
  conv => { lhs; arg 2; unfold i2Trap }
  unfold i2TC
  generalize i2Gate = G
  cases new <;> simp [nock_exec, NeedOrd.toNoun, Tag.none, Tag.this, Tag.both, ord_eqCode]

/-- `sureLook` from an axis `≥ 2`. -/
theorem sureLook_two (axe : Nat) (h2 : 2 ≤ axe) (new : NeedOrd) :
    sureLook axe new = ordRebuild new (if cap axe = 2
      then consOrd (sureLook (mas axe) (ordHalves new).1) (ordHalves new).2
      else consOrd (ordHalves new).1 (sureLook (mas axe) (ordHalves new).2)) := by
  rw [sureLook.eq_def]
  simp only [show ¬ (axe ≤ 1) by omega, dite_false]

theorem consOrd_cases (a b : NeedOrd) :
    (consOrd a b = NeedOrd.none ∧ a = NeedOrd.none ∧ b = NeedOrd.none) ∨ consOrd a b = NeedOrd.pair a b := by
  unfold consOrd
  by_cases h : a = NeedOrd.none ∧ b = NeedOrd.none
  · left; simp [h]
  · right; simp [h]

/-- **The trap of `+inter1-to-inter2`** from every axis `≥ 1`: `sureLook`. -/
theorem i2_trap (B S KC : Noun) (hK : slot? 0x1ffff KC = some layer1) (hcn : slot? 350 KC = some cnArm) :
    ∀ axe, 1 ≤ axe → ∀ new : NeedOrd,
    nock (i2TC axe new (C B (C S KC))) i2Trap = some (sureLook axe new).toNoun := by
  have har := cf_arith
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
    intro ha new
    by_cases a1 : axe = 1
    · subst a1; exact i2_trap_one _ new
    · have h2 : 2 ≤ axe := by omega
      have hcap := cap_gate layer1 har.2.2.2 axe h2
      have hmas := mas_gate layer1 har axe h2
      have hm1 : 1 ≤ masF axe := masF_pos axe h2
      have hm := mas_lt axe h2
      have hne : ¬ (1 = axe) := by omega
      rw [sureLook_two axe h2, ← masF_eq_mas]
      have ihh := ih (masF axe) (by rw [masF_eq_mas]; exact hm) hm1 (ordHalves new).1
      have iht := ih (masF axe) (by rw [masF_eq_mas]; exact hm) hm1 (ordHalves new).2
      unfold i2TC at ihh iht ⊢
      conv => { lhs; arg 2; unfold i2Trap }
      generalize i2Gate = G at ihh iht ⊢
      rcases capF_cases axe h2 with hc2 | hc3
      · have hc : cap axe = 2 := by rw [← capF_eq_cap]; exact hc2
        simp only [hc, if_true]
        have hcn' := cn_gate_ord KC (sureLook (masF axe) (ordHalves new).1) (ordHalves new).2
        generalize sureLook (masF axe) (ordHalves new).1 = r at ihh hcn' ⊢
        rcases consOrd_cases r (ordHalves new).2 with ⟨e, -, -⟩ | e <;> rw [e] at hcn' ⊢ <;>
        cases new <;>
        simp only [ordHalves, NeedOrd.toNoun, Tag.none] at ihh hcn' ⊢ <;>
        simp [nock_exec, NeedOrd.toNoun, Tag.none, Tag.this, Tag.both, ord_eqCode, hne, hK, cap_arm, cap.arm_at,
          hcap, hc2, mas_arm, mas.arm_at, hmas, ihh, hcn, cnArm, hcn', ordRebuild, wut_ord]
      · have hc : cap axe ≠ 2 := by rw [← capF_eq_cap, hc3]; omega
        simp only [hc, if_false]
        have hcn' := cn_gate_ord KC (ordHalves new).1 (sureLook (masF axe) (ordHalves new).2)
        generalize sureLook (masF axe) (ordHalves new).2 = r at iht hcn' ⊢
        rcases consOrd_cases (ordHalves new).1 r with ⟨e, -, -⟩ | e <;> rw [e] at hcn' ⊢ <;>
        cases new <;>
        simp only [ordHalves, NeedOrd.toNoun, Tag.none] at iht hcn' ⊢ <;>
        simp [nock_exec, NeedOrd.toNoun, Tag.none, Tag.this, Tag.both, ord_eqCode, hne, hK, cap_arm, cap.arm_at,
          hcap, hc3, mas_arm, mas.arm_at, hmas, iht, hcn, cnArm, hcn', ordRebuild, wut_ord]

/-! ## The gate of the `+rep:in` -/

/-- **The gate of the `+rep:in`** on an axis and an accumulator: `sureOfStep`. -/
theorem i2_gate_step (B INTR : Noun) (less : Cape) (axe : Nat) (new : NeedOrd) :
    nock (C i2Gate (C (C (A axe) new.toNoun) (C B (C (C INTR less.toNoun) compK)))) i2Gate
      = (sureOfStep less new axe).map NeedOrd.toNoun := by
  have ha := aic_gate compK compK_layer1 axe less
  have haa := aic_at
  have ht := i2_trap B (C INTR less.toNoun) compK compK_layer1 compK_cn
  unfold sureOfStep
  by_cases a1 : axe = 1
  · subst a1
    conv => { lhs; arg 2; unfold i2Gate }
    simp [nock_exec]
  · have a1' : ¬ (1 = axe) := fun h => a1 h.symm
    simp only [a1, if_false]
    by_cases a0 : axe = 0
    · subst a0
      simp [axeInLessCape] at ha
      conv => { lhs; arg 2; unfold i2Gate }
      generalize compK = KC at haa ha
      simp [nock_exec, haa, ha, axeInLessCape]
    · have ht' := ht axe (by omega) new
      unfold i2TC at ht'
      simp only [axeInLessCape, a0, if_false, Option.map_some] at ha ⊢
      conv => { lhs; arg 2; unfold i2Gate }
      generalize compK = KC at haa ha ht'
      generalize i2Trap = T at ht'
      cases e : axeInCape axe less
      · simp [nock_exec, a1', haa, ha, e, loob, ht']
      · simp [nock_exec, a1', haa, ha, e, loob]

/-! ## The gate of `+inter1-to-inter2` and of `+sure-of` -/

/-- **The `+rep:in` over `lok.sure.intr`** from `ned.sure.intr`: `sureOf`. -/
theorem i2_rep (NED : NeedOrd) (lok : CSet) (FORK : Noun) (less : Cape) :
    nock (C i2Body (C (C (C (C NED.toNoun (HoonSet.toNoun lok)) FORK) less.toNoun) compK)) i2Rep
      = (sureOf NED lok less).map NeedOrd.toNoun := by
  have hrep := rep_gate_list A NeedOrd.toNoun (fun axe acc => sureOfStep less acc axe) in.battery layer2 i2Gate
    (A 0) (C i2Body (C (C (C (C NED.toNoun (HoonSet.toNoun lok)) FORK) less.toNoun) compK)) (HoonSet.toNoun lok)
    (cs_tree _) (HoonSet.toList lok) (cs_preorder _) NED
    (fun p _ acc => i2_gate_step i2Body (C (C NED.toNoun (HoonSet.toNoun lok)) FORK) less p acc)
  have hL := compK_layer2
  unfold sureOf
  unfold i2Rep
  generalize i2Body = BD at hrep ⊢
  generalize i2Gate = GT at hrep ⊢
  generalize compK = KC at hrep hL ⊢
  simp [nock_exec, hL, in_arm, in.arm_at, in.rep.arm_at, rep_arm, hrep]

/-- The autocons of a formula that is a cell, kept folded. -/
theorem nock_pair (s X Y : Noun) (hX : ∃ b c, X = C b c) :
    nock s (C X Y) = (nock s X).bind fun l => (nock s Y).bind fun r => some (C l r) := by
  obtain ⟨b, c, rfl⟩ := hX
  exact nock_cell s b c Y

/-- **The gate of `+inter1-to-inter2`** on `[[[ned lok] ~] less]`: `[sure ~]`
with `sure` the noun of `sureOf ned lok less`, the `+turn` over `~` giving
`~`. -/
theorem i2_gate (NED : NeedOrd) (lok : CSet) (less : Cape) :
    nock (C i2Body (C (C (C (C NED.toNoun (HoonSet.toNoun lok)) (A 0)) less.toNoun) compK)) i2Body
      = (sureOf NED lok less).map fun r => C r.toNoun (A 0) := by
  have hr := i2_rep NED lok (A 0) less
  have hL := compK_layer2
  conv => { lhs; arg 2; unfold i2Body }
  rw [nock_op7]
  simp only [nock_op0, slot?_one, Option.bind_some]
  rw [nock_pair _ i2Rep i2Turn ⟨_, _, rfl⟩, hr]
  cases e : sureOf NED lok less with
  | none => rfl
  | some r =>
    simp only [Option.map_some, Option.bind_some]
    unfold i2Turn
    generalize i2Body = BD
    generalize compK = KC at hL
    simp [nock_exec, hL, turn.arm_at, turn_arm, fin_turn_nil]

/-- **The gate of `+sure-of`** on `[[ned lok] less]`: `sureOf ned lok less`. -/
theorem so_gate (NED : NeedOrd) (lok : CSet) (less : Cape) :
    nock (C soBody (C (C (C NED.toNoun (HoonSet.toNoun lok)) less.toNoun) compK)) soBody
      = (sureOf NED lok less).map NeedOrd.toNoun := by
  have hg := i2_gate NED lok less
  have hat := i2_at
  conv => { lhs; arg 2; unfold soBody }
  generalize compK = KC at hg hat ⊢
  cases e : sureOf NED lok less with
  | none =>
    rw [e] at hg
    simp [nock_exec, hat, i2_arm, hg]
  | some r =>
    rw [e] at hg
    simp [nock_exec, hat, i2_arm, hg]

end Compiler
end Formalization
