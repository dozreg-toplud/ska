import lemmas.Compiler.CompRunShapeMayCut
import lemmas.Compiler.CompRunShapeColl

/-!
# `+laze-may` (README Gaps 26, track A)

`lmy_gate`: the gate body of `+laze-may` (arm `0x2eeeb` of `K`, `lmyBody` of
`CompRunShapeMayCut.lean`) on `[laz less]` is `lazeMay laz less` (`Ska/RunShape.lean`) on every
`laze` over `CSet` and every cape, with no fuel: `+laze-to-inter1` (`lzt_gate`),
`+inter1-to-inter2` (`i12_gate`), then the trap (`lmy_trap`): the `+roll` over `fork.intr` from
`sure.intr` (`roll_gate_M`) whose gate (`lmy_gstep`) runs the trap again on both branches and
unites (`uno_gate`); `lmy_trap` and `lmy_roll` are one `mutual` block over `I2`.  `lmy_call`:
the formula `msMay` of `member` (`CompSccLoopMemShape.lean`), on a subject `S` with `K` at axis
`8191`, the `laze` at axis `2` and the cape at axis `2032`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- `lmyB` on a subject whose axis `31` is `K`: the bunt of `need-inter2`. -/
theorem lmy_b_at (S : Noun) (h : slot? 31 S = some compK) : nock S lmyB = some i2nBunt := by
  have hb := i2n_bunt
  unfold i2nBuntF at hb
  unfold lmyB
  simp only [nock_op7, nock_op9, nock_op0, h, slot?_one, Option.bind_some] at hb ⊢
  exact hb

/-- **The gate of the `+roll`** on a fork and the accumulator: the trap again on both branches,
then `+uni-need-ord` twice. -/
theorem lmy_gstep (INTR BD SM : Noun) (y n : I2) (acc : NeedOrd)
    (hy : nock (C lmyTrap (C y.toNoun (C BD (C SM compK)))) lmyTrap = some (mayGo y).toNoun)
    (hn : nock (C lmyTrap (C n.toNoun (C BD (C SM compK)))) lmyTrap = some (mayGo n).toNoun) :
    nock (C lmyGate (C (C (I2.forkN (y, n)) acc.toNoun) (C lmyTrap (C INTR (C BD (C SM compK)))))) lmyGate
      = some (uniOrd (uniOrd acc (mayGo y)) (mayGo n)).toNoun := by
  have hu := uno_gate compK compK_cn
  have hua := uno_at
  unfold lmyGate I2.forkN
  generalize lmyTrap = TR at hy hn ⊢
  generalize compK = KC at hu hua hy hn ⊢
  simp [nock_exec, hua, uno_arm, hy, hn, hu]

mutual
/-- **The trap of `+laze-may`** on every `need-inter2`: `mayGo`. -/
theorem lmy_trap (BD SM : Noun) : ∀ intr : I2,
    nock (C lmyTrap (C intr.toNoun (C BD (C SM compK)))) lmyTrap = some (mayGo intr).toNoun
  | I2.mk s f => by
    have hr := lmy_roll BD SM (I2.mk s f).toNoun f s
    have hL := compK_layer2
    have hroll := roll_gate_M layer2 lmyGate (C i2nBunt i2nBunt) s.toNoun
      (C lmyTrap (C (I2.mk s f).toNoun (C BD (C SM compK))))
      (fun x acc => nock (C lmyGate (C (C x acc) (C lmyTrap (C (I2.mk s f).toNoun (C BD (C SM compK)))))) lmyGate)
      (f.map I2.forkN) (fun _ _ _ => rfl)
    rw [hr] at hroll
    have hb := lmy_b_at (C lmyTrap (C (I2.mk s f).toNoun (C BD (C SM compK)))) rfl
    have hb2 : nock (C lmyTrap (C (I2.mk s f).toNoun (C BD (C SM compK)))) (C lmyB lmyB)
        = some (C i2nBunt i2nBunt) := by
      rw [nock_pair _ lmyB lmyB ⟨_, _, rfl⟩, hb]; rfl
    clear hb
    rw [mayGo]
    conv => { lhs; arg 2; unfold lmyTrap }
    simp only [I2.toNoun_mk, I2.forksNoun_eq] at hroll hb2 ⊢
    generalize lmyTrap = TR at hroll hb2 ⊢
    generalize compK = KC at hL hroll hb2 ⊢
    simp [nock_exec, hL, roll.arm_at, roll_arm, hb2, hroll]

/-- The `+roll` over the forks, on every fork list and accumulator. -/
theorem lmy_roll (BD SM INTR : Noun) : ∀ (f : List (I2 × I2)) (acc : NeedOrd),
    (f.map I2.forkN).foldlM (fun acc x => nock (C lmyGate (C (C x acc) (C lmyTrap (C INTR (C BD (C SM compK))))))
      lmyGate) acc.toNoun = some (mayF f acc).toNoun
  | [], acc => rfl
  | (y, n) :: r, acc => by
    have hs := lmy_gstep INTR BD SM y n acc (lmy_trap BD SM y) (lmy_trap BD SM n)
    have hr := lmy_roll BD SM INTR r (uniOrd (uniOrd acc (mayGo y)) (mayGo n))
    simp only [mayF]
    rw [List.map_cons, List.foldlM_cons, hs]
    exact hr
end

/-- **`+laze-may` on every `laze` and cape**: `lazeMay`. -/
theorem lmy_gate (laz : Laze CSet) (less : Cape) :
    nock (C lmyBody (C (C laz.toNoun less.toNoun) compK)) lmyBody = (lazeMay laz less).map NeedOrd.toNoun := by
  unfold lazeMay
  have hla := lzt_at
  have hl := lzt_gate laz
  have hia := i2_at
  have hi := i12_gate less (lazeToI1 laz)
  cases e : i12 less (lazeToI1 laz) with
  | none =>
    rw [e] at hi
    conv => { lhs; arg 2; unfold lmyBody }
    generalize I1.toNounC (lazeToI1 laz) = L at hl hi
    generalize lmyTrap = TR
    generalize lmyBody = BD
    generalize compK = KC at hla hl hia hi ⊢
    simp [nock_exec, hla, lzt_arm, hl, hia, i2_arm, hi]
  | some intr =>
    rw [e, Option.map_some] at hi
    have ht := lmy_trap lmyBody (C laz.toNoun less.toNoun) intr
    conv => { lhs; arg 2; unfold lmyBody }
    generalize I1.toNounC (lazeToI1 laz) = L at hl hi
    generalize lmyTrap = TR at ht ⊢
    generalize lmyBody = BD at ht ⊢
    generalize compK = KC at hla hl hia hi ht ⊢
    simp [nock_exec, hla, lzt_arm, hl, hia, i2_arm, hi, ht]

/-- **The call `(laze-may l cape.less.b)` of `member`** (`msMay`): on a subject with `K` at axis
`8191`, `l` at axis `2` and the cape at axis `2032`, `lazeMay`. -/
theorem lmy_call (S : Noun) (laz : Laze CSet) (less : Cape) (hk : slot? 8191 S = some compK)
    (hl : slot? 2 S = some laz.toNoun) (hc : slot? 2032 S = some less.toNoun) :
    nock S msMay = (lazeMay laz less).map NeedOrd.toNoun := by
  have hg := lmy_gate laz less
  have ha := lmy_at
  unfold msMay
  generalize compK = KC at hg ha hk
  simp [nock_exec, hk, ha, lmy_arm, hl, hc]
  exact hg

end Compiler
end Formalization
