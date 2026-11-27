import lemmas.Compiler.CompShapeColFix

/-!
# `+inter2-orig` with forks

`oi_gate`: the gate body of `+inter2-orig` (arm `1367` of `K`, `oiBody` of
`CompShapeCol.lean`) on `[[intr fix less] K]` is `orig less intr fix`
(`Ska/ShapeCol.lean`), forks to any depth; `none` is the crash of
`?>  ?=(^ fixes)` (`fix` with fewer forks than `intr` at some node).  Its
trap over `forks` and `fixes` is `origLoop` (`oi_loop`, mutual with
`oi_gate`): the two recursive calls on the branches, then
`+msg-need-ord-fix-aware` of their results with `sure.fix` (`fx_gate_K`)
united into the accumulator (`uno_gate`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The subject of the trap of `+inter2-orig`: `[trap [fixes [forks [acc core]]]]`. -/
def oiT (FIXES FORKS : Noun) (acc : NeedOrd) (CORE : Noun) : Noun := C oiTrap (C FIXES (C FORKS (C acc.toNoun CORE)))

/-- The core of `+inter2-orig` with `fix` of sure `fs`. -/
def oiCore (INTR : Noun) (fs : NeedOrd) (FFK : Noun) (less : Cape) : Noun :=
  C oiBody (C (C INTR (C (C fs.toNoun FFK) less.toNoun)) compK)

mutual
/-- **`+inter2-orig`** is `orig`. -/
theorem oi_gate (less : Cape) : ∀ intr fix : I2,
    nock (C oiBody (C (C intr.toNoun (C fix.toNoun less.toNoun)) compK)) oiBody = (orig less intr fix).map NeedOrd.toNoun
  | I2.mk s fk, I2.mk fs ffk => by
    have h := oi_loop less fs (I2.mk s fk).toNoun (I2.forksNoun ffk) fk ffk s
    unfold oiT oiCore at h
    simp only [I2.toNoun_mk] at h ⊢
    rw [orig]
    conv => { lhs; arg 2; unfold oiBody }
    rw [← I2.forksNoun_eq, ← I2.forksNoun_eq] at h
    generalize oiTrap = OT at h ⊢
    generalize oiBody = OB at h ⊢
    generalize compK = KC at h ⊢
    simp [nock_exec, h]

/-- **The trap of `+inter2-orig`** over `forks` and `fixes` is `origLoop`. -/
theorem oi_loop (less : Cape) (fs : NeedOrd) (INTR FFK : Noun) : ∀ (fk ffk : List (I2 × I2)) (acc : NeedOrd),
    nock (oiT (listN (ffk.map I2.forkN)) (listN (fk.map I2.forkN)) acc (oiCore INTR fs FFK less)) oiTrap
      = (origLoop less fs fk ffk acc).map NeedOrd.toNoun
  | [], ffk, acc => by
    unfold oiT oiCore
    conv => { lhs; arg 2; unfold oiTrap }
    generalize oiTrap = OT
    generalize oiFork = OF
    generalize oiBody = OB
    simp [nock_exec, listN, origLoop]
  | (y, n) :: r, [], acc => by
    unfold oiT oiCore
    conv => { lhs; arg 2; unfold oiTrap }
    generalize oiTrap = OT
    generalize oiFork = OF
    generalize oiBody = OB
    simp [nock_exec, listN, origLoop, I2.forkN]
  | (y, n) :: r, (fy, fn) :: fr, acc => by
    have hy := oi_gate less y fy
    have hn := oi_gate less n fn
    have hfa := fx_at
    have hua := uno_at
    unfold oiT oiCore
    rw [origLoop]
    cases ey : orig less y fy with
    | none =>
      rw [ey] at hy
      conv => { lhs; arg 2; unfold oiTrap oiFork }
      generalize oiTrap = OT at hy ⊢
      generalize oiBody = OB at hy ⊢
      generalize compK = KC at hy hfa hua ⊢
      simp [nock_exec, listN, I2.forkN, hy]
    | some oy =>
      cases en : orig less n fn with
      | none =>
        rw [ey] at hy; rw [en] at hn
        conv => { lhs; arg 2; unfold oiTrap oiFork }
        generalize oiTrap = OT at hy hn ⊢
        generalize oiBody = OB at hy hn ⊢
        generalize compK = KC at hy hn hfa hua ⊢
        simp [nock_exec, listN, I2.forkN, hy, hn]
      | some on =>
        rw [ey] at hy; rw [en] at hn
        have hm := fx_gate_K fs oy on less
        have hu := uno_gate compK compK_cn acc (msgFix oy on fs less)
        have ih := oi_loop less fs INTR FFK r fr (uniOrd acc (msgFix oy on fs less))
        unfold oiT oiCore at ih
        unfold fxS at hm
        simp only [Option.bind_some]
        rw [← ih]
        conv => { lhs; arg 2; unfold oiTrap oiFork }
        generalize oiTrap = OT at hy hn ih ⊢
        generalize oiBody = OB at hy hn ih ⊢
        generalize compK = KC at hy hn hfa hua hm hu ih ⊢
        simp [nock_exec, listN, I2.forkN, hy, hn, hfa, fx_arm, hm, hua, uno_arm, hu]
end

end Compiler
end Formalization
