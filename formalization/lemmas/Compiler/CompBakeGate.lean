import lemmas.Compiler.CompBakeAll

/-!
# `+bake-need` against the model, when it bakes

The test of a node in full (`bn_testG`: `?=(^ k)`, `all:ca`, `+need-fits`
by `nf_gate`), the loop on every need and sock (`bn_loopB`: `bakeGo`,
the branch that bakes by `bn_all`, the cells rebuilt by `+cons-need` on
any residual halves, a `%both` with two `%none` halves made `[%this r]`),
and the gate (`bn_gateB`: `bakedNoun (bakeNeed ned know)`).  No side
condition: `bn_gate` of `CompBakeNeed.lean` is the case `NoBake`.
README Gaps 9, the MAP of 2026-11-27.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- **The test of a node of `+bake-need`**, in full. -/
theorem bn_testG (IMM KNOW : Noun) (ned : Need) (k : Sock) (Y R : Noun) :
    nock (C bnLoop (C k.toNoun (C IMM (C bnBody (C (C ned.toNoun KNOW) compK))))) (C (A 6) (C bnTest (C Y R)))
      = if bakeTest (needFits ned) k
        then nock (C bnLoop (C k.toNoun (C IMM (C bnBody (C (C ned.toNoun KNOW) compK))))) Y
        else nock (C bnLoop (C k.toNoun (C IMM (C bnBody (C (C ned.toNoun KNOW) compK))))) R := by
  have hl := compK_lib
  have hnfat := nf_at
  unfold bnTest
  generalize bnLoop = LP
  generalize bnBody = BD
  cases k with
  | void => simp [nock_exec, Sock.toNoun, bakeTest]
  | mk c d =>
    have ha := ca_all_gate (C ca.battery lib) c
    have hnf := nf_gate ned d
    generalize nfBody = NB at hnf hnfat
    generalize compK = KC at hl hnf hnfat
    cases hc : Ca.all c with
    | false =>
      rw [hc] at ha
      simp [nock_exec, Sock.toNoun, hl, ca.lib.arm_at, ca_lib_arm, ca.all.arm_at, ca_all_arm, ha, loob, bakeTest, hc]
    | true =>
      rw [hc] at ha
      cases hf : needFits ned d with
      | false =>
        rw [hf] at hnf
        simp [nock_exec, Sock.toNoun, hl, ca.lib.arm_at, ca_lib_arm, ca.all.arm_at, ca_all_arm, ha, loob, bakeTest,
          hc, hf, hnfat, hnf]
      | true =>
        rw [hf] at hnf
        simp [nock_exec, Sock.toNoun, hl, ca.lib.arm_at, ca_lib_arm, ca.all.arm_at, ca_all_arm, ha, loob, bakeTest,
          hc, hf, hnfat, hnf]

/-- A passing test is on a cell sock. -/
theorem bakeTest_mk {f : Noun → Bool} {k : Sock} (h : bakeTest f k = true) : ∃ c d, k = Sock.mk c d := by
  cases k with
  | void => simp [bakeTest] at h
  | mk c d => exact ⟨c, d, rfl⟩

/-- The branch that bakes: `[[%none ~] (all ...)]`. -/
theorem bn_yes (KNOW : Noun) (ned : Need) (c : Cape) (d : Noun) (imm : List (Nat × Noun)) :
    nock (C bnLoop (C (Sock.mk c d).toNoun (C (immNoun imm) (C bnBody (C (C ned.toNoun KNOW) compK))))) bnYes
      = some (bakedNoun (Need.none, bakeAll ned (Sock.mk c d) imm)) := by
  have h := bn_all KNOW (Sock.mk c d).toNoun ned c d imm
  simp only [immNoun] at h
  unfold bnYes
  generalize bnAll = BA at h
  simp [nock_exec, h, bakedNoun, Need.toNoun, Tag.none, immNoun]

/-- **The loop of `+bake-need`** on every need and sock: `bakeGo`. -/
theorem bn_loopB (KNOW : Noun) : ∀ (ned : Need) (k : Sock) (imm : List (Nat × Noun)),
    nock (C bnLoop (C k.toNoun (C (immNoun imm) (C bnBody (C (C ned.toNoun KNOW) compK))))) bnLoop
      = some (bakedNoun (bakeGo ned k imm))
  | Need.none, k, imm => by
    rw [bn_unfold, bn_testG]
    split
    · next ht =>
      obtain ⟨c, d, rfl⟩ := bakeTest_mk ht
      rw [bn_yes]; simp [bakeGo, bakeAll]
    · unfold bnRec
      generalize bnLoop = LP
      generalize bnBody = BD
      simp [nock_exec, Need.toNoun, Tag.none, bakeGo, bakedNoun, immNoun]
  | Need.this r, k, imm => by
    rw [bn_unfold, bn_testG]
    split
    · next ht =>
      obtain ⟨c, d, rfl⟩ := bakeTest_mk ht
      rw [bn_yes]; simp [bakeGo, bakeAll, ht, sockData]
    · next ht =>
      unfold bnRec
      generalize bnLoop = LP
      generalize bnBody = BD
      simp [nock_exec, Need.toNoun, Tag.none, Tag.this, bakeGo, ht, bakedNoun, immNoun]
  | Need.pair p q, k, imm => by
    rw [bn_unfold, bn_testG]
    split
    · next ht =>
      obtain ⟨c, d, rfl⟩ := bakeTest_mk ht
      rw [bn_yes]; simp [bakeGo, ht]
    · next ht =>
      have ihp := bn_loopB KNOW p (So.hed k) imm
      have ihq := bn_loopB KNOW q (So.tel k) (bakeGo p (So.hed k) imm).2
      have hcn := cn_gate compK (bakeGo p (So.hed k) imm).1 (bakeGo q (So.tel k) (bakeGo p (So.hed k) imm).2).1
      obtain ⟨a, b, hp⟩ := cd_need_cell p
      rw [hp] at ihp
      have hhed := so_hed_gate (C so.battery lib) k
      have htel := so_tel_gate (C so.battery lib) k
      have hl := compK_lib
      have hcna := compK_cn
      unfold bnRec
      unfold cnArm at hcna
      simp only [bakedNoun, immNoun] at ihp ihq
      generalize bnLoop = LP at ihp ihq ⊢
      generalize bnBody = BD at ihp ihq ⊢
      generalize compK = KC at ihp ihq hcn hl hcna ⊢
      simp [nock_exec, Need.toNoun, hp, eqCode, hl, so.lib.arm_at, so_lib_arm, so.hed.arm_at, so_hed_arm, hhed,
        so.tel.arm_at, so_tel_arm, htel, ihp, ihq, hcna, hcn, bakeGo, ht, bakedNoun, immNoun]
  | Need.both r h t, k, imm => by
    rw [bn_unfold, bn_testG]
    split
    · next ht =>
      obtain ⟨c, d, rfl⟩ := bakeTest_mk ht
      rw [bn_yes]; simp [bakeGo, ht]
    · next ht =>
      have ihh := bn_loopB KNOW h (So.hed k) imm
      have iht := bn_loopB KNOW t (So.tel k) (bakeGo h (So.hed k) imm).2
      have hcn := cn_gate compK (bakeGo h (So.hed k) imm).1 (bakeGo t (So.tel k) (bakeGo h (So.hed k) imm).2).1
      obtain ⟨a, b, hh⟩ := cd_need_cell h
      rw [hh] at ihh
      have hhed := so_hed_gate (C so.battery lib) k
      have htel := so_tel_gate (C so.battery lib) k
      have hl := compK_lib
      have hcna := compK_cn
      unfold bnRec
      unfold cnArm at hcna
      simp only [bakedNoun, immNoun] at ihh iht
      simp only [bakeGo, ht, if_false]
      generalize ex : consNeed (bakeGo h (So.hed k) imm).1 (bakeGo t (So.tel k) (bakeGo h (So.hed k) imm).2).1 = x at hcn
      generalize bnLoop = LP at ihh iht ⊢
      generalize bnBody = BD at ihh iht ⊢
      generalize compK = KC at ihh iht hcn hl hcna ⊢
      cases x with
      | pair x1 x2 =>
        obtain ⟨a1, b1, hx⟩ := cd_need_cell x1
        simp only [Need.toNoun] at hcn
        rw [hx] at hcn
        simp [nock_exec, Need.toNoun, hh, hx, Tag.none, Tag.this, Tag.both, hl, so.lib.arm_at, so_lib_arm,
          so.hed.arm_at, so_hed_arm, hhed, so.tel.arm_at, so_tel_arm, htel, ihh, iht, hcna, hcn, bakedNoun, immNoun]
      | none =>
        simp [nock_exec, Need.toNoun, hh, Tag.none, Tag.this, Tag.both, hl, so.lib.arm_at, so_lib_arm,
          so.hed.arm_at, so_hed_arm, hhed, so.tel.arm_at, so_tel_arm, htel, ihh, iht, hcna, hcn, bakedNoun, immNoun]
      | this _ => simp [consNeed] at ex; split at ex <;> cases ex
      | both _ _ _ => simp [consNeed] at ex; split at ex <;> cases ex

/-- **The gate of `+bake-need`** on every need and sock: `bakeNeed`. -/
theorem bn_gateB (ned : Need) (know : Sock) :
    nock (C bnBody (C (C ned.toNoun know.toNoun) compK)) bnBody = some (bakedNoun (bakeNeed ned know)) := by
  have hl := bn_loopB know.toNoun ned know []
  simp only [immNoun, listNoun] at hl
  conv => { lhs; arg 2; unfold bnBody }
  generalize bnLoop = LP at hl
  generalize bnBody = BD at hl ⊢
  simp [nock_exec, hl, bakeNeed]

end Compiler
end Formalization
