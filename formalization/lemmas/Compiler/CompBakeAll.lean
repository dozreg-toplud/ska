import lemmas.Compiler.CompBakeFits

/-!
# The trap `all` of `+bake-need` against the model

The branch of `+bake-need` that bakes a whole part (`bnYes`, the trap
`bnAll`): on a cell sock `j`, the trap puts the registers of the need with
their data on the front of `imm` (`bn_all`: `bakeAll`), through `hed:so`,
`tel:so` (`so_hed_gate`, `so_tel_gate`) and `+known-sock` (arm `1500` of
`K`, `ks_at`).  README Gaps 9, the MAP of 2026-11-27.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- `imm` of `$baked` as a noun. -/
def immNoun (imm : List (Nat × Noun)) : Noun := listNoun (fun p : Nat × Noun => C (A p.1) p.2) imm

theorem ks_at : slot? 1500 compK = some (C (A 8) (C (C (A 1) (C (A 1) (A 0))) (C (C (A 1) (C (A 6) (C (C (A 3)
    (C (A 0) (A 6))) (C (C (A 0) (A 6)) (C (A 0) (A 0)))))) (C (A 0) (A 1))))) := by
  kernel_rfl

/-- **The trap `all` of `+bake-need`** on a cell sock: `bakeAll`. -/
theorem bn_all (KNOW K0 : Noun) : ∀ (ned : Need) (c : Cape) (d : Noun) (imm : List (Nat × Noun)),
    nock (C bnAll (C (Sock.mk c d).toNoun (C bnLoop (C K0 (C (immNoun imm) (C bnBody
        (C (C ned.toNoun KNOW) compK))))))) bnAll
      = some (immNoun (bakeAll ned (Sock.mk c d) imm))
  | Need.none, c, d, imm => by
    conv => { lhs; arg 2; unfold bnAll }
    generalize bnAll = BA
    generalize bnLoop = LP
    generalize bnBody = BD
    simp [nock_exec, Need.toNoun, Sock.toNoun, Tag.none, bakeAll]
  | Need.this r, c, d, imm => by
    have hks := ks_at
    conv => { lhs; arg 2; unfold bnAll }
    generalize bnAll = BA
    generalize bnLoop = LP
    generalize bnBody = BD
    generalize compK = KC at hks ⊢
    simp [nock_exec, Need.toNoun, Sock.toNoun, Tag.none, Tag.this, bakeAll, hks, immNoun, listNoun, sockData]
  | Need.pair p q, c, d, imm => by
    obtain ⟨c1, d1, e1⟩ := so_hed_mk c d
    obtain ⟨c2, d2, e2⟩ := so_tel_mk c d
    have ihp := bn_all KNOW K0 p c1 d1 imm
    have ihq := bn_all KNOW K0 q c2 d2 (bakeAll p (Sock.mk c1 d1) imm)
    obtain ⟨a, b, hp⟩ := cd_need_cell p
    have hhed := so_hed_gate (C so.battery lib) (Sock.mk c d)
    have htel := so_tel_gate (C so.battery lib) (Sock.mk c d)
    rw [e1] at hhed
    rw [e2] at htel
    have hl := compK_lib
    simp only [bakeAll, e1, e2]
    rw [hp] at ihp
    simp only [Sock.toNoun] at hhed htel ihp ihq
    conv => { lhs; arg 2; unfold bnAll }
    generalize bnAll = BA at ihp ihq ⊢
    generalize bnLoop = LP at ihp ihq ⊢
    generalize bnBody = BD at ihp ihq ⊢
    generalize compK = KC at ihp ihq hl ⊢
    simp [nock_exec, Need.toNoun, Sock.toNoun, hp, Tag.none, Tag.this, hl, so.lib.arm_at, so_lib_arm,
      so.hed.arm_at, so_hed_arm, hhed, so.tel.arm_at, so_tel_arm, htel, ihp, ihq]
  | Need.both r h t, c, d, imm => by
    obtain ⟨c1, d1, e1⟩ := so_hed_mk c d
    obtain ⟨c2, d2, e2⟩ := so_tel_mk c d
    have ihh := bn_all KNOW K0 h c1 d1 ((r, d) :: imm)
    have iht := bn_all KNOW K0 t c2 d2 (bakeAll h (Sock.mk c1 d1) ((r, d) :: imm))
    have hhed := so_hed_gate (C so.battery lib) (Sock.mk c d)
    have htel := so_tel_gate (C so.battery lib) (Sock.mk c d)
    rw [e1] at hhed
    rw [e2] at htel
    have hl := compK_lib
    have hks := ks_at
    simp only [bakeAll, e1, e2, sockData]
    simp only [immNoun, listNoun] at ihh
    simp only [immNoun] at iht
    simp only [Sock.toNoun] at hhed htel ihh iht
    conv => { lhs; arg 2; unfold bnAll }
    generalize bnAll = BA at ihh iht ⊢
    generalize bnLoop = LP at ihh iht ⊢
    generalize bnBody = BD at ihh iht ⊢
    generalize compK = KC at ihh iht hl hks ⊢
    simp [nock_exec, Need.toNoun, Sock.toNoun, Tag.none, Tag.this, Tag.both, hl, so.lib.arm_at, so_lib_arm,
      so.hed.arm_at, so_hed_arm, hhed, so.tel.arm_at, so_tel_arm, htel, ihh, iht, hks, immNoun, listNoun]

end Compiler
end Formalization
