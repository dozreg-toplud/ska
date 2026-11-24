import lemmas.Compiler.CompChaseFin

/-!
# The gate of the `+rep:by` of `+to-straight`: `TsStepAt` from `rj`

The gate `tsGBody` on a pair `[k b]` and an accumulator `new`, in the subject
`tsY` (`rename`, `[[%this ~] core]`), is `renameStep` (`ts_step`): its test
`&(!=(0w0 k) (bypassable & b))` (`ts_byp`), the slam of `rename` on
`b(fin [%bom ~])` (`mr_inner_bom`), `+chase-fin` on `fin.b` (`cf_gate`) and
`+put:by` (`put_gate`).  So `TsStepAt` holds given only the link of the gate
`rj` of `+chase-fin` in the core (`TsRjAt`, `ts_step_at`), and the end of
`+compile-unary` assumes only that (`cu_finish_rj`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- **The link of the gate `rj` of `+chase-fin`** in every core of the
renaming branch, stated. -/
def TsRjAt (ctx : Noun) : Prop :=
  ∀ (SB Bo BN D G : Noun) (o sub : Nat) (bs : TreapMap mugF Blob),
    CfRjAt (renReg sub 1) (tsSt SB (HoonMap.toNoun Blob.toNoun bs) Bo BN D G ctx o sub)

/-- The core of the renaming branch meets `CfCore`. -/
theorem ts_st_cf {ctx : Noun} (hc : CompIn ctx) (SB Bo BN D G : Noun) (o sub : Nat)
    (bs : TreapMap mugF Blob) (hrj : TsRjAt ctx) :
    CfCore bs (renReg sub 1) (tsSt SB (HoonMap.toNoun Blob.toNoun bs) Bo BN D G ctx o sub) := by
  have hy := ts_byp_at
  have hch := ts_chase_at
  refine ⟨?_, ?_, ?_, ?_, ⟨tsRenBat, A 0, tsS7 BN BN (tsS0 D G ctx o sub) sub, ?_,
    fun r => ts_ren hc BN BN D G o sub r⟩, hrj SB Bo BN D G o sub bs⟩
  · simp [tsSt, tsCoreSt, tsS7, tsS5, nock_exec]
  · simp [tsSt, tsCoreSt, tsS7, tsS5, tsS0, nock_exec, hc]
  · simp only [tsSt, tsCoreSt, nock_exec]; exact hy
  · simp only [tsSt, tsCoreSt, nock_exec]; exact hch
  · simp [tsSt, tsCoreSt, tsRenG, nock_exec]


/-- **The gate of the `+rep:by` of the renaming branch** on a pair `(k, b)`
and an accumulator `new`: `renameStep`. -/
theorem ts_step {ctx : Noun} (hc : CompIn ctx) (hrj : TsRjAt ctx) (SB Bo BN D G : Noun) (o sub : Nat)
    (bs new : TreapMap mugF Blob) (k : Nat) (b : Blob) :
    nock (C tsGBody (C (C (Tr.pairNoun Blob.toNoun (k, b)) (HoonMap.toNoun Blob.toNoun new))
        (tsY SB (HoonMap.toNoun Blob.toNoun bs) Bo BN D G ctx o sub))) tsGBody
      = (renameStep bs (renReg sub 1) new (k, b)).map (HoonMap.toNoun Blob.toNoun) := by
  have hcf := ts_st_cf hc SB Bo BN D G o sub bs hrj
  have hren := fun r => ts_ren hc BN BN D G o sub r
  obtain ⟨par, body, fin⟩ := b
  have hmr := mr_inner_bom mrInner mrBody tsRenBat (A 0) (tsS7 BN BN (tsS0 D G ctx o sub) sub) compTypes
    (renReg sub 1) hren mr_types_layer2 par body
  simp only [Blob.toNoun, Termin.toNoun, unitNoun, Tag.bom] at hmr
  have hcfg := cf_gate hcf cfBody fin
  have hbyp := ts_byp (tsSt SB (HoonMap.toNoun Blob.toNoun bs) Bo BN D G ctx o sub) ⟨par, body, fin⟩
  have hput := fun (f' : Termin) => put_gate layer2 gorIn_morIn_layer2 (A k)
    (Blob.toNoun ⟨par.map (renReg sub 1), body.map (renPole (renReg sub 1)), f'⟩)
    (HoonMap.toNoun Blob.toNoun new) _
    (putF_hoonMap Blob.toNoun new k ⟨par.map (renReg sub 1), body.map (renPole (renReg sub 1)), f'⟩)
  simp only [Blob.toNoun] at hput hbyp
  have hy := ts_byp_at
  have hcfa := ts_cf_at
  have hL := hcf.hL
  have hY := hcf.hY
  have h382 : slot? 382 (tsSt SB (HoonMap.toNoun Blob.toNoun bs) Bo BN D G ctx o sub)
      = some (C (A 8) (C (C (A 1) (C (A 0x6d6f62) (A 0))) (C (C (A 1) cfBody) (C (A 0) (A 1))))) := by
    simp only [tsSt, tsCoreSt, nock_exec]; exact ts_cf_at
  unfold tsY tsRenameG tsRenG
  unfold tsRenG at hren
  generalize tsSt SB (HoonMap.toNoun Blob.toNoun bs) Bo BN D G ctx o sub = S at hcf hbyp hcfg hL hY h382 ⊢
  unfold renameStep keepBlock
  conv => { lhs; arg 2; unfold tsGBody }
  by_cases hk : k = 0
  · subst hk
    simp only [Tr.pairNoun, ne_eq, not_true_eq_false, false_and, if_false]
    cases e : chaseFin bs (renReg sub 1) fin <;> rw [e] at hcfg <;>
      simp [nock_exec, hmr, h382, hcfg, hL, by_arm, by.arm_at, by.put.arm_at, put_arm, hput]
  · have hk' : ¬ (0 = k) := fun h => hk h.symm
    cases hb : bypassable true ⟨par, body, fin⟩
    · rw [hb] at hbyp
      simp only [Tr.pairNoun, hb, Bool.false_eq_true, and_false, if_false]
      cases e : chaseFin bs (renReg sub 1) fin <;> rw [e] at hcfg <;>
        simp [nock_exec, hk', Blob.toNoun, hY, ts_byp_arm, hbyp, hmr, h382, hcfg, hL, by_arm, by.arm_at, by.put.arm_at,
          put_arm, hput]
    · rw [hb] at hbyp
      simp only [Tr.pairNoun, hb, ne_eq, hk, not_false_eq_true, and_self, if_true]
      simp [nock_exec, hk', Blob.toNoun, hY, ts_byp_arm, hbyp]

/-- **`TsStepAt` from the link of `rj`.** -/
theorem ts_step_at {ctx : Noun} (hc : CompIn ctx) (hrj : TsRjAt ctx) : TsStepAt ctx := by
  intro SB Bo BN D G o sub bs new p _
  obtain ⟨k, b⟩ := p
  exact ts_step hc hrj SB Bo BN D G o sub bs new k b

/-- **The end of `+compile-unary` from its entry state, given only the gate
`rj` of `+chase-fin`**: `cu_finish_step` with `TsStepAt` from `ts_step_at`. -/
theorem cu_finish_rj {ctx : Noun} (h7 : slot? 7 ctx = some compK) {cod : Noun}
    (hcode : slot? 52 ctx = some cod)
    (n : Nomm) (hpu : n.pure = true) (h6 : noSix n = true) (ht : tenOk n = true)
    (cache mono sup : Noun) (hrj : TsRjAt ctx) :
    ((nock (crSubj mono n.toNoun (CGoal.toL (CGoal.done : CGoal CSet)).toNoun (listNoun A []) sup
        (compCore genEntry (cuRest cache) ctx)) crDol).bind (fun R =>
      (slot? 2 R).bind fun N => (slot? 3 R).bind fun G =>
        nock (C kerfBat (C N (C comp.door (C G ctx)))) kerfBat)).bind (fun K =>
      (slot? 4 K).bind fun O => (slot? 5 K).bind fun SUB => (slot? 3 K).bind fun G2 =>
        nock (C tsBat (C (tsSample O SUB) (C comp.door (C G2 ctx)))) tsBat)
      = (finishLU (S := CSet) (Map := TreapMap mugF) n).map Straight.toNoun :=
  cu_finish_step h7 hcode n hpu h6 ht cache mono sup (ts_step_at (comp_ctx_pill ctx h7).1 hrj)

end Compiler
end Formalization
