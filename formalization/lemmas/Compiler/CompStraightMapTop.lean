import lemmas.Compiler.CompStraightMapBlk

/-!
# The map path of `+to-straight`: the branch

README Gaps 20.  The map branch of the arm `$` (`tsMapBr`, `tsm_br_eq`) on
`[ord core]` in a core of the map path: `+count-args`, then the `+rep:by` of
the gate `tsmGate` over the blocks from the accumulator `[~ gen]` (the bunt of
the gate's sample, `tsmRepBuntF`, gives `[[0 *blob] [~ gen]]`), then `=<
new`: the noun of `[ord (countArgs ord) (renameBlocks bs f)]`
(`tsm_branch`), which is the model's map path on a run of inputs
(`toStraightF_run`, `mapBlocks_stateless`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The bunt of `blob`, arm `170` of the types core. -/
noncomputable def tsmBlobBunt : Noun :=
  (evalFuel 2000 compTypes (C (A 7) (C (C (A 9) (C (A 170) (C (A 0) (A 1)))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))).getD (A 0)

/-- **The map branch** on `[ord core]`: `[ord (countArgs ord) new]` with `new`
the renaming path of the blocks by `f`, a crash where it is `none`. -/
theorem tsm_branch {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (hT : slot? 0x1ffff R = some compTypes) (hK : slot? 0xffff R = some compK) (ord : NeedOrd)
    (hRB : nock (C ord.toNoun (C tsCoreBat (C G R))) tsmRepBuntF = some (C (C (A 0) tsmBlobBunt) (C (A 0) G))) :
    nock (C ord.toNoun (C tsCoreBat (C G R))) tsMapBr
      = (renameBlocks bs rn).map fun new =>
          C ord.toNoun (C (A (countArgs ord)) (HoonMap.toNoun Blob.toNoun new)) := by
  have hca := ca_at
  have hcg := ca_gate compK compK_layer1 ord
  have ha : Tree (HoonMap.toNoun Blob.toNoun bs) := by
    rw [hoonMap_toNoun]; exact Tree.of_isMap (bs.2 Blob.toNoun)
  have hP : preorder (HoonMap.toNoun Blob.toNoun bs) = (TreapMap.rap bs).map (Tr.pairNoun Blob.toNoun) := by
    rw [hoonMap_toNoun]; exact TreapMap.preorder_toNoun Blob.toNoun bs
  have hrep := rep_gate_list (Tr.pairNoun Blob.toNoun) (fun m => C (HoonMap.toNoun Blob.toNoun m) G)
    (fun p s => renameStep bs rn s p) by.battery layer2 tsmGate (C (A 0) tsmBlobBunt)
    (C ord.toNoun (C tsCoreBat (C G R))) _ ha _ hP HoonMap.empty
    (fun p _ s => by obtain ⟨k, b⟩ := p; exact tsm_gate hc hT ord.toNoun s k b)
  rw [HoonMap.toNoun_empty] at hrep
  have heta : (fun s p => renameStep bs rn s p) = renameStep bs rn := rfl
  rw [heta] at hrep
  rw [renameBlocks_rap]
  have hB := hc.hB
  have hL := hc.hL
  simp only [nock_exec] at hB
  rw [tsm_br_eq]
  generalize tsCoreBat = K at hrep hRB ⊢
  generalize tsmGate = GT at hrep ⊢
  generalize tsmRepBuntF = RBF at hRB ⊢
  generalize caBody = CB at hca hcg ⊢
  generalize ord.toNoun = ORD at hcg hrep hRB ⊢
  cases e : (TreapMap.rap bs).foldlM (renameStep bs rn) HoonMap.empty <;> rw [e] at hrep <;>
    simp [nock_exec, hK, hca, hcg, hL, hB, hRB, by_arm, by.arm_at, by.rep.arm_at, rep_arm, hrep]

end Compiler
end Formalization
