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

/-! ## `rer` with proxies -/

/-- **The gate `unproxy`** of `+to-straight`: `+get:by` of `cond.gen` at `r`,
`def.u.e` on a hit, else `r`; the model's `unproxy`. -/
theorem tsm_unproxy {ctx : Noun} (hc : CompIn ctx) (g : Gen (TreapMap mugF)) (x : GenRest) (Bo D : Noun)
    (o : Nat) (NED : Noun) (r : Nat) :
    nock (C tsUnBat (C (A r) (C Bo (tsS0N D (genNoun g x) ctx o NED)))) tsUnBat = some (A (unproxy g.cond r)) := by
  have hgc : SomeIn layer2 ∧ GorIn mugF layer2 := ⟨someIn_layer2, gorIn_morIn_layer2.1⟩
  have hget := getF_hoonMap condValNoun g.cond r
  have hg := get_gate layer2 hgc (A r) (HoonMap.toNoun condValNoun g.cond) _ hget
  conv => { lhs; arg 2; unfold tsUnBat }
  unfold unproxy
  simp only [tsS0N]
  generalize tsBat = T
  generalize tsUnBat = UB
  cases e : HoonMap.get g.cond r <;>
    simp [nock_exec, genNoun, hc, by_arm, by.arm_at, by.get.arm_at, get_arm, hg, e, unitNoun, condValNoun]

/-- **`rer` with `proxies` `&` and `run` `&`**: `[(ren (u r)) gen]` for an
`unproxy` gate that gives `u` and a `ren` gate that gives `ren`; so `rer` is
stateless (`RerS`) with the renaming `ren ∘ u`. -/
theorem tsm_rer_prox (UB US UC RB RS RC GEN SB N R0 INS REST : Noun) (u ren : Nat → Nat)
    (hu : ∀ r, nock (C UB (C (A r) UC)) UB = some (A (u r)))
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r))) :
    RerS (fun r => ren (u r)) GEN (C SB (C (C RB (C RS RC)) (C (A 0) (C N (C R0 (C INS
      (C (A 0) (C (C UB (C US UC)) REST)))))))) := by
  intro r
  have h1 := hu r
  have h2 := hren (u r)
  conv => { lhs; arg 2; unfold tsRerBody }
  generalize tsRerMap = M
  generalize tsCoreBat = K
  simp [nock_exec, h1, h2]

/-! ## The arm `$` with proxies -/

/-- **The arm `$` with `proxies` `&`** (and `run` `&`): `rewrite-input` gives
`needToOrd ned` and keeps `gen` (`tsn_ri`, for the stateless `rer`), the
test `&(run !proxies)` is `|`, so `$` is the map branch on `[(needToOrd ned)
core]`. -/
theorem tsm_dol (SB REN N R0 INS REST : Noun) (f : Nat → Nat) (ned : Need)
    (hrer : RerS f (C (A 0) (A 0)) (C SB (C REN (C (A 0) (C N (C R0 (C INS (C (A 0) REST))))))))
    (hN : slot? 488 REST = some ned.toNoun) :
    nock (C tsCoreBat (C (C (A 0) (A 0)) (C SB (C REN (C (A 0) (C N (C R0 (C INS (C (A 0) REST)))))))))
        (C (A 9) (C (A 190) (C (A 0) (A 1))))
      = nock (C (needToOrd ned).toNoun (C tsCoreBat (C (C (A 0) (A 0)) (C SB (C REN (C (A 0) (C N (C R0
          (C INS (C (A 0) REST)))))))))) tsMapBr := by
  have hri := tsn_ri _ f hrer ned
  have hdol := ts_dol_at
  have hria := ts_ri_at
  generalize tsCoreBat = K at hri hdol hria ⊢
  generalize tsRiBody = RIB at hri hria ⊢
  generalize tsRenameBr = RNB at hdol ⊢
  generalize tsMapBr = MB at hdol ⊢
  generalize (needToOrd ned).toNoun = ORD at hri ⊢
  generalize ned.toNoun = NED at hri hN ⊢
  simp [nock_exec, hdol, hria, hri, hN]

/-! ## The core with proxies -/

/-- **The `|^` core of `+to-straight` with `proxies` `&` and `run` `&`**: the
arm `$` returns the noun of the straight whose blocks are the renaming path
of `bs` by `ren ∘ u` (`u` the `unproxy` gate, `ren` the `ren` gate), the
form of the model's map path on a run of inputs (`toStraightF_run`:
`renameBlocks bs (proxRen cond true ren)`).  The hypotheses on the core are
those of `MapCoreS` but `rer` (given by `tsm_rer_prox`), the types core and
`K` in the rest, and the bunt of the sample of the fold's gate. -/
theorem tsm_core {bs : TreapMap mugF Blob} (UB US UC RB RS RC SB N R0 INS REST : Noun) (u ren : Nat → Nat)
    (ned : Need)
    (hu : ∀ r, nock (C UB (C (A r) UC)) UB = some (A (u r)))
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r)))
    (hN : slot? 488 (C (C UB (C US UC)) REST) = some ned.toNoun)
    (hL : slot? 0x7fffffff (C SB (C (C RB (C RS RC)) (C (A 0) (C N (C R0 (C INS (C (A 0)
      (C (C UB (C US UC)) REST)))))))) = some layer2)
    (hU : ∀ J, nock (C tsmArgBody (C J (C tsCoreBat (C (C (A 0) (A 0)) (C SB (C (C RB (C RS RC)) (C (A 0)
      (C N (C R0 (C INS (C (A 0) (C (C UB (C US UC)) REST)))))))))))) tsmArgBuntF1 = some (C (A 0) (C (A 0) (A 0))))
    (hB : slot? 4094 (C tsCoreBat (C (C (A 0) (A 0)) (C SB (C (C RB (C RS RC)) (C (A 0) (C N (C R0 (C INS
      (C (A 0) (C (C UB (C US UC)) REST)))))))))) = some (HoonMap.toNoun Blob.toNoun bs))
    (hT : slot? 0x1ffff (C SB (C (C RB (C RS RC)) (C (A 0) (C N (C R0 (C INS (C (A 0)
      (C (C UB (C US UC)) REST)))))))) = some compTypes)
    (hK : slot? 0xffff (C SB (C (C RB (C RS RC)) (C (A 0) (C N (C R0 (C INS (C (A 0)
      (C (C UB (C US UC)) REST)))))))) = some compK)
    (hRB : nock (C (needToOrd ned).toNoun (C tsCoreBat (C (C (A 0) (A 0)) (C SB (C (C RB (C RS RC)) (C (A 0)
      (C N (C R0 (C INS (C (A 0) (C (C UB (C US UC)) REST))))))))))) tsmRepBuntF
      = some (C (C (A 0) tsmBlobBunt) (C (A 0) (C (A 0) (A 0))))) :
    nock (C tsCoreBat (C (C (A 0) (A 0)) (C SB (C (C RB (C RS RC)) (C (A 0) (C N (C R0 (C INS
        (C (A 0) (C (C UB (C US UC)) REST)))))))))) (C (A 9) (C (A 190) (C (A 0) (A 1))))
      = (renameBlocks bs (fun r => ren (u r))).map fun new =>
          Straight.toNoun (⟨needToOrd ned, countArgs (needToOrd ned), new⟩ : Straight (TreapMap mugF)) := by
  have hrer := tsm_rer_prox UB US UC RB RS RC (C (A 0) (A 0)) SB N R0 INS REST u ren hu hren
  have hc : MapCoreS bs (fun r => ren (u r)) (C (A 0) (A 0)) _ := ⟨hrer, hL, hU, hB⟩
  rw [tsm_dol SB (C RB (C RS RC)) N R0 INS (C (C UB (C US UC)) REST) _ ned hrer hN,
    tsm_branch hc hT hK (needToOrd ned) hRB]
  rfl

end Compiler
end Formalization
