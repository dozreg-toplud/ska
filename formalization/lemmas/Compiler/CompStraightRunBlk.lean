import lemmas.Compiler.CompStraightRunOps

/-!
# `+to-straight` with `run` `|`: a block, the gate of the fold, the branch

README Gaps 20.  In a core of the map path with the state (`MapCoreM`):
`rewrite-body` (`tsr_bodG`, `tsr_bod`: the `+spin` of `rewrite-op`, the
model's `rewriteBody rr`); the step of the model's fold `mapBlocks`
(`mapStep`) and the fold over `rap`, the order of `+rep:by`
(`mapBlocks_rap`); the gate `tsmGate` of the `+rep:by` on `[k b]` and the
accumulator `[new gen-acc]` (`tsr_gate`: `=.  gen  gen-acc`, the test
`&(!=(0 k) (bypassable & b))`, then three `=^`, `mapStep`); and the map
branch `tsMapBr` (`tsr_branch`: `[ord (countArgs ord) new]` with `new` the
model's `mapBlocks rr bs st0`, `st0` the core's state).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## `rewrite-body` -/

/-- **The gate of the `+spin` of `rewrite-body`** with the state:
`(rewrite-op(gen gen) op)`. -/
theorem tsr_bodG {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun} (hc : MapCoreM bs rr R)
    (B J G0 : Noun) (op : Pole) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmBodG (C (C (Pole.toNoun op) (rmN st)) (C B (C J (C tsCoreBat (C G0 R)))))) tsmBodG
      = (rewriteOp rr op st).map fun p => C (Pole.toNoun p.1) (rmN p.2) := by
  have ho := tsr_op hc op st
  have hoa := tsmOp_at
  generalize tsCoreBat = K at ho hoa ⊢
  generalize tsmOpBody = OB at ho hoa ⊢
  generalize rmN st = GS at ho ⊢
  simp [nock_exec, tsmBodG, hoa, ho]

/-- **`rewrite-body` with the state**: the model's `rewriteBody rr`. -/
theorem tsr_bod {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun} (hc : MapCoreM bs rr R)
    (hT : slot? 0x1ffff R = some compTypes) (bod : List Pole) (st : Nat × TreapMap mugF Nat) :
    nock (C tsmBodBody (C (listNoun Pole.toNoun bod) (C tsCoreBat (C (rmN st) R)))) tsmBodBody
      = (rewriteBody rr bod st).map fun p => C (listNoun Pole.toNoun p.1) (rmN p.2) := by
  cases bod with
  | nil =>
    conv => { lhs; arg 2; unfold tsmBodBody }
    simp [nock_exec, listNoun, rewriteBody, List.mapM_nil, pure, StateT.pure]
  | cons a0 as =>
    have hsp := spin_arm_l2
    rw [spin_gate_eq] at hsp
    have hs1 := spin.arm_at
    have hSpin := spin_gate_T Pole.toNoun Pole.toNoun rmN layer2 spinIn_layer2 tsmBodG
      (C tsmPoleBunt (rmN st)) (C tsmBodBody (C (listNoun Pole.toNoun (a0 :: as)) (C tsCoreBat (C (rmN st) R))))
      (fun a s => rewriteOp rr a s) (a0 :: as) st
      (fun a _ s => tsr_bodG hc _ _ _ a s)
    rw [spinM_mapM] at hSpin
    have e : ∀ x : Option (List Pole × (Nat × TreapMap mugF Nat)),
        x.map (fun r => C (listN (r.1.map Pole.toNoun)) (rmN r.2))
          = x.map (fun r => C (listNoun Pole.toNoun r.1) (rmN r.2)) := by
      intro x; cases x <;> simp [listNoun_map_listN]
    rw [e, ← listNoun_map_listN] at hSpin
    simp only [listNoun, List.map_cons] at hSpin
    have hpb := tsm_pole_bunt (C tsmBodBody (C (listNoun Pole.toNoun (a0 :: as)) (C tsCoreBat (C (rmN st) R))))
      (rmN st) (by simp [nock_exec, hT]) (by simp [nock_exec])
    simp only [listNoun] at hpb
    have hL := hc.hL
    unfold rewriteBody
    conv => { lhs; arg 2; unfold tsmBodBody }
    generalize tsmBodBuntF = BF at hpb ⊢
    generalize tsCoreBat = K at hSpin hpb ⊢
    generalize tsmBodG = BG at hSpin ⊢
    generalize tsmBodBody = BB at hSpin hpb ⊢
    generalize rmN st = GS at hSpin hpb ⊢
    simp [nock_exec, listNoun, hL, hs1, spin.axis, hsp, hSpin, hpb]

/-! ## The step of the fold and the order of `+rep:by` -/

/-- One step of the model's `mapBlocks` on a pair `(k, b)` of the blocks
and the accumulator `(new, st)`. -/
def mapStep (rr : Nat → RM (TreapMap mugF) Nat) (bs : TreapMap mugF Blob)
    (acc : TreapMap mugF Blob × (Nat × TreapMap mugF Nat)) (p : Nat × Blob) :
    Option (TreapMap mugF Blob × (Nat × TreapMap mugF Nat)) :=
  if p.1 ≠ 0 ∧ bypassable true p.2 then some acc else
  (rewriteBlob rr bs p.2 acc.2).map fun q => (HoonMap.put acc.1 p.1 q.1, q.2)

theorem map_fold_keys (rr : Nat → RM (TreapMap mugF) Nat) (bs : TreapMap mugF Blob) :
    ∀ (L : List (Nat × Blob)), (∀ p ∈ L, HoonMap.get bs p.1 = some p.2) →
    ∀ (acc : Option (TreapMap mugF Blob × (Nat × TreapMap mugF Nat))),
    (L.map Prod.fst).foldl (fun acc k => acc.bind fun (new, st) =>
        (HoonMap.get bs k).bind fun b =>
          if k ≠ 0 ∧ bypassable true b then some (new, st) else
          (rewriteBlob rr bs b st).map fun (b1, st1) => (HoonMap.put new k b1, st1)) acc
      = acc.bind fun a => L.foldlM (mapStep rr bs) a
  | [], _, acc => by cases acc <;> rfl
  | p :: L, hL, acc => by
    have hp := hL p (by simp)
    have ih := map_fold_keys rr bs L (fun q hq => hL q (by simp [hq]))
    simp only [List.map_cons, List.foldl_cons]
    rw [ih]
    cases acc with
    | none => rfl
    | some a =>
      obtain ⟨new, st⟩ := a
      simp only [Option.bind_some, hp, List.foldlM_cons]
      unfold mapStep
      by_cases h : p.1 ≠ 0 ∧ bypassable true p.2 = true
      · simp only [if_pos h]; rfl
      · simp only [if_neg h]
        cases rewriteBlob rr bs p.2 st <;> rfl

/-- **`mapBlocks` on treaps is the fold of `mapStep` over `rap`**, the order
of `+rep:by`. -/
theorem mapBlocks_rap (rr : Nat → RM (TreapMap mugF) Nat) (bs : TreapMap mugF Blob)
    (st0 : Nat × TreapMap mugF Nat) :
    mapBlocks rr bs st0 = ((TreapMap.rap bs).foldlM (mapStep rr bs) (HoonMap.empty, st0)).map Prod.fst := by
  unfold mapBlocks
  rw [treapMap_keys]
  rw [map_fold_keys rr bs (TreapMap.rap bs) (fun p hp => by
    rw [hoonMap_get]; exact (TreapMap.mem_rap bs p.1 p.2).1 hp) (some (HoonMap.empty, st0))]
  rfl

/-! ## The gate of the fold -/

/-- **The gate `tsmGate` of the `+rep:by` of the map branch with the state**
on a pair `[k b]` and the accumulator `[new gen-acc]`: `mapStep`. -/
theorem tsr_gate {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun} (hc : MapCoreM bs rr R)
    (hT : slot? 0x1ffff R = some compTypes) (ORD G0 : Noun) (new : TreapMap mugF Blob) (k : Nat) (b : Blob)
    (st : Nat × TreapMap mugF Nat) :
    nock (C tsmGate (C (C (Tr.pairNoun Blob.toNoun (k, b)) (C (HoonMap.toNoun Blob.toNoun new) (rmN st)))
        (C ORD (C tsCoreBat (C G0 R))))) tsmGate
      = (mapStep rr bs (new, st) (k, b)).map fun p => C (HoonMap.toNoun Blob.toNoun p.1) (rmN p.2) := by
  obtain ⟨par, body, fin⟩ := b
  have hp := tsr_par hc.hrer hc.hL par
  have hpa := tsmPar_at
  have hb := tsr_bod hc hT body
  have hba := tsmBod_at
  have hf := tsr_fin hc fin
  have hfa := tsmFin_at
  have hY := (tsm_core_l2 (G := rmN st) hc.hL).2
  have hbyp := ts_byp (C tsCoreBat (C (rmN st) R)) ⟨par, body, fin⟩
  have hL := hc.hL
  have hput := fun (b1 : Blob) => put_gate layer2 gorIn_morIn_layer2 (A k) (Blob.toNoun b1)
    (HoonMap.toNoun Blob.toNoun new) _ (putF_hoonMap Blob.toNoun new k b1)
  simp only [Blob.toNoun] at hput hbyp
  unfold mapStep rewriteBlob
  simp only [bind, StateT.bind, pure, StateT.pure]
  conv => { lhs; arg 2; unfold tsmGate }
  generalize tsCoreBat = K at hp hpa hb hba hf hfa hY hbyp ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  generalize tsmBodBody = BB at hb hba ⊢
  generalize tsmFinBody = FB at hf hfa ⊢
  by_cases hk : k = 0
  · subst hk
    simp only [Tr.pairNoun, ne_eq, not_true_eq_false, false_and, if_false]
    cases e1 : rewritePar rr par st with
    | none => simp [nock_exec, hp, hpa, e1]
    | some p1 =>
      obtain ⟨par1, st1⟩ := p1
      cases e2 : rewriteBody rr body st1 with
      | none => simp [nock_exec, hp, hpa, hb, hba, e1, e2]
      | some p2 =>
        obtain ⟨body1, st2⟩ := p2
        cases e3 : rewriteFin rr bs fin st2 with
        | none => simp [nock_exec, hp, hpa, hb, hba, hf, hfa, e1, e2, e3]
        | some p3 =>
          obtain ⟨fin1, st3⟩ := p3
          have hq := hput ⟨par1, body1, fin1⟩
          simp only at hq
          simp [nock_exec, hp, hpa, hb, hba, hf, hfa, hL, by_arm, by.arm_at, by.put.arm_at, put_arm, hq, e1, e2,
            e3]
  · have hk' : ¬ (0 = k) := fun h => hk h.symm
    cases hby : bypassable true ⟨par, body, fin⟩
    · rw [hby] at hbyp
      simp only [Tr.pairNoun, hby, Bool.false_eq_true, and_false, if_false]
      cases e1 : rewritePar rr par st with
      | none => simp [nock_exec, hk', Blob.toNoun, hY, ts_byp_arm, hbyp, loob, hp, hpa, e1]
      | some p1 =>
        obtain ⟨par1, st1⟩ := p1
        cases e2 : rewriteBody rr body st1 with
        | none => simp [nock_exec, hk', Blob.toNoun, hY, ts_byp_arm, hbyp, loob, hp, hpa, hb, hba, e1, e2]
        | some p2 =>
          obtain ⟨body1, st2⟩ := p2
          cases e3 : rewriteFin rr bs fin st2 with
          | none => simp [nock_exec, hk', Blob.toNoun, hY, ts_byp_arm, hbyp, loob, hp, hpa, hb, hba, hf, hfa, e1, e2, e3]
          | some p3 =>
            obtain ⟨fin1, st3⟩ := p3
            have hq := hput ⟨par1, body1, fin1⟩
            simp only at hq
            simp [nock_exec, hk', Blob.toNoun, hY, ts_byp_arm, hbyp, loob, hp, hpa, hb, hba, hf, hfa, hL, by_arm,
              by.arm_at, by.put.arm_at, put_arm, hq, e1, e2, e3]
    · rw [hby] at hbyp
      simp only [Tr.pairNoun, hby, ne_eq, hk, not_false_eq_true, and_self, if_true]
      simp [nock_exec, hk', Blob.toNoun, hY, ts_byp_arm, hbyp, loob]

/-! ## The branch -/

/-- **The map branch with the state** on `[ord core]`, the core's state
being `st0`: `[ord (countArgs ord) new]` with `new` the model's `mapBlocks
rr bs st0`, a crash where it is `none`. -/
theorem tsr_branch {bs : TreapMap mugF Blob} {rr : Nat → RM (TreapMap mugF) Nat} {R : Noun} (hc : MapCoreM bs rr R)
    (hT : slot? 0x1ffff R = some compTypes) (hK : slot? 0xffff R = some compK) (ord : NeedOrd)
    (st0 : Nat × TreapMap mugF Nat)
    (hRB : nock (C ord.toNoun (C tsCoreBat (C (rmN st0) R))) tsmRepBuntF
      = some (C (C (A 0) tsmBlobBunt) (C (A 0) (rmN st0)))) :
    nock (C ord.toNoun (C tsCoreBat (C (rmN st0) R))) tsMapBr
      = (mapBlocks rr bs st0).map fun new =>
          C ord.toNoun (C (A (countArgs ord)) (HoonMap.toNoun Blob.toNoun new)) := by
  have hca := ca_at
  have hcg := ca_gate compK compK_layer1 ord
  have ha : Tree (HoonMap.toNoun Blob.toNoun bs) := by
    rw [hoonMap_toNoun]; exact Tree.of_isMap (bs.2 Blob.toNoun)
  have hP : preorder (HoonMap.toNoun Blob.toNoun bs) = (TreapMap.rap bs).map (Tr.pairNoun Blob.toNoun) := by
    rw [hoonMap_toNoun]; exact TreapMap.preorder_toNoun Blob.toNoun bs
  have hrep := rep_gate_list (Tr.pairNoun Blob.toNoun) (fun p => C (HoonMap.toNoun Blob.toNoun p.1) (rmN p.2))
    (fun p s => mapStep rr bs s p) by.battery layer2 tsmGate (C (A 0) tsmBlobBunt)
    (C ord.toNoun (C tsCoreBat (C (rmN st0) R))) _ ha _ hP (HoonMap.empty, st0)
    (fun p _ s => by obtain ⟨k, b⟩ := p; obtain ⟨new, st⟩ := s; exact tsr_gate hc hT ord.toNoun (rmN st0) new k b st)
  simp only [HoonMap.toNoun_empty] at hrep
  have heta : (fun s p => mapStep rr bs s p) = mapStep rr bs := rfl
  rw [heta] at hrep
  rw [mapBlocks_rap]
  have hB := hc.hB (rmN st0)
  have hL := hc.hL
  simp only [nock_exec] at hB
  rw [tsm_br_eq]
  generalize tsCoreBat = K at hrep hRB hB ⊢
  generalize tsmGate = GT at hrep ⊢
  generalize tsmRepBuntF = RBF at hRB ⊢
  generalize caBody = CB at hca hcg ⊢
  generalize ord.toNoun = ORD at hcg hrep hRB ⊢
  generalize rmN st0 = GS at hrep hRB hB ⊢
  cases e : (TreapMap.rap bs).foldlM (mapStep rr bs) (HoonMap.empty, st0) <;> rw [e] at hrep <;>
    simp [nock_exec, hK, hca, hcg, hL, hB, hRB, by_arm, by.arm_at, by.rep.arm_at, rep_arm, hrep]

end Compiler
end Formalization
