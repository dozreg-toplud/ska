import lemmas.Compiler.CompStraightMapOps
import lemmas.Compiler.CompStraightN

/-!
# The map path of `+to-straight`: a block and the gate of the fold

README Gaps 20.  In a core of the map path (`MapCoreS`): `rewrite-fin` on
`%bom` and `%lti` (`tsm_fin_bom_none`, `tsm_fin_bom_some`, `tsm_fin_lti`)
and on any terminator (`tsm_fin`, `chaseFin bs f`); `rewrite-body`
(`tsm_bod`, the `+spin` of `rewrite-op`, `body.map (renPole f)`); and the
gate `tsmGate` of the `+rep:by` of the map branch on a pair `[k b]` and an
accumulator `[new G]` (`tsm_gate`): `renameStep bs f`, the step of the
renaming path, with `gen` kept.  The model's map path is the same step on a
run of inputs (`mapBlocks_stateless`, `keepBlock`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- `layer2` and `+bypassable` in the core. -/
theorem tsm_core_l2 {G R : Noun} (hL : slot? 0x7fffffff R = some layer2) :
    slot? 0x1ffffffff (C tsCoreBat (C G R)) = some layer2 ∧ slot? 46 (C tsCoreBat (C G R)) = some tsBypArm := by
  have h := ts_byp_at
  unfold tsBypArm
  generalize tsCoreBat = K at h ⊢
  exact ⟨by simp [nock_exec, hL], by simp [nock_exec, h]⟩

/-- `+chase` crashes on a jump whose target is a cell. -/
theorem tsm_chase_cell {bs : TreapMap mugF Blob} {G R : Noun}
    (hB : slot? 4094 (C tsCoreBat (C G R)) = some (HoonMap.toNoun Blob.toNoun bs))
    (hL : slot? 0x7fffffff R = some layer2) (br x y : Noun) :
    nock (C tsChaseBat (C (C br (C (A 0) (C x y))) (C tsCoreBat (C G R)))) tsChaseBat = none := by
  have hgc : NeedIn layer2 ∧ SomeIn layer2 ∧ GorIn mugF layer2 :=
    ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩
  have hg := got_gate_nil layer2 hgc (C x y) (HoonMap.toNoun Blob.toNoun bs) (by
    rw [hoonMap_toNoun]; exact cf_getF_cell Blob.toNoun x y bs.1)
  have hB' := hB
  simp only [nock_exec] at hB'
  have key : ∀ Bd Bt, nock (C Bd (C Bt (C (C br (C (A 0) (C x y))) (C tsCoreBat (C G R))))) tsChaseBody = none := by
    intro Bd Bt
    unfold tsChaseBody
    simp [nock_exec, hB', hL, by_arm, by.arm_at, by.got.arm_at, got_arm, hg]
  conv => { lhs; arg 2; unfold tsChaseBat }
  simp only [nock_exec, key]

theorem tsm_fin_bom_none {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R) :
    nock (C tsmFinBody (C (Termin.toNoun (Termin.bom Option.none)) (C tsCoreBat (C G R)))) tsmFinBody
      = (chaseFin bs rn (Termin.bom Option.none)).map fun t => C (Termin.toNoun t) G := by
  conv => { lhs; arg 2; unfold tsmFinBody }
  generalize tsCoreBat = K
  simp [nock_exec, Termin.toNoun, unitNoun, chaseFin, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp,
    Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti]

theorem tsm_fin_bom_some {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (x : Nat) :
    nock (C tsmFinBody (C (Termin.toNoun (Termin.bom (some x))) (C tsCoreBat (C G R)))) tsmFinBody
      = (chaseFin bs rn (Termin.bom (some x))).map fun t => C (Termin.toNoun t) G := by
  obtain ⟨hL', hY⟩ := tsm_core_l2 (G := G) hc.hL
  have ht := ch_gate bs true (C tsCoreBat (C G R)) hc.hB hL' hY ⟨[], x⟩
  rw [show loob true = A 0 from rfl] at ht
  simp only [Jmp.toNoun, listNoun] at ht
  have h21 := (tsm_core_arms G R).2
  conv => { lhs; arg 2; unfold tsmFinBody }
  generalize tsCoreBat = K at ht h21 ⊢
  cases et : chase bs true ⟨[], x⟩ <;> rw [et] at ht <;>
    simp [nock_exec, Termin.toNoun, Jmp.toNoun, listNoun, unitNoun, chaseFin, Tag.clq, Tag.eqq, Tag.brn,
      Tag.brz, Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, h21, tsChaseArm, ht, et]

theorem tsm_fin_lti {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (n s : Nat) (z o : Jmp) :
    nock (C tsmFinBody (C (Termin.toNoun (Termin.lti n s z o)) (C tsCoreBat (C G R)))) tsmFinBody
      = (chaseFin bs rn (Termin.lti n s z o)).map fun t => C (Termin.toNoun t) G := by
  have hx := tsm_chase_cell hc.hB hc.hL (A 0) (A s) (C (Jmp.toNoun z) (Jmp.toNoun o))
  have h21 := (tsm_core_arms G R).2
  conv => { lhs; arg 2; unfold tsmFinBody }
  generalize tsCoreBat = K at hx h21 ⊢
  simp [nock_exec, Termin.toNoun, chaseFin, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf,
    Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti, h21, tsChaseArm, hx]

/-- **`rewrite-fin`** on any terminator: `chaseFin bs f`, `gen` kept, a crash
where `chaseFin` is `none`. -/
theorem tsm_fin {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R) (fin : Termin) :
    nock (C tsmFinBody (C (Termin.toNoun fin) (C tsCoreBat (C G R)))) tsmFinBody
      = (chaseFin bs rn fin).map fun t => C (Termin.toNoun t) G := by
  cases fin with
  | clq s z o => exact tsm_fin_clq hc s z o
  | eqq l r z o => exact tsm_fin_eqq hc l r z o
  | brn s z o => exact tsm_fin_brn hc s z o
  | brz s z o => exact tsm_fin_brz hc s z o
  | hop t => exact tsm_fin_hop hc t
  | jmp a v => exact tsm_fin_jmp hc a v
  | jmf a v n => exact tsm_fin_jmf hc a v n
  | jsp a s => exact tsm_fin_jsp hc a s
  | jsf a s n => exact tsm_fin_jsf hc a s n
  | don s => exact tsm_fin_don hc s
  | bom o =>
    cases o with
    | none => exact tsm_fin_bom_none hc
    | some x => exact tsm_fin_bom_some hc x
  | lti n s z o => exact tsm_fin_lti hc n s z o

/-! ## `rewrite-body` -/

/-- **The gate of the `+spin` of `rewrite-body`** on one op. -/
theorem tsm_bodG {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (B J : Noun) (op : Pole) :
    nock (C tsmBodG (C (C (Pole.toNoun op) G) (C B (C J (C tsCoreBat (C G R)))))) tsmBodG
      = some (C (Pole.toNoun (renPole rn op)) G) := by
  have ho := tsm_op hc op
  have hoa := tsmOp_at
  generalize tsCoreBat = K at ho hoa ⊢
  generalize tsmOpBody = OB at ho hoa ⊢
  simp [nock_exec, tsmBodG, hoa, ho]

/-- The bunt of `pole`, which `rewrite-body` computes for the sample of its
gate (arm `2743` of the types core). -/
noncomputable def tsmPoleBunt : Noun :=
  (evalFuel 3000 compTypes (C (A 7) (C (C (A 9) (C (A 2743) (C (A 0) (A 1)))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))).getD (A 0)

theorem tsm_pole_bunt_ct :
    nock compTypes (C (A 7) (C (C (A 9) (C (A 2743) (C (A 0) (A 1)))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))
      = some tsmPoleBunt := nock_of_evalFuel (fuel := 3000) (by kernel_rfl)

theorem tsm_pole_bunt (X G : Noun) (h : slot? 0x1fffff X = some compTypes) (hg : slot? 30 X = some G) :
    nock X tsmBodBuntF = some (C tsmPoleBunt G) := by
  have e := tsm_pole_bunt_ct
  unfold tsmBodBuntF
  rw [nock_cell, nock_op0 X 30, hg]
  have e2 : nock X (C (A 7) (C (C (A 9) (C (A 2743) (C (A 0) (A 2097151)))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))
      = some tsmPoleBunt := by
    rw [nock_op7, nock_op9, nock_op0, h]
    rw [nock_op7, nock_op9, nock_op0] at e
    exact e
  rw [e2]; rfl

/-- **`rewrite-body`**: the ops renamed by `renPole f`, `gen` kept. -/
theorem tsm_bod {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (hT : slot? 0x1ffff R = some compTypes) (bod : List Pole) :
    nock (C tsmBodBody (C (listNoun Pole.toNoun bod) (C tsCoreBat (C G R)))) tsmBodBody
      = some (C (listNoun Pole.toNoun (bod.map (renPole rn))) G) := by
  cases bod with
  | nil =>
    conv => { lhs; arg 2; unfold tsmBodBody }
    simp [nock_exec, listNoun]
  | cons a0 as =>
    have hsp := spin_arm_l2
    rw [spin_gate_eq] at hsp
    have hs1 := spin.arm_at
    have hSpin := spin_gate_T Pole.toNoun Pole.toNoun (fun _ : Unit => G) layer2 spinIn_layer2 tsmBodG
      (C tsmPoleBunt G) (C tsmBodBody (C (listNoun Pole.toNoun (a0 :: as)) (C tsCoreBat (C G R))))
      (fun a (_ : Unit) => some (renPole rn a, ())) (a0 :: as) ()
      (fun a _ _ => by rw [tsm_bodG hc]; rfl)
    rw [spinM_pure] at hSpin
    simp only [Option.map_some] at hSpin
    rw [← listNoun_map_listN, ← listNoun_map_listN] at hSpin
    simp only [listNoun, List.map_cons] at hSpin
    have hpb := tsm_pole_bunt (C tsmBodBody (C (listNoun Pole.toNoun (a0 :: as)) (C tsCoreBat (C G R)))) G
      (by simp [nock_exec, hT]) (by simp [nock_exec])
    simp only [listNoun] at hpb
    have hL := hc.hL
    conv => { lhs; arg 2; unfold tsmBodBody }
    generalize tsmBodBuntF = BF at hpb ⊢
    generalize tsCoreBat = K at hSpin hpb ⊢
    generalize tsmBodG = BG at hSpin ⊢
    generalize tsmBodBody = BB at hSpin hpb ⊢
    simp [nock_exec, listNoun, hL, hs1, spin.axis, hsp, hSpin, hpb]

/-! ## The gate of the fold -/

/-- **The gate `tsmGate` of the `+rep:by` of the map branch** on a pair
`[k b]` and the accumulator `[new G]`: `renameStep bs f`, `gen` kept. -/
theorem tsm_gate {bs : TreapMap mugF Blob} {rn : Nat → Nat} {G R : Noun} (hc : MapCoreS bs rn G R)
    (hT : slot? 0x1ffff R = some compTypes) (ORD : Noun) (new : TreapMap mugF Blob) (k : Nat) (b : Blob) :
    nock (C tsmGate (C (C (Tr.pairNoun Blob.toNoun (k, b)) (C (HoonMap.toNoun Blob.toNoun new) G))
        (C ORD (C tsCoreBat (C G R))))) tsmGate
      = (renameStep bs rn new (k, b)).map fun m => C (HoonMap.toNoun Blob.toNoun m) G := by
  obtain ⟨par, body, fin⟩ := b
  have hp := tsm_par hc.hrer hc.hL par
  have hpa := tsmPar_at
  have hb := tsm_bod hc hT body
  have hba := tsmBod_at
  have hf := tsm_fin hc fin
  have hfa := tsmFin_at
  have hY := (tsm_core_l2 (G := G) hc.hL).2
  have hbyp := ts_byp (C tsCoreBat (C G R)) ⟨par, body, fin⟩
  have hL := hc.hL
  have hput := fun (f' : Termin) => put_gate layer2 gorIn_morIn_layer2 (A k)
    (Blob.toNoun ⟨par.map rn, body.map (renPole rn), f'⟩)
    (HoonMap.toNoun Blob.toNoun new) _
    (putF_hoonMap Blob.toNoun new k ⟨par.map rn, body.map (renPole rn), f'⟩)
  simp only [Blob.toNoun] at hput hbyp
  unfold renameStep keepBlock
  conv => { lhs; arg 2; unfold tsmGate }
  generalize tsCoreBat = K at hp hpa hb hba hf hfa hY hbyp ⊢
  generalize tsmParBody = PB at hp hpa ⊢
  generalize tsmBodBody = BB at hb hba ⊢
  generalize tsmFinBody = FB at hf hfa ⊢
  by_cases hk : k = 0
  · subst hk
    simp only [Tr.pairNoun, ne_eq, not_true_eq_false, false_and, if_false]
    cases e : chaseFin bs rn fin <;> rw [e] at hf <;>
      simp [nock_exec, hp, hpa, hb, hba, hf, hfa, hL, by_arm, by.arm_at, by.put.arm_at, put_arm, hput]
  · have hk' : ¬ (0 = k) := fun h => hk h.symm
    cases hby : bypassable true ⟨par, body, fin⟩
    · rw [hby] at hbyp
      simp only [Tr.pairNoun, hby, Bool.false_eq_true, and_false, if_false]
      cases e : chaseFin bs rn fin <;> rw [e] at hf <;>
        simp [nock_exec, hk', Blob.toNoun, hY, ts_byp_arm, hbyp, loob, hp, hpa, hb, hba, hf, hfa, hL, by_arm, by.arm_at,
          by.put.arm_at, put_arm, hput]
    · rw [hby] at hbyp
      simp only [Tr.pairNoun, hby, ne_eq, hk, not_false_eq_true, and_self, if_true]
      simp [nock_exec, hk', Blob.toNoun, hY, ts_byp_arm, hbyp, loob]

end Compiler
end Formalization
