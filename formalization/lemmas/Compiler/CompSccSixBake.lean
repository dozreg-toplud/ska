import lemmas.Compiler.CompShapeColRet
import lemmas.Compiler.CompBakeGate
import lemmas.Ska.BakeNeedRun

/-!
# The top on `SixOk` with the real bake

The chain of `CompSccSixSc.lean` (`cu_gate_scc_one_six_q_L`) without
`NoBakeOneO`: `+bake-need` runs on `ned-final` with the sock `less.b`
(`bn_gateB`, every need and sock), and the gate `finish` runs `+add-ops` of
the `%imm` ops of `imm.bak` and `+to-straight` of the residual `ned.bak`
(README Gaps 9, plan (a), (b), (d)).

1. `fin_turn_imm`: the `+turn` of `|=([r v] [%imm v r])` over `imm.bak`;
   `fin_gate_ts_B`, `fin_gate_finishLF_six_B`: the gate `finish` on the
   tuple with `ned.bak` and `imm.bak` returns `finTail` with the bake
   `fun n => bakeNeed n know`, given that the residual's registers are a run
   (what `TsOn` needs; the map path of `+to-straight` with `run` false is not
   linked);
2. `mem_final_B`: the final pass of `member` with any `bak` (`hbn`) and
   `need-new` the `+need-to-ordered` of `ned.bak`; `mem_to_finish_six_B`,
   `mem_gate_six_B` (the product's `chg` reads `needToOrd` of the residual);
3. `BakeRunO` (the one hypothesis in place of `NoBakeOneO`: the residual of
   every final pass is a run), `csi_gate_scc_one_m_six_B`,
   `csi_gate_scc_one_f_six_B`, **`cu_gate_scc_one_six_q_B`** (any `ordOf`
   that `+shape-collapse` returns);
4. **`cu_gate_scc_one_six_bake`**: with `ordOf := scOrd fuel · cape` and
   `FixRet`, the n-ary entry is `finishLFB env nm (scOrd fuel p.1 cape)
   (Sock.mk cape DATA)`.

`BakeRunO` holds when the baked registers are a prefix or a suffix of the
registers of `ned-final` in preorder (`Ska/BakeNeedRun.lean`:
`bake_run_of_infix`, `bake_run_head`, `bake_run_tail_pair`,
`bake_run_tail_both`); under cape `|` nothing is baked (`bakeRunO_no`);
on a wholly known head whenever the `ord` is a cell with a `%this` head
(`bakeRunO_head`, by `noar_pair_this`).  The example at the end is `%s01`
of the bake check, `[6 [0 2] [0 6] [0 7]]` on the bell `[[& |] [dh dt]]`:
its `#guard`s run the model's final pass, which bakes the head's register
and leaves a run of two arguments.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## The `+turn` over `imm.bak` -/

/-- The product of the gate `|=([r v] [%imm v r])` on a noun `[r v]`. -/
def immOpN : Noun → Noun
  | Noun.cell a b => C (A Tag.imm) (C b a)
  | x => x

theorem immNoun_listN (imm : List (Nat × Noun)) :
    immNoun imm = listN (imm.map fun p => C (A p.1) p.2) := by
  induction imm with
  | nil => rfl
  | cons p r ih =>
    simp only [immNoun, listNoun, List.map_cons, listN, appendN_cons] at ih ⊢
    rw [ih]

theorem immOps_listN (imm : List (Nat × Noun)) :
    listN ((imm.map fun p => C (A p.1) p.2).map immOpN)
      = listNoun Pole.toNoun (imm.map fun (r, v) => Pole.imm v r) := by
  induction imm with
  | nil => rfl
  | cons p r ih =>
    simp only [List.map_cons, listN, appendN_cons, listNoun] at ih ⊢
    rw [ih]
    rfl

/-- **The `+turn` of `finish` over `imm.bak`**: the list of the `%imm` ops. -/
theorem fin_turn_imm (bc : Noun) (imm : List (Nat × Noun)) :
    nock (C turn.battery (C (C (immNoun imm) (C (C (C (A 1) (A 0x6d6d69)) (C (C (A 0) (A 13)) (C (A 0) (A 12))))
        (C (C (A 0) (A 0)) bc))) layer2)) turn.battery
      = some (listNoun Pole.toNoun (imm.map fun (r, v) => Pole.imm v r)) := by
  have h := turn_gate layer2 homoIn_layer2 (C (C (A 1) (A 0x6d6d69)) (C (C (A 0) (A 13)) (C (A 0) (A 12))))
    (C (A 0) (A 0)) bc immOpN (imm.map fun p => C (A p.1) p.2) (by
      intro x hx
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
      simp [nock_exec, immOpN, Tag.imm])
  rw [immNoun_listN, h, immOps_listN]

/-! ## The gate `finish` with the real bake -/

theorem fin_gate_ts_B (Q : TreapMap mugF (Nat × List Nat) → Prop) (hT : TsOn Q) {ctx : Noun}
    (h7 : slot? 7 ctx = some compK) (c2 c6 c14 NEWN SUR REST G0 : Noun)
    (less : Cape) (hcomp : slot? 6 REST = some (C comp.door (C G0 ctx))) (hdone : slot? 14 REST = some (A 0))
    (hless : slot? 496 REST = some less.toNoun) (hl2 : slot? 0x3ffffff REST = some layer2)
    (g : Gen (TreapMap mugF)) (x : GenRest) (hs0 : x.soft = A 0) (hQ : Q g.cond)
    (nedF : Need) (know : Sock)
    (hrun : isRun (flattenNeed (bakeNeed nedF know).1) ((flattenNeed (bakeNeed nedF know).1).headD 0) 0 = true)
    (o : Nat) (laz : Lazy CSet) :
    nock (C finBody (C (A 0) (finCtx c2 c6 c14 NEWN laz.toNoun nedF.toNoun (bakeNeed nedF know).1.toNoun
        (immNoun (bakeNeed nedF know).2) o SUR (genNoun g x) REST))) finBody
      = (finTail nedF less o laz (fun n => bakeNeed n know) g).map Straight.toNoun := by
  have hc := (comp_ctx_pill ctx h7).1
  have hcz := comp_coerce_lazy_all h7 x (fun o => fin_softOut x hs0 o) nedF o laz less g
  have hczat := comp_cz_at
  have hsdat := sd_at
  have haoat := comp_add_ops_at
  have htsat := comp_ts_at
  unfold finTail
  dsimp only
  generalize bakeNeed nedF know = bak at hrun ⊢
  obtain ⟨nedB, imm⟩ := bak
  simp only at hrun ⊢
  cases e1 : coerceLazyL nedF less o laz g with
  | none =>
    rw [e1] at hcz
    simp only [compCore] at hcz
    conv => { lhs; arg 2; unfold finBody }
    simp only [finCtx]
    generalize comp.door = Dr at hcz hczat hsdat haoat htsat hcomp
    simp [nock_exec, hcomp, hdone, hless, hczat, comp_cz_arm, hcz]
  | some r1 =>
    obtain ⟨u1, g3⟩ := r1
    rw [e1] at hcz
    have hsd := sd_empty ctx hc g3 x hs0
    have hao := comp_add_ops x hc g3 o (imm.map fun (r, v) => Pole.imm v r)
    have kc3 := (kc_coerceLazyL nedF less o laz).keep g u1 g3 e1
    cases e2 : addOps o (imm.map fun (r, v) => Pole.imm v r) g3 with
    | none =>
      rw [e2] at hao
      simp only [compCore, Option.map_some] at hcz hsd hao
      conv => { lhs; arg 2; unfold finBody }
      simp only [finCtx, Option.bind_some]
      generalize comp.door = Dr at hcz hczat hsdat haoat htsat hcomp hsd hao
      generalize sdArm = SD at hsdat hsd
      simp [nock_exec, hcomp, hdone, hless, hl2, hczat, comp_cz_arm, hcz, hsdat, hsd, haoat, comp_add_ops_arm,
        turn.arm_at, turn_arm, fin_turn_imm, hao, e2]
    | some r2 =>
      obtain ⟨u2, g4⟩ := r2
      rw [e2] at hao
      have kc4 := (KC.addOps' o (imm.map fun (r, v) => Pole.imm v r)).keep g3 u2 g4 e2
      have hts := hT ctx h7 g4 x o nedB (by rw [kc4, kc3]; exact hQ) hrun
      simp only [compCore, Option.map_some, tsSampleN] at hcz hsd hao hts
      conv => { lhs; arg 2; unfold finBody }
      simp only [finCtx, Option.bind_some]
      generalize comp.door = Dr at hcz hczat hsdat haoat htsat hcomp hsd hao hts
      generalize sdArm = SD at hsdat hsd
      simp [nock_exec, hcomp, hdone, hless, hl2, hczat, comp_cz_arm, hcz, hsdat, hsd, haoat, comp_add_ops_arm,
        turn.arm_at, turn_arm, fin_turn_imm, hao, htsat, comp_ts_arm, hts, e2]
      all_goals exact hts

theorem fin_gate_finishLF_six_B (Q : TreapMap mugF (Nat × List Nat) → Prop) (hT : TsOn Q) {ctx : Noun}
    (env : CallEnv) (h7 : slot? 7 ctx = some compK) (c2 c6 c14 NEWN SUR REST G0 : Noun)
    (less : Cape) (hcomp : slot? 6 REST = some (C comp.door (C G0 ctx))) (hdone : slot? 14 REST = some (A 0))
    (hless : slot? 496 REST = some less.toNoun) (hl2 : slot? 0x3ffffff REST = some layer2)
    (x : GenRest) (hs0 : x.soft = A 0)
    (nm : Nomm) (ord : NeedOrd) (nex : NextL CSet) (g1 g2 : Gen (TreapMap mugF)) (nedF : Need) (know : Sock)
    (hrunL : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))
    (hargs : nex.th.args = [])
    (hQ : Q g1.cond)
    (hnoar : needOrdAllocRegs ord g1 = some (nedF, g2))
    (hrun : isRun (flattenNeed (bakeNeed nedF know).1) ((flattenNeed (bakeNeed nedF know).1).headD 0) 0 = true) :
    nock (C finBody (C (A 0) (finCtx c2 c6 c14 NEWN nex.laz.toNoun nedF.toNoun (bakeNeed nedF know).1.toNoun
        (immNoun (bakeNeed nedF know).2) nex.th.there SUR (genNoun g2 x) REST))) finBody
      = (finishLFC (S := CSet) (Map := TreapMap mugF) env nm ord less (fun n => bakeNeed n know)).map
          Straight.toNoun := by
  have kc2 := (kc_needOrdAllocRegs (Map := TreapMap mugF) ord).keep g1 nedF g2 hnoar
  rw [finishLFC_tail, hrunL]
  simp only [Option.bind_some, hargs, ne_eq, not_true_eq_false, if_false, hnoar]
  exact fin_gate_ts_B Q hT h7 c2 c6 c14 NEWN SUR REST G0 less hcomp hdone hless hl2 g2 x hs0
    (by rw [kc2]; exact hQ) nedF know hrun nex.th.there nex.laz

/-! ## `member` with the real bake -/

/-- **The final pass of `member`** (`mem_final`) with any `bak`: `hbn` gives
the product `[NEDB IMM]` of `+bake-need`, and `need-new` is the
`+need-to-ordered` of `NEDB` (`hn2`). -/
theorem mem_final_B (GN NM DCTX CAPE DATA FOL KEEP ML TOP CA DN KIDS ML0 CB SCC LONG JH CACHE0 : Noun)
    (NEXN G1N NF LNED LLOK LREST O G2 NO SUR NN NEDB IMM : Noun)
    (hmode : edit? 46 (A 0x6e7572) (C GN (memS3 NM DCTX
        (memS0 (C (C CAPE DATA) FOL) KEEP ML TOP CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0))))
      = some (C GN (memS3 NM DCTX
        (memS0 (C (C CAPE DATA) FOL) KEEP ML TOP CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0)))))
    (hrun : nock (crSubj (A 1) NM (C (A 0x656e6f64) (A 0)) (A 0) (A 0) (C comp.door (C GN DCTX))) crDol
      = some (C NEXN G1N))
    (hcs : nock (C csBody (C (C NEXN CAPE) (C comp.door (C G1N DCTX)))) csBody
      = some (C (C NF (C (C (C LNED LLOK) LREST) O)) G2))
    (hbn : nock (C bnBody (C (C NF (C CAPE DATA)) compK)) bnBody = some (C NEDB IMM))
    (hn1 : nock (C ntaBody (C LNED compK)) ntaBody = some NO)
    (hso : nock (C soBody (C (C (C NO LLOK) CAPE) compK)) soBody = some SUR)
    (hn2 : nock (C ntaBody (C NEDB compK)) ntaBody = some NN) :
    nock (C GN (memS3 NM DCTX
        (memS0 (C (C CAPE DATA) FOL) KEEP ML TOP CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0)))) memFinal
      = some (C (C NN (C (C (C LNED LLOK) LREST) (C NF (C (C NEDB IMM) (C O SUR))))) G2) := by
  conv => { lhs; arg 2; unfold memFinal }
  simp [nock_exec, memF2, memF3, hmode, mem_run_call, hrun, mem_cs_call, hcs, mem_bak_call, hbn, mem_sur_call, hn1,
    hso, mem_tuple_call, hn2]

/-- The subject at the push of `finish` on the final pass, with `ned.bak`
and `imm.bak`. -/
def memFCB (keep : Bool) (WAS SUR NN LZ NF NEDB IMM : Noun) (o : Nat) (G2 NM DCTX B ML TOP CA CTX : Noun) : Noun :=
  finCtx (memMovedN keep WAS SUR) (memSurKN keep WAS SUR) WAS NN LZ NF NEDB IMM o SUR G2
    (memS3 NM DCTX (memS0 B (loob keep) ML TOP CA CTX))

theorem mem_to_finish_six_B (cape : Cape) (DATA FOL : Noun) (keep : Bool)
    (ML TOP CACHE DN KIDS ML0 CB SCC CODE LSR JH CACHE0 : Noun)
    (nm : Nomm) (C1 C2 C3 C4 SURE : Noun)
    (hinl : nock (C inlBody (C (C (C (C cape.toNoun DATA) FOL) (C (C CODE LSR) (C JH CACHE))) compK)) inlBody
      = some (C nm.toNoun (cacheN C1 C2 C3 C4 SURE)))
    (env : CallEnv) (hn : SixOk nm = true) (ha : Bake.NoAx0 nm)
    (nex : NextL CSet) (g1 : Gen (TreapMap mugF))
    (hrunL : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))
    (ord : NeedOrd) (hsc : nock (C scBody (C (C nex.laz.toNoun cape.toNoun) compK)) scBody = some ord.toNoun)
    (hargs : nex.th.args = []) (nedF : Need) (g2 : Gen (TreapMap mugF))
    (hnoar : needOrdAllocRegs ord g1 = some (nedF, g2))
    (sur : NeedOrd) (hsur : sureOf (needToOrd nex.laz.sure.ned) nex.laz.sure.lok cape = some sur)
    (WAS SURE' : Noun) (hwas : getF mugF (C (C cape.toNoun DATA) FOL) SURE = some WAS)
    (hw : WAS = A 0 ∨ ∃ u, WAS = C (A 0) u)
    (hput : putF mugF (C (C cape.toNoun DATA) FOL) (memSurKN keep WAS sur.toNoun) SURE = some SURE') :
    nock (C memBody (C (memSam (C (C cape.toNoun DATA) FOL) (A 0x656e6f64) (loob keep) ML TOP CACHE)
        (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0))) memBody
      = nock (C (C finBody (C (A 0) (memFCB keep WAS sur.toNoun
            (needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1).toNoun nex.laz.toNoun nedF.toNoun
            (bakeNeed nedF (Sock.mk cape DATA)).1.toNoun (immNoun (bakeNeed nedF (Sock.mk cape DATA)).2)
            nex.th.there (genNoun g2 (cuRest (cacheN C1 C2 C3 C4 SURE))) nm.toNoun
            (memDCtx SCC (C CODE LSR) JH ML TOP (C (C cape.toNoun DATA) FOL)) (C (C cape.toNoun DATA) FOL) ML TOP
            (cacheN C1 C2 C3 C4 SURE') (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0))))
          (memFCB keep WAS sur.toNoun
            (needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1).toNoun nex.laz.toNoun nedF.toNoun
            (bakeNeed nedF (Sock.mk cape DATA)).1.toNoun (immNoun (bakeNeed nedF (Sock.mk cape DATA)).2)
            nex.th.there (genNoun g2 (cuRest (cacheN C1 C2 C3 C4 SURE))) nm.toNoun
            (memDCtx SCC (C CODE LSR) JH ML TOP (C (C cape.toNoun DATA) FOL)) (C (C cape.toNoun DATA) FOL) ML TOP
            (cacheN C1 C2 C3 C4 SURE') (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0))) memProd := by
  have h7 : slot? 7 (memDCtx SCC (C CODE LSR) JH ML TOP (C (C cape.toNoun DATA) FOL)) = some compK := rfl
  have hcode : slot? 52 (memDCtx SCC (C CODE LSR) JH ML TOP (C (C cape.toNoun DATA) FOL)) = some CODE := by
    simp [memDCtx, nock_exec]
  rw [mem_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨_, _, _, rfl⟩ hinl, mem_r3, mem_res]
  -- the run
  have hrunN := comp_run_entry_six h7 hcode env nm hn ha Option.none (cuRest (cacheN C1 C2 C3 C4 SURE)) (A 1) (A 0)
    (cu_entry_nosoft _)
  rw [← gen0_eq, show (CGoal.toL CGoal.done : CGoalL CSet) = CGoalL.done from rfl, hrunL] at hrunN
  rw [show (CGoalL.done : CGoalL CSet) = CGoal.toL CGoal.done from rfl, cu_done_noun, gen0_eq] at hrunN
  simp only [listNoun, Option.map_some, compCore] at hrunN
  -- +collapse-shape
  have hcsN := cs_gate _ h7 (cuRest (cacheN C1 C2 C3 C4 SURE)) g1 nex cape.toNoun ord hsc
  simp only [hargs, ne_eq, not_true_eq_false, if_false, hnoar, Option.map_some, compCore] at hcsN
  have hlz := lazy_toNoun_eta nex.laz
  rw [hlz] at hcsN
  -- the calls of K
  have hbn : nock (C bnBody (C (C nedF.toNoun (C cape.toNoun DATA)) compK)) bnBody
      = some (C (bakeNeed nedF (Sock.mk cape DATA)).1.toNoun (immNoun (bakeNeed nedF (Sock.mk cape DATA)).2)) :=
    bn_gateB nedF (Sock.mk cape DATA)
  have hn1 := nta_gate compK nex.laz.sure.ned
  have hso := so_gate (needToOrd nex.laz.sure.ned) nex.laz.sure.lok cape
  rw [hsur, Option.map_some] at hso
  have hn2 := nta_gate compK (bakeNeed nedF (Sock.mk cape DATA)).1
  rw [mem_final_B (hmode := mem_mode_noop _ _) (hrun := hrunN) (hcs := hcsN) (hbn := hbn) (hn1 := hn1) (hso := hso)
    (hn2 := hn2)]
  simp only [Option.bind_some]
  rw [mem_after (keep := keep) (hG2 := cu_gen_cache _ _) (hwas := hwas) (hw := hw) (hput := hput)]
  rw [hlz]
  rfl

theorem mem_gate_six_B (Q : TreapMap mugF (Nat × List Nat) → Prop) (hT : TsOn Q) (cape : Cape) (DATA FOL : Noun)
    (keep : Bool) (CACHE DN KIDS ML0 CB SCC CODE LSR JH CACHE0 : Noun)
    (nm : Nomm) (C1 C2 C3 C4 SURE : Noun)
    (hinl : nock (C inlBody (C (C (C (C cape.toNoun DATA) FOL) (C (C CODE LSR) (C JH CACHE))) compK)) inlBody
      = some (C nm.toNoun (cacheN C1 C2 C3 C4 SURE)))
    (env : CallEnv) (hn : SixOk nm = true) (ha : Bake.NoAx0 nm)
    (nex : NextL CSet) (g1 : Gen (TreapMap mugF))
    (hrunL : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))
    (hQ : Q g1.cond)
    (ord : NeedOrd) (hsc : nock (C scBody (C (C nex.laz.toNoun cape.toNoun) compK)) scBody = some ord.toNoun)
    (hargs : nex.th.args = []) (nedF : Need) (g2 : Gen (TreapMap mugF))
    (hnoar : needOrdAllocRegs ord g1 = some (nedF, g2))
    (hrun : isRun (flattenNeed (bakeNeed nedF (Sock.mk cape DATA)).1)
      ((flattenNeed (bakeNeed nedF (Sock.mk cape DATA)).1).headD 0) 0 = true)
    (sur : NeedOrd) (hsur : sureOf (needToOrd nex.laz.sure.ned) nex.laz.sure.lok cape = some sur)
    (WAS SURE' : Noun) (hwas : getF mugF (C (C cape.toNoun DATA) FOL) SURE = some WAS)
    (hw : WAS = A 0 ∨ ∃ u, WAS = C (A 0) u)
    (hput : putF mugF (C (C cape.toNoun DATA) FOL) (memSurKN keep WAS sur.toNoun) SURE = some SURE') :
    nock (C memBody (C (memSam (C (C cape.toNoun DATA) FOL) (A 0x656e6f64) (loob keep) (A 0) (A 0) CACHE)
        (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0))) memBody
      = (finishLFC (S := CSet) (Map := TreapMap mugF) env nm ord cape
          (fun n => bakeNeed n (Sock.mk cape DATA))).map fun st =>
          C (memChgN (memMovedN keep WAS sur.toNoun) (needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1).toNoun)
            (C (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))) (cacheN C1 C2 C3 C4 SURE')) := by
  rw [mem_to_finish_six_B cape DATA FOL keep (A 0) (A 0) CACHE DN KIDS ML0 CB SCC CODE LSR JH CACHE0 nm C1 C2 C3 C4 SURE
    hinl env hn ha nex g1 hrunL ord hsc hargs nedF g2 hnoar sur hsur WAS SURE' hwas hw hput]
  have hmv : memMovedN keep WAS sur.toNoun = A 0 ∨ memMovedN keep WAS sur.toNoun = A 1 := by
    unfold memMovedN; split <;> simp
  have hnn : ∃ p q, (needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1).toNoun = C p q := nord_cell _
  unfold memFCB
  rw [mem_prod_new (hmv := hmv) (hnn := hnn)]
  obtain ⟨hs6, hs14, hs496, hl2⟩ := mem_rest_slots nm.toNoun SCC (C CODE LSR) JH (A 0) (A 0) cape.toNoun DATA FOL
    (loob keep) (cacheN C1 C2 C3 C4 SURE') DN KIDS ML0 CB CACHE0
  have hf := fin_gate_finishLF_six_B Q hT env
    (rfl : slot? 7 (memDCtx SCC (C CODE LSR) JH (A 0) (A 0) (C (C cape.toNoun DATA) FOL)) = some compK)
    (memMovedN keep WAS sur.toNoun) (memSurKN keep WAS sur.toNoun) WAS
    (needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1).toNoun
    sur.toNoun _ cuBunt cape hs6 hs14 hs496 hl2 (cuRest (cacheN C1 C2 C3 C4 SURE)) rfl nm ord nex g1 g2
    nedF (Sock.mk cape DATA) hrunL hargs hQ hnoar hrun
  rw [hf, Option.map_map]
  rfl

/-! ## The SCC of one bell -/

/-- **The residual of the bake is a run** on every final pass of `nm` with
the `ord` `ordOf`: the registers that `+bake-need` leaves of those of
`+need-ord-alloc-regs` (`ordOf nex`) under the sock `[cape DATA]`.  It
stands for `NoBakeOneO` (nothing baked) in the tops of this file. -/
def BakeRunO (env : CallEnv) (nm : Nomm) (ordOf : NextL CSet → NeedOrd) (cape : Cape) (DATA : Noun) : Prop :=
  ∀ nex g1 nedF g2, runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))
      = some (nex, g1) →
    needOrdAllocRegs (ordOf nex) g1 = some (nedF, g2) →
    isRun (flattenNeed (bakeNeed nedF (Sock.mk cape DATA)).1)
      ((flattenNeed (bakeNeed nedF (Sock.mk cape DATA)).1).headD 0) 0 = true

/-- The residual is a run when its registers are an infix of those of
`ned-final` (`bake_run_of_infix`): in particular a known prefix or suffix
in preorder (`bake_run_head`, `bake_run_tail_pair`, `bake_run_tail_both`). -/
theorem bakeRunO_of_infix (env : CallEnv) (nm : Nomm) (ordOf : NextL CSet → NeedOrd) (cape : Cape) (DATA : Noun)
    (h : ∀ nex g1 nedF g2, runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))
      = some (nex, g1) → needOrdAllocRegs (ordOf nex) g1 = some (nedF, g2) →
      flattenNeed (bakeNeed nedF (Sock.mk cape DATA)).1 <:+: flattenNeed nedF) :
    BakeRunO env nm ordOf cape DATA :=
  fun nex g1 nedF g2 hr hno => bake_run_of_infix nedF _ (isRun_needOrdAllocRegs hno) (h nex g1 nedF g2 hr hno)

/-- Under cape `|` nothing is baked, so the residual is `ned-final`, a run. -/
theorem bakeRunO_no (env : CallEnv) (nm : Nomm) (ordOf : NextL CSet → NeedOrd) (DATA : Noun) :
    BakeRunO env nm ordOf Cape.no DATA :=
  bakeRunO_of_infix env nm ordOf Cape.no DATA fun _ _ nedF _ _ _ => by
    rw [bakeNeed, (bakeGo_no nedF DATA []).1]; exact List.infix_refl _

theorem csi_gate_scc_one_m_six_B (Q : TreapMap mugF (Nat × List Nat) → Prop) (hT : TsOn Q) (cape : Cape)
    (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (env : CallEnv) (hn : SixOk nm = true) (ha : Bake.NoAx0 nm)
    (nex : NextL CSet) (g1 : Gen (TreapMap mugF))
    (hrunL : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))
    (hQ : Q g1.cond) (hargs : nex.th.args = [])
    (ord : NeedOrd) (hsc : nock (C scBody (C (C nex.laz.toNoun cape.toNoun) compK)) scBody = some ord.toNoun)
    (nedF : Need) (g2 : Gen (TreapMap mugF))
    (hnoar : needOrdAllocRegs ord g1 = some (nedF, g2))
    (hrun : isRun (flattenNeed (bakeNeed nedF (Sock.mk cape DATA)).1)
      ((flattenNeed (bakeNeed nedF (Sock.mk cape DATA)).1).headD 0) 0 = true)
    (SURE' : Noun) (hput : putF mugF (C (C cape.toNoun DATA) FOL) (sccSur nex cape).toNoun SURE = some SURE') :
    nock (C csiBody (C (csiSam (setOne (C (C cape.toNoun DATA) FOL)) (C CODE (C JETS CALLS)) JH
        (cacheN NARY MONO SCCS INL SURE)) compK)) csiBody
      = (finishLFC (S := CSet) (Map := TreapMap mugF) env nm ord cape
          (fun n => bakeNeed n (Sock.mk cape DATA))).bind fun st =>
          (putF mugF (C (C cape.toNoun DATA) FOL) st.toNoun NARY).map fun NARYU =>
            C (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))) (cacheN NARYU MONO SCCS INL' SURE') := by
  have hcache : cacheN NARY MONO SCCS INL SURE = C NARY (C MONO (C SCCS (C INL SURE))) := rfl
  rw [hcache, csi_to_final _ _ _ _ _ _ hnary (csi_kids_noself _ CODE JETS CALLS JH _ hcalls) (ju_has_kids _)]
  have hsur := scc_sur_six_L env hn ha hrunL cape
  have hi := inl_gate_ind (C (C cape.toNoun DATA) FOL) CODE (C JETS CALLS) JH NARY MONO SCCS INL SURE INL' nm
    (indPure_of_sixOk nm hn) hinl
  obtain ⟨WAS, hwas, hw⟩ := getF_of_putF _ _ SURE hput
  have hput' : putF mugF (C (C cape.toNoun DATA) FOL) (memSurKN false WAS (sccSur nex cape).toNoun) SURE
      = some SURE' := by simpa [memSurKN] using hput
  have hm := mem_gate_six_B Q hT cape DATA FOL false (C NARY (C MONO (C SCCS (C INL SURE)))) (A 0)
    (kidsOne (C (C cape.toNoun DATA) FOL)) (A 0) csiBody (setOne (C (C cape.toNoun DATA) FOL)) CODE (C JETS CALLS) JH
    (C NARY (C MONO (C SCCS (C INL SURE)))) nm NARY MONO SCCS INL' SURE hi env hn ha nex g1 hrunL hQ
    ord hsc hargs nedF g2 hnoar hrun (sccSur nex cape) hsur WAS SURE' hwas hw hput'
  cases e : finishLFC (S := CSet) (Map := TreapMap mugF) env nm ord cape (fun n => bakeNeed n (Sock.mk cape DATA)) with
  | none =>
    rw [e, Option.map_none] at hm
    exact csi_final_one_none _ _ _ _ _ _ _ _ hm
  | some st =>
    rw [e, Option.map_some] at hm
    obtain ⟨NARYU, hp, -, -⟩ := putF_spec mugF NARY (C (C cape.toNoun DATA) FOL) st.toNoun hnmap
    have hu := uni_by_one (mug := mugF) layer2 gorIn_morIn_layer2 NARY (C (C cape.toNoun DATA) FOL) st.toNoun hnmap
    rw [hp] at hu
    rw [csi_final_one (hm := hm) (huni := hu)]
    simp [hp, cacheN]

theorem csi_gate_scc_one_f_six_B (Q : TreapMap mugF (Nat × List Nat) → Prop) (hT : TsOn Q) (cape : Cape)
    (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (env : CallEnv) (hn : SixOk nm = true) (hax : Bake.NoAx0 nm)
    (ordOf : NextL CSet → NeedOrd) (hsc : ScAt env nm ordOf cape)
    (hQ : ∀ nex g1, runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))
      = some (nex, g1) → Q g1.cond)
    (hbake : BakeRunO env nm ordOf cape DATA) :
    nock (C csiBody (C (csiSam (setOne (C (C cape.toNoun DATA) FOL)) (C CODE (C JETS CALLS)) JH
        (cacheN NARY MONO SCCS INL SURE)) compK)) csiBody
      = (runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))).bind fun p =>
          (finishLFC (S := CSet) (Map := TreapMap mugF) env nm (ordOf p.1) cape
            (fun n => bakeNeed n (Sock.mk cape DATA))).bind fun st =>
            (putF mugF (C (C cape.toNoun DATA) FOL) st.toNoun NARY).bind fun NARYU =>
              (putF mugF (C (C cape.toNoun DATA) FOL) (sccSur p.1 cape).toNoun SURE).map fun SURE' =>
                C (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))) (cacheN NARYU MONO SCCS INL' SURE') := by
  have hi := inl_gate_ind (C (C cape.toNoun DATA) FOL) CODE (C JETS CALLS) JH NARY MONO SCCS INL SURE INL' nm
    (indPure_of_sixOk nm hn) hinl
  have hcrash : (runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = none ∨
      ∃ nex g1, runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1) ∧
        (nex.th.args ≠ [] ∨ needOrdAllocRegs (ordOf nex) g1 = none)) →
      nock (C csiBody (C (csiSam (setOne (C (C cape.toNoun DATA) FOL)) (C CODE (C JETS CALLS)) JH
        (cacheN NARY MONO SCCS INL SURE)) compK)) csiBody = none := by
    intro hc
    have hcache : cacheN NARY MONO SCCS INL SURE = C NARY (C MONO (C SCCS (C INL SURE))) := rfl
    rw [hcache, csi_to_final _ _ _ _ _ _ hnary (csi_kids_noself _ CODE JETS CALLS JH _ hcalls) (ju_has_kids _)]
    exact csi_final_one_none _ _ _ _ _ _ _ _ (mem_gate_none_six_L cape DATA FOL false (A 0) (A 0)
      (C NARY (C MONO (C SCCS (C INL SURE)))) (A 0) (kidsOne _) (A 0) csiBody _ CODE (C JETS CALLS) JH
      (C NARY (C MONO (C SCCS (C INL SURE)))) nm _ hi env hn hax ordOf hsc hc)
  cases hr : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) with
  | none => exact hcrash (Or.inl hr)
  | some p =>
    obtain ⟨nex, g1⟩ := p
    simp only [Option.bind_some]
    by_cases ha : nex.th.args = []
    · cases hno : needOrdAllocRegs (ordOf nex) g1 with
      | none =>
        have hf : finishLFC (S := CSet) (Map := TreapMap mugF) env nm (ordOf nex) cape
            (fun n => bakeNeed n (Sock.mk cape DATA)) = Option.none := by
          unfold finishLFC; simp [hr, ha, hno]
        rw [hf, hcrash (Or.inr ⟨nex, g1, hr, Or.inr hno⟩)]
        rfl
      | some q =>
        obtain ⟨nedF, g2⟩ := q
        obtain ⟨SURE', hp, -, -⟩ := putF_spec mugF SURE (C (C cape.toNoun DATA) FOL) (sccSur nex cape).toNoun hsmap
        rw [csi_gate_scc_one_m_six_B Q hT cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hcalls
          nm INL' hinl env hn hax nex g1 hr (hQ nex g1 hr) ha (ordOf nex) (hsc nex g1 hr) nedF g2 hno
          (hbake nex g1 nedF g2 hr hno) SURE' hp]
        cases finishLFC (S := CSet) (Map := TreapMap mugF) env nm (ordOf nex) cape
            (fun n => bakeNeed n (Sock.mk cape DATA)) with
        | none => rfl
        | some st =>
          obtain ⟨NARYU, hq, -, -⟩ := putF_spec mugF NARY (C (C cape.toNoun DATA) FOL) st.toNoun hnmap
          simp [hq, hp]
    · have hf : finishLFC (S := CSet) (Map := TreapMap mugF) env nm (ordOf nex) cape
          (fun n => bakeNeed n (Sock.mk cape DATA)) = Option.none := by
        unfold finishLFC; simp [hr, ha]
      rw [hf, hcrash (Or.inr ⟨nex, g1, hr, Or.inl ha⟩)]
      rfl

/-! ## The tops -/

/-- **The gate of `+compile-unary` on an SCC of one bell, on the class with
`%6`, with the real bake**: `cu_gate_scc_one_six_q_L` with the n-ary entry
`finishLFC … (fun n => bakeNeed n (Sock.mk cape DATA))` (the model with
`+bake-need` of `less.b`, `finishLFB`) and `BakeRunO` (the residual of the
bake is a run) in place of `NoBakeOneO` (nothing baked). -/
theorem cu_gate_scc_one_six_q_B (Q : TreapMap mugF (Nat × List Nat) → Prop) (hT : TsOn Q) (cape : Cape)
    (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (env : CallEnv) (hn : SixOk nm = true) (hax : Bake.NoAx0 nm)
    (ordOf : NextL CSet → NeedOrd) (hsc : ScAt env nm ordOf cape)
    (hQ1 : ∀ nex g1, runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))
      = some (nex, g1) → Q g1.cond)
    (hbake : BakeRunO env nm ordOf cape DATA)
    (FUNC V : Noun) (n : Nomm) (hn' : SixOk n = true) (hax' : Bake.NoAx0 n)
    (hQ2 : ∀ nex g1 q g2, runLC env Option.none n (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))
      = some (nex, g1) → kerf nex g1 = some (q, g2) → Q g2.cond)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    nock (C cuGB (C (cuSam FUNC (setOne (C (C cape.toNoun DATA) FOL)) CODE (C JETS CALLS) JH
        (cacheN NARY MONO SCCS INL SURE)) compK)) cuGB
      = (runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))).bind fun p =>
          (finishLFB (S := CSet) (Map := TreapMap mugF) env nm (ordOf p.1) (Sock.mk cape DATA)).bind fun st =>
            (putF mugF (C (C cape.toNoun DATA) FOL) st.toNoun NARY).bind fun NARYU =>
              (putF mugF (C (C cape.toNoun DATA) FOL) (sccSur p.1 cape).toNoun SURE).bind fun SURE' =>
                (finishLUC (S := CSet) (Map := TreapMap mugF) env n).map fun st' =>
                  C (C st'.toNoun (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))))
                    (cacheN NARYU MONO SCCS INL' SURE') := by
  have hcsi := csi_gate_scc_one_f_six_B Q hT cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap
    hsmap hcalls nm INL' hinl env hn hax ordOf hsc hQ1 hbake
  rw [← cu_csi_eq FUNC] at hcsi
  simp only [finishLFB, sockCape]
  cases hr : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) with
  | none =>
    rw [hr] at hcsi
    exact cu_gate_none _ hcsi
  | some p =>
    obtain ⟨nex, g1⟩ := p
    rw [hr] at hcsi
    simp only [Option.bind_some] at hcsi ⊢
    cases e : finishLFC (S := CSet) (Map := TreapMap mugF) env nm (ordOf nex) cape
        (fun n => bakeNeed n (Sock.mk cape DATA)) with
    | none =>
      rw [e] at hcsi
      exact cu_gate_none _ hcsi
    | some st =>
      obtain ⟨NARYU, hq, -, -⟩ := putF_spec mugF NARY (C (C cape.toNoun DATA) FOL) st.toNoun hnmap
      obtain ⟨SURE', hp, -, -⟩ := putF_spec mugF SURE (C (C cape.toNoun DATA) FOL) (sccSur nex cape).toNoun hsmap
      rw [e] at hcsi
      simp only [Option.bind_some, hq, hp, Option.map_some] at hcsi ⊢
      exact cu_gate_six Q hT FUNC _ CODE (C JETS CALLS) JH _ _ _ V env n hn' hax' hQ2 hcsi hgot hv

/-- **The top on `SixOk` with the real bake and the `ord` of
`+shape-collapse`**: `cu_gate_scc_one_six_fix` with the n-ary entry
`finishLFB env nm (scOrd fuel p.1 cape) (Sock.mk cape DATA)` and
`BakeRunO` in place of `NoBakeOneO`.  Hypotheses: the state nouns,
`NoSelfCall`, `SixOk`, `NoAx0`, `FixRet` (the model's loop of
`+inter2-collapse` stops within `fuel` rounds) and `BakeRunO` (the residual
of `+bake-need` is a run; `bakeRunO_of_infix`, `bakeRunO_no`). -/
theorem cu_gate_scc_one_six_bake (fuel : Nat) (cape : Cape) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (env : CallEnv) (hn : SixOk nm = true) (hax : Bake.NoAx0 nm) (hfix : FixRet env nm cape fuel)
    (hbake : BakeRunO env nm (fun nex => scOrd fuel nex cape) cape DATA)
    (FUNC V : Noun) (n : Nomm) (hn' : SixOk n = true) (hax' : Bake.NoAx0 n)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    nock (C cuGB (C (cuSam FUNC (setOne (C (C cape.toNoun DATA) FOL)) CODE (C JETS CALLS) JH
        (cacheN NARY MONO SCCS INL SURE)) compK)) cuGB
      = (runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))).bind fun p =>
          (finishLFB (S := CSet) (Map := TreapMap mugF) env nm (scOrd fuel p.1 cape) (Sock.mk cape DATA)).bind fun st =>
            (putF mugF (C (C cape.toNoun DATA) FOL) st.toNoun NARY).bind fun NARYU =>
              (putF mugF (C (C cape.toNoun DATA) FOL) (sccSur p.1 cape).toNoun SURE).bind fun SURE' =>
                (finishLUC (S := CSet) (Map := TreapMap mugF) env n).map fun st' =>
                  C (C st'.toNoun (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))))
                    (cacheN NARYU MONO SCCS INL' SURE') :=
  cu_gate_scc_one_six_q_B (fun _ => True) tsMapAt_holds cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE
    hnary hnmap hsmap hcalls nm INL' hinl env hn hax (fun nex => scOrd fuel nex cape)
    (scAt_of_scRet env nm cape fuel (scRet_of_fixRet env hn hax cape fuel hfix)) (fun _ _ _ => trivial) hbake
    FUNC V n hn' hax' (fun _ _ _ _ _ _ => trivial) hgot hv

/-! ## A known head -/

/-- `+need-ord-alloc-regs` of a cell shape whose head is `%this`. -/
theorem noar_pair_this (q : NeedOrd) (g g' : Gen (TreapMap mugF)) (nedF : Need)
    (h : needOrdAllocRegs (NeedOrd.pair NeedOrd.this q) g = some (nedF, g')) :
    ∃ r t, nedF = Need.pair (Need.this r) t := by
  simp only [needOrdAllocRegs, cra_bind] at h
  obtain ⟨hh, g1, e1, tt, g2, -, e3⟩ := h
  obtain ⟨r, g0, -, e1'⟩ := e1
  simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e1'
  obtain ⟨rfl, -⟩ := e1'
  simp only [reduceCtorEq, false_and, if_false, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e3
  exact ⟨r, tt, e3.1.symm⟩

/-- **`BakeRunO` for a wholly known head** (cape `[c |]` with `c` wholly
known, data a cell) whenever the `ord` of every final pass is a cell with a
`%this` head: the head's register is baked away and the rest is a suffix
(`bake_run_head`). -/
theorem bakeRunO_head (env : CallEnv) (nm : Nomm) (ordOf : NextL CSet → NeedOrd) (ch : Cape) (dh dt : Noun)
    (hc : Ca.all ch = true)
    (h : ∀ nex g1, runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))
      = some (nex, g1) → ∃ q, ordOf nex = NeedOrd.pair NeedOrd.this q) :
    BakeRunO env nm ordOf (Cape.cell ch Cape.no) (C dh dt) := by
  intro nex g1 nedF g2 hr hno
  have hrun := isRun_needOrdAllocRegs hno
  obtain ⟨q, hq⟩ := h nex g1 hr
  rw [hq] at hno
  obtain ⟨r, t, rfl⟩ := noar_pair_this q g1 g2 _ hno
  exact (bake_run_head (Need.this r) t dh dt hc rfl hrun).2

/-- `%s01` of `tools/hoon/bakedump.hoon`: `[6 [0 2] [0 6] [0 7]]` on the
bell `[[& |] [0 0]]` (the head of the subject known, `0`). -/
def sixHead : Nomm := Nomm.n6 (Nomm.n0 2) (Nomm.n0 6) (Nomm.n0 7)

/-- The cape `[& |]`. -/
def capeHead : Cape := Cape.cell Cape.yes Cape.no

/- The model's final pass of `sixHead` (over `LS`, `FM`, in the
environment of the dumps): the `ord` of `+shape-collapse` is `[%this
[%this %this]]` (the real compiler's, `%s01` of `Ska/BakeNeedCheck.lean`),
`+bake-need` under `[[& |] [0 0]]` bakes one register (the head's) and
leaves a run of two. -/
#guard ((runLC (S := LS) (Map := FM) envR Option.none sixHead (CGoalL.done : CGoalL LS) [] gen0).bind fun p =>
    (shapeCol 64 p.1.laz capeHead).bind fun ord => (needOrdAllocRegs ord p.2).map fun q =>
      let b := bakeNeed q.1 (Sock.mk capeHead (C (A 0) (A 0)))
      (ord, b.2.length, (flattenNeed b.1).length, isRun (flattenNeed b.1) ((flattenNeed b.1).headD 0) 0))
  = some (NeedOrd.pair NeedOrd.this (NeedOrd.pair NeedOrd.this NeedOrd.this), 1, 2, true)

/- The n-ary entry of the model with the bake (`finishLFB`) succeeds there
with two arguments, the head being an `%imm` in the prologue. -/
#guard ((runLC (S := LS) (Map := FM) envR Option.none sixHead (CGoalL.done : CGoalL LS) [] gen0).bind fun p =>
    (finishLFB (S := LS) (Map := FM) envR sixHead ((shapeCol 64 p.1.laz capeHead).getD NeedOrd.none)
      (Sock.mk capeHead (C (A 0) (A 0)))).map fun st => st.nargs) = some 2

/-- **The top with the real bake on a known head** (`sixHead` as the SCC's
nomm and as the code's nomm, the bell `[[& |] DATA]` with the head of `DATA`
known): `BakeRunO` from `bakeRunO_head` once the `ord` is a cell with a
`%this` head (`hord`, what the `#guard`s compute: `[%this [%this %this]]`);
`FixRet` stays. -/
example (fuel : Nat) (dh dt FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C capeHead.toNoun (C dh dt)) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C capeHead.toNoun (C dh dt)) FOL) CALLS) (INL' : Noun)
    (hinl : InlOK (C (C capeHead.toNoun (C dh dt)) FOL) CODE INL sixHead INL') (env : CallEnv)
    (hfix : FixRet env sixHead capeHead fuel)
    (hord : ∀ nex g1, runLC env Option.none sixHead (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))
      = some (nex, g1) → ∃ q, scOrd fuel nex capeHead = NeedOrd.pair NeedOrd.this q)
    (FUNC V : Noun) (hgot : getF mugF FUNC CODE = some (C (A 0) V))
    (hv : slot? 2 V = some sixHead.toNoun) :=
  cu_gate_scc_one_six_bake fuel capeHead (C dh dt) FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hsmap
    hcalls _ INL' hinl env rfl (by simp [sixHead, Bake.NoAx0]) hfix
    (bakeRunO_head env _ _ Cape.yes dh dt rfl hord) FUNC V sixHead rfl (by simp [sixHead, Bake.NoAx0]) hgot hv

end Compiler
end Formalization
