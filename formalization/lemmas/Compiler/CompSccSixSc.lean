import lemmas.Compiler.CompStraightMapSix
import lemmas.Compiler.CompShapeColL2i
import lemmas.Compiler.CompCoerceLazyGen

/-!
# The top on `SixOk` with the `ord` of `+shape-collapse`

The chain of `CompSccSix.lean` (`cu_gate_scc_one_six`) without `FinSure`:
the final pass may leave forks and bonds in its `laz`.

1. `+coerce-lazy` on any lazy need: `comp_coerce_lazy_all` in place of
   `cz_gate_L` (`fin_gate_ts_L`, `fin_gate_finishLF_six_L`);
2. the `laz` noun of `+collapse-shape` read by `mem_final` is `[[ned lok]
   forks bonds]` for any forks and bonds (`lazy_toNoun_eta`,
   `mem_to_finish_six_L`, `mem_gate_six_L`);
3. `+sure-of` of the sure part (what goes into `sure.cache`) succeeds and is
   `sccSur` without `FinSure` (`scc_sur_six_L`);
4. the `ord` of the n-ary entry is any `ordOf nex` that `+shape-collapse`
   returns (`ScAt`, `NoBakeOneO`; `csi_gate_scc_one_m_six_L`,
   `mem_gate_none_six_L`, `csi_gate_scc_one_f_six_L`,
   `cu_gate_scc_one_six_q_L`);
5. with `ordOf := scOrd fuel · cape` (the model's `shapeCol`), `ScAt`
   follows from `sc_gate` when the model returns at `fuel` (`ScRet`):
   **`cu_gate_scc_one_six_sc`** and **`cu_gate_scc_one_six_fol_sc`**, with
   `+to-straight` by `tsMapAt_holds`.

The example at the end is the bare `[6 [0 2] [0 3] [1 0]]` as the SCC's
nomm, the case where `sccSur` was not the Hoon's `ord`; its `#guard` runs
the model's final pass and `shapeCol` and finds the Hoon's `[[%this ~] %this ~]`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## The named hypotheses -/

/-- **`+shape-collapse` returns `ordOf nex`** on the `laz` of the final pass
of `nm`. -/
def ScAt (env : CallEnv) (nm : Nomm) (ordOf : NextL CSet → NeedOrd) (cape : Cape) : Prop :=
  ∀ nex g1, runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1) →
    nock (C scBody (C (C nex.laz.toNoun cape.toNoun) compK)) scBody = some (ordOf nex).toNoun

/-- **`NoBakeOneC` with the `ord` `ordOf`**: nothing baked from the
registers that `+need-ord-alloc-regs` gives `ordOf nex`. -/
def NoBakeOneO (env : CallEnv) (nm : Nomm) (ordOf : NextL CSet → NeedOrd) (cape : Cape) (DATA : Noun) : Prop :=
  ∀ nex g1 nedF g2, runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))
      = some (nex, g1) →
    needOrdAllocRegs (ordOf nex) g1 = some (nedF, g2) → NoBake nedF (Sock.mk cape DATA)

theorem noBakeOneO_no (env : CallEnv) (nm : Nomm) (ordOf : NextL CSet → NeedOrd) (DATA : Noun) :
    NoBakeOneO env nm ordOf Cape.no DATA :=
  fun _ _ nedF _ _ _ => noBake_no nedF DATA

/-- The `ord` of the model: `shapeCol` at `fuel`. -/
noncomputable def scOrd (fuel : Nat) (nex : NextL CSet) (cape : Cape) : NeedOrd :=
  (shapeCol fuel nex.laz cape).getD NeedOrd.none

/-- **The model's `+shape-collapse` returns at `fuel`** on the `laz` of the
final pass of `nm`. -/
def ScRet (env : CallEnv) (nm : Nomm) (cape : Cape) (fuel : Nat) : Prop :=
  ∀ nex g1, runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1) →
    (shapeCol fuel nex.laz cape).isSome

/-- `ScAt` of the model's `ord` from `sc_gate`. -/
theorem scAt_of_scRet (env : CallEnv) (nm : Nomm) (cape : Cape) (fuel : Nat) (h : ScRet env nm cape fuel) :
    ScAt env nm (fun nex => scOrd fuel nex cape) cape := by
  intro nex g1 hr
  have hs := h nex g1 hr
  cases e : shapeCol fuel nex.laz cape with
  | none => rw [e] at hs; cases hs
  | some r =>
    have hg := sc_gate nex.laz cape fuel r e
    simp only [scOrd, e, Option.getD_some]
    exact hg

/-! ## The pieces without `FinSure` -/

theorem lazy_toNoun_eta (l : Lazy CSet) :
    l.toNoun = C (C l.sure.ned.toNoun (HoonSet.toNoun l.sure.lok)) (C (Lazy.forksNoun l.fork) (Lazy.bondsNoun l.bond)) := by
  cases l; rfl

/-- `+sure-of` of the sure part of the final pass succeeds and is `sccSur`. -/
theorem scc_sur_six_L (env : CallEnv) {nm : Nomm} (hn : SixOk nm = true) (ha : Bake.NoAx0 nm)
    {nex : NextL CSet} {g1 : Gen (TreapMap mugF)}
    (hrun : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))
    (cape : Cape) :
    sureOf (needToOrd nex.laz.sure.ned) nex.laz.sure.lok cape = some (sccSur nex cape) := by
  have hr : CrLok nex.laz.sure := lall_root (entry_lok env hn ha hrun)
  obtain ⟨r, hr'⟩ := sureOf_some cape nex.laz.sure.lok hr (needToOrd nex.laz.sure.ned)
  simp only [sccSur, hr']
  rfl

theorem fin_gate_ts_L (Q : TreapMap mugF (Nat × List Nat) → Prop) (hT : TsOn Q) {ctx : Noun} (h7 : slot? 7 ctx = some compK) (c2 c6 c14 NEWN SUR REST G0 : Noun)
    (less : Cape) (hcomp : slot? 6 REST = some (C comp.door (C G0 ctx))) (hdone : slot? 14 REST = some (A 0))
    (hless : slot? 496 REST = some less.toNoun) (hl2 : slot? 0x3ffffff REST = some layer2)
    (g : Gen (TreapMap mugF)) (x : GenRest) (hs0 : x.soft = A 0) (hQ : Q g.cond)
    (nedF : Need) (hrun : isRun (flattenNeed nedF) ((flattenNeed nedF).headD 0) 0 = true)
    (o : Nat) (laz : Lazy CSet) :
    nock (C finBody (C (A 0) (finCtx c2 c6 c14 NEWN laz.toNoun nedF.toNoun nedF.toNoun (A 0) o SUR
        (genNoun g x) REST))) finBody
      = (finTail nedF less o laz (fun n => (n, [])) g).map Straight.toNoun := by
  have hc := (comp_ctx_pill ctx h7).1
  have hcz := comp_coerce_lazy_all h7 x (fun o => fin_softOut x hs0 o) nedF o laz less g
  have hczat := comp_cz_at
  have hsdat := sd_at
  have haoat := comp_add_ops_at
  have htsat := comp_ts_at
  unfold finTail
  simp only [List.map_nil]
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
    have hao := comp_add_ops x hc g3 o []
    have kc3 := (kc_coerceLazyL nedF less o laz).keep g u1 g3 e1
    simp only [listNoun] at hao
    cases e2 : addOps o [] g3 with
    | none =>
      rw [e2] at hao
      simp only [compCore, Option.map_some] at hcz hsd hao
      conv => { lhs; arg 2; unfold finBody }
      simp only [finCtx, Option.bind_some]
      generalize comp.door = Dr at hcz hczat hsdat haoat htsat hcomp hsd hao
      generalize sdArm = SD at hsdat hsd
      simp [nock_exec, hcomp, hdone, hless, hl2, hczat, comp_cz_arm, hcz, hsdat, hsd, haoat, comp_add_ops_arm,
        turn.arm_at, turn_arm, fin_turn_nil, hao, e2]
    | some r2 =>
      obtain ⟨u2, g4⟩ := r2
      rw [e2] at hao
      have kc4 := (KC.addOps' o []).keep g3 u2 g4 e2
      have hts := hT ctx h7 g4 x o nedF (by rw [kc4, kc3]; exact hQ) hrun
      simp only [compCore, Option.map_some, tsSampleN] at hcz hsd hao hts
      conv => { lhs; arg 2; unfold finBody }
      simp only [finCtx, Option.bind_some]
      generalize comp.door = Dr at hcz hczat hsdat haoat htsat hcomp hsd hao hts
      generalize sdArm = SD at hsdat hsd
      simp [nock_exec, hcomp, hdone, hless, hl2, hczat, comp_cz_arm, hcz, hsdat, hsd, haoat, comp_add_ops_arm,
        turn.arm_at, turn_arm, fin_turn_nil, hao, htsat, comp_ts_arm, hts, e2]
      all_goals exact hts

theorem fin_gate_finishLF_six_L (Q : TreapMap mugF (Nat × List Nat) → Prop) (hT : TsOn Q) {ctx : Noun} (env : CallEnv) (h7 : slot? 7 ctx = some compK) (c2 c6 c14 NEWN SUR REST G0 : Noun)
    (less : Cape) (hcomp : slot? 6 REST = some (C comp.door (C G0 ctx))) (hdone : slot? 14 REST = some (A 0))
    (hless : slot? 496 REST = some less.toNoun) (hl2 : slot? 0x3ffffff REST = some layer2)
    (x : GenRest) (hs0 : x.soft = A 0)
    (nm : Nomm) (ord : NeedOrd) (nex : NextL CSet) (g1 g2 : Gen (TreapMap mugF)) (nedF : Need)
    (hrunL : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))
    (hargs : nex.th.args = [])
    (hQ : Q g1.cond)
    (hnoar : needOrdAllocRegs ord g1 = some (nedF, g2)) :
    nock (C finBody (C (A 0) (finCtx c2 c6 c14 NEWN nex.laz.toNoun nedF.toNoun nedF.toNoun (A 0) nex.th.there SUR
        (genNoun g2 x) REST))) finBody
      = (finishLFC (S := CSet) (Map := TreapMap mugF) env nm ord less (fun n => (n, []))).map Straight.toNoun := by
  have kc2 := (kc_needOrdAllocRegs (Map := TreapMap mugF) ord).keep g1 nedF g2 hnoar
  have hrun := isRun_needOrdAllocRegs hnoar
  rw [finishLFC_tail, hrunL]
  simp only [Option.bind_some, hargs, ne_eq, not_true_eq_false, if_false, hnoar]
  exact fin_gate_ts_L Q hT h7 c2 c6 c14 NEWN SUR REST G0 less hcomp hdone hless hl2 g2 x hs0
    (by rw [kc2]; exact hQ) nedF hrun nex.th.there nex.laz

theorem mem_to_finish_six_L (cape : Cape) (DATA FOL : Noun) (keep : Bool)
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
    (hb : NoBake nedF (Sock.mk cape DATA))
    (sur : NeedOrd) (hsur : sureOf (needToOrd nex.laz.sure.ned) nex.laz.sure.lok cape = some sur)
    (WAS SURE' : Noun) (hwas : getF mugF (C (C cape.toNoun DATA) FOL) SURE = some WAS)
    (hw : WAS = A 0 ∨ ∃ u, WAS = C (A 0) u)
    (hput : putF mugF (C (C cape.toNoun DATA) FOL) (memSurKN keep WAS sur.toNoun) SURE = some SURE') :
    nock (C memBody (C (memSam (C (C cape.toNoun DATA) FOL) (A 0x656e6f64) (loob keep) ML TOP CACHE)
        (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0))) memBody
      = nock (C (C finBody (C (A 0) (memFC keep WAS sur.toNoun (needToOrd nedF).toNoun nex.laz.toNoun nedF.toNoun
            nex.th.there (genNoun g2 (cuRest (cacheN C1 C2 C3 C4 SURE))) nm.toNoun
            (memDCtx SCC (C CODE LSR) JH ML TOP (C (C cape.toNoun DATA) FOL)) (C (C cape.toNoun DATA) FOL) ML TOP
            (cacheN C1 C2 C3 C4 SURE') (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0))))
          (memFC keep WAS sur.toNoun (needToOrd nedF).toNoun nex.laz.toNoun nedF.toNoun
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
  have hbn := fin_bak ord g1 g2 nedF (Sock.mk cape DATA) hnoar hb
  simp only [Sock.toNoun] at hbn
  have hn1 := nta_gate compK nex.laz.sure.ned
  have hso := so_gate (needToOrd nex.laz.sure.ned) nex.laz.sure.lok cape
  rw [hsur, Option.map_some] at hso
  have hn2 := nta_gate compK nedF
  rw [mem_final (hmode := mem_mode_noop _ _) (hrun := hrunN) (hcs := hcsN) (hbn := hbn) (hn1 := hn1) (hso := hso)
    (hn2 := hn2)]
  simp only [Option.bind_some]
  rw [mem_after (keep := keep) (hG2 := cu_gen_cache _ _) (hwas := hwas) (hw := hw) (hput := hput)]
  rw [hlz]
  rfl

theorem mem_gate_six_L (Q : TreapMap mugF (Nat × List Nat) → Prop) (hT : TsOn Q)  (cape : Cape) (DATA FOL : Noun) (keep : Bool)
    (CACHE DN KIDS ML0 CB SCC CODE LSR JH CACHE0 : Noun)
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
    (hb : NoBake nedF (Sock.mk cape DATA))
    (sur : NeedOrd) (hsur : sureOf (needToOrd nex.laz.sure.ned) nex.laz.sure.lok cape = some sur)
    (WAS SURE' : Noun) (hwas : getF mugF (C (C cape.toNoun DATA) FOL) SURE = some WAS)
    (hw : WAS = A 0 ∨ ∃ u, WAS = C (A 0) u)
    (hput : putF mugF (C (C cape.toNoun DATA) FOL) (memSurKN keep WAS sur.toNoun) SURE = some SURE') :
    nock (C memBody (C (memSam (C (C cape.toNoun DATA) FOL) (A 0x656e6f64) (loob keep) (A 0) (A 0) CACHE)
        (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0))) memBody
      = (finishLFC (S := CSet) (Map := TreapMap mugF) env nm ord cape (fun n => (n, []))).map fun st =>
          C (memChgN (memMovedN keep WAS sur.toNoun) (needToOrd nedF).toNoun)
            (C (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))) (cacheN C1 C2 C3 C4 SURE')) := by
  rw [mem_to_finish_six_L cape DATA FOL keep (A 0) (A 0) CACHE DN KIDS ML0 CB SCC CODE LSR JH CACHE0 nm C1 C2 C3 C4 SURE
    hinl env hn ha nex g1 hrunL ord hsc hargs nedF g2 hnoar hb sur hsur WAS SURE' hwas hw hput]
  have hmv : memMovedN keep WAS sur.toNoun = A 0 ∨ memMovedN keep WAS sur.toNoun = A 1 := by
    unfold memMovedN; split <;> simp
  have hnn : ∃ p q, (needToOrd nedF).toNoun = C p q := nord_cell _
  unfold memFC
  rw [mem_prod_new (hmv := hmv) (hnn := hnn)]
  obtain ⟨hs6, hs14, hs496, hl2⟩ := mem_rest_slots nm.toNoun SCC (C CODE LSR) JH (A 0) (A 0) cape.toNoun DATA FOL
    (loob keep) (cacheN C1 C2 C3 C4 SURE') DN KIDS ML0 CB CACHE0
  have hf := fin_gate_finishLF_six_L Q hT env (rfl : slot? 7 (memDCtx SCC (C CODE LSR) JH (A 0) (A 0) (C (C cape.toNoun DATA) FOL))
      = some compK) (memMovedN keep WAS sur.toNoun) (memSurKN keep WAS sur.toNoun) WAS (needToOrd nedF).toNoun
    sur.toNoun _ cuBunt cape hs6 hs14 hs496 hl2 (cuRest (cacheN C1 C2 C3 C4 SURE)) rfl nm ord nex g1 g2
    nedF hrunL hargs hQ hnoar
  rw [hf, Option.map_map]
  rfl

theorem csi_gate_scc_one_m_six_L (Q : TreapMap mugF (Nat × List Nat) → Prop) (hT : TsOn Q)  (cape : Cape) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
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
    (hb : NoBake nedF (Sock.mk cape DATA))
    (SURE' : Noun) (hput : putF mugF (C (C cape.toNoun DATA) FOL) (sccSur nex cape).toNoun SURE = some SURE') :
    nock (C csiBody (C (csiSam (setOne (C (C cape.toNoun DATA) FOL)) (C CODE (C JETS CALLS)) JH
        (cacheN NARY MONO SCCS INL SURE)) compK)) csiBody
      = (finishLFC (S := CSet) (Map := TreapMap mugF) env nm ord cape (fun n => (n, []))).bind fun st =>
          (putF mugF (C (C cape.toNoun DATA) FOL) st.toNoun NARY).map fun NARYU =>
            C (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))) (cacheN NARYU MONO SCCS INL' SURE') := by
  have hcache : cacheN NARY MONO SCCS INL SURE = C NARY (C MONO (C SCCS (C INL SURE))) := rfl
  rw [hcache, csi_to_final _ _ _ _ _ _ hnary (csi_kids_noself _ CODE JETS CALLS JH _ hcalls) (ju_has_kids _)]
  have hsur := scc_sur_six_L env hn ha hrunL cape
  have hi := inl_gate_ind (C (C cape.toNoun DATA) FOL) CODE (C JETS CALLS) JH NARY MONO SCCS INL SURE INL' nm (indPure_of_sixOk nm hn) hinl
  obtain ⟨WAS, hwas, hw⟩ := getF_of_putF _ _ SURE hput
  have hput' : putF mugF (C (C cape.toNoun DATA) FOL) (memSurKN false WAS (sccSur nex cape).toNoun) SURE
      = some SURE' := by simpa [memSurKN] using hput
  have hm := mem_gate_six_L Q hT cape DATA FOL false (C NARY (C MONO (C SCCS (C INL SURE)))) (A 0)
    (kidsOne (C (C cape.toNoun DATA) FOL)) (A 0) csiBody (setOne (C (C cape.toNoun DATA) FOL)) CODE (C JETS CALLS) JH
    (C NARY (C MONO (C SCCS (C INL SURE)))) nm NARY MONO SCCS INL' SURE hi env hn ha nex g1 hrunL hQ
    ord hsc hargs nedF g2 hnoar hb (sccSur nex cape) hsur WAS SURE' hwas hw hput'
  cases e : finishLFC (S := CSet) (Map := TreapMap mugF) env nm ord cape (fun n => (n, [])) with
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

theorem mem_gate_none_six_L (cape : Cape) (DATA FOL : Noun) (keep : Bool)
    (ML TOP CACHE DN KIDS ML0 CB SCC CODE LSR JH CACHE0 : Noun) (nm : Nomm) (CA : Noun)
    (hinl : nock (C inlBody (C (C (C (C cape.toNoun DATA) FOL) (C (C CODE LSR) (C JH CACHE))) compK)) inlBody
      = some (C nm.toNoun CA))
    (env : CallEnv) (hn : SixOk nm = true) (ha : Bake.NoAx0 nm)
    (ordOf : NextL CSet → NeedOrd) (hsc : ScAt env nm ordOf cape)
    (hcrash : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = none ∨
      ∃ nex g1, runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1) ∧
        (nex.th.args ≠ [] ∨ needOrdAllocRegs (ordOf nex) g1 = none)) :
    nock (C memBody (C (memSam (C (C cape.toNoun DATA) FOL) (A 0x656e6f64) (loob keep) ML TOP CACHE)
        (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0))) memBody = none := by
  have h7 : slot? 7 (memDCtx SCC (C CODE LSR) JH ML TOP (C (C cape.toNoun DATA) FOL)) = some compK := rfl
  have hcode : slot? 52 (memDCtx SCC (C CODE LSR) JH ML TOP (C (C cape.toNoun DATA) FOL)) = some CODE := by
    simp [memDCtx, nock_exec]
  rw [mem_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨_, _, _, rfl⟩ hinl, mem_r3, mem_res]
  have hrunN := comp_run_entry_six h7 hcode env nm hn ha Option.none (cuRest CA) (A 1) (A 0) (cu_entry_nosoft _)
  rcases hcrash with hr | ⟨nex, g1, hr, hc⟩
  · have hr' : runLC env Option.none nm (CGoal.toL (CGoal.done : CGoal CSet)) [] (gen0 : Gen (TreapMap mugF)) = none := hr
    rw [← gen0_eq, hr', cu_done_noun] at hrunN
    simp only [listNoun, Option.map_none, compCore] at hrunN
    rw [mem_final_run_none (hmode := mem_mode_noop _ _) (hrun := hrunN)]
    rfl
  · have hr' : runLC env Option.none nm (CGoal.toL (CGoal.done : CGoal CSet)) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1) := hr
    rw [← gen0_eq, hr', cu_done_noun] at hrunN
    simp only [listNoun, Option.map_some, compCore] at hrunN
    have hcsN := cs_gate _ h7 (cuRest CA) g1 nex cape.toNoun (ordOf nex) (hsc nex g1 hr)
    have hnone : (if nex.th.args ≠ [] then Option.none else
        (needOrdAllocRegs (ordOf nex) g1).map fun p =>
          C (C p.1.toNoun (C nex.laz.toNoun (A nex.th.there))) (genNoun p.2 (cuRest CA))) = Option.none := by
      rcases hc with ha | hn
      · simp [ha]
      · simp [hn]
    rw [hnone] at hcsN
    simp only [compCore] at hcsN
    rw [mem_final_cs_none (hmode := mem_mode_noop _ _) (hrun := hrunN) (hcs := hcsN)]
    rfl

theorem csi_gate_scc_one_f_six_L (Q : TreapMap mugF (Nat × List Nat) → Prop) (hT : TsOn Q)  (cape : Cape) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (env : CallEnv) (hn : SixOk nm = true) (hax : Bake.NoAx0 nm)
    (ordOf : NextL CSet → NeedOrd) (hsc : ScAt env nm ordOf cape)
    (hQ : ∀ nex g1, runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1) →
      Q g1.cond)
    (hbake : NoBakeOneO env nm ordOf cape DATA) :
    nock (C csiBody (C (csiSam (setOne (C (C cape.toNoun DATA) FOL)) (C CODE (C JETS CALLS)) JH
        (cacheN NARY MONO SCCS INL SURE)) compK)) csiBody
      = (runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))).bind fun p =>
          (finishLFC (S := CSet) (Map := TreapMap mugF) env nm (ordOf p.1) cape (fun n => (n, []))).bind fun st =>
            (putF mugF (C (C cape.toNoun DATA) FOL) st.toNoun NARY).bind fun NARYU =>
              (putF mugF (C (C cape.toNoun DATA) FOL) (sccSur p.1 cape).toNoun SURE).map fun SURE' =>
                C (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))) (cacheN NARYU MONO SCCS INL' SURE') := by
  have hi := inl_gate_ind (C (C cape.toNoun DATA) FOL) CODE (C JETS CALLS) JH NARY MONO SCCS INL SURE INL' nm (indPure_of_sixOk nm hn) hinl
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
        have hf : finishLFC (S := CSet) (Map := TreapMap mugF) env nm (ordOf nex) cape (fun n => (n, []))
            = Option.none := by
          unfold finishLFC; simp [hr, ha, hno]
        rw [hf, hcrash (Or.inr ⟨nex, g1, hr, Or.inr hno⟩)]
        rfl
      | some q =>
        obtain ⟨nedF, g2⟩ := q
        obtain ⟨SURE', hp, -, -⟩ := putF_spec mugF SURE (C (C cape.toNoun DATA) FOL) (sccSur nex cape).toNoun hsmap
        rw [csi_gate_scc_one_m_six_L Q hT cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hcalls nm INL'
          hinl env hn hax nex g1 hr (hQ nex g1 hr) ha (ordOf nex) (hsc nex g1 hr) nedF g2 hno
          (hbake nex g1 nedF g2 hr hno) SURE' hp]
        cases finishLFC (S := CSet) (Map := TreapMap mugF) env nm (ordOf nex) cape (fun n => (n, [])) with
        | none => rfl
        | some st =>
          obtain ⟨NARYU, hq, -, -⟩ := putF_spec mugF NARY (C (C cape.toNoun DATA) FOL) st.toNoun hnmap
          simp [hq, hp]
    · have hf : finishLFC (S := CSet) (Map := TreapMap mugF) env nm (ordOf nex) cape (fun n => (n, []))
          = Option.none := by
        unfold finishLFC; simp [hr, ha]
      rw [hf, hcrash (Or.inr ⟨nex, g1, hr, Or.inl ha⟩)]
      rfl

/-! ## The top -/

theorem cu_gate_scc_one_six_q_L (Q : TreapMap mugF (Nat × List Nat) → Prop) (hT : TsOn Q) (cape : Cape) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (env : CallEnv) (hn : SixOk nm = true) (hax : Bake.NoAx0 nm)
    (ordOf : NextL CSet → NeedOrd) (hsc : ScAt env nm ordOf cape)
    (hQ1 : ∀ nex g1, runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))
      = some (nex, g1) → Q g1.cond)
    (hbake : NoBakeOneO env nm ordOf cape DATA)
    (FUNC V : Noun) (n : Nomm) (hn' : SixOk n = true) (hax' : Bake.NoAx0 n)
    (hQ2 : ∀ nex g1 q g2, runLC env Option.none n (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))
      = some (nex, g1) → kerf nex g1 = some (q, g2) → Q g2.cond)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    nock (C cuGB (C (cuSam FUNC (setOne (C (C cape.toNoun DATA) FOL)) CODE (C JETS CALLS) JH
        (cacheN NARY MONO SCCS INL SURE)) compK)) cuGB
      = (runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))).bind fun p =>
          (finishLFC (S := CSet) (Map := TreapMap mugF) env nm (ordOf p.1) cape (fun n => (n, []))).bind fun st =>
            (putF mugF (C (C cape.toNoun DATA) FOL) st.toNoun NARY).bind fun NARYU =>
              (putF mugF (C (C cape.toNoun DATA) FOL) (sccSur p.1 cape).toNoun SURE).bind fun SURE' =>
                (finishLUC (S := CSet) (Map := TreapMap mugF) env n).map fun st' =>
                  C (C st'.toNoun (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))))
                    (cacheN NARYU MONO SCCS INL' SURE') := by
  have hcsi := csi_gate_scc_one_f_six_L Q hT cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hsmap
    hcalls nm INL' hinl env hn hax ordOf hsc hQ1 hbake
  rw [← cu_csi_eq FUNC] at hcsi
  cases hr : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) with
  | none =>
    rw [hr] at hcsi
    exact cu_gate_none _ hcsi
  | some p =>
    obtain ⟨nex, g1⟩ := p
    rw [hr] at hcsi
    simp only [Option.bind_some] at hcsi ⊢
    cases e : finishLFC (S := CSet) (Map := TreapMap mugF) env nm (ordOf nex) cape (fun n => (n, [])) with
    | none =>
      rw [e] at hcsi
      exact cu_gate_none _ hcsi
    | some st =>
      obtain ⟨NARYU, hq, -, -⟩ := putF_spec mugF NARY (C (C cape.toNoun DATA) FOL) st.toNoun hnmap
      obtain ⟨SURE', hp, -, -⟩ := putF_spec mugF SURE (C (C cape.toNoun DATA) FOL) (sccSur nex cape).toNoun hsmap
      rw [e] at hcsi
      simp only [Option.bind_some, hq, hp, Option.map_some] at hcsi ⊢
      exact cu_gate_six Q hT FUNC _ CODE (C JETS CALLS) JH _ _ _ V env n hn' hax' hQ2 hcsi hgot hv

/-- **The gate of `+compile-unary` on an SCC of one bell, on the class with
`%6`, with the `ord` of `+shape-collapse`**: for nomms `nm` (the SCC's, after
`+inlined`) and `n` (the code's) of `SixOk` with `Bake.NoAx0`, the n-ary
entry is `finishLFC` with the `ord` `scOrd fuel p.1 cape` (the model's
`shapeCol` of the final pass's `laz`, forks and bonds included), and
`sure.cache` gets `sccSur`.  Hypotheses: the state nouns, `NoSelfCall`,
`NoBakeOneO` of that `ord`, and that the model's `shapeCol` returns at
`fuel` (`ScRet`).  No `FinSure`, no `TsMapAt`. -/
theorem cu_gate_scc_one_six_sc (fuel : Nat) (cape : Cape) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (env : CallEnv) (hn : SixOk nm = true) (hax : Bake.NoAx0 nm) (hret : ScRet env nm cape fuel)
    (hbake : NoBakeOneO env nm (fun nex => scOrd fuel nex cape) cape DATA)
    (FUNC V : Noun) (n : Nomm) (hn' : SixOk n = true) (hax' : Bake.NoAx0 n)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    nock (C cuGB (C (cuSam FUNC (setOne (C (C cape.toNoun DATA) FOL)) CODE (C JETS CALLS) JH
        (cacheN NARY MONO SCCS INL SURE)) compK)) cuGB
      = (runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))).bind fun p =>
          (finishLFC (S := CSet) (Map := TreapMap mugF) env nm (scOrd fuel p.1 cape) cape (fun n => (n, []))).bind fun st =>
            (putF mugF (C (C cape.toNoun DATA) FOL) st.toNoun NARY).bind fun NARYU =>
              (putF mugF (C (C cape.toNoun DATA) FOL) (sccSur p.1 cape).toNoun SURE).bind fun SURE' =>
                (finishLUC (S := CSet) (Map := TreapMap mugF) env n).map fun st' =>
                  C (C st'.toNoun (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))))
                    (cacheN NARYU MONO SCCS INL' SURE') :=
  cu_gate_scc_one_six_q_L (fun _ => True) tsMapAt_holds cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE
    hnary hnmap hsmap hcalls nm INL' hinl env hn hax (fun nex => scOrd fuel nex cape)
    (scAt_of_scRet env nm cape fuel hret) (fun _ _ _ => trivial) hbake FUNC V n hn' hax' (fun _ _ _ _ _ _ => trivial)
    hgot hv

/-- **`cu_gate_scc_one_six_sc` on the nomms that `+fol-loop` makes**: on the
nomms, `SixOk`, `FolMade` and `ScRet`. -/
theorem cu_gate_scc_one_six_fol_sc (fuel : Nat) (cape : Cape) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (env : CallEnv) (hn : SixOk nm = true) (hf : FolMade nm) (hret : ScRet env nm cape fuel)
    (hbake : NoBakeOneO env nm (fun nex => scOrd fuel nex cape) cape DATA)
    (FUNC V : Noun) (n : Nomm) (hn' : SixOk n = true) (hf' : FolMade n)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    nock (C cuGB (C (cuSam FUNC (setOne (C (C cape.toNoun DATA) FOL)) CODE (C JETS CALLS) JH
        (cacheN NARY MONO SCCS INL SURE)) compK)) cuGB
      = (runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))).bind fun p =>
          (finishLFC (S := CSet) (Map := TreapMap mugF) env nm (scOrd fuel p.1 cape) cape (fun n => (n, []))).bind fun st =>
            (putF mugF (C (C cape.toNoun DATA) FOL) st.toNoun NARY).bind fun NARYU =>
              (putF mugF (C (C cape.toNoun DATA) FOL) (sccSur p.1 cape).toNoun SURE).bind fun SURE' =>
                (finishLUC (S := CSet) (Map := TreapMap mugF) env n).map fun st' =>
                  C (C st'.toNoun (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))))
                    (cacheN NARYU MONO SCCS INL' SURE') :=
  cu_gate_scc_one_six_sc fuel cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hsmap hcalls nm INL'
    hinl env hn (folMade_noAx0 hf) hret hbake FUNC V n hn' (folMade_noAx0 hf') hgot hv

/-! ## The bare `%6` as the SCC's nomm -/

/-- `[6 [0 2] [0 3] [1 0]]`: the final pass leaves a fork in `laz`, so
`FinSure` is false of it and `sccSur` is not the Hoon's `ord`. -/
def sixBare : Nomm := Nomm.n6 (Nomm.n0 2) (Nomm.n0 3) (Nomm.n1 (A 0))

/- The model's final pass of `sixBare` (over `LS`, `FM`, in the
environment of the dumps), then `shapeCol` of its `laz` under cape `|`:
`[[%this ~] %this ~]`, the product of the Hoon's `+shape-collapse`
(`sc_a01` of `Ska/ShapeColCheck.lean`, dumped from the real compiler). -/
#guard ((runLC (S := LS) (Map := FM) envR Option.none sixBare (CGoalL.done : CGoalL LS) [] gen0).map fun p =>
    shapeCol 64 p.1.laz Cape.no) = some (some (NeedOrd.pair NeedOrd.this NeedOrd.this))

/- The old `ord`, `+sure-of` of the sure part, is `[[%this ~] %none ~]`
there: what goes into `sure.cache`, not the `ord`. -/
#guard ((runLC (S := LS) (Map := FM) envR Option.none sixBare (CGoalL.done : CGoalL LS) [] gen0).map fun p =>
    sureOfS (needToOrd p.1.laz.sure.ned) p.1.laz.sure.lok Cape.no) = some (some (NeedOrd.pair NeedOrd.this NeedOrd.none))

/- The model's fixed point takes three rounds there, so the fuel `3`
suffices. -/
#guard ((runLC (S := LS) (Map := FM) envR Option.none sixBare (CGoalL.done : CGoalL LS) [] gen0).map fun p =>
    (shapeCol 3 p.1.laz Cape.no, shapeCol 2 p.1.laz Cape.no)) =
  some (some (NeedOrd.pair NeedOrd.this NeedOrd.this), Option.none)

/-- **The top on the bare `%6`** as the SCC's nomm and as the code's nomm,
cape `|`: the hypotheses left are the state nouns and `ScRet` (the model's
`shapeCol` returns at `fuel` on the final pass). -/
example (fuel : Nat) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C Cape.no.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C Cape.no.toNoun DATA) FOL) CALLS) (INL' : Noun)
    (hinl : InlOK (C (C Cape.no.toNoun DATA) FOL) CODE INL sixBare INL') (env : CallEnv)
    (hret : ScRet env sixBare Cape.no fuel)
    (FUNC V : Noun) (hgot : getF mugF FUNC CODE = some (C (A 0) V))
    (hv : slot? 2 V = some sixBare.toNoun) :=
  cu_gate_scc_one_six_sc fuel Cape.no DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hsmap hcalls _
    INL' hinl env rfl (by simp [sixBare, Bake.NoAx0]) hret (noBakeOneO_no env _ _ DATA) FUNC V sixBare rfl
    (by simp [sixBare, Bake.NoAx0]) hgot hv

end Compiler
end Formalization
