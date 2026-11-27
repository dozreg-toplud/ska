import lemmas.Compiler.CompShapeColNorm
import lemmas.Compiler.CompStraightRunIn

/-!
# The one-bell top with the real bake and no hypothesis on the bake

Written by `tools/gen/bakeany.py` (README Gaps 9).  `+to-straight` is
linked on every input need (`tsAny_holds`, `CompStraightRunIn.lean`: the
renaming path, the map path with proxies, and the map path with `run` `|`
through the state `[re-gen m]`).  So the chain of `CompSccSixBake.lean` from
`fin_gate_ts_B` to `cu_gate_scc_one_six_q_B` holds with `TsAny` in place of
`TsOn Q` and without the residual of `+bake-need` being a run (`BakeRunO`):
each theorem is copied as `<name>_any` with the hypothesis `hrun` (and
`hbake`) dropped.  The top **`cu_gate_scc_one_six_bake_all`** assumes the
state nouns, `SixOk`, `NoSelfCall` and `NoAx0` (`FolMade` in `_fol_all`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- `TsAny` gives `TsOn Q` for every `Q`. -/
theorem tsOn_of_any (Q : TreapMap mugF (Nat × List Nat) → Prop) (h : TsAny) : TsOn Q :=
  fun ctx h7 g x o ned _ _ => h ctx h7 g x o ned

theorem fin_gate_ts_B_any (Q : TreapMap mugF (Nat × List Nat) → Prop) (hT : TsAny) {ctx : Noun}
    (h7 : slot? 7 ctx = some compK) (c2 c6 c14 NEWN SUR REST G0 : Noun)
    (less : Cape) (hcomp : slot? 6 REST = some (C comp.door (C G0 ctx))) (hdone : slot? 14 REST = some (A 0))
    (hless : slot? 496 REST = some less.toNoun) (hl2 : slot? 0x3ffffff REST = some layer2)
    (g : Gen (TreapMap mugF)) (x : GenRest) (hs0 : x.soft = A 0) (hQ : Q g.cond)
    (nedF : Need) (know : Sock)
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
  generalize bakeNeed nedF know = bak
  obtain ⟨nedB, imm⟩ := bak
  try simp only
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
      have hts := hT ctx h7 g4 x o nedB
      simp only [compCore, Option.map_some, tsSampleN] at hcz hsd hao hts
      conv => { lhs; arg 2; unfold finBody }
      simp only [finCtx, Option.bind_some]
      generalize comp.door = Dr at hcz hczat hsdat haoat htsat hcomp hsd hao hts
      generalize sdArm = SD at hsdat hsd
      simp [nock_exec, hcomp, hdone, hless, hl2, hczat, comp_cz_arm, hcz, hsdat, hsd, haoat, comp_add_ops_arm,
        turn.arm_at, turn_arm, fin_turn_imm, hao, htsat, comp_ts_arm, hts, e2]
      all_goals exact hts


theorem fin_gate_finishLF_six_B_any (Q : TreapMap mugF (Nat × List Nat) → Prop) (hT : TsAny) {ctx : Noun}
    (env : CallEnv) (h7 : slot? 7 ctx = some compK) (c2 c6 c14 NEWN SUR REST G0 : Noun)
    (less : Cape) (hcomp : slot? 6 REST = some (C comp.door (C G0 ctx))) (hdone : slot? 14 REST = some (A 0))
    (hless : slot? 496 REST = some less.toNoun) (hl2 : slot? 0x3ffffff REST = some layer2)
    (x : GenRest) (hs0 : x.soft = A 0)
    (nm : Nomm) (ord : NeedOrd) (nex : NextL CSet) (g1 g2 : Gen (TreapMap mugF)) (nedF : Need) (know : Sock)
    (hrunL : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))
    (hargs : nex.th.args = [])
    (hQ : Q g1.cond)
    (hnoar : needOrdAllocRegs ord g1 = some (nedF, g2)) :
    nock (C finBody (C (A 0) (finCtx c2 c6 c14 NEWN nex.laz.toNoun nedF.toNoun (bakeNeed nedF know).1.toNoun
        (immNoun (bakeNeed nedF know).2) nex.th.there SUR (genNoun g2 x) REST))) finBody
      = (finishLFC (S := CSet) (Map := TreapMap mugF) env nm ord less (fun n => bakeNeed n know)).map
          Straight.toNoun := by
  have kc2 := (kc_needOrdAllocRegs (Map := TreapMap mugF) ord).keep g1 nedF g2 hnoar
  rw [finishLFC_tail, hrunL]
  simp only [Option.bind_some, hargs, ne_eq, not_true_eq_false, if_false, hnoar]
  exact fin_gate_ts_B_any Q hT h7 c2 c6 c14 NEWN SUR REST G0 less hcomp hdone hless hl2 g2 x hs0
    (by rw [kc2]; exact hQ) nedF know nex.th.there nex.laz


theorem mem_gate_six_B_any (Q : TreapMap mugF (Nat × List Nat) → Prop) (hT : TsAny) (cape : Cape) (DATA FOL : Noun)
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
  have hf := fin_gate_finishLF_six_B_any Q hT env
    (rfl : slot? 7 (memDCtx SCC (C CODE LSR) JH (A 0) (A 0) (C (C cape.toNoun DATA) FOL)) = some compK)
    (memMovedN keep WAS sur.toNoun) (memSurKN keep WAS sur.toNoun) WAS
    (needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1).toNoun
    sur.toNoun _ cuBunt cape hs6 hs14 hs496 hl2 (cuRest (cacheN C1 C2 C3 C4 SURE)) rfl nm ord nex g1 g2
    nedF (Sock.mk cape DATA) hrunL hargs hQ hnoar
  rw [hf, Option.map_map]
  rfl


theorem csi_gate_scc_one_m_six_B_any (Q : TreapMap mugF (Nat × List Nat) → Prop) (hT : TsAny) (cape : Cape)
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
  have hm := mem_gate_six_B_any Q hT cape DATA FOL false (C NARY (C MONO (C SCCS (C INL SURE)))) (A 0)
    (kidsOne (C (C cape.toNoun DATA) FOL)) (A 0) csiBody (setOne (C (C cape.toNoun DATA) FOL)) CODE (C JETS CALLS) JH
    (C NARY (C MONO (C SCCS (C INL SURE)))) nm NARY MONO SCCS INL' SURE hi env hn ha nex g1 hrunL hQ
    ord hsc hargs nedF g2 hnoar (sccSur nex cape) hsur WAS SURE' hwas hw hput'
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


theorem csi_gate_scc_one_f_six_B_any (Q : TreapMap mugF (Nat × List Nat) → Prop) (hT : TsAny) (cape : Cape)
    (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (env : CallEnv) (hn : SixOk nm = true) (hax : Bake.NoAx0 nm)
    (ordOf : NextL CSet → NeedOrd) (hsc : ScAt env nm ordOf cape)
    (hQ : ∀ nex g1, runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))
      = some (nex, g1) → Q g1.cond) :
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
        rw [csi_gate_scc_one_m_six_B_any Q hT cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hcalls
          nm INL' hinl env hn hax nex g1 hr (hQ nex g1 hr) ha (ordOf nex) (hsc nex g1 hr) nedF g2 hno SURE' hp]
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


theorem cu_gate_scc_one_six_q_B_any (Q : TreapMap mugF (Nat × List Nat) → Prop) (hT : TsAny) (cape : Cape)
    (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (env : CallEnv) (hn : SixOk nm = true) (hax : Bake.NoAx0 nm)
    (ordOf : NextL CSet → NeedOrd) (hsc : ScAt env nm ordOf cape)
    (hQ1 : ∀ nex g1, runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))
      = some (nex, g1) → Q g1.cond)
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
  have hcsi := csi_gate_scc_one_f_six_B_any Q hT cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap
    hsmap hcalls nm INL' hinl env hn hax ordOf hsc hQ1
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
      exact cu_gate_six Q (tsOn_of_any Q hT) FUNC _ CODE (C JETS CALLS) JH _ _ _ V env n hn' hax' hQ2 hcsi hgot hv


/-- **The one-bell top on `SixOk` with the real bake**, nothing assumed on
`+shape-collapse`, on the bake or on `+to-straight`: the n-ary entry is
`finishLFB env nm (scOrdR p.1 cape) (Sock.mk cape DATA)`. -/
theorem cu_gate_scc_one_six_bake_all (cape : Cape) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (env : CallEnv) (hn : SixOk nm = true) (hax : Bake.NoAx0 nm)
    (FUNC V : Noun) (n : Nomm) (hn' : SixOk n = true) (hax' : Bake.NoAx0 n)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    nock (C cuGB (C (cuSam FUNC (setOne (C (C cape.toNoun DATA) FOL)) CODE (C JETS CALLS) JH
        (cacheN NARY MONO SCCS INL SURE)) compK)) cuGB
      = (runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))).bind fun p =>
          (finishLFB (S := CSet) (Map := TreapMap mugF) env nm (scOrdR p.1 cape) (Sock.mk cape DATA)).bind fun st =>
            (putF mugF (C (C cape.toNoun DATA) FOL) st.toNoun NARY).bind fun NARYU =>
              (putF mugF (C (C cape.toNoun DATA) FOL) (sccSur p.1 cape).toNoun SURE).bind fun SURE' =>
                (finishLUC (S := CSet) (Map := TreapMap mugF) env n).map fun st' =>
                  C (C st'.toNoun (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))))
                    (cacheN NARYU MONO SCCS INL' SURE') :=
  cu_gate_scc_one_six_q_B_any (fun _ => True) tsAny_holds cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE
    hnary hnmap hsmap hcalls nm INL' hinl env hn hax (fun nex => scOrdR nex cape)
    (scAt_R env hn hax cape (normRun_six env hn)) (fun _ _ _ => trivial) FUNC V n hn' hax'
    (fun _ _ _ _ _ _ => trivial) hgot hv

/-- `cu_gate_scc_one_six_bake_all` on the nomms that `+fol-loop` makes
(`FolMade`). -/
theorem cu_gate_scc_one_six_bake_fol_all (cape : Cape)
    (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (env : CallEnv) (hn : SixOk nm = true) (hf : FolMade nm)
    (FUNC V : Noun) (n : Nomm) (hn' : SixOk n = true) (hf' : FolMade n)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    nock (C cuGB (C (cuSam FUNC (setOne (C (C cape.toNoun DATA) FOL)) CODE (C JETS CALLS) JH
        (cacheN NARY MONO SCCS INL SURE)) compK)) cuGB
      = (runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))).bind fun p =>
          (finishLFB (S := CSet) (Map := TreapMap mugF) env nm (scOrdR p.1 cape) (Sock.mk cape DATA)).bind fun st =>
            (putF mugF (C (C cape.toNoun DATA) FOL) st.toNoun NARY).bind fun NARYU =>
              (putF mugF (C (C cape.toNoun DATA) FOL) (sccSur p.1 cape).toNoun SURE).bind fun SURE' =>
                (finishLUC (S := CSet) (Map := TreapMap mugF) env n).map fun st' =>
                  C (C st'.toNoun (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))))
                    (cacheN NARYU MONO SCCS INL' SURE') :=
  cu_gate_scc_one_six_bake_all cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hsmap hcalls nm
    INL' hinl env hn (folMade_noAx0 hf) FUNC V n hn' (folMade_noAx0 hf') hgot hv

/-- `%m01` of `tools/hoon/bakedump.hoon`: `[[0 2] [0 6] [0 7]]` on the bell
`[[| [& |]] [0 7 0]]` (the middle of the subject known, `7`). -/
def m01Nomm : Nomm := Nomm.cons (Nomm.n0 2) (Nomm.cons (Nomm.n0 6) (Nomm.n0 7))

/-- The cape `[| [& |]]`. -/
def capeM01 : Cape := Cape.cell Cape.no (Cape.cell Cape.yes Cape.no)

/- The model's final pass of `m01Nomm` (over `LS`, `FM`, in the environment
of the dumps): the `ord` is `[%this [%this %this]]`, the registers `[5 6 7]`;
`+bake-need` bakes the middle one and leaves `[5 7]`, not a run, so
`+to-straight` takes the map path with `run` `|` (`tsr_at`). -/
#guard ((runLC (S := LS) (Map := FM) envR Option.none m01Nomm (CGoalL.done : CGoalL LS) [] gen0).bind fun p =>
    (shapeCol 64 p.1.laz capeM01).bind fun ord => (needOrdAllocRegs ord p.2).map fun q =>
      let b := bakeNeed q.1 (Sock.mk capeM01 (C (A 0) (C (A 7) (A 0))))
      (ord, b.2.length, flattenNeed q.1, flattenNeed b.1, isRun (flattenNeed b.1) ((flattenNeed b.1).headD 0) 0))
  = some (NeedOrd.pair NeedOrd.this (NeedOrd.pair NeedOrd.this NeedOrd.this), 1, [5, 6, 7], [5, 7], false)

/- The n-ary entry of the model with the bake succeeds there with two
arguments. -/
#guard ((runLC (S := LS) (Map := FM) envR Option.none m01Nomm (CGoalL.done : CGoalL LS) [] gen0).bind fun p =>
    (finishLFB (S := LS) (Map := FM) envR m01Nomm ((shapeCol 64 p.1.laz capeM01).getD NeedOrd.none)
      (Sock.mk capeM01 (C (A 0) (C (A 7) (A 0))))).map fun st => st.nargs) = some 2

/-- **The top with the real bake on `%m01`** (a known middle, whose residual
is not a run): `m01Nomm` as the SCC's nomm and as the code's nomm, with no
hypothesis but the state nouns. -/
example (FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C capeM01.toNoun (C (A 0) (C (A 7) (A 0)))) FOL) NARY = some (A 0))
    (hnmap : IsMap mugF NARY) (hsmap : IsMap mugF SURE)
    (hcalls : NoSelfCall (C (C capeM01.toNoun (C (A 0) (C (A 7) (A 0)))) FOL) CALLS) (INL' : Noun)
    (hinl : InlOK (C (C capeM01.toNoun (C (A 0) (C (A 7) (A 0)))) FOL) CODE INL m01Nomm INL') (env : CallEnv)
    (FUNC V : Noun) (hgot : getF mugF FUNC CODE = some (C (A 0) V))
    (hv : slot? 2 V = some m01Nomm.toNoun) :=
  cu_gate_scc_one_six_bake_all capeM01 (C (A 0) (C (A 7) (A 0))) FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE
    hnary hnmap hsmap hcalls _ INL' hinl env rfl (by simp [m01Nomm, Bake.NoAx0]) FUNC V m01Nomm rfl
    (by simp [m01Nomm, Bake.NoAx0]) hgot hv

end Compiler
end Formalization
