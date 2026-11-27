import lemmas.Compiler.CompSccCallGate
import lemmas.Compiler.CompRunAllSix
import lemmas.Compiler.CompKernGen
import lemmas.Compiler.CompStraightN
import lemmas.Ska.DatFacts

/-!
# The gate of `+compile-unary` on an SCC of one bell, on the class with `%6`

The chain of `CompSccCallGate.lean` (`cu_gate_scc_one_f_c`, on `indOk`)
restated on `SixOk` (the plain class with `%6`) with `Bake.NoAx0`.  What the
old chain read of `indOk` (README Gaps 9) and what takes its place here:

1. the run at the entry (`comp_run_entry_c`): `comp_run_entry_six`, from
   `comp_run_all_l6`;
2. `+inlined` is the identity (`inl_gate_ind`): `indPure_of_sixOk`;
3. `args.then` empty (`args_frag_c`): not needed, the final pass splits on
   it and both sides crash;
4. a fork-free result of the final pass (`scc_sur_frag_c`, for
   `+shape-collapse` and `+coerce-lazy`): a named hypothesis, `FinSure`.
   It is false on `SixOk` in general (a `%6` under `%done` leaves a fork
   in the result), and `+shape-collapse` on forks has no model.  `+sure-of`
   succeeds by `GRes` (`scc_sur_six`).  `FinSure` holds of `[7 [1 k] c]`
   for every `c` (`finSure_n7_n1`);
5. `cond` empty at `+to-straight` (`mem_cond_frag_c`, `crx_run`): the
   named hypothesis `TsOn Q` with `Q` of the `cond` that the passes reach.
   `TsMapAt` (`Q` true: `+to-straight` on every `cond`, the map branch
   that track I is proving) closes it with no hypothesis on the run;
   `TsOn` of an empty `cond` is proved (`tsOn_empty`, by `tsn_at`);
6. `+kerf` of the unary pass on a fork-free result (`comp_kerf`):
   `comp_kerf_all`.

`Bake.NoAx0` of the two nomms comes from `+fol-loop` (`folLoop_noAx0`):
`FolMade` (`cu_gate_scc_one_six_fol`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun}

/-! ## The named hypotheses -/

/-- **`+to-straight` on the sample `[%next [[ned ~] ~ ~] ~ o]`** of a final
pass, on every state whose `cond` meets `Q`: the noun of `toStraightF`. -/
def TsOn (Q : TreapMap mugF (Nat × List Nat) → Prop) : Prop :=
  ∀ (ctx : Noun), slot? 7 ctx = some compK → ∀ (g : Gen (TreapMap mugF)) (x : GenRest) (o : Nat) (ned : Need),
    Q g.cond → isRun (flattenNeed ned) ((flattenNeed ned).headD 0) 0 = true →
    nock (C tsBat (C (tsSampleN (A o) ned.toNoun) (compCore g x ctx))) tsBat
      = (toStraightF g.cond g.blocks ned o).map Straight.toNoun

/-- **The map branch of `+to-straight`** (README Gaps 9, track I):
`tsn_at` on every `cond`, the one hypothesis of `cu_gate_scc_one_six`
that is not on the state nouns or the run. -/
def TsMapAt : Prop := TsOn fun _ => True

/-- On an empty `cond` the renaming branch is linked (`tsn_at`). -/
theorem tsOn_empty : TsOn fun c => ∀ k, HoonMap.get c k = Option.none :=
  fun _ h7 g x o ned hq hrun => tsn_at h7 g x o ned hq hrun

/-- **The final pass of `nm` returns a fork-free `laz`.** -/
def FinSure (env : CallEnv) (nm : Nomm) : Prop :=
  ∀ nex g1, runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1) →
    nex.laz = Lazy.ofSure nex.laz.sure

/-- `[7 [1 k] c]` returns `[*sure ~ ~]` on every goal, so its final pass is
fork-free for every `c`. -/
theorem finSure_n7_n1 (env : CallEnv) (k : Noun) (c : Nomm) : FinSure env (Nomm.n7 (Nomm.n1 k) c) := by
  intro nex g1 h
  simp only [runLC] at h
  obtain ⟨n1, g2, -, h⟩ := bind_some h
  simp only [NextL.goal] at h
  obtain ⟨o, g3, -, h⟩ := bind_some h
  simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

/-! ## The facts of the class -/

theorem indPure_of_sixOk : ∀ (n : Nomm), SixOk n = true → indPure n = true
  | Nomm.cons p q, h => by
    simp only [SixOk, Bool.and_eq_true] at h
    simp only [indPure, Bool.and_eq_true]; exact ⟨indPure_of_sixOk p h.1, indPure_of_sixOk q h.2⟩
  | Nomm.n0 _, _ => rfl
  | Nomm.n1 _, _ => rfl
  | Nomm.n2 p q Option.none, h => by
    simp only [SixOk, Bool.and_eq_true] at h
    simp only [indPure, Bool.and_eq_true]; exact ⟨indPure_of_sixOk p h.1, indPure_of_sixOk q h.2⟩
  | Nomm.n3 p, h => by simp only [SixOk] at h; simp only [indPure]; exact indPure_of_sixOk p h
  | Nomm.n4 p, h => by simp only [SixOk] at h; simp only [indPure]; exact indPure_of_sixOk p h
  | Nomm.n5 p q, h => by
    simp only [SixOk, Bool.and_eq_true] at h
    simp only [indPure, Bool.and_eq_true]; exact ⟨indPure_of_sixOk p h.1, indPure_of_sixOk q h.2⟩
  | Nomm.n6 p q r, h => by
    simp only [SixOk, Bool.and_eq_true] at h
    simp only [indPure, Bool.and_eq_true]
    exact ⟨⟨indPure_of_sixOk p h.1.1, indPure_of_sixOk q h.1.2⟩, indPure_of_sixOk r h.2⟩
  | Nomm.n7 p q, h => by
    simp only [SixOk, Bool.and_eq_true] at h
    simp only [indPure, Bool.and_eq_true]; exact ⟨indPure_of_sixOk p h.1, indPure_of_sixOk q h.2⟩
  | Nomm.n10 a v q, h => by
    simp only [SixOk, Bool.and_eq_true] at h
    simp only [indPure, Bool.and_eq_true]; exact ⟨indPure_of_sixOk v h.1.2, indPure_of_sixOk q h.2⟩
  | Nomm.n2 _ _ (some _), h => by simp [SixOk] at h
  | Nomm.n11s _ _ _, h => by simp [SixOk] at h
  | Nomm.n11d _ _ _ _, h => by simp [SixOk] at h
  | Nomm.n12 _ _, h => by simp [SixOk] at h
  | Nomm.mean _ _ _ _ _, h => by simp [SixOk] at h

/-- **`+run` at the entry of `+comp` on the class with `%6`.** -/
theorem comp_run_entry_six (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (n : Nomm) (hn : SixOk n = true) (ha : Bake.NoAx0 n) :
    CompRunAtC env ctx n (CGoal.toL CGoal.done) [] genEntry :=
  fun msup => comp_run_all_l6 h7 hcode env n hn ha msup [] CGoalL.done genEntry rfl

theorem lall_root {Q : Sure CSet → Prop} {laz : Lazy CSet} (h : LAll Q laz) : Q laz.sure := by
  obtain ⟨s, fk, bd⟩ := laz
  exact h.1

/-- What the run at the entry returns: no look at `0` anywhere in its `laz`. -/
theorem entry_lok (env : CallEnv) {n : Nomm} (hn : SixOk n = true) (ha : Bake.NoAx0 n) {nex : NextL CSet}
    {g1 : Gen (TreapMap mugF)}
    (hrun : runLC env Option.none n (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1)) :
    LAll CrLok nex.laz := by
  obtain ⟨-, -, hG, -⟩ := res_all6 env n hn ha Option.none [] CGoalL.done gen0 g1 nex rfl hrun
  simp only [NextL.goal, GInv] at hG
  exact lall_mono (fun s h => h.1) hG.1.1

/-- `+sure-of` of the result succeeds and is `sccSur`, given `FinSure`. -/
theorem scc_sur_six (env : CallEnv) {nm : Nomm} (hn : SixOk nm = true) (ha : Bake.NoAx0 nm) (hfs : FinSure env nm)
    {nex : NextL CSet} {g1 : Gen (TreapMap mugF)}
    (hrun : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))
    (cape : Cape) :
    nex.laz = Lazy.ofSure nex.laz.sure ∧
      sureOf (needToOrd nex.laz.sure.ned) nex.laz.sure.lok cape = some (sccSur nex cape) := by
  have hr : CrLok nex.laz.sure := lall_root (entry_lok env hn ha hrun)
  obtain ⟨r, hr'⟩ := sureOf_some cape nex.laz.sure.lok hr (needToOrd nex.laz.sure.ned)
  refine ⟨hfs nex g1 hrun, ?_⟩
  simp only [sccSur, hr']
  rfl

/-! ## The final pass of `+compile-scc-in` (copied from `CompFinish.lean` and `CompSccCallGate.lean`, with `TsOn Q` for `cond` empty and `comp_run_entry_six`) -/

theorem fin_gate_ts (Q : TreapMap mugF (Nat × List Nat) → Prop) (hT : TsOn Q) {ctx : Noun} (h7 : slot? 7 ctx = some compK) (c2 c6 c14 NEWN SUR REST G0 : Noun)
    (less : Cape) (hcomp : slot? 6 REST = some (C comp.door (C G0 ctx))) (hdone : slot? 14 REST = some (A 0))
    (hless : slot? 496 REST = some less.toNoun) (hl2 : slot? 0x3ffffff REST = some layer2)
    (g : Gen (TreapMap mugF)) (x : GenRest) (hs0 : x.soft = A 0) (hQ : Q g.cond)
    (nedF : Need) (hrun : isRun (flattenNeed nedF) ((flattenNeed nedF).headD 0) 0 = true)
    (o : Nat) (s : Sure CSet) :
    nock (C finBody (C (A 0) (finCtx c2 c6 c14 NEWN (Lazy.ofSure s).toNoun nedF.toNoun nedF.toNoun (A 0) o SUR
        (genNoun g x) REST))) finBody
      = (finTail nedF less o (Lazy.ofSure s) (fun n => (n, [])) g).map Straight.toNoun := by
  have hc := (comp_ctx_pill ctx h7).1
  have hcz := cz_gate_L h7 x o (fin_softOut x hs0 o) nedF s less g
  have hczat := comp_cz_at
  have hsdat := sd_at
  have haoat := comp_add_ops_at
  have htsat := comp_ts_at
  unfold finTail
  simp only [List.map_nil]
  cases e1 : coerceLazyL nedF less o (Lazy.ofSure s) g with
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
    have kc3 := (kc_coerceLazyL nedF less o (Lazy.ofSure s)).keep g u1 g3 e1
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

theorem fin_gate_finishLF_six (Q : TreapMap mugF (Nat × List Nat) → Prop) (hT : TsOn Q) {ctx : Noun} (env : CallEnv) (h7 : slot? 7 ctx = some compK) (c2 c6 c14 NEWN SUR REST G0 : Noun)
    (less : Cape) (hcomp : slot? 6 REST = some (C comp.door (C G0 ctx))) (hdone : slot? 14 REST = some (A 0))
    (hless : slot? 496 REST = some less.toNoun) (hl2 : slot? 0x3ffffff REST = some layer2)
    (x : GenRest) (hs0 : x.soft = A 0)
    (nm : Nomm) (ord : NeedOrd) (nex : NextL CSet) (g1 g2 : Gen (TreapMap mugF)) (nedF : Need) (s : Sure CSet)
    (hrunL : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))
    (hargs : nex.th.args = []) (hlaz : nex.laz = Lazy.ofSure s)
    (hQ : Q g1.cond)
    (hnoar : needOrdAllocRegs ord g1 = some (nedF, g2)) :
    nock (C finBody (C (A 0) (finCtx c2 c6 c14 NEWN nex.laz.toNoun nedF.toNoun nedF.toNoun (A 0) nex.th.there SUR
        (genNoun g2 x) REST))) finBody
      = (finishLFC (S := CSet) (Map := TreapMap mugF) env nm ord less (fun n => (n, []))).map Straight.toNoun := by
  have kc2 := (kc_needOrdAllocRegs (Map := TreapMap mugF) ord).keep g1 nedF g2 hnoar
  have hrun := isRun_needOrdAllocRegs hnoar
  rw [finishLFC_tail, hrunL]
  simp only [Option.bind_some, hargs, ne_eq, not_true_eq_false, if_false, hnoar]
  rw [hlaz]
  exact fin_gate_ts Q hT h7 c2 c6 c14 NEWN SUR REST G0 less hcomp hdone hless hl2 g2 x hs0
    (by rw [kc2]; exact hQ) nedF hrun nex.th.there s


theorem mem_to_finish_six (cape : Cape) (DATA FOL : Noun) (keep : Bool)
    (ML TOP CACHE DN KIDS ML0 CB SCC CODE LSR JH CACHE0 : Noun)
    (nm : Nomm) (C1 C2 C3 C4 SURE : Noun)
    (hinl : nock (C inlBody (C (C (C (C cape.toNoun DATA) FOL) (C (C CODE LSR) (C JH CACHE))) compK)) inlBody
      = some (C nm.toNoun (cacheN C1 C2 C3 C4 SURE)))
    (env : CallEnv) (hn : SixOk nm = true) (ha : Bake.NoAx0 nm)
    (nex : NextL CSet) (g1 : Gen (TreapMap mugF))
    (hrunL : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))
    (s : Sure CSet) (hlaz : nex.laz = Lazy.ofSure s)
    (ord : NeedOrd) (hsc : nock (C scBody (C (C nex.laz.toNoun cape.toNoun) compK)) scBody = some ord.toNoun)
    (hargs : nex.th.args = []) (nedF : Need) (g2 : Gen (TreapMap mugF))
    (hnoar : needOrdAllocRegs ord g1 = some (nedF, g2))
    (hb : NoBake nedF (Sock.mk cape DATA))
    (sur : NeedOrd) (hsur : sureOf (needToOrd s.ned) s.lok cape = some sur)
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
  have hlz : nex.laz.toNoun = C (C s.ned.toNoun (HoonSet.toNoun s.lok)) (C (A 0) (A 0)) := by
    rw [hlaz, Lazy.toNoun_ofSure]; rfl
  rw [hlz] at hcsN
  -- the calls of K
  have hbn := fin_bak ord g1 g2 nedF (Sock.mk cape DATA) hnoar hb
  simp only [Sock.toNoun] at hbn
  have hn1 := nta_gate compK s.ned
  have hso := so_gate (needToOrd s.ned) s.lok cape
  rw [hsur, Option.map_some] at hso
  have hn2 := nta_gate compK nedF
  rw [mem_final (hmode := mem_mode_noop _ _) (hrun := hrunN) (hcs := hcsN) (hbn := hbn) (hn1 := hn1) (hso := hso)
    (hn2 := hn2)]
  simp only [Option.bind_some]
  rw [mem_after (keep := keep) (hG2 := cu_gen_cache _ _) (hwas := hwas) (hw := hw) (hput := hput)]
  rw [hlz]
  rfl


theorem mem_gate_six (Q : TreapMap mugF (Nat × List Nat) → Prop) (hT : TsOn Q)  (cape : Cape) (DATA FOL : Noun) (keep : Bool)
    (CACHE DN KIDS ML0 CB SCC CODE LSR JH CACHE0 : Noun)
    (nm : Nomm) (C1 C2 C3 C4 SURE : Noun)
    (hinl : nock (C inlBody (C (C (C (C cape.toNoun DATA) FOL) (C (C CODE LSR) (C JH CACHE))) compK)) inlBody
      = some (C nm.toNoun (cacheN C1 C2 C3 C4 SURE)))
    (env : CallEnv) (hn : SixOk nm = true) (ha : Bake.NoAx0 nm)
    (nex : NextL CSet) (g1 : Gen (TreapMap mugF))
    (hrunL : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))
    (hQ : Q g1.cond)
    (s : Sure CSet) (hlaz : nex.laz = Lazy.ofSure s)
    (ord : NeedOrd) (hsc : nock (C scBody (C (C nex.laz.toNoun cape.toNoun) compK)) scBody = some ord.toNoun)
    (hargs : nex.th.args = []) (nedF : Need) (g2 : Gen (TreapMap mugF))
    (hnoar : needOrdAllocRegs ord g1 = some (nedF, g2))
    (hb : NoBake nedF (Sock.mk cape DATA))
    (sur : NeedOrd) (hsur : sureOf (needToOrd s.ned) s.lok cape = some sur)
    (WAS SURE' : Noun) (hwas : getF mugF (C (C cape.toNoun DATA) FOL) SURE = some WAS)
    (hw : WAS = A 0 ∨ ∃ u, WAS = C (A 0) u)
    (hput : putF mugF (C (C cape.toNoun DATA) FOL) (memSurKN keep WAS sur.toNoun) SURE = some SURE') :
    nock (C memBody (C (memSam (C (C cape.toNoun DATA) FOL) (A 0x656e6f64) (loob keep) (A 0) (A 0) CACHE)
        (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0))) memBody
      = (finishLFC (S := CSet) (Map := TreapMap mugF) env nm ord cape (fun n => (n, []))).map fun st =>
          C (memChgN (memMovedN keep WAS sur.toNoun) (needToOrd nedF).toNoun)
            (C (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))) (cacheN C1 C2 C3 C4 SURE')) := by
  rw [mem_to_finish_six cape DATA FOL keep (A 0) (A 0) CACHE DN KIDS ML0 CB SCC CODE LSR JH CACHE0 nm C1 C2 C3 C4 SURE
    hinl env hn ha nex g1 hrunL s hlaz ord hsc hargs nedF g2 hnoar hb sur hsur WAS SURE' hwas hw hput]
  have hmv : memMovedN keep WAS sur.toNoun = A 0 ∨ memMovedN keep WAS sur.toNoun = A 1 := by
    unfold memMovedN; split <;> simp
  have hnn : ∃ p q, (needToOrd nedF).toNoun = C p q := nord_cell _
  unfold memFC
  rw [mem_prod_new (hmv := hmv) (hnn := hnn)]
  obtain ⟨hs6, hs14, hs496, hl2⟩ := mem_rest_slots nm.toNoun SCC (C CODE LSR) JH (A 0) (A 0) cape.toNoun DATA FOL
    (loob keep) (cacheN C1 C2 C3 C4 SURE') DN KIDS ML0 CB CACHE0
  have hf := fin_gate_finishLF_six Q hT env (rfl : slot? 7 (memDCtx SCC (C CODE LSR) JH (A 0) (A 0) (C (C cape.toNoun DATA) FOL))
      = some compK) (memMovedN keep WAS sur.toNoun) (memSurKN keep WAS sur.toNoun) WAS (needToOrd nedF).toNoun
    sur.toNoun _ cuBunt cape hs6 hs14 hs496 hl2 (cuRest (cacheN C1 C2 C3 C4 SURE)) rfl nm ord nex g1 g2
    nedF s hrunL hargs hlaz hQ hnoar
  rw [hf, Option.map_map]
  rfl


theorem csi_gate_scc_one_m_six (Q : TreapMap mugF (Nat × List Nat) → Prop) (hT : TsOn Q)  (cape : Cape) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (env : CallEnv) (hn : SixOk nm = true) (ha : Bake.NoAx0 nm) (hfs : FinSure env nm)
    (nex : NextL CSet) (g1 : Gen (TreapMap mugF))
    (hrunL : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))
    (hQ : Q g1.cond) (hargs : nex.th.args = [])
    (nedF : Need) (g2 : Gen (TreapMap mugF))
    (hnoar : needOrdAllocRegs (sccSur nex cape) g1 = some (nedF, g2))
    (hb : NoBake nedF (Sock.mk cape DATA))
    (SURE' : Noun) (hput : putF mugF (C (C cape.toNoun DATA) FOL) (sccSur nex cape).toNoun SURE = some SURE') :
    nock (C csiBody (C (csiSam (setOne (C (C cape.toNoun DATA) FOL)) (C CODE (C JETS CALLS)) JH
        (cacheN NARY MONO SCCS INL SURE)) compK)) csiBody
      = (finishLFC (S := CSet) (Map := TreapMap mugF) env nm (sccSur nex cape) cape (fun n => (n, []))).bind fun st =>
          (putF mugF (C (C cape.toNoun DATA) FOL) st.toNoun NARY).map fun NARYU =>
            C (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))) (cacheN NARYU MONO SCCS INL' SURE') := by
  have hcache : cacheN NARY MONO SCCS INL SURE = C NARY (C MONO (C SCCS (C INL SURE))) := rfl
  rw [hcache, csi_to_final _ _ _ _ _ _ hnary (csi_kids_noself _ CODE JETS CALLS JH _ hcalls) (ju_has_kids _)]
  obtain ⟨hlz, hsur⟩ := scc_sur_six env hn ha hfs hrunL cape
  have hsc := hsc_of_sure nex nex.laz.sure hlz cape (sccSur nex cape) hsur
  have hi := inl_gate_ind (C (C cape.toNoun DATA) FOL) CODE (C JETS CALLS) JH NARY MONO SCCS INL SURE INL' nm (indPure_of_sixOk nm hn) hinl
  obtain ⟨WAS, hwas, hw⟩ := getF_of_putF _ _ SURE hput
  have hput' : putF mugF (C (C cape.toNoun DATA) FOL) (memSurKN false WAS (sccSur nex cape).toNoun) SURE
      = some SURE' := by simpa [memSurKN] using hput
  have hm := mem_gate_six Q hT cape DATA FOL false (C NARY (C MONO (C SCCS (C INL SURE)))) (A 0)
    (kidsOne (C (C cape.toNoun DATA) FOL)) (A 0) csiBody (setOne (C (C cape.toNoun DATA) FOL)) CODE (C JETS CALLS) JH
    (C NARY (C MONO (C SCCS (C INL SURE)))) nm NARY MONO SCCS INL' SURE hi env hn ha nex g1 hrunL hQ nex.laz.sure hlz
    (sccSur nex cape) hsc hargs nedF g2 hnoar hb (sccSur nex cape) hsur WAS SURE' hwas hw hput'
  cases e : finishLFC (S := CSet) (Map := TreapMap mugF) env nm (sccSur nex cape) cape (fun n => (n, [])) with
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


theorem mem_gate_none_six (cape : Cape) (DATA FOL : Noun) (keep : Bool)
    (ML TOP CACHE DN KIDS ML0 CB SCC CODE LSR JH CACHE0 : Noun) (nm : Nomm) (CA : Noun)
    (hinl : nock (C inlBody (C (C (C (C cape.toNoun DATA) FOL) (C (C CODE LSR) (C JH CACHE))) compK)) inlBody
      = some (C nm.toNoun CA))
    (env : CallEnv) (hn : SixOk nm = true) (ha : Bake.NoAx0 nm) (hfs : FinSure env nm)
    (hcrash : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = none ∨
      ∃ nex g1, runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1) ∧
        (nex.th.args ≠ [] ∨ needOrdAllocRegs (sccSur nex cape) g1 = none)) :
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
    obtain ⟨hlz, hsur⟩ := scc_sur_six env hn ha hfs hr cape
    have hsc := hsc_of_sure nex nex.laz.sure hlz cape (sccSur nex cape) hsur
    have hcsN := cs_gate _ h7 (cuRest CA) g1 nex cape.toNoun (sccSur nex cape) hsc
    have hnone : (if nex.th.args ≠ [] then Option.none else
        (needOrdAllocRegs (sccSur nex cape) g1).map fun p =>
          C (C p.1.toNoun (C nex.laz.toNoun (A nex.th.there))) (genNoun p.2 (cuRest CA))) = Option.none := by
      rcases hc with ha | hn
      · simp [ha]
      · simp [hn]
    rw [hnone] at hcsN
    simp only [compCore] at hcsN
    rw [mem_final_cs_none (hmode := mem_mode_noop _ _) (hrun := hrunN) (hcs := hcsN)]
    rfl


theorem csi_gate_scc_one_f_six (Q : TreapMap mugF (Nat × List Nat) → Prop) (hT : TsOn Q)  (cape : Cape) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (env : CallEnv) (hn : SixOk nm = true) (hax : Bake.NoAx0 nm) (hfs : FinSure env nm)
    (hQ : ∀ nex g1, runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1) →
      Q g1.cond)
    (hbake : NoBakeOneC env nm cape DATA) :
    nock (C csiBody (C (csiSam (setOne (C (C cape.toNoun DATA) FOL)) (C CODE (C JETS CALLS)) JH
        (cacheN NARY MONO SCCS INL SURE)) compK)) csiBody
      = (runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))).bind fun p =>
          (finishLFC (S := CSet) (Map := TreapMap mugF) env nm (sccSur p.1 cape) cape (fun n => (n, []))).bind fun st =>
            (putF mugF (C (C cape.toNoun DATA) FOL) st.toNoun NARY).bind fun NARYU =>
              (putF mugF (C (C cape.toNoun DATA) FOL) (sccSur p.1 cape).toNoun SURE).map fun SURE' =>
                C (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))) (cacheN NARYU MONO SCCS INL' SURE') := by
  have hi := inl_gate_ind (C (C cape.toNoun DATA) FOL) CODE (C JETS CALLS) JH NARY MONO SCCS INL SURE INL' nm (indPure_of_sixOk nm hn) hinl
  have hcrash : (runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = none ∨
      ∃ nex g1, runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1) ∧
        (nex.th.args ≠ [] ∨ needOrdAllocRegs (sccSur nex cape) g1 = none)) →
      nock (C csiBody (C (csiSam (setOne (C (C cape.toNoun DATA) FOL)) (C CODE (C JETS CALLS)) JH
        (cacheN NARY MONO SCCS INL SURE)) compK)) csiBody = none := by
    intro hc
    have hcache : cacheN NARY MONO SCCS INL SURE = C NARY (C MONO (C SCCS (C INL SURE))) := rfl
    rw [hcache, csi_to_final _ _ _ _ _ _ hnary (csi_kids_noself _ CODE JETS CALLS JH _ hcalls) (ju_has_kids _)]
    exact csi_final_one_none _ _ _ _ _ _ _ _ (mem_gate_none_six cape DATA FOL false (A 0) (A 0)
      (C NARY (C MONO (C SCCS (C INL SURE)))) (A 0) (kidsOne _) (A 0) csiBody _ CODE (C JETS CALLS) JH
      (C NARY (C MONO (C SCCS (C INL SURE)))) nm _ hi env hn hax hfs hc)
  cases hr : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) with
  | none => exact hcrash (Or.inl hr)
  | some p =>
    obtain ⟨nex, g1⟩ := p
    simp only [Option.bind_some]
    by_cases ha : nex.th.args = []
    · cases hno : needOrdAllocRegs (sccSur nex cape) g1 with
      | none =>
        have hf : finishLFC (S := CSet) (Map := TreapMap mugF) env nm (sccSur nex cape) cape (fun n => (n, []))
            = Option.none := by
          unfold finishLFC; simp [hr, ha, hno]
        rw [hf, hcrash (Or.inr ⟨nex, g1, hr, Or.inr hno⟩)]
        rfl
      | some q =>
        obtain ⟨nedF, g2⟩ := q
        obtain ⟨SURE', hp, -, -⟩ := putF_spec mugF SURE (C (C cape.toNoun DATA) FOL) (sccSur nex cape).toNoun hsmap
        rw [csi_gate_scc_one_m_six Q hT cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hcalls nm INL'
          hinl env hn hax hfs nex g1 hr (hQ nex g1 hr) ha nedF g2 hno (hbake nex g1 nedF g2 hr hno) SURE' hp]
        cases finishLFC (S := CSet) (Map := TreapMap mugF) env nm (sccSur nex cape) cape (fun n => (n, [])) with
        | none => rfl
        | some st =>
          obtain ⟨NARYU, hq, -, -⟩ := putF_spec mugF NARY (C (C cape.toNoun DATA) FOL) st.toNoun hnmap
          simp [hq, hp]
    · have hf : finishLFC (S := CSet) (Map := TreapMap mugF) env nm (sccSur nex cape) cape (fun n => (n, []))
          = Option.none := by
        unfold finishLFC; simp [hr, ha]
      rw [hf, hcrash (Or.inr ⟨nex, g1, hr, Or.inl ha⟩)]
      rfl

/-! ## The unary pass -/

/-- **The trap of `+compile-unary` on the class with `%6`**: as `cu_trap_c`,
with `+kerf` on every lazy need (`comp_kerf_all`) and `+to-straight` by
`TsOn Q` on the `cond` that `+kerf` leaves. -/
theorem cu_trap_six (Q : TreapMap mugF (Nat × List Nat) → Prop) (hT : TsOn Q)
    (FUNC SCC CODE LSR JH CACHE NM CA V : Noun) (env : CallEnv) (n : Nomm) (hn : SixOk n = true)
    (ha : Bake.NoAx0 n)
    (hQ : ∀ nex g1 q g2, runLC env Option.none n (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))
      = some (nex, g1) → kerf nex g1 = some (q, g2) → Q g2.cond)
    (hcsi : nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuCsi = some (C NM CA))
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuTrap
      = (finishLUC (S := CSet) (Map := TreapMap mugF) env n).map fun st => C (C st.toNoun NM) CA := by
  have h7 : slot? 7 (cuCtx FUNC SCC CODE LSR JH NM) = some compK := rfl
  have hcode : slot? 52 (cuCtx FUNC SCC CODE LSR JH NM) = some CODE := by simp [cuCtx, nock_exec]
  obtain ⟨hc, hl, hm⟩ := comp_ctx_pill _ h7
  rw [cu_trap_entry FUNC SCC CODE LSR JH CACHE NM CA hcsi,
    cu_trap_run FUNC SCC CODE LSR JH CACHE NM CA V n hgot hv,
    comp_run_entry_six h7 hcode env n hn ha Option.none (cuRest CA) (A 0) (A 0) (cu_entry_nosoft CA)]
  have hf : finishLUC (S := CSet) (Map := TreapMap mugF) env n
      = ((runLC env Option.none n (CGoal.toL (CGoal.done : CGoal CSet)) [] genEntry).bind fun p => kerf p.1 p.2).bind
          fun q => toStraightF q.2.cond q.2.blocks (Need.this q.1.2) q.1.1 := by
    rw [Option.bind_assoc]; rfl
  rw [hf]
  cases e : runLC (S := CSet) (Map := TreapMap mugF) env Option.none n (CGoal.toL (CGoal.done : CGoal CSet)) []
      genEntry with
  | none => simp
  | some p =>
    obtain ⟨nex, g1⟩ := p
    have hlok := entry_lok env hn ha (nex := nex) (g1 := g1) e
    have hk := comp_kerf_all hc hl hm (cuRest CA) g1 nex (walk_mdP (cu_entry_nosoft CA) g1.bo hlok)
    simp only [compCore] at hk
    simp only [Option.bind_some, Option.map_some, NextL.goal, CGoalL.toNoun]
    rw [cu_trap_kerf, hk]
    cases e2 : kerf nex g1 with
    | none => simp
    | some q =>
      obtain ⟨⟨o, sub⟩, g2⟩ := q
      have h : nock (C tsBat (C (tsSampleN (A o) (C (A 0x73696874) (A sub)))
            (C comp.door (C (genNoun g2 (cuRest CA)) (cuCtx FUNC SCC CODE LSR JH NM))))) tsBat
          = (toStraightF g2.cond g2.blocks (Need.this sub) o).map Straight.toNoun :=
        hT _ h7 g2 (cuRest CA) o (Need.this sub) (hQ nex g1 _ g2 e e2) (by simp [flattenNeed, isRun])
      simp only [Option.map_some, Option.bind_some]
      unfold cuS4
      rw [cu_trap_end, tsSample_eq, h, cu_gen_cache]
      cases toStraightF g2.cond g2.blocks (Need.this sub) o <;> rfl

/-- **The gate of `+compile-unary` on the class with `%6`**: `finishLUC env n`. -/
theorem cu_gate_six (Q : TreapMap mugF (Nat × List Nat) → Prop) (hT : TsOn Q)
    (FUNC SCC CODE LSR JH CACHE NM CA V : Noun) (env : CallEnv) (n : Nomm) (hn : SixOk n = true)
    (ha : Bake.NoAx0 n)
    (hQ : ∀ nex g1 q g2, runLC env Option.none n (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))
      = some (nex, g1) → kerf nex g1 = some (q, g2) → Q g2.cond)
    (hcsi : nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuCsi = some (C NM CA))
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    nock (C cuGB (C (cuSam FUNC SCC CODE LSR JH CACHE) compK)) cuGB
      = (finishLUC (S := CSet) (Map := TreapMap mugF) env n).map fun st => C (C st.toNoun NM) CA := by
  rw [cu_gate_rp, ← cu_trap_six Q hT FUNC SCC CODE LSR JH CACHE NM CA V env n hn ha hQ hcsi hgot hv]
  apply Option.ext
  intro y
  rw [cu_rp_iff]
  have hk : nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) rpK
      = nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuTrap := by
    unfold cuTC
    simp [rpK, nock_exec]
  rw [hk]

/-! ## The top -/

theorem cu_gate_scc_one_six_q (Q : TreapMap mugF (Nat × List Nat) → Prop) (hT : TsOn Q) (cape : Cape) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (env : CallEnv) (hn : SixOk nm = true) (hax : Bake.NoAx0 nm) (hfs : FinSure env nm)
    (hQ1 : ∀ nex g1, runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))
      = some (nex, g1) → Q g1.cond)
    (hbake : NoBakeOneC env nm cape DATA)
    (FUNC V : Noun) (n : Nomm) (hn' : SixOk n = true) (hax' : Bake.NoAx0 n)
    (hQ2 : ∀ nex g1 q g2, runLC env Option.none n (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))
      = some (nex, g1) → kerf nex g1 = some (q, g2) → Q g2.cond)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    nock (C cuGB (C (cuSam FUNC (setOne (C (C cape.toNoun DATA) FOL)) CODE (C JETS CALLS) JH
        (cacheN NARY MONO SCCS INL SURE)) compK)) cuGB
      = (runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))).bind fun p =>
          (finishLFC (S := CSet) (Map := TreapMap mugF) env nm (sccSur p.1 cape) cape (fun n => (n, []))).bind fun st =>
            (putF mugF (C (C cape.toNoun DATA) FOL) st.toNoun NARY).bind fun NARYU =>
              (putF mugF (C (C cape.toNoun DATA) FOL) (sccSur p.1 cape).toNoun SURE).bind fun SURE' =>
                (finishLUC (S := CSet) (Map := TreapMap mugF) env n).map fun st' =>
                  C (C st'.toNoun (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))))
                    (cacheN NARYU MONO SCCS INL' SURE') := by
  have hcsi := csi_gate_scc_one_f_six Q hT cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hsmap hcalls
    nm INL' hinl env hn hax hfs hQ1 hbake
  rw [← cu_csi_eq FUNC] at hcsi
  cases hr : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) with
  | none =>
    rw [hr] at hcsi
    exact cu_gate_none _ hcsi
  | some p =>
    obtain ⟨nex, g1⟩ := p
    rw [hr] at hcsi
    simp only [Option.bind_some] at hcsi ⊢
    cases e : finishLFC (S := CSet) (Map := TreapMap mugF) env nm (sccSur nex cape) cape (fun n => (n, [])) with
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
`%6`** (the analogue of `cu_gate_scc_one_f_c`): for nomms `nm` (the SCC's,
after `+inlined`) and `n` (the code's) of `SixOk` with `Bake.NoAx0`, under the
map branch of `+to-straight` (`TsMapAt`), a fork-free final pass
(`FinSure`), the state nouns' hypotheses of `cu_gate_scc_one_f_c` and
`NoBakeOneC`, the gate returns the noun of the model. -/
theorem cu_gate_scc_one_six (hT : TsMapAt) (cape : Cape) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (env : CallEnv) (hn : SixOk nm = true) (hax : Bake.NoAx0 nm) (hfs : FinSure env nm)
    (hbake : NoBakeOneC env nm cape DATA)
    (FUNC V : Noun) (n : Nomm) (hn' : SixOk n = true) (hax' : Bake.NoAx0 n)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    nock (C cuGB (C (cuSam FUNC (setOne (C (C cape.toNoun DATA) FOL)) CODE (C JETS CALLS) JH
        (cacheN NARY MONO SCCS INL SURE)) compK)) cuGB
      = (runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))).bind fun p =>
          (finishLFC (S := CSet) (Map := TreapMap mugF) env nm (sccSur p.1 cape) cape (fun n => (n, []))).bind fun st =>
            (putF mugF (C (C cape.toNoun DATA) FOL) st.toNoun NARY).bind fun NARYU =>
              (putF mugF (C (C cape.toNoun DATA) FOL) (sccSur p.1 cape).toNoun SURE).bind fun SURE' =>
                (finishLUC (S := CSet) (Map := TreapMap mugF) env n).map fun st' =>
                  C (C st'.toNoun (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))))
                    (cacheN NARYU MONO SCCS INL' SURE') :=
  cu_gate_scc_one_six_q (fun _ => True) hT cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hsmap
    hcalls nm INL' hinl env hn hax hfs (fun _ _ _ => trivial) hbake FUNC V n hn' hax' (fun _ _ _ _ _ _ => trivial)
    hgot hv

/-! ## `NoAx0` from `+fol-loop` -/

/-- **`n` is a nomm that `+fol-loop` returns** (at some fuel, on some
formula, subject, state, with some environment and memo). -/
def FolMade (n : Nomm) : Prop :=
  ∃ (M : Type → Type → Type) (_ : Ana.Treap M) (R : Type) (fenv : Ana.Env R) (memoF : Ana.Memo M) (k : Nat),
    ∃ fol sub seat mk bc df gen out gen',
    Ana.folLoop fenv memoF k fol sub seat mk bc df gen = some (out, gen') ∧ out.nomm = n

theorem folMade_noAx0 {n : Nomm} (h : FolMade n) : Bake.NoAx0 n := by
  obtain ⟨M, _, R, fenv, memoF, k, fol, sub, seat, mk, bc, df, gen, out, gen', e, rfl⟩ := h
  exact Ana.folLoop_noAx0 fenv memoF k fol sub seat mk bc df gen out gen' e

/-- **The top on `SixOk` with `NoAx0` from `+fol-loop`**: `cu_gate_scc_one_six`
for nomms that `+fol-loop` makes (`FolMade`); on the nomms, nothing but
the class `SixOk` and the fork-free final pass `FinSure`. -/
theorem cu_gate_scc_one_six_fol (hT : TsMapAt) (cape : Cape) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (env : CallEnv) (hn : SixOk nm = true) (hf : FolMade nm) (hfs : FinSure env nm)
    (hbake : NoBakeOneC env nm cape DATA)
    (FUNC V : Noun) (n : Nomm) (hn' : SixOk n = true) (hf' : FolMade n)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    nock (C cuGB (C (cuSam FUNC (setOne (C (C cape.toNoun DATA) FOL)) CODE (C JETS CALLS) JH
        (cacheN NARY MONO SCCS INL SURE)) compK)) cuGB
      = (runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))).bind fun p =>
          (finishLFC (S := CSet) (Map := TreapMap mugF) env nm (sccSur p.1 cape) cape (fun n => (n, []))).bind fun st =>
            (putF mugF (C (C cape.toNoun DATA) FOL) st.toNoun NARY).bind fun NARYU =>
              (putF mugF (C (C cape.toNoun DATA) FOL) (sccSur p.1 cape).toNoun SURE).bind fun SURE' =>
                (finishLUC (S := CSet) (Map := TreapMap mugF) env n).map fun st' =>
                  C (C st'.toNoun (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))))
                    (cacheN NARYU MONO SCCS INL' SURE') :=
  cu_gate_scc_one_six hT cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hsmap hcalls nm INL'
    hinl env hn (folMade_noAx0 hf) hfs hbake FUNC V n hn' (folMade_noAx0 hf')  hgot hv

/-! ## Examples with `%6` -/

/-- `[6 [0 2] [4 0 3] [1 0]]`, the `%6` of `sixEx`. -/
example : sixEx = Nomm.n6 (Nomm.n0 2) (Nomm.n4 (Nomm.n0 3)) (Nomm.n1 (A 0)) := rfl

/-- **A `%6` in both passes**: the SCC's nomm `[7 [1 0] [6 [0 2] [4 0 3] [1 0]]]`
(its final pass is fork-free, `finSure_n7_n1`) and the code's nomm the same;
the hypotheses left are `TsMapAt` and those on the state nouns. -/
example (hT : TsMapAt) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C Cape.no.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C Cape.no.toNoun DATA) FOL) CALLS) (INL' : Noun)
    (hinl : InlOK (C (C Cape.no.toNoun DATA) FOL) CODE INL (Nomm.n7 (Nomm.n1 (A 0)) sixEx) INL') (env : CallEnv)
    (FUNC V : Noun) (hgot : getF mugF FUNC CODE = some (C (A 0) V))
    (hv : slot? 2 V = some (Nomm.n7 (Nomm.n1 (A 0)) sixEx).toNoun) :=
  cu_gate_scc_one_six hT Cape.no DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hsmap hcalls _ INL'
    hinl env rfl (by simp [sixEx, Bake.NoAx0]) (finSure_n7_n1 env _ _) (noBakeOneC_no env _ DATA) FUNC V _ rfl
    (by simp [sixEx, Bake.NoAx0]) hgot hv

/-- **The bare `%6` as the code's nomm**: the unary pass asks no fork-free
result, so `n` is `[6 [0 2] [4 0 3] [1 0]]` itself, compiled under
`%done` (phase S, the fork of `[[yes ..] [nuh ..]]` in its result, then
`+kerf` on it); the SCC's nomm is `[7 [1 0] [7 [0 1] [6 [0 2] [4 0 3] [1 0]]]]`. -/
example (hT : TsMapAt) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C Cape.no.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C Cape.no.toNoun DATA) FOL) CALLS) (INL' : Noun)
    (hinl : InlOK (C (C Cape.no.toNoun DATA) FOL) CODE INL (Nomm.n7 (Nomm.n1 (A 0)) (Nomm.n7 (Nomm.n0 1) sixEx)) INL')
    (env : CallEnv) (FUNC V : Noun) (hgot : getF mugF FUNC CODE = some (C (A 0) V))
    (hv : slot? 2 V = some sixEx.toNoun) :=
  cu_gate_scc_one_six hT Cape.no DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hsmap hcalls _ INL'
    hinl env rfl (by simp [sixEx, Bake.NoAx0]) (finSure_n7_n1 env _ _) (noBakeOneC_no env _ DATA) FUNC V sixEx rfl
    (by simp [sixEx, Bake.NoAx0]) hgot hv

end Compiler
end Formalization
