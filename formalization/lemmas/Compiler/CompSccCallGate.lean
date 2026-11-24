import lemmas.Compiler.CompSccCall

/-!
# `+compile-scc-in` and `+compile-unary` on an SCC of one bell, with indirect calls

The theorems of `CompSccOne.lean` (`csi_gate_scc_one_f`, `cu_gate_scc_one_f`)
and the chain under them (`fin_gate_finishLF`, `mem_to_finish`, `mem_gate`,
`csi_gate_one`, `csi_gate_scc_one_m`, `mem_gate_none`), for a nomm of the
fragment with indirect calls (`indOk`), against the models with calls:
`finishLFC env` (the final pass with `runLC env ~`) and `finishLUC env`
(`+compile-unary`), for every `env`.  The proofs are those of the pure
fragment with the run link `comp_run_entry_c` and the facts of
`CompSccCall.lean` (`mem_cond_frag_c`, `args_frag_c`, `scc_sur_frag_c`,
`inl_gate_ind`, `cu_gate_c`) in place of their pure versions.

What survives unchanged of the hypotheses of `cu_gate_scc_one_f`: `hnary`,
`hnmap`, `hsmap` (statements on `nary.cache`, `sure.cache`), `NoSelfCall`
(on `calls.long-ska`: an indirect call has no callee there), `InlOK` (on
`inl.cache` and `code.long-ska`; `+inlined` is the identity on
`indPure` nomms, `inl_gate_ind`), `hgot`, `hv`.  What changes: the fragment
(`indOk nm`, `indOk n` instead of pure, `%6`-free, `tenOk`), and
`NoBakeOne` becomes `NoBakeOneC env` (the same statement on the run of
`runLC env ~`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- **`finishLFC` is the run with calls, the check of `args`,
`+need-ord-alloc-regs`, then `finTail`.** -/
theorem finishLFC_tail (env : CallEnv) (nm : Nomm) (ord : NeedOrd) (less : Cape)
    (bake : Need → Need × List (Nat × Noun)) :
    finishLFC (S := CSet) (Map := TreapMap mugF) env nm ord less bake
      = (runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))).bind fun (nex, g1) =>
          if nex.th.args ≠ [] then Option.none else
          (needOrdAllocRegs ord g1).bind fun (nedF, g2) => finTail nedF less nex.th.there nex.laz bake g2 := rfl

/-- Nothing is baked whenever the final pass with calls gets to `+bake-need`. -/
def NoBakeOneC (env : CallEnv) (nm : Nomm) (cape : Cape) (DATA : Noun) : Prop :=
  ∀ nex g1 nedF g2, runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))
      = some (nex, g1) →
    needOrdAllocRegs (sccSur nex cape) g1 = some (nedF, g2) → NoBake nedF (Sock.mk cape DATA)

/-- **The gate `finish` returns the noun of `finishLF`**, the model of the
final pass for a bell alone in its SCC, with the bake that bakes nothing:
given the run of the final pass (`runL` from `gen0` gives `nex` and `g1`,
with `args.then.nex = ~`, a fork-free `laz`, `cond` empty) and the shape
`ord` that `+need-ord-alloc-regs` allocates from `g1` (`ned-final` and
`g2`), the gate on the subject that holds them returns
`finishLF nm ord less (fun n => (n, []))`. -/
theorem fin_gate_finishLF_c {ctx : Noun} (env : CallEnv) (h7 : slot? 7 ctx = some compK) (c2 c6 c14 NEWN SUR REST G0 : Noun)
    (less : Cape) (hcomp : slot? 6 REST = some (C comp.door (C G0 ctx))) (hdone : slot? 14 REST = some (A 0))
    (hless : slot? 496 REST = some less.toNoun) (hl2 : slot? 0x3ffffff REST = some layer2)
    (x : GenRest) (hs0 : x.soft = A 0)
    (nm : Nomm) (ord : NeedOrd) (nex : NextL CSet) (g1 g2 : Gen (TreapMap mugF)) (nedF : Need) (s : Sure CSet)
    (hrunL : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))
    (hargs : nex.th.args = []) (hlaz : nex.laz = Lazy.ofSure s)
    (hcond1 : ∀ k, HoonMap.get g1.cond k = Option.none)
    (hnoar : needOrdAllocRegs ord g1 = some (nedF, g2)) :
    nock (C finBody (C (A 0) (finCtx c2 c6 c14 NEWN nex.laz.toNoun nedF.toNoun nedF.toNoun (A 0) nex.th.there SUR
        (genNoun g2 x) REST))) finBody
      = (finishLFC (S := CSet) (Map := TreapMap mugF) env nm ord less (fun n => (n, []))).map Straight.toNoun := by
  have kc2 := (kc_needOrdAllocRegs (Map := TreapMap mugF) ord).keep g1 nedF g2 hnoar
  have hrun := isRun_needOrdAllocRegs hnoar
  rw [finishLFC_tail, hrunL]
  simp only [Option.bind_some, hargs, ne_eq, not_true_eq_false, if_false, hnoar]
  rw [hlaz]
  exact fin_gate h7 c2 c6 c14 NEWN SUR REST G0 less hcomp hdone hless hl2 g2 x hs0
    (fun k => by rw [kc2]; exact hcond1 k) nedF hrun nex.th.there s


/-- **The gate `member` on its final pass, up to the push of `finish`.**
From the sample `[b %done keep map-local top cache]` (with `b` the noun of a
bell whose `less` is `[cape data]`) in the context `memCtx`, the gate runs
`+inlined`, the run, `+collapse-shape`, `+bake-need`, `+sure-of`, the
updates of `sure.cache`, and pushes `finish` on the subject `memFC`. -/
theorem mem_to_finish_c (cape : Cape) (DATA FOL : Noun) (keep : Bool)
    (ML TOP CACHE DN KIDS ML0 CB SCC CODE LSR JH CACHE0 : Noun)
    (nm : Nomm) (C1 C2 C3 C4 SURE : Noun)
    (hinl : nock (C inlBody (C (C (C (C cape.toNoun DATA) FOL) (C (C CODE LSR) (C JH CACHE))) compK)) inlBody
      = some (C nm.toNoun (cacheN C1 C2 C3 C4 SURE)))
    (env : CallEnv) (hn : indOk nm = true)
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
  have hrunN := comp_run_entry_c h7 hcode env nm hn Option.none (cuRest (cacheN C1 C2 C3 C4 SURE)) (A 1) (A 0)
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


/-- **The gate `member` on the final pass of an SCC of one bell** (`mode`
`%done`, `map-local` and `top` empty): it returns `[chg (~(put by ~) b
straight) cache]`, where `straight` is the noun of `finishLF nm ord cape (fun
n => (n, []))`, `cache` is the cache of `+inlined` with `sure.cache` put at
`b` (`SURE'`), and `chg` is `memChgN` of `moved` and `need-new`; it crashes
when `finishLF` is `none`.  The hypotheses are those of `mem_to_finish_c`;
`cond` empty and the fork-free `laz` come from the fragment
(`mem_cond_frag`, `mem_laz_frag`). -/
theorem mem_gate_c (cape : Cape) (DATA FOL : Noun) (keep : Bool)
    (CACHE DN KIDS ML0 CB SCC CODE LSR JH CACHE0 : Noun)
    (nm : Nomm) (C1 C2 C3 C4 SURE : Noun)
    (hinl : nock (C inlBody (C (C (C (C cape.toNoun DATA) FOL) (C (C CODE LSR) (C JH CACHE))) compK)) inlBody
      = some (C nm.toNoun (cacheN C1 C2 C3 C4 SURE)))
    (env : CallEnv) (hn : indOk nm = true)
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
    nock (C memBody (C (memSam (C (C cape.toNoun DATA) FOL) (A 0x656e6f64) (loob keep) (A 0) (A 0) CACHE)
        (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0))) memBody
      = (finishLFC (S := CSet) (Map := TreapMap mugF) env nm ord cape (fun n => (n, []))).map fun st =>
          C (memChgN (memMovedN keep WAS sur.toNoun) (needToOrd nedF).toNoun)
            (C (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))) (cacheN C1 C2 C3 C4 SURE')) := by
  rw [mem_to_finish_c cape DATA FOL keep (A 0) (A 0) CACHE DN KIDS ML0 CB SCC CODE LSR JH CACHE0 nm C1 C2 C3 C4 SURE
    hinl env hn nex g1 hrunL s hlaz ord hsc hargs nedF g2 hnoar hb sur hsur WAS SURE' hwas hw hput]
  have hmv : memMovedN keep WAS sur.toNoun = A 0 ∨ memMovedN keep WAS sur.toNoun = A 1 := by
    unfold memMovedN; split <;> simp
  have hnn : ∃ p q, (needToOrd nedF).toNoun = C p q := nord_cell _
  unfold memFC
  rw [mem_prod_new (hmv := hmv) (hnn := hnn)]
  obtain ⟨hs6, hs14, hs496, hl2⟩ := mem_rest_slots nm.toNoun SCC (C CODE LSR) JH (A 0) (A 0) cape.toNoun DATA FOL
    (loob keep) (cacheN C1 C2 C3 C4 SURE') DN KIDS ML0 CB CACHE0
  have hf := fin_gate_finishLF_c env (rfl : slot? 7 (memDCtx SCC (C CODE LSR) JH (A 0) (A 0) (C (C cape.toNoun DATA) FOL))
      = some compK) (memMovedN keep WAS sur.toNoun) (memSurKN keep WAS sur.toNoun) WAS (needToOrd nedF).toNoun
    sur.toNoun _ cuBunt cape hs6 hs14 hs496 hl2 (cuRest (cacheN C1 C2 C3 C4 SURE)) rfl nm ord nex g1 g2
    nedF s hrunL hargs hlaz (mem_cond_frag_c env hn hrunL) hnoar
  rw [hf, Option.map_map]
  rfl


/-- **`+compile-scc-in` on an SCC of one bell `b` that is not in
`nary.cache` and does not call itself**, on the final pass whose straight
`st` the model gives (`hst`): it returns `[[[b st] ~ ~] cache]`, where
`cache` is the cache of `+inlined` with `sure.cache` updated (`SURE'`) and
`nary` united with `[[b st] ~ ~]` (`NARYU`, `huni`).  The other hypotheses
are those of `csi_to_final` (the cache test, `kids`, `done`) and of
`mem_gate_c` (with `keep` false, as `final` is called with `|`). -/
theorem csi_gate_one_c (cape : Cape) (DATA FOL CODE LSR JH NARY CR KIDS : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0))
    (hkids : nock (C (A 0) (C csiBody (C (csiSam (setOne (C (C cape.toNoun DATA) FOL)) (C CODE LSR) JH (C NARY CR))
      compK))) csiKids = some KIDS)
    (hju : juHasF mugF (C (C cape.toNoun DATA) FOL) (C (C cape.toNoun DATA) FOL) KIDS = some false)
    (nm : Nomm) (C1 C2 C3 C4 SURE : Noun)
    (hinl : nock (C inlBody (C (C (C (C cape.toNoun DATA) FOL) (C (C CODE LSR) (C JH (C NARY CR)))) compK)) inlBody
      = some (C nm.toNoun (cacheN C1 C2 C3 C4 SURE)))
    (env : CallEnv) (hn : indOk nm = true)
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
    (hput : putF mugF (C (C cape.toNoun DATA) FOL) (memSurKN false WAS sur.toNoun) SURE = some SURE')
    (st : Straight (TreapMap mugF))
    (hst : finishLFC (S := CSet) (Map := TreapMap mugF) env nm ord cape (fun n => (n, [])) = some st)
    (NARYU : Noun)
    (huni : nock (C by.uni.battery (C (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0)))
      (C by.battery (C C1 layer2)))) by.uni.battery = some NARYU) :
    nock (C csiBody (C (csiSam (setOne (C (C cape.toNoun DATA) FOL)) (C CODE LSR) JH (C NARY CR)) compK)) csiBody
      = some (C (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))) (C NARYU (C C2 (C C3 (C C4 SURE'))))) := by
  rw [csi_to_final _ _ _ _ _ _ hnary hkids hju]
  have hm := mem_gate_c cape DATA FOL false (C NARY CR) (A 0) KIDS (A 0) csiBody
    (setOne (C (C cape.toNoun DATA) FOL)) CODE LSR JH (C NARY CR) nm C1 C2 C3 C4 SURE hinl env hn nex g1 hrunL s
    hlaz ord hsc hargs nedF g2 hnoar hb sur hsur WAS SURE' hwas hw hput
  rw [hst, Option.map_some] at hm
  exact csi_final_one (hm := hm) (huni := huni)


/-- **`+compile-scc-in` on an SCC of one bell `b` with no callee, not in
`nary.cache`, whose nomm is pure, `%6`-free and `tenOk`**: the gate
returns `[[[b st] ~ ~] cache']` with `st` the straight of `finishLF nm sur
cape` (`sur` the shape `sccSur` of the run) and crashes when that is
`none`; `cache'` has `nary` with `st` put at `b` (`putF`, the `+uni:by`),
`inl` as `InlOK` says, and `sure` with `sur` put at `b` (`SURE'`).  The
hypotheses on the model: the run succeeds, `+need-ord-alloc-regs` of `sur`
succeeds, nothing is baked. -/
theorem csi_gate_scc_one_m_c (cape : Cape) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (env : CallEnv) (hn : indOk nm = true)
    (nex : NextL CSet) (g1 : Gen (TreapMap mugF))
    (hrunL : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))
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
  obtain ⟨hlz, hsur⟩ := scc_sur_frag_c env hn hrunL cape
  have hargs := args_frag_c env hn hrunL
  have hsc := hsc_of_sure nex nex.laz.sure hlz cape (sccSur nex cape) hsur
  have hi := inl_gate_ind (C (C cape.toNoun DATA) FOL) CODE (C JETS CALLS) JH NARY MONO SCCS INL SURE INL' nm (indPure_of_indOk nm hn) hinl
  obtain ⟨WAS, hwas, hw⟩ := getF_of_putF _ _ SURE hput
  have hput' : putF mugF (C (C cape.toNoun DATA) FOL) (memSurKN false WAS (sccSur nex cape).toNoun) SURE
      = some SURE' := by simpa [memSurKN] using hput
  have hm := mem_gate_c cape DATA FOL false (C NARY (C MONO (C SCCS (C INL SURE)))) (A 0)
    (kidsOne (C (C cape.toNoun DATA) FOL)) (A 0) csiBody (setOne (C (C cape.toNoun DATA) FOL)) CODE (C JETS CALLS) JH
    (C NARY (C MONO (C SCCS (C INL SURE)))) nm NARY MONO SCCS INL' SURE hi env hn nex g1 hrunL nex.laz.sure hlz
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


/-- **`member` on its final pass crashes when the run does**, or when
`+collapse-shape` does: `args.then` not `~`, or `+need-ord-alloc-regs` of
`sccSur` crashing. -/
theorem mem_gate_none_c (cape : Cape) (DATA FOL : Noun) (keep : Bool)
    (ML TOP CACHE DN KIDS ML0 CB SCC CODE LSR JH CACHE0 : Noun) (nm : Nomm) (CA : Noun)
    (hinl : nock (C inlBody (C (C (C (C cape.toNoun DATA) FOL) (C (C CODE LSR) (C JH CACHE))) compK)) inlBody
      = some (C nm.toNoun CA))
    (env : CallEnv) (hn : indOk nm = true)
    (hcrash : runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = none ∨
      ∃ nex g1, runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1) ∧
        (nex.th.args ≠ [] ∨ needOrdAllocRegs (sccSur nex cape) g1 = none)) :
    nock (C memBody (C (memSam (C (C cape.toNoun DATA) FOL) (A 0x656e6f64) (loob keep) ML TOP CACHE)
        (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0))) memBody = none := by
  have h7 : slot? 7 (memDCtx SCC (C CODE LSR) JH ML TOP (C (C cape.toNoun DATA) FOL)) = some compK := rfl
  have hcode : slot? 52 (memDCtx SCC (C CODE LSR) JH ML TOP (C (C cape.toNoun DATA) FOL)) = some CODE := by
    simp [memDCtx, nock_exec]
  rw [mem_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨_, _, _, rfl⟩ hinl, mem_r3, mem_res]
  have hrunN := comp_run_entry_c h7 hcode env nm hn Option.none (cuRest CA) (A 1) (A 0) (cu_entry_nosoft _)
  rcases hcrash with hr | ⟨nex, g1, hr, hc⟩
  · have hr' : runLC env Option.none nm (CGoal.toL (CGoal.done : CGoal CSet)) [] (gen0 : Gen (TreapMap mugF)) = none := hr
    rw [← gen0_eq, hr', cu_done_noun] at hrunN
    simp only [listNoun, Option.map_none, compCore] at hrunN
    rw [mem_final_run_none (hmode := mem_mode_noop _ _) (hrun := hrunN)]
    rfl
  · have hr' : runLC env Option.none nm (CGoal.toL (CGoal.done : CGoal CSet)) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1) := hr
    rw [← gen0_eq, hr', cu_done_noun] at hrunN
    simp only [listNoun, Option.map_some, compCore] at hrunN
    obtain ⟨hlz, hsur⟩ := scc_sur_frag_c env hn hr cape
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


/-- **`+compile-scc-in` on an SCC of one bell, with the model hypotheses
folded in**: on the fragment (`nm` pure, `%6`-free, `tenOk`) and when
nothing is baked (`NoBakeOne`), the gate returns the noun of the model:
`[[[b st] ~ ~] cache']` with `st` from the run of `nm` and `finishLF` with
`ord := sccSur`, `nary` with `st` put at `b`, `inl` as `InlOK` says and
`sure` with `sccSur` put at `b`; it crashes when the model is `none`.  The
other hypotheses speak of the state nouns only. -/
theorem csi_gate_scc_one_f_c (cape : Cape) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (env : CallEnv) (hn : indOk nm = true)
    (hbake : NoBakeOneC env nm cape DATA) :
    nock (C csiBody (C (csiSam (setOne (C (C cape.toNoun DATA) FOL)) (C CODE (C JETS CALLS)) JH
        (cacheN NARY MONO SCCS INL SURE)) compK)) csiBody
      = (runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))).bind fun p =>
          (finishLFC (S := CSet) (Map := TreapMap mugF) env nm (sccSur p.1 cape) cape (fun n => (n, []))).bind fun st =>
            (putF mugF (C (C cape.toNoun DATA) FOL) st.toNoun NARY).bind fun NARYU =>
              (putF mugF (C (C cape.toNoun DATA) FOL) (sccSur p.1 cape).toNoun SURE).map fun SURE' =>
                C (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))) (cacheN NARYU MONO SCCS INL' SURE') := by
  have hi := inl_gate_ind (C (C cape.toNoun DATA) FOL) CODE (C JETS CALLS) JH NARY MONO SCCS INL SURE INL' nm (indPure_of_indOk nm hn) hinl
  have hcrash : (runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = none ∨
      ∃ nex g1, runLC env Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1) ∧
        (nex.th.args ≠ [] ∨ needOrdAllocRegs (sccSur nex cape) g1 = none)) →
      nock (C csiBody (C (csiSam (setOne (C (C cape.toNoun DATA) FOL)) (C CODE (C JETS CALLS)) JH
        (cacheN NARY MONO SCCS INL SURE)) compK)) csiBody = none := by
    intro hc
    have hcache : cacheN NARY MONO SCCS INL SURE = C NARY (C MONO (C SCCS (C INL SURE))) := rfl
    rw [hcache, csi_to_final _ _ _ _ _ _ hnary (csi_kids_noself _ CODE JETS CALLS JH _ hcalls) (ju_has_kids _)]
    exact csi_final_one_none _ _ _ _ _ _ _ _ (mem_gate_none_c cape DATA FOL false (A 0) (A 0)
      (C NARY (C MONO (C SCCS (C INL SURE)))) (A 0) (kidsOne _) (A 0) csiBody _ CODE (C JETS CALLS) JH
      (C NARY (C MONO (C SCCS (C INL SURE)))) nm _ hi env hn hc)
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
        rw [csi_gate_scc_one_m_c cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hcalls nm INL'
          hinl env hn nex g1 hr nedF g2 hno (hbake nex g1 nedF g2 hr hno) SURE' hp]
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


/-- **The gate of `+compile-unary` on `[func [b ~ ~] long-ska jets-hot
cache]` with the model hypotheses folded in**: under the hypotheses of
`csi_gate_scc_one_f_c`, and for the nomm `n` of `func` (pure, `%6`-free,
`tenOk`), it returns `finishLU n` with the n-ary map and the cache of the
model, and crashes when the model of the SCC is `none`. -/
theorem cu_gate_scc_one_f_c (cape : Cape) (DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0)) (hnmap : IsMap mugF NARY)
    (hsmap : IsMap mugF SURE) (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (nm : Nomm) (INL' : Noun) (hinl : InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL')
    (env : CallEnv) (hn : indOk nm = true)
    (hbake : NoBakeOneC env nm cape DATA)
    (FUNC V : Noun) (n : Nomm) (hn' : indOk n = true)
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
  have hcsi := csi_gate_scc_one_f_c cape DATA FOL CODE JETS CALLS JH NARY MONO SCCS INL SURE hnary hnmap hsmap hcalls
    nm INL' hinl env hn hbake
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
      exact cu_gate_c FUNC _ CODE (C JETS CALLS) JH _ _ _ V env n hn' hcsi hgot hv


/-- With the cape `|` nothing is baked (`noBake_no`), so `NoBakeOneC` holds
and `cu_gate_scc_one_f_c` has no hypothesis on the model but the fragment. -/
theorem noBakeOneC_no (env : CallEnv) (nm : Nomm) (DATA : Noun) : NoBakeOneC env nm Cape.no DATA :=
  fun _ _ nedF _ _ _ => noBake_no nedF DATA

end Compiler
end Formalization
