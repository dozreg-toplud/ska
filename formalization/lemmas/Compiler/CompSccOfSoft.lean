import lemmas.Compiler.CompSccOfStr
import lemmas.Compiler.CompRunSoftChain
import lemmas.Compiler.CompSccLoopSoftMemDone

/-!
# The chain of the gate with soft members (README Gaps 19 (g))

The `D` chain of `CompSccOfStr.lean` with the callee SCCs whose members make soft calls: their
loop runs at track I's `cfgRealS r snd` and its `%done` gate is `memGate_done_realS` at
`MemDoneCallS`.  New names (suffix `S`); nothing above is changed.

* `EMDS`: `EMD` without its `NoSoft` clause (`AgreeIPC` for `AgreeIP`), blind to `soft`
  (`eMDS_soft`); `eMDS_of`; `ExtSE E` (`ExtS` and `E` kept), `yOkS_xnE`;
* `crxts_of_xtE`: `crxts_of_xt` with the equation of the run at one state in place of `sof`
  false everywhere;
* `MemRunS`: the member's nomm is `SoftChainOk` (with its leaves `LeafQ` at every soft map) or
  `DirOk` with `DirCallsTN` and the soft model equal to `runLC` on it (`sim`);
* **`memDoneCall_ofS`**: track I's `MemDoneCallS` from `comp_run_softChain` at `XN EMDS ~`,
  or from `comp_run_dirXTN` at `XN EMD ~` through `crxts_of_xtE`;
* `MemDoneRestDS`, `memDoneCall_of_restDS`, **`sccLoopAtD_realS`** (`memGate_done_realS`);
* `SccLoopDataDS` (the loop data at `cfgRealS`), `CalleeHDS` (an SCC has the loop data of
  `CompSccOfStr.lean` or of this file), `calleeCompiled_stepHDS`, `calleeCompiled_heightsDS`,
  `calleeCompiled_heights0DS`, `CalleeHSDS`, `calleeH_of_SDS`, `calleeHSDS_of_Str`;
* `member_cfgRealS_sweep`, `maySweep_cfgRealS`, **`memGate_cfgRealS_of`**: a `%may` / `%must`
  gate at `cfgReal` is one at `cfgRealS` (`compRealS` differs only on `%done`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.SccLoop

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## The rest predicate of a member run with soft calls -/

/-- **`EMD` without its `NoSoft` clause**: `AgreeIPC` at `PeS`, `RKD` at `PfS`, `QK` of the loop,
the members' `sure` entries; every clause reads only `cache`. -/
def EMDS (env : CallEnv) (SC0 MO0 : Noun) (inl : Noun → Option Nomm) (P Pf : Noun → Prop) (S : Noun)
    (st : St Noun NeedOrd) (xs x : GenRest) : Prop :=
  AgreeIPC env (PeS P S st) x ∧ RKD SC0 MO0 inl (PfS Pf S) x ∧ QK env (RKD SC0 MO0 inl Pf) P S xs x.cache ∧
    SureHolds (tapList S) st.sure x.cache

theorem eMDS_of {env : CallEnv} {SC0 MO0 : Noun} {inl : Noun → Option Nomm} {P Pf : Noun → Prop} {S : Noun}
    {st : St Noun NeedOrd} {xs x : GenRest} (h : EMD env SC0 MO0 inl P Pf S st xs x) :
    EMDS env SC0 MO0 inl P Pf S st xs x :=
  ⟨h.1.2, h.2.1, h.2.2.1, h.2.2.2⟩

/-- `EMDS` does not read `soft`. -/
theorem eMDS_soft {env : CallEnv} {SC0 MO0 : Noun} {inl : Noun → Option Nomm} {P Pf : Noun → Prop} {S : Noun}
    {st : St Noun NeedOrd} {xs : GenRest} (x : GenRest) (s : Noun) (h : EMDS env SC0 MO0 inl P Pf S st xs x) :
    EMDS env SC0 MO0 inl P Pf S st xs { x with soft := s } := h

/-- **`ExtS` with `E` kept**: the `Y` of a member run with soft calls. -/
def ExtSE (E : GenRest → Prop) (x y : GenRest) : Prop := ExtS x y ∧ (E x → E y)

/-- At `XN E msup` with `E` blind to `soft`, `ExtSE E` is a `YOkS`. -/
theorem yOkS_xnE {E : GenRest → Prop} (hE : ∀ x s, E x → E { x with soft := s }) (msup : Option Nomm) :
    YOkS (XN E msup) (ExtSE E) :=
  ⟨fun x => ⟨extS_refl x, id⟩, fun h1 h2 => ⟨extS_trans h1.1 h2.1, fun h => h2.2 (h1.2 h)⟩,
    fun hX hy => ⟨hy.2 hX.1, hX.2.1, hX.2.2⟩, fun s h => ⟨extS_soft s h.1, fun hx => hE _ s (h.2 hx)⟩,
    fun s hX => ⟨hE _ s hX.1, hX.2.1, hX.2.2⟩⟩

/-- **`crxts_of_xt` at one state**: the threaded link of `R` from `g` is the one of `RS` from
`GenSf.ofGen g` when `RS` there is `R` with an empty `soft.gen` (`hsim`) and `Y` keeps an empty
`soft`. -/
theorem crxts_of_xtE {R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)}
    {RS : Nomm → CGoalL CSet → List Nat → CMS (TreapMap mugF) (NextL CSet)} {ctx : Noun}
    {X : GenRest → Noun → Noun → Prop} {Y : GenRest → GenRest → Prop} {n : Nomm} {goal : CGoalL CSet}
    {region : List Nat} {g : Gen (TreapMap mugF)}
    (hsim : RS n goal region (GenSf.ofGen g) = (R n goal region g).map embS)
    (hYs : ∀ x x', x.soft = A 0 → Y x x' → x'.soft = A 0)
    (h : CompRunAtXT R ctx X Y n goal region g) :
    CompRunAtXTS RS ctx X Y n goal region (GenSf.ofGen g) := by
  intro x mono sup' hx hX
  have hx0 : x.soft = A 0 := by rw [hx]; exact softMapNoun_empty
  obtain ⟨x', hY', he⟩ := h x mono sup' (noSoft_of_nil hx0) hX
  refine ⟨x', hY', ?_⟩
  have hx' : { x' with soft := A 0 } = x' := by
    have h0 := hYs _ _ hx0 hY'
    cases x'; simp only at h0 ⊢; rw [h0]
  show nock (crSubj mono n.toNoun goal.toNoun (listNoun A region) sup' (compCore g x ctx)) crDol = _
  rw [he, hsim]
  cases R n goal region g with
  | none => rfl
  | some p =>
    simp only [Option.map_some, embS, GenSf.ofGen, softMapNoun_empty, hx']

/-! ## The `%done` call of a member -/

/-- **The class of a member's nomm in a loop with soft calls**: the corpus's soft shape
(`SoftChainOk` at `EMDS`, with the leaves `LeafQ` at every soft map), or `DirOk` with its calls
at `EMD` and the soft model equal to `runLC` on it from `gen0` (`sim`). -/
def MemRunS (r : RealCfg) (snd : Nomm → NeedOrd → Bool) (order : List Noun) (kids : Noun → List Noun)
    (st : St Noun NeedOrd) (env : CallEnv) (SC0 MO0 : Noun) (inl : Noun → Option Nomm) (P Pf : Noun → Prop)
    (S : Noun) (xs : GenRest) (CODE ctx : Noun) (nm : Nomm) : Prop :=
  (SoftChainOk (envDoneS r snd order kids st) snd CODE ctx (EMDS env SC0 MO0 inl P Pf S st xs) [] Option.none nm ∧
    ∀ sm : TreapMap mugF SoftCall, LeafQ (fun x => x.soft = softMapNoun sm) (envDoneS r snd order kids st) ctx
      (XN (EMDS env SC0 MO0 inl P Pf S st xs))
      (fun a c => ExtSE (EMDS env SC0 MO0 inl P Pf S st xs) a c ∧ c.soft = a.soft)) ∨
  (DirOk nm = true ∧
    DirCallsTN (envDoneS r snd order kids st) CODE ctx (EMD env SC0 MO0 inl P Pf S st xs)
      (ExtE (EMD env SC0 MO0 inl P Pf S st xs)) Option.none nm ∧
    runLCS (S := CSet) (Map := TreapMap mugF) (envDoneS r snd order kids st) snd Option.none nm CGoalL.done []
      (GenSf.ofGen gen0) = (runLC (envDoneS r snd order kids st) Option.none nm CGoalL.done [] gen0).map embS)

/-- **`MemDoneCallS` from the threaded run** (`comp_run_softChain` at `XN EMDS ~`, `ExtSE EMDS`, or
`comp_run_dirXTN` at `XN EMD ~`, `ExtE EMD` through `crxts_of_xtE`): the facts of the model and of
track A's arms as in `MemDoneCallS`, `+inlined` keeping the cache (`InlKeep`), and the class
`MemRunS` of the member's nomm. -/
theorem memDoneCall_ofS (r : RealCfg) (snd : Nomm → NeedOrd → Bool) (order : List Noun) (kids : Noun → List Noun)
    (nout : Noun → NeedOrd) (env : CallEnv) (SC0 MO0 : Noun) (inl : Noun → Option Nomm) (P Pf : Noun → Prop)
    (S : Noun) (xs : GenRest) (hrs : r.scc = tapList S) (hPS : ∀ k ∈ tapList S, ¬ P k)
    (st : St Noun NeedOrd) (keep : Bool) (DN KIDS ML0 CB SCC CODE LSR JH CACHE0 b ML CACHE : Noun)
    (hR : LoopR r.scc (fun _ => []) nout (QK env (RKD SC0 MO0 inl Pf) P S xs) st.ml st.sure ML CACHE)
    (cape : Cape) (DATA FOL : Noun) (nm : Nomm) (fuel : Nat) (hb : b = C (C cape.toNoun DATA) FOL)
    (hinfo : r.info b = ⟨nm, cape, DATA, fuel⟩) (CA1 : Noun)
    (hinl : nock (C inlBody (C (C b (C (C CODE LSR) (C JH CACHE))) compK)) inlBody = some (C nm.toNoun CA1))
    (hik : InlKeep inl CACHE CA1)
    (hm : MemRunS r snd order kids st env SC0 MO0 inl P Pf S xs CODE (memDCtx SCC (C CODE LSR) JH ML (A 0) b) nm)
    (nex : NextL CSet) (g1 : GenSf (TreapMap mugF))
    (hrunL : runLCS (envDoneS r snd order kids st) snd Option.none nm (CGoalL.done : CGoalL CSet) []
      (GenSf.ofGen gen0) = some (nex, g1))
    (ord : NeedOrd) (hcol : shapeCol fuel nex.laz cape = some ord) (hargs : nex.th.args = [])
    (nedF : Need) (g2 : Gen (TreapMap mugF)) (hnoar : needOrdAllocRegs ord g1.g = some (nedF, g2))
    (hrun : isRun (flattenNeed (bakeNeed nedF (Sock.mk cape DATA)).1)
        ((flattenNeed (bakeNeed nedF (Sock.mk cape DATA)).1).headD 0) 0 = true)
    (hreq : ∀ u sf3, coerceLazyLS nedF cape nex.th.there nex.laz ⟨g2, g1.soft⟩ = some (u, sf3) →
        ∀ p ∈ TreapMap.tap sf3.soft, ReqTN p.2.req)
    (sur : NeedOrd) (hsur : sureOf (needToOrd nex.laz.sure.ned) nex.laz.sure.lok cape = some sur)
    (hfin : ∃ s, finishLFCS (S := CSet) (Map := TreapMap mugF) (envDoneS r snd order kids st) snd TreapMap.tap nm ord
        cape (fun n => bakeNeed n (Sock.mk cape DATA)) = some s)
    (hcs : ∀ (x1 : GenRest) (C1 C2 C3 C4 SURE' : Noun) (prev : NeedOrd), st.ml b = some prev →
        msgOrd (needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1) prev cape ≠ needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1 →
        ∃ t, (∃ s : Straight (TreapMap mugF), C (msgOrd (needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1) prev cape).toNoun t = s.toNoun) ∧ nock (C finBody (C (C (A 0) (msgOrd (needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1) prev cape).toNoun)
              (memFCR keep (wasN (st.sure b)) sur.toNoun
                (needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1).toNoun nex.laz.toNoun nedF.toNoun
                (bakeNeed nedF (Sock.mk cape DATA)).1.toNoun (immNoun (bakeNeed nedF (Sock.mk cape DATA)).2)
                nex.th.there (genNoun g2 x1) nm.toNoun
                (memDCtx SCC (C CODE LSR) JH ML (A 0) b) b ML
                (A 0) (cacheN C1 C2 C3 C4 SURE') (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0)))) finBody
          = some (C (msgOrd (needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1) prev cape).toNoun t)) :
    MemDoneCallS r snd order kids (fun _ => []) nout env (RKD SC0 MO0 inl Pf) P S xs st keep DN KIDS ML0 CB SCC CODE
      LSR JH CACHE0 b ML CACHE := by
  have hE0 : EMD env SC0 MO0 inl P Pf S st xs (cuRest CA1) := eMD_start hPS hR.2.2.2 (hrs ▸ hR.2.1) hik
  have h7 : slot? 7 (memDCtx SCC (C CODE LSR) JH ML (A 0) b) = some compK := rfl
  have h52 : slot? 52 (memDCtx SCC (C CODE LSR) JH ML (A 0) b) = some CODE := by simp [memDCtx, nock_exec]
  rcases hm with ⟨hn, hL⟩ | ⟨hn, hd, hsim⟩
  · have hrun' := comp_run_softChain h7 h52 (envDoneS r snd order kids st) snd (EMDS env SC0 MO0 inl P Pf S st xs)
      (ExtSE (EMDS env SC0 MO0 inl P Pf S st xs)) (fun msup => yOkS_xnE (fun x s h => eMDS_soft x s h) msup) hL []
      nm Option.none hn (GenSf.ofGen genEntry)
    refine ⟨cape, DATA, FOL, nm, fuel, hb, hinfo, CA1, hinl, nex, g1, hrunL,
      XN (EMDS env SC0 MO0 inl P Pf S st xs) Option.none, ExtSE (EMDS env SC0 MO0 inl P Pf S st xs), hrun',
      ⟨eMDS_of hE0, rfl, rfl⟩, ?_, ord, hcol, hargs, nedF, g2, hnoar, hrun, hreq, sur, hsur, hfin, hcs⟩
    intro x1 hy
    obtain ⟨hA1, -, hQ1, hS1⟩ := hy.2 (eMDS_of hE0)
    obtain ⟨C1, C2, C3, C4, SU, hc, -⟩ := hA1
    exact ⟨C1, C2, C3, C4, SU, hc, hc ▸ hQ1, hrs ▸ hc ▸ hS1, fun b' _ k hk => by simp at hk⟩
  · have hrun' := comp_run_dirXTN h7 h52 (envDoneS r snd order kids st) (EMD env SC0 MO0 inl P Pf S st xs)
      (ExtE (EMD env SC0 MO0 inl P Pf S st xs))
      (fun msup => yOk_xn msup (fun x => ⟨ext_refl x, id⟩) (fun h1 h2 => ⟨ext_trans h1.1 h2.1, fun h => h2.2 (h1.2 h)⟩)
        (fun hx h => ext_noSoft hx h.1) (fun hE h => h.2 hE)) nm hn Option.none [] hd CGoalL.done genEntry rfl
    have hf : (runLCM (S := CSet) (Map := TreapMap mugF) (envDoneS r snd order kids st) false Option.none)
        = runLC (envDoneS r snd order kids st) Option.none := by
      funext n g rg; exact runLCM_false _ n _ g rg
    rw [hf] at hrun'
    have hrunS := crxts_of_xtE (RS := runLCS (envDoneS r snd order kids st) snd Option.none) hsim
      (fun x x' h0 hy => hy.1.1.trans h0) hrun'
    refine ⟨cape, DATA, FOL, nm, fuel, hb, hinfo, CA1, hinl, nex, g1, hrunL,
      XN (EMD env SC0 MO0 inl P Pf S st xs) Option.none, ExtE (EMD env SC0 MO0 inl P Pf S st xs), hrunS,
      ⟨hE0, rfl, rfl⟩, ?_, ord, hcol, hargs, nedF, g2, hnoar, hrun, hreq, sur, hsur, hfin, hcs⟩
    intro x1 hy
    obtain ⟨hA1, -, hQ1, hS1⟩ := hy.2 hE0
    obtain ⟨-, C1, C2, C3, C4, SU, hc, -⟩ := hA1
    exact ⟨C1, C2, C3, C4, SU, hc, hc ▸ hQ1, hrs ▸ hc ▸ hS1, fun b' _ k hk => by simp at hk⟩

/-- **What a `%done` call of `member` still takes with soft calls** once the run is linked:
`MemDoneCallS` with the threaded run replaced by `+inlined` keeping the cache (`InlKeep`, track A)
and the class `MemRunS`. -/
def MemDoneRestDS (r : RealCfg) (snd : Nomm → NeedOrd → Bool) (order : List Noun) (kids : Noun → List Noun)
    (env : CallEnv) (SC0 MO0 : Noun) (inl : Noun → Option Nomm) (P Pf : Noun → Prop) (S : Noun) (xs : GenRest)
    (st : St Noun NeedOrd) (keep : Bool) (DN KIDS ML0 CB SCC CODE LSR JH CACHE0 b ML CACHE : Noun) : Prop :=
  ∃ (cape : Cape) (DATA FOL : Noun) (nm : Nomm) (fuel : Nat), b = C (C cape.toNoun DATA) FOL ∧
    r.info b = ⟨nm, cape, DATA, fuel⟩ ∧ ∃ CA1,
    nock (C inlBody (C (C b (C (C CODE LSR) (C JH CACHE))) compK)) inlBody = some (C nm.toNoun CA1) ∧
    InlKeep inl CACHE CA1 ∧
    MemRunS r snd order kids st env SC0 MO0 inl P Pf S xs CODE (memDCtx SCC (C CODE LSR) JH ML (A 0) b) nm ∧
    ∃ (nex : NextL CSet) (g1 : GenSf (TreapMap mugF)),
      runLCS (envDoneS r snd order kids st) snd Option.none nm (CGoalL.done : CGoalL CSet) [] (GenSf.ofGen gen0)
        = some (nex, g1) ∧
    ∃ ord, shapeCol fuel nex.laz cape = some ord ∧ nex.th.args = [] ∧
    ∃ (nedF : Need) (g2 : Gen (TreapMap mugF)), needOrdAllocRegs ord g1.g = some (nedF, g2) ∧
      isRun (flattenNeed (bakeNeed nedF (Sock.mk cape DATA)).1)
        ((flattenNeed (bakeNeed nedF (Sock.mk cape DATA)).1).headD 0) 0 = true ∧
      (∀ u sf3, coerceLazyLS nedF cape nex.th.there nex.laz ⟨g2, g1.soft⟩ = some (u, sf3) →
        ∀ p ∈ TreapMap.tap sf3.soft, ReqTN p.2.req) ∧
    ∃ sur, sureOf (needToOrd nex.laz.sure.ned) nex.laz.sure.lok cape = some sur ∧
      (∃ s, finishLFCS (S := CSet) (Map := TreapMap mugF) (envDoneS r snd order kids st) snd TreapMap.tap nm ord cape
        (fun n => bakeNeed n (Sock.mk cape DATA)) = some s) ∧
      ∀ (x1 : GenRest) (C1 C2 C3 C4 SURE' : Noun) (prev : NeedOrd), st.ml b = some prev →
        msgOrd (needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1) prev cape ≠ needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1 →
        ∃ t, (∃ s : Straight (TreapMap mugF), C (msgOrd (needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1) prev cape).toNoun t = s.toNoun) ∧ nock (C finBody (C (C (A 0) (msgOrd (needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1) prev cape).toNoun)
              (memFCR keep (wasN (st.sure b)) sur.toNoun
                (needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1).toNoun nex.laz.toNoun nedF.toNoun
                (bakeNeed nedF (Sock.mk cape DATA)).1.toNoun (immNoun (bakeNeed nedF (Sock.mk cape DATA)).2)
                nex.th.there (genNoun g2 x1) nm.toNoun
                (memDCtx SCC (C CODE LSR) JH ML (A 0) b) b ML
                (A 0) (cacheN C1 C2 C3 C4 SURE') (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0)))) finBody
          = some (C (msgOrd (needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1) prev cape).toNoun t)

theorem memDoneCall_of_restDS {r : RealCfg} {snd : Nomm → NeedOrd → Bool} {order : List Noun}
    {kids : Noun → List Noun} {nout : Noun → NeedOrd} {env : CallEnv} {SC0 MO0 : Noun} {inl : Noun → Option Nomm}
    {P Pf : Noun → Prop} {S : Noun} {xs : GenRest} (hrs : r.scc = tapList S) (hPS : ∀ k ∈ tapList S, ¬ P k)
    {st : St Noun NeedOrd} {keep : Bool} {DN KIDS ML0 CB SCC CODE LSR JH CACHE0 b ML CACHE : Noun}
    (hR : LoopR r.scc (fun _ => []) nout (QK env (RKD SC0 MO0 inl Pf) P S xs) st.ml st.sure ML CACHE)
    (h : MemDoneRestDS r snd order kids env SC0 MO0 inl P Pf S xs st keep DN KIDS ML0 CB SCC CODE LSR JH CACHE0 b ML
      CACHE) :
    MemDoneCallS r snd order kids (fun _ => []) nout env (RKD SC0 MO0 inl Pf) P S xs st keep DN KIDS ML0 CB SCC CODE
      LSR JH CACHE0 b ML CACHE := by
  obtain ⟨cape, DATA, FOL, nm, fuel, hb, hinfo, CA1, hinl, hik, hm, nex, g1, hrunL, ord, hcol, hargs, nedF, g2,
    hnoar, hrun, hreq, sur, hsur, hfin, hcs⟩ := h
  exact memDoneCall_ofS r snd order kids nout env SC0 MO0 inl P Pf S xs hrs hPS st keep DN KIDS ML0 CB SCC CODE LSR
    JH CACHE0 b ML CACHE hR cape DATA FOL nm fuel hb hinfo CA1 hinl hik hm nex g1 hrunL ord hcol hargs nedF g2 hnoar
    hrun hreq sur hsur hfin hcs

/-- **`SccLoopAtAStr` from a loop with soft calls** (`memGate_done_realS` with `rKD_sure`,
`sure_miss_of_agree` at the rest of the loop, `memDoneCall_of_restDS` at every call): at a rest
where `calleeCompiled_sccDStr` runs the loop (`LoopRest`), the configuration `cfgRealS r snd order
kids` with `CfgOf` and `Ranked`, the `%may` and `%must` gates, the agreement of `env`, the members
bells, and per `%done` call `MemDoneRestDS`. -/
theorem sccLoopAtD_realS (env : CallEnv) (SC0 MO0 : Noun) (inl : Noun → Option Nomm) (P Pf : Noun → Prop)
    (S CODE JETS CALLS JH : Noun) (x : GenRest) (NR CR : Noun)
    (hx : LoopRest env (RKD SC0 MO0 inl Pf) P S x NR CR) (hPS : ∀ k ∈ tapList S, ¬ P k)
    (hbell : ∀ k ∈ tapList S, ∃ b' : Bell, b'.toNoun = k)
    (r : RealCfg) (snd : Nomm → NeedOrd → Bool) (order : List Noun) (kids : Noun → List Noun)
    (rk : Ranked (cfgRealS r snd order kids)) (nout : Noun → NeedOrd)
    (hcfg : CfgOf (cfgRealS r snd order kids) S (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR)))
    (hmay : MemGate (cfgRealS r snd order kids)
      (LoopRS (cfgRealS r snd order kids).scc (fun _ => []) nout (QK env (RKD SC0 MO0 inl Pf) P S x))
      (csiCtx (A 1) (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR)) S (C CODE (C JETS CALLS)) JH (C NR CR))
      (fun _ => (cfgRealS r snd order kids).none) (A 0) Mode.may (A 0x79616d))
    (hmust : ∀ TOP, TopN (maySweep (cfgRealS r snd order kids) (St.empty : St Noun NeedOrd)).ml TOP →
      MemGate (cfgRealS r snd order kids)
        (LoopRS (cfgRealS r snd order kids).scc (fun _ => []) nout (QK env (RKD SC0 MO0 inl Pf) P S x))
        (csiCtx (A 1) (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR)) S (C CODE (C JETS CALLS)) JH (C NR CR))
        (topOf (cfgRealS r snd order kids) (maySweep (cfgRealS r snd order kids) (St.empty : St Noun NeedOrd))) TOP
        Mode.must (A 0x7473756d))
    (henv : ∀ (s : St Noun NeedOrd), compileSccIn (cfgRealS r snd order kids) false
      (fuelR (cfgRealS r snd order kids) rk) St.empty = some s → ∀ b' : Bell, b'.toNoun ∈ (cfgRealS r snd order kids).scc →
        env.need b' = s.ml b'.toNoun ∧ ∀ v, s.sure b'.toNoun = some v → env.sure b' = v)
    (hcall : ∀ (st : St Noun NeedOrd) (keep : Bool) (b ML CACHE : Noun), b ∈ r.scc →
      LoopR r.scc (fun _ => []) nout (QK env (RKD SC0 MO0 inl Pf) P S x) st.ml st.sure ML CACHE →
      MemDoneRestDS r snd order kids env SC0 MO0 inl P Pf S x st keep (A 1) (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR))
        (A 0) csiBody S CODE (C JETS CALLS) JH (C NR CR) b ML CACHE) :
    SccLoopAtAStr env (RKD SC0 MO0 inl Pf) P S CODE JETS CALLS JH x NR CR := by
  obtain ⟨hA, hR, hc, hmiss⟩ := hx
  have hrs : r.scc = tapList S := hcfg.scc
  have hxS : ∀ b ∈ r.scc, ∀ N u, slot? 31 x.cache = some N → getF mugF b N ≠ some (C (A 0) u) := by
    intro b hb
    refine sure_miss_of_agree hA hPS hbell (fun N hN k hk => ?_) b (hrs ▸ hb)
    rw [hc] at hN
    have : N = NR := by simpa [nock_exec] using hN.symm
    subst this; exact hmiss k hk
  refine ⟨cfgRealS r snd order kids, rk, fun _ => [], nout, hcfg, hmay, ?_, hmust, henv⟩
  exact memGate_done_realS r snd order kids (fun _ => []) nout env (RKD SC0 MO0 inl Pf) P S x rKD_sure
    (fun b hb => hrs ▸ hb) hxS (A 1) _ (A 0) csiBody S CODE (C JETS CALLS) JH (C NR CR)
    (fun st keep b ML CACHE hb hL => memDoneCall_of_restDS hrs hPS hL (hcall st keep b ML CACHE hb hL))

/-! ## The loop data and the induction on height -/

/-- **The loop data of an SCC callee with soft calls** (`SccLoopDataDStr` at `cfgRealS r snd`,
each `%done` call's `MemDoneRestDS` under the hypothesis `IH`). -/
def SccLoopDataDS (env : CallEnv) (SC0 MO0 CODE JETS CALLS JH : Noun) (inl : Noun → Option Nomm)
    (P Pf : Noun → Prop) (S : Noun) (IH : Prop) : Prop :=
  ∀ x NR CR, LoopRest env (RKD SC0 MO0 inl Pf) P S x NR CR →
    ∃ (r : RealCfg) (snd : Nomm → NeedOrd → Bool) (order : List Noun) (kids : Noun → List Noun)
      (rk : Ranked (cfgRealS r snd order kids)) (nout : Noun → NeedOrd),
      CfgOf (cfgRealS r snd order kids) S (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR)) ∧
      MemGate (cfgRealS r snd order kids)
        (LoopRS (cfgRealS r snd order kids).scc (fun _ => []) nout (QK env (RKD SC0 MO0 inl Pf) P S x))
        (csiCtx (A 1) (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR)) S (C CODE (C JETS CALLS)) JH (C NR CR))
        (fun _ => (cfgRealS r snd order kids).none) (A 0) Mode.may (A 0x79616d) ∧
      (∀ TOP, TopN (maySweep (cfgRealS r snd order kids) (St.empty : St Noun NeedOrd)).ml TOP →
        MemGate (cfgRealS r snd order kids)
          (LoopRS (cfgRealS r snd order kids).scc (fun _ => []) nout (QK env (RKD SC0 MO0 inl Pf) P S x))
          (csiCtx (A 1) (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR)) S (C CODE (C JETS CALLS)) JH (C NR CR))
          (topOf (cfgRealS r snd order kids) (maySweep (cfgRealS r snd order kids) (St.empty : St Noun NeedOrd))) TOP
          Mode.must (A 0x7473756d)) ∧
      (∀ (s : St Noun NeedOrd), compileSccIn (cfgRealS r snd order kids) false (fuelR (cfgRealS r snd order kids) rk)
        St.empty = some s → ∀ b' : Bell, b'.toNoun ∈ (cfgRealS r snd order kids).scc →
          env.need b' = s.ml b'.toNoun ∧ ∀ v, s.sure b'.toNoun = some v → env.sure b' = v) ∧
      ∀ (st : St Noun NeedOrd) (keep : Bool) (b ML CACHE : Noun), b ∈ r.scc →
        LoopR r.scc (fun _ => []) nout (QK env (RKD SC0 MO0 inl Pf) P S x) st.ml st.sure ML CACHE → IH →
        MemDoneRestDS r snd order kids env SC0 MO0 inl P Pf S x st keep (A 1)
          (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR)) (A 0) csiBody S CODE (C JETS CALLS) JH (C NR CR) b ML CACHE

/-- **The table's data of one callee with soft members admitted**: a one-bell callee, or an SCC `S`
with, at every `(P, Pf)` above `b`, the loop data at `cfgReal` (`SccLoopDataDStr`) or at
`cfgRealS` (`SccLoopDataDS`). -/
def CalleeHDS (env : CallEnv) (SC0 MO0 CODE JETS CALLS JH : Noun) (inl : Noun → Option Nomm) (ht : Noun → Nat)
    (D : Bell → Prop) (b : Bell) : Prop :=
  OneCalleeA env SC0 CODE CALLS inl b ∨
    ∃ S, getF mugF b.toNoun SC0 = some (C (A 0) S) ∧
      ((∀ n, S ≠ C n (C (A 0) (A 0))) ∨ ∃ n, S = C n (C (A 0) (A 0)) ∧ CalleeIn CALLS n n) ∧
      ∀ P Pf, Above ht (ht b.toNoun) P Pf →
        SccLoopDataDStr env SC0 MO0 CODE JETS CALLS JH inl P Pf S (CCBelowD env SC0 MO0 CODE JETS CALLS JH inl ht D (ht b.toNoun)) ∨
        SccLoopDataDS env SC0 MO0 CODE JETS CALLS JH inl P Pf S (CCBelowD env SC0 MO0 CODE JETS CALLS JH inl ht D (ht b.toNoun))

/-- **One step of the induction on height with soft members**: `calleeCompiled_stepHDStr` with
`sccLoopAtD_realS` for an SCC whose loop runs at `cfgRealS`. -/
theorem calleeCompiled_stepHDS {env : CallEnv} {SC0 MO0 CODE JETS CALLS JH : Noun} {inl : Noun → Option Nomm}
    {ht : Noun → Nat} {D : Bell → Prop} (hsg : SccsGood SC0)
    (hcj : IsMap mugF CALLS ∧ ∀ k v, Get CALLS k v → IsSet mugF v) (hht : HtScc SC0 ht)
    {b : Bell} (hT : CalleeHDS env SC0 MO0 CODE JETS CALLS JH inl ht D b)
    (hIH : CCBelowD env SC0 MO0 CODE JETS CALLS JH inl ht D (ht b.toNoun))
    {P Pf : Noun → Prop} (hab : Above ht (ht b.toNoun) P Pf) {ctx : Noun} (hctx : CtxK CODE JETS CALLS JH ctx)
    {nb : NeedOrd} (hnb : env.need b = some nb) :
    CalleeCompiledP env (RKD SC0 MO0 inl Pf) P ctx b nb := by
  obtain ⟨h7, hl, hj, h107⟩ := hctx
  have hnPf : ∀ k, Pf k → ht k ≠ ht b.toNoun := fun k hk e => Nat.lt_irrefl _ (e ▸ hab.2 k hk)
  rcases hT with hone | ⟨S, hsc, hnd, hdat⟩
  · obtain ⟨cape, DATA, FOL, nm, fuel, envb, p, st, rfl, hsc, hinl, hcalls, hcode, hn, hax, hfix, hone⟩ := hone
    have e : nb = st.need := Option.some.inj (hnb.symm.trans hone.2.2.1)
    subst e
    exact calleeCompiled_oneKD h7 hl hj h107 env envb cape DATA FOL nm fuel p st inl hsc hinl hcalls hcode hn hax
      hfix hone P Pf (fun h => hnPf _ (hab.1 _ h) rfl) (fun h => hnPf _ h rfl)
  · have hS : ∀ k ∈ tapList S, ht k = ht b.toNoun := hht _ _ hsc
    have hPfS : ∀ k ∈ tapList S, ¬ Pf k := fun k hk h => hnPf k h (hS k hk)
    have hPS : ∀ k ∈ tapList S, ¬ P k := fun k hk h => hPfS k hk (hab.1 k h)
    have hbell : ∀ k ∈ tapList S, ∃ b' : Bell, b'.toNoun = k := fun k hk => ((hsg _ _ hsc).2.2 k hk).2
    refine calleeCompiled_sccDStr h7 hl hj h107 env inl P Pf b nb S hsg hcj hsc hnd hPS hPfS hnb fun x NR CR hx => ?_
    rcases hdat P Pf hab with hd | hd
    · obtain ⟨r, order, kids, rk, nout, hcfg, hmay, hmust, henv, hcall⟩ := hd x NR CR hx
      exact sccLoopAtD_realStr env SC0 MO0 inl P Pf S CODE JETS CALLS JH x NR CR hx hPS hbell r order kids rk nout
        hcfg hmay hmust henv fun st keep b0 ML CACHE hb hL => hcall st keep b0 ML CACHE hb hL hIH
    · obtain ⟨r, snd, order, kids, rk, nout, hcfg, hmay, hmust, henv, hcall⟩ := hd x NR CR hx
      exact sccLoopAtD_realS env SC0 MO0 inl P Pf S CODE JETS CALLS JH x NR CR hx hPS hbell r snd order kids rk nout
        hcfg hmay hmust henv fun st keep b0 ML CACHE hb hL => hcall st keep b0 ML CACHE hb hL hIH

/-- **Every callee is compiled, by induction on height, with soft members admitted.** -/
theorem calleeCompiled_heightsDS {env : CallEnv} {SC0 MO0 CODE JETS CALLS JH : Noun} {inl : Noun → Option Nomm}
    {ht : Noun → Nat} {D : Bell → Prop} (hsg : SccsGood SC0)
    (hcj : IsMap mugF CALLS ∧ ∀ k v, Get CALLS k v → IsSet mugF v) (hht : HtScc SC0 ht)
    (hT : ∀ b, D b → CalleeHDS env SC0 MO0 CODE JETS CALLS JH inl ht D b) :
    ∀ (b : Bell) (P Pf : Noun → Prop) (ctx : Noun) (nb : NeedOrd), D b → Above ht (ht b.toNoun) P Pf →
      CtxK CODE JETS CALLS JH ctx → env.need b = some nb → CalleeCompiledP env (RKD SC0 MO0 inl Pf) P ctx b nb := by
  have H : ∀ m, CCBelowD env SC0 MO0 CODE JETS CALLS JH inl ht D m := by
    intro m
    induction m with
    | zero => intro b' P' Pf' ctx' nb' _ hlt; exact absurd hlt (Nat.not_lt_zero _)
    | succ m ih =>
      intro b' P' Pf' ctx' nb' hD hlt hab hctx hnb
      exact calleeCompiled_stepHDS hsg hcj hht (hT b' hD) (cCBelowD_mono (Nat.le_of_lt_succ hlt) ih) hab hctx hnb
  exact fun b P Pf ctx nb hD hab hctx hnb => H (ht b.toNoun + 1) b P Pf ctx nb hD (Nat.lt_succ_self _) hab hctx hnb

/-- **At the gate** (`P = Pf = ∅`), with soft members admitted. -/
theorem calleeCompiled_heights0DS {env : CallEnv} {SC0 MO0 CODE JETS CALLS JH : Noun} {inl : Noun → Option Nomm}
    {ht : Noun → Nat} {D : Bell → Prop} (hsg : SccsGood SC0)
    (hcj : IsMap mugF CALLS ∧ ∀ k v, Get CALLS k v → IsSet mugF v) (hht : HtScc SC0 ht)
    (hT : ∀ b, D b → CalleeHDS env SC0 MO0 CODE JETS CALLS JH inl ht D b) {b : Bell} {ctx : Noun} {nb : NeedOrd}
    (hD : D b) (hctx : CtxK CODE JETS CALLS JH ctx) (hnb : env.need b = some nb) :
    CalleeCompiled env (RKD SC0 MO0 inl (fun _ => False)) ctx b nb := by
  intro x NR MO SC RS hA hR hc h0
  obtain ⟨CA', h1, h2, h3, h4, h5⟩ := calleeCompiled_heightsDS hsg hcj hht hT b _ _ ctx nb hD (above_empty ht _) hctx hnb
    x NR MO SC RS (agreeIP_of_E _ hA) hR hc h0
  exact ⟨CA', h1, h2, agreeE_of_IP h3, h4, h5⟩

/-- **The table's data of one callee with static calls and soft members admitted**: a one-bell
callee, or an SCC with `SccLoopDataSDStr` (no soft call, static calls) or `SccLoopDataDS` (soft
members, calls under the induction hypothesis). -/
def CalleeHSDS (env : CallEnv) (SC0 MO0 CODE JETS CALLS JH : Noun) (inl : Noun → Option Nomm) (ht : Noun → Nat)
    (D : Bell → Prop) (b : Bell) : Prop :=
  OneCalleeA env SC0 CODE CALLS inl b ∨
    ∃ S, getF mugF b.toNoun SC0 = some (C (A 0) S) ∧
      ((∀ n, S ≠ C n (C (A 0) (A 0))) ∨ ∃ n, S = C n (C (A 0) (A 0)) ∧ CalleeIn CALLS n n) ∧
      ∀ P Pf, Above ht (ht b.toNoun) P Pf →
        SccLoopDataSDStr env SC0 MO0 CODE JETS CALLS JH inl P Pf S ht D (ht b.toNoun) ∨
        SccLoopDataDS env SC0 MO0 CODE JETS CALLS JH inl P Pf S (CCBelowD env SC0 MO0 CODE JETS CALLS JH inl ht D (ht b.toNoun))

theorem calleeH_of_SDS {env : CallEnv} {SC0 MO0 CODE JETS CALLS JH : Noun} {inl : Noun → Option Nomm}
    {ht : Noun → Nat} {D : Bell → Prop} (hsg : SccsGood SC0) (hht : HtScc SC0 ht) {b : Bell}
    (H : CalleeHSDS env SC0 MO0 CODE JETS CALLS JH inl ht D b) : CalleeHDS env SC0 MO0 CODE JETS CALLS JH inl ht D b := by
  rcases H with hone | ⟨S, hsc, hnd, hdat⟩
  · exact Or.inl hone
  · refine Or.inr ⟨S, hsc, hnd, fun P Pf hab => ?_⟩
    have hS : ∀ k ∈ tapList S, ht k = ht b.toNoun := hht _ _ hsc
    have hPS : ∀ k ∈ tapList S, ¬ P k := fun k hk hp =>
      Nat.lt_irrefl _ ((hS k hk) ▸ hab.2 k (hab.1 k hp))
    rcases hdat P Pf hab with hd | hd
    · exact Or.inl (sccLoopData_of_SDStr hPS (fun k hk => ((hsg _ _ hsc).2.2 k hk).2) hab hS hd)
    · exact Or.inr hd

/-! ## The sweeps' gates carry over to `cfgRealS` -/

/-- **`member` of the sweeps is the same at `cfgRealS` and `cfgReal`** (`compRealS` differs from
`compReal` only on `%done`). -/
theorem member_cfgRealS_sweep (r : RealCfg) (snd : Nomm → NeedOrd → Bool) (order : List Noun)
    (kids : Noun → List Noun) (top : Noun → NeedOrd) (b : Noun) (mode : Mode) (hm : mode ≠ Mode.done) (keep : Bool)
    (st : St Noun NeedOrd) :
    member (cfgRealS r snd order kids) top b mode keep st = member (cfgReal r order kids) top b mode keep st := by
  cases mode with
  | done => exact absurd rfl hm
  | may => rfl
  | must => rfl

/-- The `%may` sweep is the same at `cfgRealS` and `cfgReal`. -/
theorem maySweep_cfgRealS (r : RealCfg) (snd : Nomm → NeedOrd → Bool) (order : List Noun)
    (kids : Noun → List Noun) (st : St Noun NeedOrd) :
    maySweep (cfgRealS r snd order kids) st = maySweep (cfgReal r order kids) st := rfl

/-- **A `%may` / `%must` gate at `cfgReal` is one at `cfgRealS`** (so track I's sweep gates for
`cfgRealShape r xs` give those of `cfgRealS { r with laze := lazeReal xs } snd`). -/
theorem memGate_cfgRealS_of (r : RealCfg) (snd : Nomm → NeedOrd → Bool) (order : List Noun)
    (kids : Noun → List Noun) {R : (Noun → Option NeedOrd) → (Noun → Option NeedOrd) → Noun → Noun → Prop}
    {ctx : Noun} {top : Noun → NeedOrd} {TOP : Noun} {mode : Mode} {MODE : Noun} (hm : mode ≠ Mode.done)
    (h : MemGate (cfgReal r order kids) R ctx top TOP mode MODE) :
    MemGate (cfgRealS r snd order kids) R ctx top TOP mode MODE := by
  intro st keep b ML CA hb hR
  rw [member_cfgRealS_sweep r snd order kids top b mode hm keep st]
  exact h st keep b ML CA hb hR

/-- A table without soft members is one with them admitted. -/
theorem calleeHSDS_of_Str {env : CallEnv} {SC0 MO0 CODE JETS CALLS JH : Noun} {inl : Noun → Option Nomm}
    {ht : Noun → Nat} {D : Bell → Prop} {b : Bell} (H : CalleeHSDStr env SC0 MO0 CODE JETS CALLS JH inl ht D b) :
    CalleeHSDS env SC0 MO0 CODE JETS CALLS JH inl ht D b := by
  rcases H with hone | ⟨S, hsc, hnd, hdat⟩
  · exact Or.inl hone
  · exact Or.inr ⟨S, hsc, hnd, fun P Pf hab => Or.inl (hdat P Pf hab)⟩

end Compiler
end Formalization
