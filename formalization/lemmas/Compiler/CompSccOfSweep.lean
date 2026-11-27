import lemmas.Compiler.CompSccOfSoft
import lemmas.Compiler.CompSccLoopSweepStep
import lemmas.Compiler.CompMonoLinkStr

/-!
# The loop data with the sweeps' gates proved (README Gaps 19 (g), the sweeps)

The loop data of `CompSccOfStr.lean` (`SccLoopDataSDStr`) and `CompSccOfSoft.lean`
(`SccLoopDataDS`) took the `%may` and `%must` member gates (`MemGate`) as fields.  Track I proved
them (`memGate_sweep_real`, `CompSccLoopSweepStep.lean`) for the configuration `cfgRealShape r xs`
(the sweeps modelled by track A's `+run-shape`, `lazeReal xs`) from `MemSweepCall` at every call:
the branch's pill computation `MemShapeBranch` (track A) and the cache the branch leaves.  Here:

* `MemSweepCallK`: `MemSweepCall` with `+inlined` keeping the cache (`InlKeep`, track A) and the
  cache after the branch in one of two cases: **the cache of `+inlined` unchanged**
  (`slot? 510 G2 = some CA1`: every `+callee-need` of the run is a jet, a member of the SCC, or a
  hit of `+callee-compiled`, track A's `ShapeCall`), or a cache that keeps `QK` and the members'
  `sure` entries (the case of a callee compiled from inside `+run-shape`: a miss of
  `+callee-compiled`, not linked);
* **`memSweepCall_of_KD`** (`RKD`, by `eMD_start`) and **`memSweepCall_of_KR`** (`RK`, by
  `eM_start` at no bell in progress): the first case discharged from `LoopRS`;
* `cfgRealShape_eq`: `cfgRealShape r xs = cfgReal r` when `r.laze = lazeReal xs`;
* **`memGate_may_KD`**, **`memGate_must_KD`**: the gates of the loop data, from `MemSweepCallK`;
* `SccLoopDataSDSw` / `SccLoopDataDSSw`: the loop data with `MemSweepCallK` per call in place of
  the gates, **`sccLoopDataSDStr_of_Sw`**, **`sccLoopDataDS_of_Sw`**; the table `CalleeHSDSw`,
  **`calleeHSDS_of_Sw`**;
* `TopLoopSh` (the hypotheses of track I's `csi_gate_ranked_shape` with `MemSweepCallK`),
  `TopDecSh`, **`topDec_of_Sh`**.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.SccLoop

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## One sweep call -/

/-- **What one `%must` / `%may` call of `member` takes, with the cache in two cases**
(`outC := fun _ => []`): the member's `r.info`, `+inlined` (its cache `CA1`) keeping the cache
(`InlKeep`), the branch's pill computation `MemShapeBranch` (track A), and the cache at axis `510`
of the `gen` the branch leaves: `CA1` itself (no callee compiled inside `+run-shape`), or a cache
keeping `QK` and the members' `sure` entries. -/
def MemSweepCallK (r : RealCfg) (xs : ShapeX) (order : List Noun) (kids : Noun → List Noun)
    (nout : Noun → NeedOrd) (envK : CallEnv) (RR : GenRest → Prop) (inl : Noun → Option Nomm) (P : Noun → Prop)
    (S : Noun) (x : GenRest) (mode : Mode) (top : Noun → NeedOrd) (TOP : Noun)
    (st : St Noun NeedOrd) (keep : Bool) (DN KIDS ML0 CB SCC CODE LSR JH CACHE0 b ML CACHE : Noun) : Prop :=
  ∃ (cape : Cape) (DATA FOL : Noun) (nm : Nomm) (fuel : Nat), b = C (C cape.toNoun DATA) FOL ∧
    r.info b = ⟨nm, cape, DATA, fuel⟩ ∧ ∃ CA1,
    nock (C inlBody (C (C b (C (C CODE LSR) (C JH CACHE))) compK)) inlBody = some (C nm.toNoun CA1) ∧
    InlKeep inl CACHE CA1 ∧
    ∃ (col sur : NeedOrd) (G2 : Noun),
      MemShapeBranch xs mode (envView r.env r.scc (viewN top st) (viewS (cfgRealShape r xs order kids) st))
        cape DATA FOL nm fuel keep SCC (C CODE LSR) JH ML TOP CA1 (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0)
        col sur G2 ∧
    (slot? 510 G2 = some CA1 ∨
      ∃ C1 C2 C3 C4 SURE, slot? 510 G2 = some (cacheN C1 C2 C3 C4 SURE) ∧ QK envK RR P S x (cacheN C1 C2 C3 C4 SURE) ∧
        SureHolds r.scc st.sure (cacheN C1 C2 C3 C4 SURE))

/-- **`MemSweepCall` from `MemSweepCallK` at `RKD`**: when the branch leaves the cache of
`+inlined`, `QK` and the members' `sure` entries hold there by `eMD_start` (the loop's `QK` and
`SureHolds` at `CACHE`, `InlKeep`). -/
theorem memSweepCall_of_KD {r : RealCfg} {xs : ShapeX} {order : List Noun} {kids : Noun → List Noun}
    {nout : Noun → NeedOrd} {env : CallEnv} {SC0 MO0 : Noun} {inl : Noun → Option Nomm} {P Pf : Noun → Prop}
    {S : Noun} {x : GenRest} {mode : Mode} {top : Noun → NeedOrd} {TOP : Noun} {st : St Noun NeedOrd} {keep : Bool}
    {DN KIDS ML0 CB SCC CODE LSR JH CACHE0 b ML CACHE : Noun}
    (hrs : r.scc = tapList S) (hPS : ∀ k ∈ tapList S, ¬ P k)
    (hR : LoopRS r.scc (fun _ => []) nout (QK env (RKD SC0 MO0 inl Pf) P S x) st.ml st.sure ML CACHE)
    (h : MemSweepCallK r xs order kids nout env (RKD SC0 MO0 inl Pf) inl P S x mode top TOP st keep DN KIDS ML0 CB SCC
      CODE LSR JH CACHE0 b ML CACHE) :
    MemSweepCall r xs order kids (fun _ => []) nout env (RKD SC0 MO0 inl Pf) P S x mode top TOP st keep DN KIDS ML0 CB
      SCC CODE LSR JH CACHE0 b ML CACHE := by
  obtain ⟨cape, DATA, FOL, nm, fuel, hb, hinfo, CA1, hinl, hik, col, sur, G2, hbrn, hc⟩ := h
  refine ⟨cape, DATA, FOL, nm, fuel, hb, hinfo, CA1, hinl, col, sur, G2, hbrn, ?_⟩
  rcases hc with hc | ⟨C1, C2, C3, C4, SURE, hG, hQ, hS⟩
  · have hsh : SureHolds (tapList S) st.sure CACHE := by rw [← hrs]; exact hR.1.2.1
    obtain ⟨hA1, -, hQ1, hS1⟩ := eMD_start hPS hR.1.2.2.2 hsh hik
    obtain ⟨-, C1, C2, C3, C4, SU, hc1, -⟩ := hA1
    change CA1 = cacheN C1 C2 C3 C4 SU at hc1
    subst hc1
    exact ⟨C1, C2, C3, C4, SU, hc, hQ1, by rw [hrs]; exact hS1, fun b' _ k hk => by simp at hk⟩
  · exact ⟨C1, C2, C3, C4, SURE, hG, hQ, hS, fun b' _ k hk => by simp at hk⟩

/-- `QK` reads its rest predicate only through `R`. -/
theorem qK_congr {env : CallEnv} {R R' : GenRest → Prop} {P : Noun → Prop} {S : Noun} {x : GenRest} {CA : Noun}
    (hRR : ∀ y, R y ↔ R' y) (h : QK env R P S x CA) : QK env R' P S x CA :=
  ⟨h.1, h.2.1, (hRR _).1 h.2.2.1, h.2.2.2⟩

/-- **`MemSweepCall` from `MemSweepCallK` at `RK`** (the top loop): `eM_start` at no bell in
progress (`RKP` at `∅` is `RK`, `rKP_empty`). -/
theorem memSweepCall_of_KR {r : RealCfg} {xs : ShapeX} {order : List Noun} {kids : Noun → List Noun}
    {nout : Noun → NeedOrd} {env : CallEnv} {SC0 : Noun} {inl : Noun → Option Nomm} {P : Noun → Prop}
    {S : Noun} {x : GenRest} {mode : Mode} {top : Noun → NeedOrd} {TOP : Noun} {st : St Noun NeedOrd} {keep : Bool}
    {DN KIDS ML0 CB SCC CODE LSR JH CACHE0 b ML CACHE : Noun}
    (hrs : r.scc = tapList S) (hPS : ∀ k ∈ tapList S, ¬ P k)
    (hR : LoopRS r.scc (fun _ => []) nout (QK env (RK SC0 inl) P S x) st.ml st.sure ML CACHE)
    (h : MemSweepCallK r xs order kids nout env (RK SC0 inl) inl P S x mode top TOP st keep DN KIDS ML0 CB SCC
      CODE LSR JH CACHE0 b ML CACHE) :
    MemSweepCall r xs order kids (fun _ => []) nout env (RK SC0 inl) P S x mode top TOP st keep DN KIDS ML0 CB
      SCC CODE LSR JH CACHE0 b ML CACHE := by
  obtain ⟨cape, DATA, FOL, nm, fuel, hb, hinfo, CA1, hinl, hik, col, sur, G2, hbrn, hc⟩ := h
  refine ⟨cape, DATA, FOL, nm, fuel, hb, hinfo, CA1, hinl, col, sur, G2, hbrn, ?_⟩
  rcases hc with hc | ⟨C1, C2, C3, C4, SURE, hG, hQ, hS⟩
  · have hsh : SureHolds (tapList S) st.sure CACHE := by rw [← hrs]; exact hR.1.2.1
    have hQ0 : QK env (RKP SC0 inl (fun _ => False)) P S x CACHE :=
      qK_congr (fun y => rKP_empty.symm) hR.1.2.2.2
    obtain ⟨hA1, -, hQ1, hS1⟩ := eM_start (Pf := fun _ => False) hPS hQ0 hsh hik
    obtain ⟨-, C1, C2, C3, C4, SU, hc1, -⟩ := hA1
    change CA1 = cacheN C1 C2 C3 C4 SU at hc1
    subst hc1
    exact ⟨C1, C2, C3, C4, SU, hc, qK_congr (fun y => rKP_empty) hQ1, by rw [hrs]; exact hS1,
      fun b' _ k hk => by simp at hk⟩
  · exact ⟨C1, C2, C3, C4, SURE, hG, hQ, hS, fun b' _ k hk => by simp at hk⟩

/-! ## The gates of the loop data -/

/-- `cfgRealShape r xs` is `cfgReal r` when `r`'s `laze` is `lazeReal xs`. -/
theorem cfgRealShape_eq {r : RealCfg} {xs : ShapeX} (h : r.laze = lazeReal xs) (order : List Noun)
    (kids : Noun → List Noun) : cfgRealShape r xs order kids = cfgReal r order kids := by
  obtain ⟨scc, info, env, laze⟩ := r
  simp only at h
  subst h
  rfl

/-- **The `%may` gate of the loop data** at `cfgReal r` (`r.laze = lazeReal xs`), from
`MemSweepCallK` at every call (`memGate_sweep_real` with `rKD_sure`, `memSweepCall_of_KD`). -/
theorem memGate_may_KD (r : RealCfg) (xs : ShapeX) (hlz : r.laze = lazeReal xs) (order : List Noun)
    (kids : Noun → List Noun) (nout : Noun → NeedOrd) (env : CallEnv) (SC0 MO0 : Noun) (inl : Noun → Option Nomm)
    (P Pf : Noun → Prop) (S CODE JETS CALLS JH : Noun) (x : GenRest) (NR CR : Noun)
    (hrs : r.scc = tapList S) (hPS : ∀ k ∈ tapList S, ¬ P k)
    (hxS : ∀ b ∈ r.scc, ∀ N u, slot? 31 x.cache = some N → getF mugF b N ≠ some (C (A 0) u))
    (hcall : ∀ (st : St Noun NeedOrd) (keep : Bool) (b ML CACHE : Noun), b ∈ r.scc →
      LoopRS r.scc (fun _ => []) nout (QK env (RKD SC0 MO0 inl Pf) P S x) st.ml st.sure ML CACHE →
      MemSweepCallK r xs order kids nout env (RKD SC0 MO0 inl Pf) inl P S x Mode.may (fun _ => NeedOrd.none) (A 0) st
        keep (A 1) (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR)) (A 0) csiBody S CODE (C JETS CALLS) JH (C NR CR) b ML
        CACHE) :
    MemGate (cfgReal r order kids) (LoopRS (cfgReal r order kids).scc (fun _ => []) nout (QK env (RKD SC0 MO0 inl Pf) P S x))
      (csiCtx (A 1) (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR)) S (C CODE (C JETS CALLS)) JH (C NR CR))
      (fun _ => (cfgReal r order kids).none) (A 0) Mode.may (A 0x79616d) := by
  rw [← cfgRealShape_eq hlz order kids]
  exact memGate_sweep_real r xs order kids (fun _ => []) nout env (RKD SC0 MO0 inl Pf) P S x rKD_sure
    (fun b hb => hrs ▸ hb) hxS Mode.may (by decide) (fun _ => NeedOrd.none) (A 0) topH_nil (A 1) _ (A 0) csiBody S CODE
    (C JETS CALLS) JH (C NR CR) fun st keep b ML CACHE hb hL => memSweepCall_of_KD hrs hPS hL (hcall st keep b ML CACHE hb hL)

/-- **The `%must` gate of the loop data**, at every `TOP` of `TopN` of the `%may` sweep's `ml`. -/
theorem memGate_must_KD (r : RealCfg) (xs : ShapeX) (hlz : r.laze = lazeReal xs) (order : List Noun)
    (kids : Noun → List Noun) (nout : Noun → NeedOrd) (env : CallEnv) (SC0 MO0 : Noun) (inl : Noun → Option Nomm)
    (P Pf : Noun → Prop) (S CODE JETS CALLS JH : Noun) (x : GenRest) (NR CR : Noun)
    (hrs : r.scc = tapList S) (hPS : ∀ k ∈ tapList S, ¬ P k)
    (hxS : ∀ b ∈ r.scc, ∀ N u, slot? 31 x.cache = some N → getF mugF b N ≠ some (C (A 0) u))
    (TOP : Noun) (hT : TopN (maySweep (cfgReal r order kids) (St.empty : St Noun NeedOrd)).ml TOP)
    (hcall : ∀ (st : St Noun NeedOrd) (keep : Bool) (b ML CACHE : Noun), b ∈ r.scc →
      LoopRS r.scc (fun _ => []) nout (QK env (RKD SC0 MO0 inl Pf) P S x) st.ml st.sure ML CACHE →
      MemSweepCallK r xs order kids nout env (RKD SC0 MO0 inl Pf) inl P S x Mode.must
        (topOf (cfgReal r order kids) (maySweep (cfgReal r order kids) (St.empty : St Noun NeedOrd))) TOP st keep
        (A 1) (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR)) (A 0) csiBody S CODE (C JETS CALLS) JH (C NR CR) b ML
        CACHE) :
    MemGate (cfgReal r order kids) (LoopRS (cfgReal r order kids).scc (fun _ => []) nout (QK env (RKD SC0 MO0 inl Pf) P S x))
      (csiCtx (A 1) (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR)) S (C CODE (C JETS CALLS)) JH (C NR CR))
      (topOf (cfgReal r order kids) (maySweep (cfgReal r order kids) (St.empty : St Noun NeedOrd))) TOP Mode.must
      (A 0x7473756d) := by
  rw [← cfgRealShape_eq hlz order kids] at hT hcall ⊢
  exact memGate_sweep_real r xs order kids (fun _ => []) nout env (RKD SC0 MO0 inl Pf) P S x rKD_sure
    (fun b hb => hrs ▸ hb) hxS Mode.must (by decide) _ TOP (topH_of_topN hT) (A 1) _ (A 0) csiBody S CODE
    (C JETS CALLS) JH (C NR CR) fun st keep b ML CACHE hb hL => memSweepCall_of_KD hrs hPS hL (hcall st keep b ML CACHE hb hL)

/-- `hxS` at a rest where the loop runs (`sure_miss_of_agree`, as in `sccLoopAtD_realStr`). -/
theorem loopRest_sureMiss {env : CallEnv} {SC0 MO0 : Noun} {inl : Noun → Option Nomm} {P Pf : Noun → Prop}
    {S : Noun} {x : GenRest} {NR CR : Noun} (hx : LoopRest env (RKD SC0 MO0 inl Pf) P S x NR CR)
    (hPS : ∀ k ∈ tapList S, ¬ P k) (hbell : ∀ k ∈ tapList S, ∃ b' : Bell, b'.toNoun = k) {bs : List Noun}
    (hrs : bs = tapList S) :
    ∀ b ∈ bs, ∀ N u, slot? 31 x.cache = some N → getF mugF b N ≠ some (C (A 0) u) := by
  obtain ⟨hA, hR, hc, hmiss⟩ := hx
  intro b hb
  refine sure_miss_of_agree hA hPS hbell (fun N hN k hk => ?_) b (hrs ▸ hb)
  rw [hc] at hN
  have : N = NR := by simpa [nock_exec] using hN.symm
  subst this; exact hmiss k hk

/-! ## The loop data with `MemSweepCallK` per call -/

/-- **`SccLoopDataSDStr` with the sweeps' gates replaced by their calls**: `r.laze = lazeReal xs`
(so `cfgReal r = cfgRealShape r xs`), and `MemSweepCallK` at every `%may` call and at every `%must`
call (at every `TOP` of `TopN`). -/
def SccLoopDataSDSw (env : CallEnv) (SC0 MO0 CODE JETS CALLS JH : Noun) (inl : Noun → Option Nomm)
    (P Pf : Noun → Prop) (S : Noun) (ht : Noun → Nat) (D : Bell → Prop) (h : Nat) : Prop :=
  ∀ x NR CR, LoopRest env (RKD SC0 MO0 inl Pf) P S x NR CR →
    ∃ (r : RealCfg) (xs : ShapeX) (order : List Noun) (kids : Noun → List Noun) (rk : Ranked (cfgReal r order kids))
      (nout : Noun → NeedOrd), r.laze = lazeReal xs ∧
      (∀ b : Bell, D b → ht b.toNoun < h → r.env.need b = env.need b ∧ r.env.sure b = env.sure b) ∧
      CfgOf (cfgReal r order kids) S (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR)) ∧
      (∀ (st : St Noun NeedOrd) (keep : Bool) (b ML CACHE : Noun), b ∈ r.scc →
        LoopRS r.scc (fun _ => []) nout (QK env (RKD SC0 MO0 inl Pf) P S x) st.ml st.sure ML CACHE →
        MemSweepCallK r xs order kids nout env (RKD SC0 MO0 inl Pf) inl P S x Mode.may (fun _ => NeedOrd.none) (A 0) st
          keep (A 1) (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR)) (A 0) csiBody S CODE (C JETS CALLS) JH (C NR CR) b
          ML CACHE) ∧
      (∀ TOP, TopN (maySweep (cfgReal r order kids) (St.empty : St Noun NeedOrd)).ml TOP →
        ∀ (st : St Noun NeedOrd) (keep : Bool) (b ML CACHE : Noun), b ∈ r.scc →
        LoopRS r.scc (fun _ => []) nout (QK env (RKD SC0 MO0 inl Pf) P S x) st.ml st.sure ML CACHE →
        MemSweepCallK r xs order kids nout env (RKD SC0 MO0 inl Pf) inl P S x Mode.must
          (topOf (cfgReal r order kids) (maySweep (cfgReal r order kids) (St.empty : St Noun NeedOrd))) TOP st keep
          (A 1) (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR)) (A 0) csiBody S CODE (C JETS CALLS) JH (C NR CR) b ML
          CACHE) ∧
      (∀ (s : St Noun NeedOrd), compileSccIn (cfgReal r order kids) false (fuelR (cfgReal r order kids) rk) St.empty
        = some s → ∀ b' : Bell, b'.toNoun ∈ (cfgReal r order kids).scc →
          env.need b' = s.ml b'.toNoun ∧ ∀ v, s.sure b'.toNoun = some v → env.sure b' = v) ∧
      ∀ (st : St Noun NeedOrd) (keep : Bool) (b ML CACHE : Noun), b ∈ r.scc →
        LoopR r.scc (fun _ => []) nout (QK env (RKD SC0 MO0 inl Pf) P S x) st.ml st.sure ML CACHE →
        MemDoneRestSDStr r order kids env SC0 MO0 inl P Pf S x st keep (A 1)
          (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR)) (A 0) csiBody S CODE (C JETS CALLS) JH (C NR CR) b ML CACHE ht D h

/-- **The old loop data from the new** (the gates by `memGate_may_KD`, `memGate_must_KD`). -/
theorem sccLoopDataSDStr_of_Sw {env : CallEnv} {SC0 MO0 CODE JETS CALLS JH : Noun} {inl : Noun → Option Nomm}
    {P Pf : Noun → Prop} {S : Noun} {ht : Noun → Nat} {D : Bell → Prop} {h : Nat}
    (hPS : ∀ k ∈ tapList S, ¬ P k) (hbell : ∀ k ∈ tapList S, ∃ b' : Bell, b'.toNoun = k)
    (H : SccLoopDataSDSw env SC0 MO0 CODE JETS CALLS JH inl P Pf S ht D h) :
    SccLoopDataSDStr env SC0 MO0 CODE JETS CALLS JH inl P Pf S ht D h := by
  intro x NR CR hx
  obtain ⟨r, xs, order, kids, rk, nout, hlz, hre, hcfg, hmay, hmust, henv, hcall⟩ := H x NR CR hx
  have hrs : r.scc = tapList S := hcfg.scc
  have hxS := loopRest_sureMiss hx hPS hbell hrs
  exact ⟨r, order, kids, rk, nout, hre, hcfg,
    memGate_may_KD r xs hlz order kids nout env SC0 MO0 inl P Pf S CODE JETS CALLS JH x NR CR hrs hPS hxS hmay,
    fun TOP hT => memGate_must_KD r xs hlz order kids nout env SC0 MO0 inl P Pf S CODE JETS CALLS JH x NR CR hrs hPS
      hxS TOP hT (hmust TOP hT), henv, hcall⟩

/-- **`SccLoopDataDS` (soft members, `cfgRealS r snd`) with the sweeps' gates replaced by their
calls** (the sweeps are the same at `cfgReal r` and `cfgRealS r snd`). -/
def SccLoopDataDSSw (env : CallEnv) (SC0 MO0 CODE JETS CALLS JH : Noun) (inl : Noun → Option Nomm)
    (P Pf : Noun → Prop) (S : Noun) (IH : Prop) : Prop :=
  ∀ x NR CR, LoopRest env (RKD SC0 MO0 inl Pf) P S x NR CR →
    ∃ (r : RealCfg) (xs : ShapeX) (snd : Nomm → NeedOrd → Bool) (order : List Noun) (kids : Noun → List Noun)
      (rk : Ranked (cfgRealS r snd order kids)) (nout : Noun → NeedOrd), r.laze = lazeReal xs ∧
      CfgOf (cfgRealS r snd order kids) S (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR)) ∧
      (∀ (st : St Noun NeedOrd) (keep : Bool) (b ML CACHE : Noun), b ∈ r.scc →
        LoopRS r.scc (fun _ => []) nout (QK env (RKD SC0 MO0 inl Pf) P S x) st.ml st.sure ML CACHE →
        MemSweepCallK r xs order kids nout env (RKD SC0 MO0 inl Pf) inl P S x Mode.may (fun _ => NeedOrd.none) (A 0) st
          keep (A 1) (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR)) (A 0) csiBody S CODE (C JETS CALLS) JH (C NR CR) b
          ML CACHE) ∧
      (∀ TOP, TopN (maySweep (cfgReal r order kids) (St.empty : St Noun NeedOrd)).ml TOP →
        ∀ (st : St Noun NeedOrd) (keep : Bool) (b ML CACHE : Noun), b ∈ r.scc →
        LoopRS r.scc (fun _ => []) nout (QK env (RKD SC0 MO0 inl Pf) P S x) st.ml st.sure ML CACHE →
        MemSweepCallK r xs order kids nout env (RKD SC0 MO0 inl Pf) inl P S x Mode.must
          (topOf (cfgReal r order kids) (maySweep (cfgReal r order kids) (St.empty : St Noun NeedOrd))) TOP st keep
          (A 1) (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR)) (A 0) csiBody S CODE (C JETS CALLS) JH (C NR CR) b ML
          CACHE) ∧
      (∀ (s : St Noun NeedOrd), compileSccIn (cfgRealS r snd order kids) false (fuelR (cfgRealS r snd order kids) rk)
        St.empty = some s → ∀ b' : Bell, b'.toNoun ∈ (cfgRealS r snd order kids).scc →
          env.need b' = s.ml b'.toNoun ∧ ∀ v, s.sure b'.toNoun = some v → env.sure b' = v) ∧
      ∀ (st : St Noun NeedOrd) (keep : Bool) (b ML CACHE : Noun), b ∈ r.scc →
        LoopR r.scc (fun _ => []) nout (QK env (RKD SC0 MO0 inl Pf) P S x) st.ml st.sure ML CACHE → IH →
        MemDoneRestDS r snd order kids env SC0 MO0 inl P Pf S x st keep (A 1)
          (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR)) (A 0) csiBody S CODE (C JETS CALLS) JH (C NR CR) b ML CACHE

/-- **The old soft loop data from the new** (`memGate_may_KD`, `memGate_must_KD`, carried over to
`cfgRealS` by `memGate_cfgRealS_of`). -/
theorem sccLoopDataDS_of_Sw {env : CallEnv} {SC0 MO0 CODE JETS CALLS JH : Noun} {inl : Noun → Option Nomm}
    {P Pf : Noun → Prop} {S : Noun} {IH : Prop}
    (hPS : ∀ k ∈ tapList S, ¬ P k) (hbell : ∀ k ∈ tapList S, ∃ b' : Bell, b'.toNoun = k)
    (H : SccLoopDataDSSw env SC0 MO0 CODE JETS CALLS JH inl P Pf S IH) :
    SccLoopDataDS env SC0 MO0 CODE JETS CALLS JH inl P Pf S IH := by
  intro x NR CR hx
  obtain ⟨r, xs, snd, order, kids, rk, nout, hlz, hcfg, hmay, hmust, henv, hcall⟩ := H x NR CR hx
  have hrs : r.scc = tapList S := hcfg.scc
  have hxS := loopRest_sureMiss hx hPS hbell hrs
  exact ⟨r, snd, order, kids, rk, nout, hcfg,
    memGate_cfgRealS_of r snd order kids (by decide)
      (memGate_may_KD r xs hlz order kids nout env SC0 MO0 inl P Pf S CODE JETS CALLS JH x NR CR hrs hPS hxS hmay),
    fun TOP hT => memGate_cfgRealS_of r snd order kids (by decide)
      (memGate_must_KD r xs hlz order kids nout env SC0 MO0 inl P Pf S CODE JETS CALLS JH x NR CR hrs hPS hxS TOP hT
        (hmust TOP hT)), henv, hcall⟩

/-- **The table's data of one callee with the sweeps' calls** (`CalleeHSDS` with
`SccLoopDataSDSw` / `SccLoopDataDSSw`). -/
def CalleeHSDSw (env : CallEnv) (SC0 MO0 CODE JETS CALLS JH : Noun) (inl : Noun → Option Nomm) (ht : Noun → Nat)
    (D : Bell → Prop) (b : Bell) : Prop :=
  OneCalleeA env SC0 CODE CALLS inl b ∨
    ∃ S, getF mugF b.toNoun SC0 = some (C (A 0) S) ∧
      ((∀ n, S ≠ C n (C (A 0) (A 0))) ∨ ∃ n, S = C n (C (A 0) (A 0)) ∧ CalleeIn CALLS n n) ∧
      ∀ P Pf, Above ht (ht b.toNoun) P Pf →
        SccLoopDataSDSw env SC0 MO0 CODE JETS CALLS JH inl P Pf S ht D (ht b.toNoun) ∨
        SccLoopDataDSSw env SC0 MO0 CODE JETS CALLS JH inl P Pf S (CCBelowD env SC0 MO0 CODE JETS CALLS JH inl ht D (ht b.toNoun))

theorem calleeHSDS_of_Sw {env : CallEnv} {SC0 MO0 CODE JETS CALLS JH : Noun} {inl : Noun → Option Nomm}
    {ht : Noun → Nat} {D : Bell → Prop} (hsg : SccsGood SC0) (hht : HtScc SC0 ht) {b : Bell}
    (H : CalleeHSDSw env SC0 MO0 CODE JETS CALLS JH inl ht D b) : CalleeHSDS env SC0 MO0 CODE JETS CALLS JH inl ht D b := by
  rcases H with hone | ⟨S, hsc, hnd, hdat⟩
  · exact Or.inl hone
  · refine Or.inr ⟨S, hsc, hnd, fun P Pf hab => ?_⟩
    have hS : ∀ k ∈ tapList S, ht k = ht b.toNoun := hht _ _ hsc
    have hPS : ∀ k ∈ tapList S, ¬ P k := fun k hk hp =>
      Nat.lt_irrefl _ ((hS k hk) ▸ hab.2 k (hab.1 k hp))
    have hbell : ∀ k ∈ tapList S, ∃ b' : Bell, b'.toNoun = k := fun k hk => ((hsg _ _ hsc).2.2 k hk).2
    rcases hdat P Pf hab with hd | hd
    · exact Or.inl (sccLoopDataSDStr_of_Sw hPS hbell hd)
    · exact Or.inr (sccLoopDataDS_of_Sw hPS hbell hd)

/-! ## The top loop -/

/-- **The top loop's data with the gates proved** (track I's `csi_gate_ranked_shape`): the
configuration `cfgRealShape r xs`, `Q := QK env (RK SC0 inl) P SCC x`, `MemSweepCallK` at every
sweep call (`RK`), `MemDoneCallStr` at every `%done` call, and the sample facts. -/
def TopLoopSh (SCC CODE JETS CALLS JH NARY CR : Noun) : Prop :=
  ∃ (r : RealCfg) (xs : ShapeX) (order : List Noun) (kids : Noun → List Noun) (rk : Ranked (cfgRealShape r xs order kids))
    (nout : Noun → NeedOrd) (env : CallEnv) (SC0 : Noun) (inl : Noun → Option Nomm) (P : Noun → Prop) (x : GenRest),
    SamOK SCC CALLS NARY ∧ (∃ b ∈ tapList SCC, getF mugF b NARY = some (A 0)) ∧
    ((∀ n, SCC ≠ C n (C (A 0) (A 0))) ∨ ∃ n, SCC = C n (C (A 0) (A 0)) ∧ CalleeIn CALLS n n) ∧
    CfgOf (cfgRealShape r xs order kids) SCC (kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR)) ∧
    (∀ k ∈ tapList SCC, ∃ b' : Bell, b'.toNoun = k) ∧ (∀ k ∈ tapList SCC, ¬ P k) ∧
    (∀ b ∈ r.scc, ∀ N u, slot? 31 x.cache = some N → getF mugF b N ≠ some (C (A 0) u)) ∧
    (∀ (st : St Noun NeedOrd) (keep : Bool) (b ML CACHE : Noun), b ∈ r.scc →
      LoopRS r.scc (fun _ => []) nout (QK env (RK SC0 inl) P SCC x) st.ml st.sure ML CACHE →
      MemSweepCallK r xs order kids nout env (RK SC0 inl) inl P SCC x Mode.may (fun _ => NeedOrd.none) (A 0) st keep
        (A 1) (kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR)) (A 0) csiBody SCC CODE (C JETS CALLS) JH (C NARY CR)
        b ML CACHE) ∧
    (∀ (st : St Noun NeedOrd) (keep : Bool) (b ML CACHE : Noun), b ∈ r.scc →
      LoopR r.scc (fun _ => []) nout (QK env (RK SC0 inl) P SCC x) st.ml st.sure ML CACHE →
      MemDoneCallStr { r with laze := lazeReal xs } order kids (fun _ => []) nout env (RK SC0 inl) P SCC x st keep (A 1)
        (kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR)) (A 0) csiBody SCC CODE (C JETS CALLS) JH (C NARY CR) b ML
        CACHE) ∧
    (∀ TOP, TopN (maySweep (cfgRealShape r xs order kids) (St.empty : St Noun NeedOrd)).ml TOP →
      ∀ (st : St Noun NeedOrd) (keep : Bool) (b ML CACHE : Noun), b ∈ r.scc →
      LoopRS r.scc (fun _ => []) nout (QK env (RK SC0 inl) P SCC x) st.ml st.sure ML CACHE →
      MemSweepCallK r xs order kids nout env (RK SC0 inl) inl P SCC x Mode.must
        (topOf (cfgRealShape r xs order kids) (maySweep (cfgRealShape r xs order kids) (St.empty : St Noun NeedOrd)))
        TOP st keep (A 1) (kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR)) (A 0) csiBody SCC CODE (C JETS CALLS) JH
        (C NARY CR) b ML CACHE) ∧
    (∀ CA, QK env (RK SC0 inl) P SCC x CA → ∃ NR REST, CA = C NR REST ∧ IsMap mugF NR) ∧
    SureHolds r.scc (St.empty : St Noun NeedOrd).sure (C NARY CR) ∧ QK env (RK SC0 inl) P SCC x (C NARY CR)

/-- **`TopLoopS` from `TopLoopSh`**: the three gates by `memGate_may_K`, `memGate_done_KStr`,
`memGate_must_K` (track I), the sweeps' calls by `memSweepCall_of_KR`. -/
theorem topLoopS_of_Sh {SCC CODE JETS CALLS JH NARY CR : Noun} (H : TopLoopSh SCC CODE JETS CALLS JH NARY CR) :
    TopLoopS SCC CODE JETS CALLS JH NARY CR := by
  obtain ⟨r, xs, order, kids, rk, nout, env, SC0, inl, P, x, hsam, hmiss, hnd, hcfg, hbell, hPS, hxS, hmay, hdone, hmust,
    hQ, hsu0, hq0⟩ := H
  have hrs : r.scc = tapList SCC := hcfg.scc
  have hS : ∀ b ∈ r.scc, b ∈ tapList SCC := fun b hb => hrs ▸ hb
  exact ⟨cfgRealShape r xs order kids, rk, r.scc, fun _ => [], nout, QK env (RK SC0 inl) P SCC x, St.empty, hsam, hmiss,
    hnd, hcfg, hbell,
    memGate_may_K r xs order kids (fun _ => []) nout env SC0 inl P SCC CODE JETS CALLS JH x NARY CR hS hxS
      fun st keep b ML CACHE hb hL => memSweepCall_of_KR hrs hPS hL (hmay st keep b ML CACHE hb hL),
    memGate_done_KStr { r with laze := lazeReal xs } order kids (fun _ => []) nout env SC0 inl P SCC CODE JETS CALLS JH x
      NARY CR hS hxS hdone,
    fun TOP hT => memGate_must_K r xs order kids (fun _ => []) nout env SC0 inl P SCC CODE JETS CALLS JH x NARY CR hS hxS
      _ TOP hT fun st keep b ML CACHE hb hL => memSweepCall_of_KR hrs hPS hL (hmust TOP hT st keep b ML CACHE hb hL),
    hQ, fun _ => rfl, hsu0, hq0⟩

/-- What decodes the top loop's map, with the gates proved: `TopLoopSh` or a lone bell. -/
def TopDecSh (SCC CODE JETS CALLS JH CACHE : Noun) : Prop :=
  (∃ NARY CR, CACHE = C NARY CR ∧ TopLoopSh SCC CODE JETS CALLS JH NARY CR) ∨ TopOneS SCC CODE JETS CALLS JH CACHE

theorem topDec_of_Sh {SCC CODE JETS CALLS JH CACHE : Noun} (H : TopDecSh SCC CODE JETS CALLS JH CACHE) :
    TopDec SCC CODE JETS CALLS JH CACHE := by
  rcases H with ⟨NARY, CR, hc, h⟩ | h
  · exact Or.inl ⟨NARY, CR, hc, topLoopS_of_Sh h⟩
  · exact Or.inr h

end Compiler
end Formalization
