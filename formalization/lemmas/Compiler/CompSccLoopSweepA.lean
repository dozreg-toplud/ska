import lemmas.Compiler.CompSccOfSweepMiss
import lemmas.Compiler.CompRunShapeMember

/-! # The sweeps' calls with track A's branch (README Gaps 21.21)

Track A's `memShape_branchA6` (`CompRunShapeMember.lean`) proves the branch of `member` off
`%done` (`MemShapeBranchA`, track I's `MemShapeBranch` restated) under per-member hypotheses.
Here they are discharged from the loop's own facts where they are the loop's:

* **`memShapeBranch_iffA`**: `MemShapeBranch x .. ↔ MemShapeBranchA x.jet x.cod ..` is `Iff.rfl`;
* `memYG`, `memYX`, `memY_genNoun`: the rest `memY CA1` of the bunt `gen` at a run state is the
  noun `genNoun (memYG st) (memYX st CA1)`, so the door of `+run-shape` is `compCore`;
* `needRead_memberT`: `+callee-need` at a member reads `map-local`, else `top` (`MlExact`, `TopH`);
* `SweepCallLeft`: what ONE direct call still takes beyond the loop's facts: the callee is a member,
  or outside the SCC, not in progress and a hit of `nary.cache` at `CA1` (the miss inside
  `+run-shape` is not in track A's `ShapeCall`); no ring (`cole`); not jetted; the soft test returns;
* `ShapeOKQ Q`: `ShapeOK` with a per-call predicate `Q`; `shapeOK_of_Q`;
* **`shapeCall_of_left`**: `ShapeCall` from `SweepCallLeft` and the loop's facts (`need` and `sure`
  by `cne_read` / `csu_gate` with `needRead_memberT` / `hit_of_agreeIP`, `hot` from the context);
* `SweepLeft`: what ONE sweep call of `member` takes; **`memSweepCall_of_A`**: `MemSweepCall` at
  `RK` from it (`memShape_branchA6`, then `memSweepCall_of_KR` with the cache `CA1` unchanged,
  `memY_cache`). -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.SccLoop

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## The two statements of the branch are one -/

/-- **Track A's statement is track I's**, word for word. -/
theorem memShapeBranch_iffA (x : ShapeX) (mode : Mode) (env : CallEnv) (cape : Cape) (DATA FOL : Noun) (nm : Nomm)
    (fuel : Nat) (keep : Bool) (SCC LONG JH ML TOP CA1 CTX : Noun) (col sur : NeedOrd) (G2 : Noun) :
    MemShapeBranch x mode env cape DATA FOL nm fuel keep SCC LONG JH ML TOP CA1 CTX col sur G2 ↔
      MemShapeBranchA x.jet x.cod mode env cape DATA FOL nm fuel keep SCC LONG JH ML TOP CA1 CTX col sur G2 :=
  Iff.rfl

theorem lazeReal_eqA (x : ShapeX) (mode : Mode) (env : CallEnv) (m : MemInfo) :
    lazeReal x mode env m = lazeRealA x.jet x.cod mode env m := rfl

/-! ## The door of `+run-shape` at the rest `memY CA1` -/

/-- The `gen` part of `memY CA1` at the run state `st`. -/
def memYG (st : RSt CSet) : Gen (TreapMap mugF) :=
  ⟨0, 1, st.idg, false, HoonMap.empty, HoonMap.empty, HoonMap.empty⟩

/-- The rest part of `memY CA1` at the run state `st`. -/
noncomputable def memYX (st : RSt CSet) (CA1 : Noun) : GenRest := ⟨CA1, A 0, HoonSet.toNoun st.sofs⟩

theorem memY_genNoun (st : RSt CSet) (CA1 : Noun) :
    rsGenNoun st (memY CA1) = genNoun (memYG st) (memYX st CA1) := rfl

/-! ## `+callee-need` at a member, any `top` -/

/-- **`NeedRead` at a member from `MlExact` and `TopH`**: an entry of `map-local` is read (`loc`),
and with none the entry of `top` (`top`). -/
theorem needRead_memberT {SCC LONG JH ML TOP B : Noun} {ml : Noun → Option NeedOrd} (hml : MlExact ml ML)
    {top : Noun → NeedOrd} (hT : TopH top TOP) {b : Bell} (hin : hasInF mugF b.toNoun SCC = some true)
    (x : GenRest) :
    NeedRead (memDCtx SCC LONG JH ML TOP B) x b ((ml b.toNoun).getD (top b.toNoun)) := by
  have h12 : slot? 12 (memDCtx SCC LONG JH ML TOP B) = some SCC := by simp [memDCtx, nock_exec]
  have h110 : slot? 110 (memDCtx SCC LONG JH ML TOP B) = some ML := by simp [memDCtx, nock_exec]
  have h222 : slot? 222 (memDCtx SCC LONG JH ML TOP B) = some TOP := by simp [memDCtx, nock_exec]
  cases hm : ml b.toNoun with
  | none =>
    have hg : getF mugF b.toNoun ML = some (A 0) :=
      getF_none hml.1 fun v hv => by obtain ⟨n, t, hn, -⟩ := hml.2.1 _ v hv; rw [hm] at hn; cases hn
    obtain ⟨TGU, hTG, hcase, hfall⟩ := hT b.toNoun
    refine NeedRead.top h12 hin h110 hg h222 ?_
    simp only [Option.getD]
    rcases hcase with rfl | ⟨u, rfl⟩
    · right
      refine ⟨hTG, needOrd_toNoun_inj ?_⟩
      rw [← hfall]
      simp [fallNone, NeedOrd.toNoun, Tag.none]
    · left
      simp only [fallNone] at hfall
      rw [hTG, hfall]
  | some n =>
    obtain ⟨t, ht⟩ := hml.2.2 _ n hm
    exact NeedRead.loc h12 hin h110 (getF_some hml.1 ht) (by simp [nock_exec])

/-- `NeedRead` reads the rest only through its cache. -/
theorem needRead_cache {ctx : Noun} {x x' : GenRest} {b : Bell} {nb : NeedOrd} (he : x.cache = x'.cache)
    (h : NeedRead ctx x b nb) : NeedRead ctx x' b nb := by
  cases h with
  | loc h1 h2 h3 h4 h5 => exact NeedRead.loc h1 h2 h3 h4 h5
  | top h1 h2 h3 h4 h5 h6 => exact NeedRead.top h1 h2 h3 h4 h5 h6
  | nary h1 h2 h3 h4 h5 => exact NeedRead.nary h1 h2 (by rw [← he]; exact h3) h4 h5

/-- `SureNoun` reads the rest only through its cache. -/
theorem sureNoun_cache {env : CallEnv} {x x' : GenRest} {b : Bell} (he : x.cache = x'.cache)
    (h : SureNoun env b x) : SureNoun env b x' := by
  unfold SureNoun at h ⊢
  rw [← he]
  exact h

/-! ## One direct call -/

/-- **What one direct call of a sweep's member run takes beyond the loop's facts**: the callee is a
member, or it is not in progress and a hit of `nary.cache` at `CA1` (no miss of `+callee-compiled`
inside `+run-shape`); no ring for it in `call.cole` (`cole`); it is not jetted (`jet`); the model's
soft test returns (`soft`). -/
structure SweepCallLeft (scc : List Noun) (jet : Bell → Bool) (P : Noun → Prop) (CA1 ctx : Noun) (env : ShapeEnv)
    (p q : Nomm) (b : Bell) (k : Option Noun) (sup : Option Nomm) : Prop where
  callee : b.toNoun ∈ scc ∨
    (¬ P b.toNoun ∧ ∃ NR u, slot? 2 CA1 = some NR ∧ getF mugF b.toNoun NR = some (C (A 0) u))
  cole : ∃ cole, slot? 6846 ctx = some cole ∧ getF mugF b.toNoun cole = some (A 0)
  jet : jet b = false
  soft : ∀ ned : NeedOrd, (konstCell k = true → ned = NeedOrd.this) →
    (konstCell k = false → env.need b = some ned) → softTest env p q b k ned (env.sure b) sup ≠ Option.none

/-- `ShapeOK` with a per-call predicate `Q` in place of `ShapeCall` at the rests of `E`. -/
def ShapeOKQ (Q : Nomm → Nomm → Bell → Option Noun → Option Nomm → Prop) : Option Nomm → Nomm → Prop
  | sup, Nomm.n2 p q (some (b, k)) => Q p q b k sup ∧ ShapeOKQ Q sup p ∧ ShapeOKQ Q sup q
  | sup, Nomm.n2 p q Option.none => ShapeOKQ Q sup p ∧ ShapeOKQ Q sup q
  | sup, Nomm.n7 p q => ShapeOKQ Q sup p ∧ ShapeOKQ Q (some p) q
  | sup, Nomm.n6 p q r => ShapeOKQ Q sup p ∧ ShapeOKQ Q sup q ∧ ShapeOKQ Q sup r
  | sup, Nomm.n3 p => ShapeOKQ Q sup p
  | sup, Nomm.n4 p => ShapeOKQ Q sup p
  | sup, Nomm.cons p q => ShapeOKQ Q sup p ∧ ShapeOKQ Q sup q
  | sup, Nomm.n5 p q => ShapeOKQ Q sup p ∧ ShapeOKQ Q sup q
  | sup, Nomm.n10 _ v q => ShapeOKQ Q sup v ∧ ShapeOKQ Q sup q
  | _, _ => True

theorem shapeOK_of_Q {ctx : Noun} {env : ShapeEnv} {E : RsRest → Prop}
    {Q : Nomm → Nomm → Bell → Option Noun → Option Nomm → Prop}
    (hQ : ∀ p q b k sup, Q p q b k sup → ∀ y, E y → ShapeCall ctx env p q b k sup y) (n : Nomm) :
    ∀ sup, ShapeOKQ Q sup n → ShapeOK ctx env E sup n := by
  induction n with
  | cons p q ihp ihq => intro sup h; simp only [ShapeOKQ] at h; simp only [ShapeOK]; exact ⟨ihp sup h.1, ihq sup h.2⟩
  | n0 => intro _ _; simp [ShapeOK]
  | n1 => intro _ _; simp [ShapeOK]
  | n2 p q i ihp ihq =>
    intro sup h
    rcases i with _ | ⟨b, k⟩
    · simp only [ShapeOKQ] at h; simp only [ShapeOK]; exact ⟨ihp sup h.1, ihq sup h.2⟩
    · simp only [ShapeOKQ] at h; simp only [ShapeOK]; exact ⟨hQ _ _ _ _ _ h.1, ihp sup h.2.1, ihq sup h.2.2⟩
  | n3 p ih => intro sup h; simp only [ShapeOKQ] at h; simp only [ShapeOK]; exact ih sup h
  | n4 p ih => intro sup h; simp only [ShapeOKQ] at h; simp only [ShapeOK]; exact ih sup h
  | n5 p q ihp ihq => intro sup h; simp only [ShapeOKQ] at h; simp only [ShapeOK]; exact ⟨ihp sup h.1, ihq sup h.2⟩
  | n6 p q r ihp ihq ihr =>
    intro sup h; simp only [ShapeOKQ] at h; simp only [ShapeOK]; exact ⟨ihp sup h.1, ihq sup h.2.1, ihr sup h.2.2⟩
  | n7 p q ihp ihq => intro sup h; simp only [ShapeOKQ] at h; simp only [ShapeOK]; exact ⟨ihp sup h.1, ihq (some p) h.2⟩
  | n10 a v q ihv ihq => intro sup h; simp only [ShapeOKQ] at h; simp only [ShapeOK]; exact ⟨ihv sup h.1, ihq sup h.2⟩
  | n11s => intro _ _; simp [ShapeOK]
  | n11d => intro _ _; simp [ShapeOK]
  | n12 => intro _ _; simp [ShapeOK]
  | mean => intro _ _; simp [ShapeOK]

/-- The call environment the sweeps see at the loop state `st`. -/
noncomputable abbrev envSw (r : RealCfg) (xs : ShapeX) (order : List Noun) (kids : Noun → List Noun)
    (top : Noun → NeedOrd) (st : St Noun NeedOrd) : CallEnv :=
  envView r.env r.scc (viewN top st) (viewS (cfgRealShape r xs order kids) st)

/-- **`ShapeCall` from `SweepCallLeft` and the loop's facts**: at a member, `+callee-need` reads
`map-local` / `top` (`MlExact`, `TopH`) and `+callee-sure` the members' `sure` entries at `CA1`
(`SureHolds`); outside, both read the hit at `CA1`, which agrees with `env` (`QK` at `CA1`). -/
theorem shapeCall_of_left {r : RealCfg} {xs : ShapeX} {order : List Noun} {kids : Noun → List Noun} {env : CallEnv}
    {RR : GenRest → Prop} {P : Noun → Prop} {S : Noun} {xg : GenRest} {st : St Noun NeedOrd}
    {top : Noun → NeedOrd} {SCC LONG JH ML TOP B CA1 : Noun}
    (hre : r.env = env) (hrs : r.scc = tapList S)
    (hset : ∀ k, hasInF mugF k SCC = some (decide (k ∈ r.scc)))
    (hml : MlExact st.ml ML) (hT : TopH top TOP)
    (hQ1 : QK env RR P S xg CA1) (hsh : SureHolds r.scc st.sure CA1)
    {p q : Nomm} {b : Bell} {k : Option Noun} {sup : Option Nomm}
    (h : SweepCallLeft r.scc xs.jet P CA1 (memDCtx SCC LONG JH ML TOP B)
      (shapeEnvOfA xs.jet xs.cod (envSw r xs order kids top st)) p q b k sup) :
    ∀ y, y = memY CA1 → ShapeCall (memDCtx SCC LONG JH ML TOP B)
      (shapeEnvOfA xs.jet xs.cod (envSw r xs order kids top st)) p q b k sup y := by
  rintro y rfl
  have h7 : slot? 7 (memDCtx SCC LONG JH ML TOP B) = some compK := rfl
  have hhot : ∃ jh, slot? 54 (memDCtx SCC LONG JH ML TOP B) = some jh := ⟨JH, by simp [memDCtx, nock_exec]⟩
  have hc : CompIn (memDCtx SCC LONG JH ML TOP B) := (comp_ctx_pill _ h7).1
  have key : ∃ nb, (envSw r xs order kids top st).need b = some nb ∧
      ∀ x : GenRest, x.cache = CA1 →
        NeedRead (memDCtx SCC LONG JH ML TOP B) x b nb ∧ SureNoun (envSw r xs order kids top st) b x := by
    by_cases hbm : b.toNoun ∈ r.scc
    · refine ⟨(st.ml b.toNoun).getD (top b.toNoun), by simp [envSw, envView, hbm, viewN], fun x hx => ?_⟩
      have hin : hasInF mugF b.toNoun SCC = some true := by rw [hset]; simp [hbm]
      refine ⟨needRead_memberT hml hT hin x, ?_⟩
      obtain ⟨S0, h31, hall⟩ := hsh
      refine ⟨S0, by rw [hx]; exact h31, ?_⟩
      have hs : (envSw r xs order kids top st).sure b = (st.sure b.toNoun).getD NeedOrd.none := by
        simp [envSw, envView, hbm, viewS, cfgRealShape, cfgReal]
      rw [hs]
      rcases hall _ hbm with ⟨v, hv, hg⟩ | ⟨hv, hg⟩
      · left; rw [hv]; exact hg
      · right; rw [hv]; exact ⟨hg, rfl⟩
    · rcases h.callee with hm | ⟨hnp, NR, u, hNR, hu⟩
      · exact absurd hm hbm
      have hin : hasInF mugF b.toNoun SCC = some false := by rw [hset]; simp [hbm]
      have hA := hQ1.1
      obtain ⟨-, NR', MO, SC, INL, SU, hcx, -, -, hag', -⟩ := hA
      have e2 : NR' = NR := by
        change CA1 = cacheN NR' MO SC INL SU at hcx
        rw [hcx] at hNR; simpa [cacheN, nock_exec] using hNR
      subst e2
      obtain ⟨⟨nb, hnb, -⟩, -⟩ := hag' b u hu
      have hag : (envSw r xs order kids top st).need b = env.need b ∧
          (envSw r xs order kids top st).sure b = env.sure b := by
        simp [envSw, envView, hbm, hre]
      have hnbR : (envSw r xs order kids top st).need b = some nb := by rw [hag.1, hnb]
      refine ⟨nb, hnbR, fun x hx => ?_⟩
      have hS12 : slot? 12 (memDCtx SCC LONG JH ML TOP B) = some SCC := by simp [memDCtx, nock_exec]
      have hnot : ¬ (P b.toNoun ∨ b.toNoun ∈ tapList S) := by
        rintro (h1 | h1)
        · exact hnp h1
        · exact hbm (hrs ▸ h1)
      obtain ⟨hr, hs⟩ := hit_of_agreeIP (x := ⟨CA1, xg.soft, xg.sofs⟩) hS12 hin hnbR hag hQ1.1 hnot
        (by exact hNR) hu
      exact ⟨needRead_cache hx.symm hr, sureNoun_cache hx.symm hs⟩
  obtain ⟨nb, hnb, hrd⟩ := key
  refine ⟨fun _ => ⟨nb, hnb, fun st1 => ?_⟩, h.cole, hhot, h.jet, fun st1 => ?_, h.soft⟩
  · simp only [rsDoor, memY_genNoun]
    exact cne_read h7 b nb _ h.cole hhot (hrd _ rfl).1 _
  · simp only [rsDoor, memY_genNoun]
    exact csu_gate hc _ b _ (hrd _ rfl).2 _

/-! ## One sweep call of `member` -/

/-- **What one `%must` / `%may` call of `member` takes beyond the loop's facts** (at the state `st`,
`top` `top`): the member's `r.info`, `+inlined` (its cache `CA1`) keeping the cache, the class of
track A's induction (`RsClsE6`), its direct calls in the code table (`CallCode`), every direct call
`SweepCallLeft`, and the model's `lazeReal` returning. -/
def SweepLeft (r : RealCfg) (xs : ShapeX) (order : List Noun) (kids : Noun → List Noun) (inl : Noun → Option Nomm)
    (P : Noun → Prop) (mode : Mode) (top : Noun → NeedOrd) (TOP : Noun) (st : St Noun NeedOrd)
    (SCC CODE LSR JH b ML CACHE : Noun) : Prop :=
  ∃ (cape : Cape) (DATA FOL : Noun) (nm : Nomm) (fuel : Nat), b = C (C cape.toNoun DATA) FOL ∧
    r.info b = ⟨nm, cape, DATA, fuel⟩ ∧ ∃ CA1,
    nock (C inlBody (C (C b (C (C CODE LSR) (C JH CACHE))) compK)) inlBody = some (C nm.toNoun CA1) ∧
    InlKeep inl CACHE CA1 ∧
    RsClsE6 (shapeEnvOfA xs.jet xs.cod (envSw r xs order kids top st)) nm ∧
    CallCode CODE (shapeCE (shapeEnvOfA xs.jet xs.cod (envSw r xs order kids top st))) nm ∧
    ShapeOKQ (SweepCallLeft r.scc xs.jet P CA1 (memDCtx SCC (C CODE LSR) JH ML TOP b)
      (shapeEnvOfA xs.jet xs.cod (envSw r xs order kids top st))) Option.none nm ∧
    (lazeReal xs mode (envSw r xs order kids top st) ⟨nm, cape, DATA, fuel⟩).isSome

/-- **`MemSweepCall` from track A's branch** (`RK`, `outC := fun _ => []`): `memShape_branchA6`
gives `MemShapeBranch` with the cache `CA1` unchanged (`memY_cache`), and `memSweepCall_of_KR`
gives the rest from the loop's `LoopRS`. Its hypotheses: `SweepLeft` per call, the loop-level
facts `hre` (`r.env` is `QK`'s `env`), `hset` (the noun `SCC` is the set of `r.scc`), `hcn` (the
code table), `hT` (`top`). -/
theorem memSweepCall_of_A {r : RealCfg} {xs : ShapeX} {order : List Noun} {kids : Noun → List Noun}
    {nout : Noun → NeedOrd} {env : CallEnv} {SC0 : Noun} {inl : Noun → Option Nomm} {P : Noun → Prop}
    {S : Noun} {x : GenRest} {mode : Mode} {top : Noun → NeedOrd} {TOP : Noun} {st : St Noun NeedOrd} {keep : Bool}
    {DN KIDS ML0 CB SCC CODE LSR JH CACHE0 b ML CACHE : Noun}
    (hm : mode = Mode.must ∨ mode = Mode.may)
    (hrs : r.scc = tapList S) (hPS : ∀ k ∈ tapList S, ¬ P k) (hre : r.env = env)
    (hset : ∀ k, hasInF mugF k SCC = some (decide (k ∈ r.scc)))
    (hcn : CodeNomms xs.cod CODE) (hT : TopH top TOP)
    (hR : LoopRS r.scc (fun _ => []) nout (QK env (RK SC0 inl) P S x) st.ml st.sure ML CACHE)
    (h : SweepLeft r xs order kids inl P mode top TOP st SCC CODE LSR JH b ML CACHE) :
    MemSweepCall r xs order kids (fun _ => []) nout env (RK SC0 inl) P S x mode top TOP st keep DN KIDS ML0 CB
      SCC CODE LSR JH CACHE0 b ML CACHE := by
  obtain ⟨cape, DATA, FOL, nm, fuel, hb, hinfo, CA1, hinl, hik, hcls, hcc, hcalls, hlr⟩ := h
  subst hb
  have hsh : SureHolds (tapList S) st.sure CACHE := by rw [← hrs]; exact hR.1.2.1
  have hQ0 : QK env (RKP SC0 inl (fun _ => False)) P S x CACHE :=
    qK_congr (fun y => rKP_empty.symm) hR.1.2.2.2
  obtain ⟨-, -, hQ1, hS1⟩ := eM_start (Pf := fun _ => False) hPS hQ0 hsh hik
  have hml : MlExact st.ml ML := hR.1.1
  obtain ⟨⟨col, sur⟩, hlr'⟩ := Option.isSome_iff_exists.1 hlr
  have hs := shapeOK_of_Q (E := (· = memY CA1))
    (fun p q b' k sup hq => shapeCall_of_left (S := S) hre hrs hset hml hT hQ1 (by rw [hrs]; exact hS1) hq) nm
    Option.none hcalls
  obtain ⟨st1, hbr⟩ := memShape_branchA6 mode hm xs.jet xs.cod (envSw r xs order kids top st) cape DATA FOL nm fuel
    keep SCC (C CODE LSR) JH ML TOP CA1 (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0) rfl
    (cod := CODE) (by simp [nock_exec]) hcn hcls hcc hs col sur hlr'
  exact memSweepCall_of_KR hrs hPS hR ⟨cape, DATA, FOL, nm, fuel, rfl, hinfo, CA1, hinl, hik, col, sur, _,
    (memShapeBranch_iffA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).2 hbr, Or.inl (memY_cache st1 CA1)⟩

end Compiler
end Formalization
