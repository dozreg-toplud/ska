import lemmas.Compiler.CompSccLoopMemStep
import lemmas.Compiler.CompRunTNClass
import lemmas.Compiler.CompSccLoopPrint

/-!
# The gate with callees of any SCC, the loop's `hloop` at `AgreeIP` (README Gaps 19 (g))

`SccLoopAt` (`CompSccOfAny.lean`) asks track I's loop at every rest `x` of a miss and carries
`PrintId`.  Here:

* `RKP SC0 inl Pf`: the rest predicate `RK` with the bells `Pf` of the SCCs whose loops are
  running missing in `nary.cache` (a nested miss inside a member run must keep them missing:
  `QK`'s last clause and `SureHolds` at a member with no `sure` entry need it); `rKP_sure`
  (blind to `sure.cache`, what `memGate_done_real` asks), `rKP_empty` (`Pf` empty is `RK`).
* `SccLoopAtA`: `SccLoopAt` without `PrintId` (`printId_pill`), asked only at rests with
  `AgreeIP env P x`, `RKP`, the cache `[NR CR]` and the members of `S` missing in `NR`
  (`calleeCompiled_sccA` has these facts where it uses the loop).
* **`calleeCompiled_sccA`**: `CalleeCompiledP env (RKP SC0 inl Pf) P` for a callee of any SCC.
* **`cu_gate_dir_sccA`**: the gate on `DirOk` with `SccCalleeA` (the new loop hypothesis).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.SccLoop

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## The rest predicate with bells in progress -/

/-- **`RK` with the bells `Pf` missing in `nary.cache`** (`Pf`: the members of the SCCs whose
loops are running; `nary.cache` gets them only at the end of their loop). -/
def RKP (SC0 : Noun) (inl : Noun → Option Nomm) (Pf : Noun → Prop) (x : GenRest) : Prop :=
  RK SC0 inl x ∧ ∀ NR, slot? 2 x.cache = some NR → ∀ k, Pf k → getF mugF k NR = some (A 0)

/-- `RKP` does not read `sure.cache`. -/
theorem rKP_sure {SC0 : Noun} {inl : Noun → Option Nomm} {Pf : Noun → Prop} :
    ∀ NR MO SC INL SU SU' s f : Noun, RKP SC0 inl Pf ⟨cacheN NR MO SC INL SU, s, f⟩ →
      RKP SC0 inl Pf ⟨cacheN NR MO SC INL SU', s, f⟩ := by
  intro NR MO SC INL SU SU' s f h
  refine ⟨rK_sure _ _ _ _ _ _ _ _ h.1, fun N hN k hk => h.2 N ?_ k hk⟩
  have e : slot? 2 (cacheN NR MO SC INL SU') = some N := hN
  rw [cacheN_slot2] at e
  rw [← e]; exact cacheN_slot2 _ _ _ _ _

theorem rKP_empty {SC0 : Noun} {inl : Noun → Option Nomm} {x : GenRest} :
    RKP SC0 inl (fun _ => False) x ↔ RK SC0 inl x :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ _ _ h => h.elim⟩⟩

theorem rKP_mono {SC0 : Noun} {inl : Noun → Option Nomm} {Pf Pf' : Noun → Prop} {x y : GenRest}
    (hP : ∀ k, Pf k → Pf' k) (hc : y.cache = x.cache) (h : RKP SC0 inl Pf' x) : RKP SC0 inl Pf y := by
  obtain ⟨⟨⟨NR, MO, INL, SU, hcx, hil, hin⟩, NRc, hNRc, hcl⟩, hf⟩ := h
  exact ⟨⟨⟨NR, MO, INL, SU, hc.trans hcx, hil, hin⟩, NRc, hc ▸ hNRc, hcl⟩,
    fun N hN k hk => hf N (hc ▸ hN) k (hP k hk)⟩

/-! ## The loop's hypotheses at `AgreeIP` -/

/-- **`SccLoopAt` without `PrintId`** (`printId_pill` proves it): a configuration that is the
pill's, `Ranked`, the three `MemGate`s for `LoopR` with `Q := QK env R P S x`, and `env` the
model's at the members. -/
def SccLoopAtA (env : CallEnv) (R : GenRest → Prop) (P : Noun → Prop) (S CODE JETS CALLS JH : Noun)
    (x : GenRest) (NR CR : Noun) : Prop :=
  ∃ (c : Cfg Noun NeedOrd) (r : Ranked c) (outC : Noun → List Noun) (nout : Noun → NeedOrd),
    CfgOf c S (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR)) ∧
    MemGate c (LoopR c.scc outC nout (QK env R P S x))
      (csiCtx (A 1) (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR)) S (C CODE (C JETS CALLS)) JH (C NR CR))
      (fun _ => c.none) (A 0) Mode.may (A 0x79616d) ∧
    MemGate c (LoopR c.scc outC nout (QK env R P S x))
      (csiCtx (A 1) (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR)) S (C CODE (C JETS CALLS)) JH (C NR CR))
      (fun _ => c.none) (A 0) Mode.done (A 0x656e6f64) ∧
    (∀ TOP, TopN (maySweep c (St.empty : St Noun NeedOrd)).ml TOP →
      MemGate c (LoopR c.scc outC nout (QK env R P S x))
        (csiCtx (A 1) (kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR)) S (C CODE (C JETS CALLS)) JH (C NR CR))
        (topOf c (maySweep c (St.empty : St Noun NeedOrd))) TOP Mode.must (A 0x7473756d)) ∧
    ∀ (s : St Noun NeedOrd), compileSccIn c false (fuelR c r) St.empty = some s → ∀ b' : Bell, b'.toNoun ∈ c.scc →
      env.need b' = s.ml b'.toNoun ∧ ∀ v, s.sure b'.toNoun = some v → env.sure b' = v

/-- What `calleeCompiled_sccA` knows at the rest where it runs the loop on `S`. -/
def LoopRest (env : CallEnv) (R : GenRest → Prop) (P : Noun → Prop) (S : Noun) (x : GenRest) (NR CR : Noun) :
    Prop :=
  AgreeIP env P x ∧ R x ∧ x.cache = C NR CR ∧ ∀ k ∈ tapList S, getF mugF k NR = some (A 0)

/-- **`CalleeCompiledP` for a callee of any SCC, with `RKP`** (`calleeCompiled_scc` with the loop
asked only at the rests where it runs, no `PrintId`, and the bells in progress `Pf` kept missing in
`nary.cache`: the new entries are the members of `S`, outside `Pf`). -/
theorem calleeCompiled_sccA {ctx CODE JETS CALLS JH SC0 : Noun} (h7 : slot? 7 ctx = some compK)
    (hl : slot? 26 ctx = some (C CODE (C JETS CALLS))) (hj : slot? 54 ctx = some JH)
    (h107 : slot? 107 ctx = some CALLS) (env : CallEnv) (inl : Noun → Option Nomm) (P Pf : Noun → Prop)
    (b : Bell) (nb : NeedOrd) (S : Noun)
    (hsg : SccsGood SC0) (hcj : IsMap mugF CALLS ∧ ∀ k v, Get CALLS k v → IsSet mugF v)
    (hsc : getF mugF b.toNoun SC0 = some (C (A 0) S))
    (hnd : (∀ n, S ≠ C n (C (A 0) (A 0))) ∨ ∃ n, S = C n (C (A 0) (A 0)) ∧ CalleeIn CALLS n n)
    (hPS : ∀ k ∈ tapList S, ¬ P k) (hPfS : ∀ k ∈ tapList S, ¬ Pf k) (hnb : env.need b = some nb)
    (hloop : ∀ x NR CR, LoopRest env (RKP SC0 inl Pf) P S x NR CR →
      SccLoopAtA env (RKP SC0 inl Pf) P S CODE JETS CALLS JH x NR CR) :
    CalleeCompiledP env (RKP SC0 inl Pf) P ctx b nb := by
  intro x NR MO SC RS hA hR hcx h0
  obtain ⟨xc, xs, xf⟩ := x
  simp only at hcx h0 ⊢
  subst hcx
  have hA0 := hA
  have hR0 := hR
  obtain ⟨hns, NR1, MO1, SC1, INL1, SU1, hc1, hnr, hsu, hag, hsa⟩ := hA
  obtain ⟨⟨⟨NR2, MO2, INL2, SU2, hc2, hil, hin⟩, NRc, hNRc, hcl⟩, hPf0⟩ := hR
  simp only [cacheN, Noun.cell.injEq] at hc1
  obtain ⟨e1, e2, e3, e4⟩ := hc1
  subst NR1 MO1 SC1 RS
  simp only [cacheN, Noun.cell.injEq] at hc2
  obtain ⟨e5, e6, e7, e8, e9⟩ := hc2
  subst NR2 MO2 INL2 SU2 SC
  have eNc : NRc = NR := by simpa [nock_exec] using hNRc.symm
  subst NRc
  obtain ⟨hSset, hbS, hSmem⟩ := hsg _ _ hsc
  have hmissS := members_miss hsg hsc hcl hnr h0
  have hsuS : ∀ k ∈ tapList S, getF mugF k SU1 = some (A 0) := by
    intro k hk
    rcases getF_cases (k := k) hsu with h | ⟨v, hv⟩
    · exact h
    · obtain ⟨b', rfl⟩ := (hSmem k hk).2
      obtain ⟨-, u, hu⟩ := hsa b' v hv (hPS _ hk)
      rw [hmissS _ hk] at hu
      cases hu
  obtain ⟨c, r, outC, nout, hcfg, hmay, hdone, hmust, henv⟩ :=
    hloop ⟨C NR (C MO (C SC0 (C INL1 SU1))), xs, xf⟩ NR (C MO (C SC0 (C INL1 SU1))) ⟨hA0, hR0, rfl, hmissS⟩
  have hcs : c.scc = tapList S := hcfg.scc
  have hq0 : QK env (RKP SC0 inl Pf) P S ⟨C NR (C MO (C SC0 (C INL1 SU1))), xs, xf⟩ (C NR (C MO (C SC0 (C INL1 SU1)))) :=
    ⟨agreeIP_mono (fun k h => Or.inl h) hA0, ext_refl _, hR0, NR, _, rfl, hmissS⟩
  have hsu0 : SureHolds c.scc (St.empty : St Noun NeedOrd).sure (C NR (C MO (C SC0 (C INL1 SU1)))) :=
    ⟨SU1, by simp [nock_exec], fun k hk => Or.inr ⟨rfl, hsuS k (hcs ▸ hk)⟩⟩
  obtain ⟨s, hs, hsome, hout, M, NR', REST, NARYU, hLR, hNR', hNU, hus, hgate⟩ :=
    csi_gate_ranked c r c.scc outC nout (QK env (RKP SC0 inl Pf) P S ⟨C NR (C MO (C SC0 (C INL1 SU1))), xs, xf⟩)
      S CODE JETS CALLS JH NR (C MO (C SC0 (C INL1 SU1))) ⟨hSset, hcj.1, hcj.2, hnr⟩ ⟨_, hbS, h0⟩ hnd hcfg
      hmay hdone St.empty hmust
      (fun CA h => by
        obtain ⟨⟨-, NR, MO, SC, INL, SU, hc, hm, -⟩, -⟩ := h
        exact ⟨NR, _, hc, hm⟩)
      (fun _ _ => printId_pill _) (fun _ => rfl) hsu0 hq0
  obtain ⟨hml, hsh, -, hAq, hEq, hRq, NRq, RESTq, eq, hmissq⟩ := hLR
  obtain ⟨eq1, eq2⟩ := Noun.cell.inj eq
  subst eq1 eq2
  have henv' := henv s hs
  have hssome := compileSccIn_sure_some c _ _ s hs
  have hmemM : ∀ k v, Get M k v → k ∈ tapList S := by
    intro k v hv
    obtain ⟨n, t, hn, -⟩ := hml.2.1 k v hv
    refine Classical.byContradiction fun hk => ?_
    rw [hout k (hcs ▸ hk)] at hn
    cases hn
  have hnotM : ∀ k u, getF mugF k NR' = some (C (A 0) u) → ¬ KIn M k := by
    rintro k u hu ⟨v, hv⟩
    rw [hmissq k (hmemM k v hv)] at hu
    cases hu
  have hbml : s.ml b.toNoun = some nb := by rw [← (henv' b (hcs ▸ hbS)).1, hnb]
  obtain ⟨hns', NRa, MOa, SCa, INLa, SUa, hca, hnra, hsua, haga, hsaa⟩ := hAq
  obtain ⟨ea1, ea2⟩ := Noun.cell.inj hca
  subst ea1
  have h31 : ∀ S31, slot? 31 (C NR' REST) = some S31 → S31 = SUa := by
    intro S31 h; rw [ea2] at h; simpa [nock_exec] using h.symm
  have hE2 : Ext ⟨C NR' REST, xs, xf⟩ ⟨C NARYU REST, xs, xf⟩ := by
    refine ⟨rfl, rfl, fun N hN => ?_, fun N hN => ⟨N, by simpa [nock_exec] using hN, mapSub_refl N⟩⟩
    have eN : N = NR' := by simpa [nock_exec] using hN.symm
    subst eN
    refine ⟨NARYU, by simp [nock_exec], fun k u hu => ?_⟩
    exact getF_some hNU ((hus _ _).2 (Or.inr ⟨getF_get_map hNR' hu, hnotM k u hu⟩))
  obtain ⟨S31, hS31, hall⟩ := hsh
  have eS := h31 S31 hS31
  subst eS
  obtain ⟨⟨⟨NRb, MOb, INLb, SUb, hcb, hilb, hinb⟩, NRd, hNRd, hcld⟩, hPfq⟩ := hRq
  have eNd : NRd = NR' := by simpa [nock_exec] using hNRd.symm
  subst eNd
  -- the bells in progress stay missing
  have hPfU : ∀ N, slot? 2 (C NARYU REST) = some N → ∀ k, Pf k → getF mugF k N = some (A 0) := by
    intro N hN k hk
    have eN : N = NARYU := by simpa [nock_exec] using hN.symm
    subst eN
    refine getF_none hNU fun v hv => ?_
    rcases (hus _ _).1 hv with hm | ⟨hn, -⟩
    · exact hPfS _ (hmemM _ _ hm) hk
    · have := hPfq NRd (by simp [nock_exec]) k hk
      rw [getF_some hNR' hn] at this
      cases this
  refine ⟨C NARYU REST, cccMiss_of_loop h7 hl hj b nb (fun g => ccc_scc_hit h7 h107 b hsc g) hgate hml hbml,
    ext_trans hEq hE2, ?_, ⟨⟨⟨NARYU, MOb, INLb, SUb, congrArg (C NARYU) (Noun.cell.inj hcb).2, hilb, hinb⟩,
      NARYU, by simp [nock_exec], fun k u hu => ?_⟩, hPfU⟩, ?_⟩
  · refine ⟨hns', NARYU, MOa, SCa, INLa, S31, congrArg (C NARYU) ea2, hNU, hsua, fun b' u hu => ?_,
      fun b' v hv hP => ?_⟩
    · rcases (hus _ _).1 (getF_get_map hNU hu) with hm | ⟨hn, -⟩
      · obtain ⟨n, t, hn, rfl⟩ := hml.2.1 _ _ hm
        have hb'S := hmemM _ _ hm
        refine ⟨⟨n, by rw [(henv' b' (hcs ▸ hb'S)).1, hn], by simp [nock_exec]⟩, ?_⟩
        rcases hall _ (hcs ▸ hb'S) with ⟨v, -, hgv⟩ | ⟨hv, -⟩
        · exact ⟨_, hgv⟩
        · have := hssome _ (hcs ▸ hb'S); rw [hv] at this; cases this
      · exact haga b' u (getF_some hnra hn)
    · by_cases hbS' : b'.toNoun ∈ tapList S
      · rcases hall _ (hcs ▸ hbS') with ⟨w, hw, hgw⟩ | ⟨hw, -⟩
        · rw [hv] at hgw
          simp only [Option.some.injEq, Noun.cell.injEq, true_and] at hgw
          subst hgw
          refine ⟨by rw [(henv' b' (hcs ▸ hbS')).2 w hw], ?_⟩
          obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hsome _ (hcs ▸ hbS'))
          obtain ⟨t, hg⟩ := hml.2.2 _ _ hn
          exact ⟨_, uni_M hNU hus hg⟩
        · have := hssome _ (hcs ▸ hbS'); rw [hw] at this; cases this
      · obtain ⟨h1, u, hu⟩ := hsaa b' v hv (fun h => h.elim hP hbS')
        exact ⟨h1, uni_key hnra hNU hus hu⟩
  · rcases (hus _ _).1 (getF_get_map hNU hu) with hm | ⟨hn, -⟩
    · have hkS := hmemM _ _ hm
      refine ⟨S, ((hSmem k hkS).1), fun k' hk' => ?_⟩
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hsome _ (hcs ▸ hk'))
      obtain ⟨t, hg⟩ := hml.2.2 _ _ hn
      exact ⟨_, uni_M hNU hus hg⟩
    · obtain ⟨S', hS', hall'⟩ := hcld k u (getF_some hNR' hn)
      refine ⟨S', hS', fun k' hk' => ?_⟩
      obtain ⟨u', hu'⟩ := hall' k' hk'
      exact uni_key hNR' hNU hus hu'
  · obtain ⟨t, hg⟩ := hml.2.2 _ _ hbml
    exact ⟨NARYU, _, by simp [nock_exec], uni_M hNU hus hg⟩

/-! ## The rest predicate of a member run -/

theorem agreeIP_re {env : CallEnv} {P : Noun → Prop} {x y : GenRest} (h : AgreeIP env P x) (hs : y.NoSoft)
    (hc : y.cache = x.cache) : AgreeIP env P y := by
  obtain ⟨-, NR, MO, SC, INL, SU, hcx, h1, h2, h3, h4⟩ := h
  exact ⟨hs, NR, MO, SC, INL, SU, hc.trans hcx, h1, h2, h3, h4⟩

theorem ext_reC {a b c : GenRest} (h1 : Ext a ⟨b.cache, a.soft, a.sofs⟩) (h2 : Ext b c) :
    Ext a ⟨c.cache, a.soft, a.sofs⟩ :=
  ⟨rfl, rfl, cacheSub_trans (y := b) h1.2.2.1 h2.2.2.1, cacheSub_trans (y := b) h1.2.2.2 h2.2.2.2⟩

/-- The bells in progress with a `sure` entry during a member run on the state `st` of the loop
on `S`: the outer ones `P`, and the members of `S` the model has a `sure` for. -/
def PeS (P : Noun → Prop) (S : Noun) (st : St Noun NeedOrd) : Noun → Prop :=
  fun k => P k ∨ (k ∈ tapList S ∧ (st.sure k).isSome = true)

/-- The bells in progress during a member run of the loop on `S`: the outer ones and `S`. -/
def PfS (Pf : Noun → Prop) (S : Noun) : Noun → Prop := fun k => Pf k ∨ k ∈ tapList S

/-- **The rest predicate of a member run** (on the state `st` of the loop on `S` started at the
rest `xs`): `AgreeIP` at `PeS`, `RKP` at `PfS` (what a nested miss keeps), and what `MemDoneCall`
asks at the end: `QK` of the loop and the members' `sure` entries. -/
def EM (env : CallEnv) (SC0 : Noun) (inl : Noun → Option Nomm) (P Pf : Noun → Prop) (S : Noun)
    (st : St Noun NeedOrd) (xs x : GenRest) : Prop :=
  AgreeIP env (PeS P S st) x ∧ RKP SC0 inl (PfS Pf S) x ∧ QK env (RKP SC0 inl Pf) P S xs x.cache ∧
    SureHolds (tapList S) st.sure x.cache

/-- **A nested miss keeps `EM`**: from `Ext`, `AgreeIP` at `PeS` and `RKP` at `PfS` at the new rest
(what `CalleeCompiledP env (RKP SC0 inl (PfS Pf S)) (PeS P S st)` gives). -/
theorem eM_step {env : CallEnv} {SC0 : Noun} {inl : Noun → Option Nomm} {P Pf : Noun → Prop} {S : Noun}
    {st : St Noun NeedOrd} {xs : GenRest} (hPS : ∀ k ∈ tapList S, ¬ P k)
    (hbell : ∀ k ∈ tapList S, ∃ b' : Bell, b'.toNoun = k) {x x' : GenRest}
    (h : EM env SC0 inl P Pf S st xs x) (he : Ext x x') (hA : AgreeIP env (PeS P S st) x')
    (hR : RKP SC0 inl (PfS Pf S) x') : EM env SC0 inl P Pf S st xs x' := by
  obtain ⟨-, -, ⟨hAq, hEq, -, -⟩, hsh⟩ := h
  have hA' := hA
  obtain ⟨-, NR, MO, SC, INL, SU, hc, hnr, hsu, -, hsa⟩ := hA'
  have hmiss : ∀ k ∈ tapList S, getF mugF k NR = some (A 0) :=
    fun k hk => hR.2 NR (by rw [hc]; exact cacheN_slot2 _ _ _ _ _) k (Or.inr hk)
  refine ⟨hA, hR, ⟨agreeIP_re (agreeIP_mono (fun k h => ?_) hA) hAq.1 rfl, ext_reC hEq he,
    rKP_mono (fun k h => Or.inl h) rfl hR, NR, C MO (C SC (C INL SU)), hc, hmiss⟩, ?_⟩
  · rcases h with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  · obtain ⟨S0, h31, hall⟩ := hsh
    refine ⟨SU, by rw [hc]; exact cacheN_slot31 _ _ _ _ _, fun k hk => ?_⟩
    rcases hall k hk with ⟨v, hv, hg⟩ | ⟨hv, hg⟩
    · obtain ⟨N', hN', hsub⟩ := he.2.2.2 S0 h31
      rw [hc, cacheN_slot31] at hN'
      obtain rfl := Option.some.inj hN'
      exact Or.inl ⟨v, hv, hsub _ _ hg⟩
    · refine Or.inr ⟨hv, ?_⟩
      rcases getF_cases (k := k) hsu with h0 | ⟨w, hw⟩
      · exact h0
      · obtain ⟨b', rfl⟩ := hbell k hk
        have hnp : ¬ PeS P S st b'.toNoun := by
          rintro (hp | ⟨-, hs⟩)
          · exact hPS _ hk hp
          · rw [hv] at hs; cases hs
        obtain ⟨-, u, hu⟩ := hsa b' w hw hnp
        rw [hmiss _ hk] at hu
        cases hu

/-- **What `+inlined` must keep** (track A): its cache `CA1` is `CACHE` with `inl.cache` replaced
by a map whose entries for the keys of `inl` are absent or `inl`'s nomm. -/
def InlKeep (inl : Noun → Option Nomm) (CACHE CA1 : Noun) : Prop :=
  ∀ NR MO SC INL SU, CACHE = cacheN NR MO SC INL SU → ∃ INL', CA1 = cacheN NR MO SC INL' SU ∧ IsMap mugF INL' ∧
    ∀ k nm, inl k = some nm → getF mugF k INL' = some (A 0) ∨ getF mugF k INL' = some (C (A 0) nm.toNoun)

/-- **`EM` at the start of a member run**, from the loop's relation at the cache `CACHE` of the call
and `+inlined` keeping it (`InlKeep`). -/
theorem eM_start {env : CallEnv} {SC0 : Noun} {inl : Noun → Option Nomm} {P Pf : Noun → Prop} {S : Noun}
    {st : St Noun NeedOrd} {xs : GenRest} (hPS : ∀ k ∈ tapList S, ¬ P k) {CACHE CA1 : Noun}
    (hQ : QK env (RKP SC0 inl Pf) P S xs CACHE) (hsh : SureHolds (tapList S) st.sure CACHE)
    (hinl : InlKeep inl CACHE CA1) : EM env SC0 inl P Pf S st xs (cuRest CA1) := by
  obtain ⟨hA, hE, hR, NRq, RESTq, hcq, hmiss⟩ := hQ
  obtain ⟨hns, NR, MO, SC, INL, SU, hc, hnr, hsu, hag, hsa⟩ := hA
  change CACHE = cacheN NR MO SC INL SU at hc
  obtain ⟨INL', hc1, hil', hin'⟩ := hinl NR MO SC INL SU hc
  have e2 : NRq = NR := by rw [hc] at hcq; exact (Noun.cell.inj hcq).1.symm
  subst e2
  obtain ⟨⟨⟨NR2, MO2, INL2, SU2, hc2, -, -⟩, NRc, hNRc, hcl⟩, hPf⟩ := hR
  have hc2' : CACHE = cacheN NR2 MO2 SC0 INL2 SU2 := hc2
  rw [hc] at hc2'
  simp only [cacheN, Noun.cell.injEq] at hc2'
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hc2'
  have hs2 : ∀ N, slot? 2 CA1 = some N ↔ slot? 2 CACHE = some N := by
    intro N; rw [hc, hc1, cacheN_slot2, cacheN_slot2]
  have hs31 : ∀ N, slot? 31 CA1 = some N ↔ slot? 31 CACHE = some N := by
    intro N; rw [hc, hc1, cacheN_slot31, cacheN_slot31]
  have hRK : ∀ s f, RKP SC inl Pf ⟨CA1, s, f⟩ :=
    fun s f => ⟨⟨⟨NRq, MO, INL', SU, hc1, hil', hin'⟩, NRc, (hs2 NRc).2 hNRc, hcl⟩,
      fun N hN k hk => hPf N ((hs2 N).1 hN) k hk⟩
  have hAc : ∀ s f, (⟨CA1, s, f⟩ : GenRest).NoSoft → AgreeIP env (fun k => P k ∨ k ∈ tapList S) ⟨CA1, s, f⟩ :=
    fun s f hn => ⟨hn, NRq, MO, SC, INL', SU, hc1, hnr, hsu, hag, hsa⟩
  obtain ⟨S0, h31, hall⟩ := hsh
  have eS : S0 = SU := by rw [hc, cacheN_slot31] at h31; exact (Option.some.inj h31).symm
  subst eS
  refine ⟨⟨cu_entry_nosoft CA1, NRq, MO, SC, INL', S0, hc1, hnr, hsu, hag, fun b' v hv hn => ?_⟩,
    ⟨(hRK _ _).1, fun N hN k hk => ?_⟩,
    ⟨hAc _ _ hns, ⟨rfl, rfl, fun N hN => hE.2.2.1 N hN |>.imp fun N' h => ⟨(hs2 N').2 h.1, h.2⟩,
      fun N hN => hE.2.2.2 N hN |>.imp fun N' h => ⟨(hs31 N').2 h.1, h.2⟩⟩, hRK _ _, NRq, _, hc1, hmiss⟩,
    ⟨S0, by show slot? 31 CA1 = some S0; rw [hc1, cacheN_slot31], hall⟩⟩
  · by_cases hb : b'.toNoun ∈ tapList S
    · rcases hall _ hb with ⟨w, hw, -⟩ | ⟨hw, hg⟩
      · exact absurd (Or.inr ⟨hb, by rw [hw]; rfl⟩) hn
      · rw [hg] at hv; cases hv
    · exact hsa b' v hv (fun h => h.elim (fun h => hn (Or.inl h)) hb)
  · rcases hk with hk | hk
    · exact hPf N ((hs2 N).1 hN) k hk
    · have : N = NRq := by
        change slot? 2 CA1 = some N at hN
        rw [hc1, cacheN_slot2] at hN; exact (Option.some.inj hN).symm
      subst this; exact hmiss k hk

end Compiler
end Formalization
