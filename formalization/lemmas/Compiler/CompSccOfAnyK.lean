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

/-! ## The per-call facts of a member run at `mono` `|` -/

/-- **A hit at `AgreeIP`**: an entry of `b` in `nary.cache`, `b` outside the bells in progress
with a `sure` entry, reads the need and the sure need of `envA`, which the run's `envR` agrees
with at `b`. -/
theorem hit_of_agreeIP {ctx : Noun} {envA envR : CallEnv} {Pe : Noun → Prop} {b : Bell} {nb : NeedOrd}
    {x : GenRest} {S : Noun} (hS : slot? 12 ctx = some S) (hin : hasInF mugF b.toNoun S = some false)
    (hnb : envR.need b = some nb) (hag : envR.need b = envA.need b ∧ envR.sure b = envA.sure b)
    (hA : AgreeIP envA Pe x) (hnp : ¬ Pe b.toNoun) {NR u : Noun} (hNR : slot? 2 x.cache = some NR)
    (hu : getF mugF b.toNoun NR = some (C (A 0) u)) : NeedRead ctx x b nb ∧ SureNoun envR b x := by
  obtain ⟨-, NR', MO, SC, INL, SU, hc, -, -, hag', hsa⟩ := hA
  have h2 : NR' = NR := by rw [hc] at hNR; simpa [cacheN, nock_exec] using hNR
  subst h2
  obtain ⟨⟨nb', hnb', hu'⟩, v, hv⟩ := hag' b u hu
  rw [← hag.1, hnb] at hnb'
  cases hnb'
  refine ⟨NeedRead.nary hS hin hNR hu hu', SU, by rw [hc]; simp [cacheN, nock_exec], Or.inl ?_⟩
  rw [hv, (hsa b v hv hnp).1, hag.2]

/-- **`CallOkTN` of a call outside the SCC at `AgreeIP`** (`callOkTN_of_E` inside a loop): a hit
reads the cache; a miss compiles the callee's SCC (`CalleeCompiledP` at the bells in progress
`Pe`) and then hits.  `E` holds `AgreeIP` at `Pe`, the rest predicate `R` and the bells `Pf ⊇ Pe`
missing in `nary.cache`, and a nested miss keeps it (`hstep`); the run's `envR` agrees with the
cache's `envA` at `b` outside `Pf`. -/
theorem callOkTN_of_IP {ctx : Noun} (h7 : slot? 7 ctx = some compK) {envR envA : CallEnv} {cod : Noun}
    {E : GenRest → Prop} {Pe Pf : Noun → Prop} {R : GenRest → Prop} {msup : Option Nomm} {p q : Nomm}
    {b : Bell} {nb : NeedOrd}
    (hcd : CodePure cod envR b) (hc : envR.cod b = some (envR.pure b)) (hri : envR.ring b = Option.none)
    (hnb : envR.need b = some nb) (hsf : envR.sof (made p msup) p q b nb = false)
    (hcole : ∃ cole, slot? 6846 ctx = some cole ∧ getF mugF b.toNoun cole = some (A 0))
    (hhot : ∃ jh, slot? 54 ctx = some jh) (hsof : ∀ x, SofRetN envR msup ctx p q b nb x)
    {SCC : Noun} (hS : slot? 12 ctx = some SCC) (hin : hasInF mugF b.toNoun SCC = some false)
    (hag : ¬ Pf b.toNoun → envR.need b = envA.need b ∧ envR.sure b = envA.sure b)
    (hEA : ∀ x, E x → AgreeIP envA Pe x) (hER : ∀ x, E x → R x)
    (hEf : ∀ x, E x → ∀ NR, slot? 2 x.cache = some NR → ∀ k, Pf k → getF mugF k NR = some (A 0))
    (hPe : ∀ k, Pe k → Pf k)
    (hstep : ∀ x x', E x → Ext x x' → AgreeIP envA Pe x' → R x' → E x')
    (hcc : CalleeCompiledP envA R Pe ctx b nb) :
    CallOkTN envR cod ctx E (ExtE E) msup p q b := by
  refine ⟨hcd, hc, hri, nb, hnb, hsf, fun x _ hE => ?_⟩
  have hnpf : ∀ y NR u, E y → slot? 2 y.cache = some NR → getF mugF b.toNoun NR = some (C (A 0) u) →
      ¬ Pf b.toNoun := by
    intro y NR u hy hN hu hp
    rw [hEf y hy NR hN _ hp] at hu; cases hu
  obtain ⟨_, NR, MO, SC, INL, SU, hcx, hnm, -⟩ := hEA x hE
  have hNR : slot? 2 x.cache = some NR := by rw [hcx]; simp [cacheN, nock_exec]
  rcases getF_cases (k := b.toNoun) hnm with h0 | ⟨u, hu⟩
  · obtain ⟨CA', hmiss, hext, hA', hR', N', u', hN', hu'⟩ := hcc x NR MO SC (C INL SU) (hEA x hE) (hER x hE) hcx h0
    have hE' := hstep x _ hE hext hA' hR'
    have hpf := hnpf _ N' u' hE' hN' hu'
    obtain ⟨hr', hs'⟩ := hit_of_agreeIP hS hin hnb (hag hpf) hA' (fun h => hpf (hPe _ h)) hN' hu'
    have hm := callNounN_of_read h7 hcole hhot hr' hs' (hsof ⟨CA', x.soft, x.sofs⟩)
    exact ⟨_, _, ⟨hext, fun _ => hE'⟩,
      callNounMT_of h7 hcole hhot (NeedStep.miss hS hin hcx h0 hmiss) hs' (hsof ⟨CA', x.soft, x.sofs⟩), hm⟩
  · have hpf := hnpf x NR u hE hNR hu
    obtain ⟨hr, hs⟩ := hit_of_agreeIP hS hin hnb (hag hpf) (hEA x hE) (fun h => hpf (hPe _ h)) hNR hu
    have hm := callNounN_of_read h7 hcole hhot hr hs (hsof x)
    exact ⟨x, _, ⟨ext_refl x, id⟩, callNounMT_of_m hm, hm⟩

/-- **`NeedRead` at a member from `MlExact`** (the context `memDCtx` of `member`, `top` `~`): an
entry of `map-local` is read (`loc`), and with none the `top` `~` gives `[%none ~]`. -/
theorem needRead_member {SCC LONG JH ML B : Noun} {ml : Noun → Option NeedOrd} (hml : MlExact ml ML) {b : Bell}
    (hin : hasInF mugF b.toNoun SCC = some true) (x : GenRest) :
    NeedRead (memDCtx SCC LONG JH ML (A 0) B) x b ((ml b.toNoun).getD NeedOrd.none) := by
  have h12 : slot? 12 (memDCtx SCC LONG JH ML (A 0) B) = some SCC := by simp [memDCtx, nock_exec]
  have h110 : slot? 110 (memDCtx SCC LONG JH ML (A 0) B) = some ML := by simp [memDCtx, nock_exec]
  have h222 : slot? 222 (memDCtx SCC LONG JH ML (A 0) B) = some (A 0) := by simp [memDCtx, nock_exec]
  cases hm : ml b.toNoun with
  | none =>
    have hg : getF mugF b.toNoun ML = some (A 0) :=
      getF_none hml.1 fun v hv => by obtain ⟨n, t, hn, -⟩ := hml.2.1 _ v hv; rw [hm] at hn; cases hn
    exact NeedRead.top h12 hin h110 hg h222 (Or.inr ⟨getF_none IsMap.nil fun v hv => get_nil.1 hv, rfl⟩)
  | some n =>
    obtain ⟨t, ht⟩ := hml.2.2 _ n hm
    exact NeedRead.loc h12 hin h110 (getF_some hml.1 ht) (by simp [nock_exec])

theorem need_done {r : RealCfg} {order : List Noun} {kids : Noun → List Noun} {st : St Noun NeedOrd} {b : Bell}
    (hb : b.toNoun ∈ r.scc) : (envDone r order kids st).need b = some ((st.ml b.toNoun).getD NeedOrd.none) := by
  simp [envDone, envView, hb, viewN]

theorem need_done_out {r : RealCfg} {order : List Noun} {kids : Noun → List Noun} {st : St Noun NeedOrd} {b : Bell}
    (hb : b.toNoun ∉ r.scc) :
    (envDone r order kids st).need b = r.env.need b ∧ (envDone r order kids st).sure b = r.env.sure b := by
  simp [envDone, envView, hb]

/-- **`SureNoun` at a member from `SureHolds`** (`envDone` reads `viewS`). -/
theorem sureNoun_done {r : RealCfg} {order : List Noun} {kids : Noun → List Noun} {st : St Noun NeedOrd} {b : Bell}
    (hb : b.toNoun ∈ r.scc) {x : GenRest} (h : SureHolds r.scc st.sure x.cache) :
    SureNoun (envDone r order kids st) b x := by
  obtain ⟨S0, h31, hall⟩ := h
  refine ⟨S0, h31, ?_⟩
  have hs : (envDone r order kids st).sure b = (st.sure b.toNoun).getD NeedOrd.none := by
    simp [envDone, envView, hb, viewS, cfgReal]
  rw [hs]
  rcases hall _ hb with ⟨v, hv, hg⟩ | ⟨hv, hg⟩
  · left; rw [hv]; exact hg
  · right; rw [hv]; exact ⟨hg, rfl⟩

/-- **`CallOkTN` of a call of a member** (`callOkTN_of_read` with `needRead_member` and
`sureNoun_done`). -/
theorem callOkTN_member {r : RealCfg} {order : List Noun} {kids : Noun → List Noun} {st : St Noun NeedOrd}
    {SCC LONG JH ML B cod : Noun} {E : GenRest → Prop} {msup : Option Nomm} {p q : Nomm} {b : Bell}
    (hcd : CodePure cod (envDone r order kids st) b)
    (hc : (envDone r order kids st).cod b = some ((envDone r order kids st).pure b))
    (hri : (envDone r order kids st).ring b = Option.none)
    (hsf : (envDone r order kids st).sof (made p msup) p q b ((st.ml b.toNoun).getD NeedOrd.none) = false)
    (hcole : ∃ cole, slot? 6846 (memDCtx SCC LONG JH ML (A 0) B) = some cole ∧ getF mugF b.toNoun cole = some (A 0))
    (hsof : ∀ x, SofRetN (envDone r order kids st) msup (memDCtx SCC LONG JH ML (A 0) B) p q b
      ((st.ml b.toNoun).getD NeedOrd.none) x)
    (hml : MlExact st.ml ML) (hin : hasInF mugF b.toNoun SCC = some true) (hb : b.toNoun ∈ r.scc)
    (hES : ∀ x, E x → SureHolds r.scc st.sure x.cache) :
    CallOkTN (envDone r order kids st) cod (memDCtx SCC LONG JH ML (A 0) B) E (ExtE E) msup p q b :=
  callOkTN_of_read rfl (fun x => ⟨ext_refl x, id⟩) hcd hc hri (need_done hb) hsf hcole
    ⟨JH, by simp [memDCtx, nock_exec]⟩ (fun x _ hEx => ⟨needRead_member hml hin x, sureNoun_done hb (hES x hEx), hsof x⟩)

/-- **`CallOkTN` of a call outside `S` in a member run** (`callOkTN_of_IP` at `E := EM`, the bells in
progress `PeS P S st` and `PfS Pf S`, `R := RKP SC0 inl (PfS Pf S)`, `envA` the model's `env` with
`r.env = env`). -/
theorem callOkTN_out {r : RealCfg} {order : List Noun} {kids : Noun → List Noun} {st : St Noun NeedOrd}
    {env : CallEnv} (hre : r.env = env) {SC0 : Noun} {inl : Noun → Option Nomm} {P Pf : Noun → Prop} {S : Noun}
    {xs : GenRest} (hrs : r.scc = tapList S) (hPf : ∀ k, P k → Pf k) (hPS : ∀ k ∈ tapList S, ¬ P k)
    (hbell : ∀ k ∈ tapList S, ∃ b' : Bell, b'.toNoun = k)
    {SCC LONG JH ML B cod : Noun} {msup : Option Nomm} {p q : Nomm} {b : Bell} {nb : NeedOrd}
    (hcd : CodePure cod (envDone r order kids st) b)
    (hc : (envDone r order kids st).cod b = some ((envDone r order kids st).pure b))
    (hri : (envDone r order kids st).ring b = Option.none)
    (hnb : (envDone r order kids st).need b = some nb)
    (hsf : (envDone r order kids st).sof (made p msup) p q b nb = false)
    (hcole : ∃ cole, slot? 6846 (memDCtx SCC LONG JH ML (A 0) B) = some cole ∧ getF mugF b.toNoun cole = some (A 0))
    (hsof : ∀ x, SofRetN (envDone r order kids st) msup (memDCtx SCC LONG JH ML (A 0) B) p q b nb x)
    (hin : hasInF mugF b.toNoun SCC = some false)
    (hcc : CalleeCompiledP env (RKP SC0 inl (PfS Pf S)) (PeS P S st) (memDCtx SCC LONG JH ML (A 0) B) b nb) :
    CallOkTN (envDone r order kids st) cod (memDCtx SCC LONG JH ML (A 0) B) (EM env SC0 inl P Pf S st xs)
      (ExtE (EM env SC0 inl P Pf S st xs)) msup p q b := by
  refine callOkTN_of_IP rfl hcd hc hri hnb hsf hcole ⟨JH, by simp [memDCtx, nock_exec]⟩ hsof
    (by simp [memDCtx, nock_exec]) hin (envA := env) (Pf := PfS Pf S) (fun h => ?_) (fun x h => h.1) (fun x h => h.2.1)
    (fun x h => h.2.1.2) ?_ (fun x x' h he hA hR => eM_step hPS hbell h he hA hR) hcc
  · have hb : b.toNoun ∉ r.scc := fun hb => h (Or.inr (hrs ▸ hb))
    rw [← hre]; exact need_done_out hb
  · rintro k (h | ⟨h, -⟩)
    · exact Or.inl (hPf k h)
    · exact Or.inr h

/-! ## `MemDoneCall` -/

/-- **`MemDoneCall` from the threaded run at `mono` `|`** (`comp_run_dirXTN` at `E := EM`,
`Y := ExtE EM`): the facts of the model and of track A's arms as in `MemDoneCall`, `+inlined`
keeping the cache (`InlKeep`), the class `DirOk` and `DirCallsTN` of the member's nomm (each call
by `callOkTN_member` or `callOkTN_out`), with no outside callees asked of `OutsHeld`
(`outC := fun _ => []`). -/
theorem memDoneCall_of (r : RealCfg) (order : List Noun) (kids : Noun → List Noun) (nout : Noun → NeedOrd)
    (env : CallEnv) (SC0 : Noun) (inl : Noun → Option Nomm) (P Pf : Noun → Prop) (S : Noun) (xs : GenRest)
    (hrs : r.scc = tapList S) (hPS : ∀ k ∈ tapList S, ¬ P k)
    (st : St Noun NeedOrd) (keep : Bool) (DN KIDS ML0 CB SCC CODE LSR JH CACHE0 b ML CACHE : Noun)
    (hR : LoopR r.scc (fun _ => []) nout (QK env (RKP SC0 inl Pf) P S xs) st.ml st.sure ML CACHE)
    (cape : Cape) (DATA FOL : Noun) (nm : Nomm) (fuel : Nat) (hb : b = C (C cape.toNoun DATA) FOL)
    (hinfo : r.info b = ⟨nm, cape, DATA, fuel⟩) (CA1 : Noun)
    (hinl : nock (C inlBody (C (C b (C (C CODE LSR) (C JH CACHE))) compK)) inlBody = some (C nm.toNoun CA1))
    (hik : InlKeep inl CACHE CA1) (hn : DirOk nm = true)
    (hd : DirCallsTN (envDone r order kids st) CODE (memDCtx SCC (C CODE LSR) JH ML (A 0) b)
      (EM env SC0 inl P Pf S st xs) (ExtE (EM env SC0 inl P Pf S st xs)) Option.none nm)
    (nex : NextL CSet) (g1 : Gen (TreapMap mugF))
    (hrunL : runLC (envDone r order kids st) Option.none nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF))
      = some (nex, g1))
    (ord : NeedOrd) (hcol : shapeCol fuel nex.laz cape = some ord) (hargs : nex.th.args = [])
    (nedF : Need) (g2 : Gen (TreapMap mugF)) (hnoar : needOrdAllocRegs ord g1 = some (nedF, g2))
    (hrun : isRun (flattenNeed (bakeNeed nedF (Sock.mk cape DATA)).1)
        ((flattenNeed (bakeNeed nedF (Sock.mk cape DATA)).1).headD 0) 0 = true)
    (sur : NeedOrd) (hsur : sureOf (needToOrd nex.laz.sure.ned) nex.laz.sure.lok cape = some sur)
    (hfin : ∃ s, finishLFC (S := CSet) (Map := TreapMap mugF) (envDone r order kids st) nm ord cape
        (fun n => bakeNeed n (Sock.mk cape DATA)) = some s)
    (hcs : ∀ (x1 : GenRest) (C1 C2 C3 C4 SURE' : Noun) (prev : NeedOrd), st.ml b = some prev →
        msgOrd (needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1) prev cape ≠ needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1 →
        ∃ t, nock (C finBody (C (C (A 0) (msgOrd (needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1) prev cape).toNoun)
              (memFCR keep (wasN (st.sure b)) sur.toNoun
                (needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1).toNoun nex.laz.toNoun nedF.toNoun
                (bakeNeed nedF (Sock.mk cape DATA)).1.toNoun (immNoun (bakeNeed nedF (Sock.mk cape DATA)).2)
                nex.th.there (genNoun g2 x1) nm.toNoun
                (memDCtx SCC (C CODE LSR) JH ML (A 0) b) b ML
                (A 0) (cacheN C1 C2 C3 C4 SURE') (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0)))) finBody
          = some (C (msgOrd (needToOrd (bakeNeed nedF (Sock.mk cape DATA)).1) prev cape).toNoun t)) :
    MemDoneCall r order kids (fun _ => []) nout env (RKP SC0 inl Pf) P S xs st keep DN KIDS ML0 CB SCC CODE LSR JH
      CACHE0 b ML CACHE := by
  have hE0 : EM env SC0 inl P Pf S st xs (cuRest CA1) := eM_start hPS hR.2.2.2 (hrs ▸ hR.2.1) hik
  have h7 : slot? 7 (memDCtx SCC (C CODE LSR) JH ML (A 0) b) = some compK := rfl
  have h52 : slot? 52 (memDCtx SCC (C CODE LSR) JH ML (A 0) b) = some CODE := by simp [memDCtx, nock_exec]
  have hrun' := comp_run_dirXTN h7 h52 (envDone r order kids st) (EM env SC0 inl P Pf S st xs)
    (ExtE (EM env SC0 inl P Pf S st xs))
    (fun msup => yOk_xn msup (fun x => ⟨ext_refl x, id⟩) (fun h1 h2 => ⟨ext_trans h1.1 h2.1, fun h => h2.2 (h1.2 h)⟩)
      (fun hx h => ext_noSoft hx h.1) (fun hE h => h.2 hE)) nm hn Option.none [] hd CGoalL.done genEntry rfl
  have hf : (runLCM (S := CSet) (Map := TreapMap mugF) (envDone r order kids st) false Option.none)
      = runLC (envDone r order kids st) Option.none := by
    funext n g rg; exact runLCM_false _ n _ g rg
  rw [hf] at hrun'
  refine ⟨cape, DATA, FOL, nm, fuel, hb, hinfo, CA1, hinl, nex, g1, hrunL, XN (EM env SC0 inl P Pf S st xs) Option.none,
    ExtE (EM env SC0 inl P Pf S st xs), hrun', ⟨hE0, rfl, rfl⟩, ?_, ord, hcol, hargs, nedF, g2, hnoar, hrun, sur, hsur,
    hfin, hcs⟩
  intro x1 hy
  obtain ⟨hA1, -, hQ1, hS1⟩ := hy.2 hE0
  obtain ⟨-, C1, C2, C3, C4, SU, hc, -⟩ := hA1
  refine ⟨C1, C2, C3, C4, SU, hc, hy.1.1, hc ▸ hQ1, hrs ▸ hc ▸ hS1, fun b' _ k hk => by simp at hk⟩

end Compiler
end Formalization
