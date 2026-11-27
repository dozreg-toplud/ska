import lemmas.Compiler.CompSccOfAnyDefs
import lemmas.Compiler.CompSccLoopClose

/-!
# The gate of `+compile-unary` with callees in SCCs of any size (README Gaps 19 (g))

A miss in `nary.cache` on a callee `b` whose SCC `S` (its `sccs` entry, the cache hit of
`+scc-of`, `ccc_scc_hit`) is not a lone bell without a self call runs track I's loop on `S`
(`csi_gate_ranked`).  The loop writes `sure.cache` at the members of `S` in every member run and
`nary.cache` only at the end (`+uni:by`), so during the loop the cache does NOT satisfy
`AgreeE`: a member has a `sure` entry, changing from sweep to sweep, and no `nary` entry.  The
invariant the loop keeps is `AgreeIP env P`: `AgreeE` with the `sure` clause asked only outside a
set `P` of bells in progress (the members of the SCCs whose loops are running, outermost first).

* `AgreeIP`, `agreeIP_of_E`, `agreeE_of_IP`: `AgreeE` is `AgreeIP` at `P` empty.
* `SccsGood SC0`: the meaning of `sccs.cache` (track P, `+tarjan`): an entry `S` of `k` is a set
  holding `k`, and every member of `S` is a bell whose entry is `S`.
* `SccClosed SC0 NR`, `NaryClosed`: the keys of `nary.cache` are a union of whole SCCs (every write
  is the `+uni:by` of a whole SCC; `%jets` deletes a set closed under callers, `+hot-stale`).
  With `SccsGood` it gives that every member of `S` misses when `b` does (`members_miss`), which
  `Ext` needs: the `+uni:by` must not overwrite an old entry.
* `RK SC0 inl`: `RInl SC0 inl` and `NaryClosed SC0`, the rest predicate of this gate.
* `CalleeCompiledP env R P`: `CalleeCompiled` at rests with `AgreeIP env P` (what a nested miss,
  inside a member run of an SCC in progress, needs); `calleeCompiled_of_P` at `P` empty.
* `QK env R P S x`: the cache invariant `Q` of track I's loop on `S`, from the rest `x` of the
  miss: `AgreeIP` at `P ∪ S`, `Ext x`, `R`, and the members of `S` still missing in `nary.cache`.
* `SccLoopAt`: what track I's loop takes on `S` (its configuration `CfgOf`, `Ranked`, the three
  `MemGate`s for `LoopR` with `Q := QK`, `PrintId`) and that `env` reads the model's final needs
  and sure needs at the members.
* **`calleeCompiled_scc`**: `CalleeCompiledP env (RK SC0 inl) P ctx b nb` from `SccLoopAt`, the
  `sccs` entry and `SccsGood`, the jug `calls`, `hnd` and `P` disjoint from `S`.
* `calleeCompiled_oneK`: `calleeCompiled_one` with `RK` (the `+put:by` of one bell keeps
  `NaryClosed`).
* `calleeCompiledP_rank`: the induction on the height of the callee's SCC in the condensation,
  stated: where it lives (track I's `MemGate` for the members of `S` takes `CalleeCompiledP` at
  `P ∪ S` for the callees of smaller height, which this step gives).
* **`cu_gate_dir_scc`**: the gate on `DirOk` with callees readable at the start, one-bell
  callees (`OneCallee`) and callees of any SCC (`SccCallee`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.SccLoop

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- A key of `NR` is a key of the `+uni:by` of `NR` and `M`. -/
theorem uni_key {NR M NARYU k : Noun} (hNR : IsMap mugF NR) (hNU : IsMap mugF NARYU)
    (hus : UniSpec NR M NARYU) {u : Noun} (h : getF mugF k NR = some (C (A 0) u)) :
    ∃ u', getF mugF k NARYU = some (C (A 0) u') := by
  by_cases hk : KIn M k
  · obtain ⟨v, hv⟩ := hk
    exact ⟨v, getF_some hNU ((hus _ _).2 (Or.inl hv))⟩
  · exact ⟨u, getF_some hNU ((hus _ _).2 (Or.inr ⟨getF_get_map hNR h, hk⟩))⟩

theorem uni_M {NR M NARYU k v : Noun} (hNU : IsMap mugF NARYU) (hus : UniSpec NR M NARYU) (h : Get M k v) :
    getF mugF k NARYU = some (C (A 0) v) :=
  getF_some hNU ((hus _ _).2 (Or.inl h))

/-! ## The model: every member has a `sure` entry -/

theorem foldl_member_sure_some {B N : Type} [DecidableEq B] [DecidableEq N] (c : Cfg B N) (top : B → N)
    (m : Mode) (keep : Bool) :
    ∀ (l : List B) (st : St B N) (b : B), (b ∈ l ∨ (st.sure b).isSome) →
      ((l.foldl (fun st x => (member c top x m keep st).2) st).sure b).isSome := by
  intro l
  induction l with
  | nil => intro st b h; simpa using h
  | cons x l ih =>
    intro st b h
    simp only [List.foldl_cons]
    apply ih
    by_cases hb : b = x
    · subst hb; right; exact (member_ml_some c top b m keep st).2
    · rcases h with h | h
      · rcases List.mem_cons.1 h with h | h
        · exact absurd h hb
        · left; exact h
      · right; rw [(member_ml_ne c top x m keep st hb).2.1]; exact h

/-- **Every member has a `sure` entry** after `compileSccIn c false`. -/
theorem compileSccIn_sure_some {B N : Type} [DecidableEq B] [DecidableEq N] (c : Cfg B N) (fuel : Nat)
    (st0 s : St B N) (h : compileSccIn c false fuel st0 = some s) : ∀ b ∈ c.scc, (s.sure b).isSome := by
  unfold compileSccIn at h
  simp only [Bool.false_eq_true, if_false, Option.map_eq_some_iff] at h
  obtain ⟨s', -, rfl⟩ := h
  exact fun b hb => foldl_member_sure_some c _ _ _ c.scc s' b (Or.inl hb)

/-! ## `CalleeCompiled` with bells in progress -/

/-- **`CalleeCompiled` at rests with `AgreeIP env P`** (a miss inside a member run of an SCC in
progress has `P` its members). -/
def CalleeCompiledP (env : CallEnv) (R : GenRest → Prop) (P : Noun → Prop) (ctx : Noun) (b : Bell)
    (nb : NeedOrd) : Prop :=
  ∀ (x : GenRest) (NR MO SC RS : Noun), AgreeIP env P x → R x → x.cache = C NR (C MO (C SC RS)) →
    getF mugF b.toNoun NR = some (A 0) →
    ∃ CA', CccMiss ctx b nb NR MO SC RS x.soft x.sofs CA' ∧ Ext x ⟨CA', x.soft, x.sofs⟩ ∧
      AgreeIP env P ⟨CA', x.soft, x.sofs⟩ ∧ R ⟨CA', x.soft, x.sofs⟩ ∧
      ∃ N' u, slot? 2 CA' = some N' ∧ getF mugF b.toNoun N' = some (C (A 0) u)

theorem calleeCompiled_of_P {env : CallEnv} {R : GenRest → Prop} {ctx : Noun} {b : Bell} {nb : NeedOrd}
    (h : CalleeCompiledP env R (fun _ => False) ctx b nb) : CalleeCompiled env R ctx b nb := by
  intro x NR MO SC RS hA hR hc h0
  obtain ⟨CA', h1, h2, h3, h4, h5⟩ := h x NR MO SC RS (agreeIP_of_E _ hA) hR hc h0
  exact ⟨CA', h1, h2, agreeE_of_IP h3, h4, h5⟩

/-- **The cache invariant `Q` of track I's loop on the SCC `S`** of a miss at the rest `x`:
`AgreeIP` with `S` in progress, `Ext` from `x`, the rest predicate `R`, and the members of `S`
still missing in `nary.cache` (a nested miss compiles an SCC disjoint from `S`). -/
def QK (env : CallEnv) (R : GenRest → Prop) (P : Noun → Prop) (S : Noun) (x : GenRest) (CA : Noun) : Prop :=
  AgreeIP env (fun k => P k ∨ k ∈ tapList S) ⟨CA, x.soft, x.sofs⟩ ∧ Ext x ⟨CA, x.soft, x.sofs⟩ ∧
    R ⟨CA, x.soft, x.sofs⟩ ∧ ∃ NR REST, CA = C NR REST ∧ ∀ k ∈ tapList S, getF mugF k NR = some (A 0)

/-- **What track I's loop on the callee's SCC `S` takes**, at the miss rest `x` whose cache is
`[NR CR]`: a configuration that is the pill's (`CfgOf`), `Ranked`, the member gates (`MemGate` on
`%may`, `%done`, and `%must` for every `TOP` of the `%may` needs) for `LoopR` with `bs` the
members and `Q := QK env R P S x`, the print (`PrintId`), and the agreement of `env` with the
model's final state at the members (true by definition of an `env` read from the model). -/
def SccLoopAt (env : CallEnv) (R : GenRest → Prop) (P : Noun → Prop) (S CODE JETS CALLS JH : Noun)
    (x : GenRest) (NR CR : Noun) : Prop :=
  ∃ (c : Cfg Noun NeedOrd) (_ : Ranked c) (outC : Noun → List Noun) (nout : Noun → NeedOrd),
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
    (∀ TOP MAY, PrintId ⟨A 1, kidsOf S (C CODE (C JETS CALLS)) JH (C NR CR), S, C CODE (C JETS CALLS), JH,
      C NR CR, TOP, MAY, listN c.order⟩) ∧
    ∀ fuel (s : St Noun NeedOrd), compileSccIn c false fuel St.empty = some s → ∀ b' : Bell, b'.toNoun ∈ c.scc →
      env.need b' = s.ml b'.toNoun ∧ ∀ v, s.sure b'.toNoun = some v → env.sure b' = v

/-- **`CalleeCompiled` for a callee of any SCC** (README Gaps 19 (g)): `b`'s `sccs` entry is
`S` (`hsc`; the miss takes the cache hit of `+scc-of`), `S` is not a lone bell without a self
call (`hnd`: that case is `calleeCompiled_oneK`), the bells in progress `P` are outside `S`, and
track I's loop on `S` takes its hypotheses at every miss rest (`SccLoopAt`).  Then at every rest
with `AgreeIP env P`, `RK SC0 inl` and a miss of `b`, the miss branch returns a cache that extends
the old one, keeps both invariants, and holds `b`. -/
theorem calleeCompiled_scc {ctx CODE JETS CALLS JH SC0 : Noun} (h7 : slot? 7 ctx = some compK)
    (hl : slot? 26 ctx = some (C CODE (C JETS CALLS))) (hj : slot? 54 ctx = some JH)
    (h107 : slot? 107 ctx = some CALLS) (env : CallEnv) (inl : Noun → Option Nomm) (P : Noun → Prop)
    (b : Bell) (nb : NeedOrd) (S : Noun)
    (hsg : SccsGood SC0) (hcj : IsMap mugF CALLS ∧ ∀ k v, Get CALLS k v → IsSet mugF v)
    (hsc : getF mugF b.toNoun SC0 = some (C (A 0) S))
    (hnd : (∀ n, S ≠ C n (C (A 0) (A 0))) ∨ ∃ n, S = C n (C (A 0) (A 0)) ∧ CalleeIn CALLS n n)
    (hPS : ∀ k ∈ tapList S, ¬ P k) (hnb : env.need b = some nb)
    (hloop : ∀ x NR CR, SccLoopAt env (RK SC0 inl) P S CODE JETS CALLS JH x NR CR) :
    CalleeCompiledP env (RK SC0 inl) P ctx b nb := by
  intro x NR MO SC RS hA hR hcx h0
  obtain ⟨xc, xs, xf⟩ := x
  simp only at hcx h0 ⊢
  subst hcx
  have hA0 := hA
  have hR0 := hR
  obtain ⟨hns, NR1, MO1, SC1, INL1, SU1, hc1, hnr, hsu, hag, hsa⟩ := hA
  obtain ⟨⟨NR2, MO2, INL2, SU2, hc2, hil, hin⟩, NRc, hNRc, hcl⟩ := hR
  simp only [cacheN, Noun.cell.injEq] at hc1
  obtain ⟨e1, e2, e3, e4⟩ := hc1
  subst NR1 MO1 SC1 RS
  simp only [cacheN, Noun.cell.injEq] at hc2
  obtain ⟨e5, e6, e7, e8, e9⟩ := hc2
  subst NR2 MO2 INL2 SU2 SC
  have eNc : NRc = NR := by simpa [nock_exec] using hNRc.symm
  subst NRc
  obtain ⟨hSset, hbS, hSmem⟩ := hsg _ _ hsc
  -- the members miss in `nary.cache` and in `sure.cache`
  have hmissS := members_miss hsg hsc hcl hnr h0
  have hsuS : ∀ k ∈ tapList S, getF mugF k SU1 = some (A 0) := by
    intro k hk
    rcases getF_cases (k := k) hsu with h | ⟨v, hv⟩
    · exact h
    · obtain ⟨b', rfl⟩ := (hSmem k hk).2
      obtain ⟨-, u, hu⟩ := hsa b' v hv (hPS _ hk)
      rw [hmissS _ hk] at hu
      cases hu
  -- track I's loop on `S`
  obtain ⟨c, r, outC, nout, hcfg, hmay, hdone, hmust, hpr, henv⟩ :=
    hloop ⟨C NR (C MO (C SC0 (C INL1 SU1))), xs, xf⟩ NR (C MO (C SC0 (C INL1 SU1)))
  have hcs : c.scc = tapList S := hcfg.scc
  have hq0 : QK env (RK SC0 inl) P S ⟨C NR (C MO (C SC0 (C INL1 SU1))), xs, xf⟩ (C NR (C MO (C SC0 (C INL1 SU1)))) :=
    ⟨agreeIP_mono (fun k h => Or.inl h) hA0, ext_refl _, hR0, NR, _, rfl, hmissS⟩
  have hsu0 : SureHolds c.scc (St.empty : St Noun NeedOrd).sure (C NR (C MO (C SC0 (C INL1 SU1)))) :=
    ⟨SU1, by simp [nock_exec], fun k hk => Or.inr ⟨rfl, hsuS k (hcs ▸ hk)⟩⟩
  obtain ⟨s, hs, hsome, hout, M, NR', REST, NARYU, hLR, hNR', hNU, hus, hgate⟩ :=
    csi_gate_ranked c r c.scc outC nout (QK env (RK SC0 inl) P S ⟨C NR (C MO (C SC0 (C INL1 SU1))), xs, xf⟩)
      S CODE JETS CALLS JH NR (C MO (C SC0 (C INL1 SU1))) ⟨hSset, hcj.1, hcj.2, hnr⟩ ⟨_, hbS, h0⟩ hnd hcfg
      hmay hdone St.empty hmust
      (fun CA h => by
        obtain ⟨⟨-, NR, MO, SC, INL, SU, hc, hm, -⟩, -⟩ := h
        exact ⟨NR, _, hc, hm⟩)
      hpr (fun _ => rfl) hsu0 hq0
  obtain ⟨hml, hsh, -, hAq, hEq, hRq, NRq, RESTq, eq, hmissq⟩ := hLR
  obtain ⟨eq1, eq2⟩ := Noun.cell.inj eq
  subst eq1 eq2
  have henv' := henv _ s hs
  have hssome := compileSccIn_sure_some c _ _ s hs
  -- facts of `M`
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
  -- the parts of the last cache
  obtain ⟨hns', NRa, MOa, SCa, INLa, SUa, hca, hnra, hsua, haga, hsaa⟩ := hAq
  obtain ⟨ea1, ea2⟩ := Noun.cell.inj hca
  subst ea1
  have h31 : ∀ S31, slot? 31 (C NR' REST) = some S31 → S31 = SUa := by
    intro S31 h; rw [ea2] at h; simpa [nock_exec] using h.symm
  -- `Ext` of the `+uni:by`
  have hE2 : Ext ⟨C NR' REST, xs, xf⟩ ⟨C NARYU REST, xs, xf⟩ := by
    refine ⟨rfl, rfl, fun N hN => ?_, fun N hN => ⟨N, by simpa [nock_exec] using hN, mapSub_refl N⟩⟩
    have eN : N = NR' := by simpa [nock_exec] using hN.symm
    subst eN
    refine ⟨NARYU, by simp [nock_exec], fun k u hu => ?_⟩
    exact getF_some hNU ((hus _ _).2 (Or.inr ⟨getF_get_map hNR' hu, hnotM k u hu⟩))
  obtain ⟨S31, hS31, hall⟩ := hsh
  have eS := h31 S31 hS31
  subst eS
  refine ⟨C NARYU REST, cccMiss_of_loop h7 hl hj b nb (fun g => ccc_scc_hit h7 h107 b hsc g) hgate hml hbml,
    ext_trans hEq hE2, ?_, ?_, ?_⟩
  · -- `AgreeIP env P` at the new cache
    refine ⟨hns', NARYU, MOa, SCa, INLa, S31, congrArg (C NARYU) ea2, hNU, hsua, fun b' u hu => ?_,
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
  · -- `RK` at the new cache
    obtain ⟨⟨NRb, MOb, INLb, SUb, hcb, hilb, hinb⟩, NRd, hNRd, hcld⟩ := hRq
    have eNd : NRd = NR' := by simpa [nock_exec] using hNRd.symm
    subst eNd
    refine ⟨⟨NARYU, MOb, INLb, SUb, congrArg (C NARYU) (Noun.cell.inj hcb).2, hilb, hinb⟩, NARYU,
      by simp [nock_exec], fun k u hu => ?_⟩
    rcases (hus _ _).1 (getF_get_map hNU hu) with hm | ⟨hn, -⟩
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

/-! ## One bell with `RK` -/

/-- **`calleeCompiled_one` with the rest predicate `RK`**: the same compile (track A's one-bell
chain with the real bake), and the `+put:by` of the one bell keeps `NaryClosed` (`sccClosed_put`). -/
theorem calleeCompiled_oneK {ctx CODE JETS CALLS JH SC0 : Noun} (h7 : slot? 7 ctx = some compK)
    (hl : slot? 26 ctx = some (C CODE (C JETS CALLS))) (hj : slot? 54 ctx = some JH)
    (h107 : slot? 107 ctx = some CALLS) (env envb : CallEnv) (cape : Cape) (DATA FOL : Noun) (nm : Nomm) (fuel : Nat)
    (p : NextL CSet × Gen (TreapMap mugF)) (st : Straight (TreapMap mugF)) (inl : Noun → Option Nomm)
    (hsc : getF mugF (C (C cape.toNoun DATA) FOL) SC0 = some (C (A 0) (setOne (C (C cape.toNoun DATA) FOL))))
    (hinl : inl (C (C cape.toNoun DATA) FOL) = some nm)
    (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (hcode : ∃ V, getF mugF (C (C cape.toNoun DATA) FOL) CODE = some (C (A 0) V) ∧ slot? 2 V = some nm.toNoun)
    (hn : SixOk nm = true) (hax : Bake.NoAx0 nm) (hfix : FixRet envb nm cape fuel)
    (hbake : BakeRunO envb nm (fun nex => scOrd fuel nex cape) cape DATA)
    (hone : CompOne env envb cape DATA nm fuel p st ⟨Sock.mk cape DATA, FOL⟩) :
    CalleeCompiled env (RK SC0 inl) ctx ⟨Sock.mk cape DATA, FOL⟩ st.need := by
  intro x NR MO SC RS hA hR hcx h0
  obtain ⟨xc, xs, xf⟩ := x
  simp only at hcx h0 ⊢
  subst hcx
  obtain ⟨hns, NR1, MO1, SC1, INL, SU, hc1, hnr, hsu, hag, hsa⟩ := hA
  obtain ⟨⟨NR2, MO2, INL2, SU2, hc2, hil, hin⟩, NRc, hNRc, hcl⟩ := hR
  simp only [cacheN, Noun.cell.injEq] at hc1
  obtain ⟨e1, e2, e3, e4⟩ := hc1
  subst NR1 MO1 SC1 RS
  simp only [cacheN, Noun.cell.injEq] at hc2
  obtain ⟨e5, e6, e7, e8, e9⟩ := hc2
  subst NR2 MO2 INL2 SU2 SC
  have eNc : NRc = NR := by simpa [nock_exec] using hNRc.symm
  subst NRc
  have hsu0 : getF mugF (C (C cape.toNoun DATA) FOL) SU = some (A 0) := by
    rcases getF_cases (k := (C (C cape.toNoun DATA) FOL)) hsu with h | ⟨v, hv⟩
    · exact h
    · obtain ⟨-, u, hu⟩ := hsa ⟨Sock.mk cape DATA, FOL⟩ v hv
      exact absurd (hu.symm.trans h0) (by simp)
  obtain ⟨INL', hiok, hil', hin'⟩ : ∃ INL', InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL' ∧ IsMap mugF INL' ∧
      ∀ k nm', inl k = some nm' → getF mugF k INL' = some (A 0) ∨ getF mugF k INL' = some (C (A 0) nm'.toNoun) := by
    rcases hin (C (C cape.toNoun DATA) FOL) nm hinl with hi0 | hi1
    · obtain ⟨INL', hp, hmo, -⟩ := putF_spec mugF INL (C (C cape.toNoun DATA) FOL) nm.toNoun hil
      refine ⟨INL', Or.inr ⟨hi0, hcode, hp⟩, hmo, fun k nm' hk => ?_⟩
      by_cases e : k = (C (C cape.toNoun DATA) FOL)
      · subst e
        rw [hinl] at hk
        cases hk
        exact Or.inr (getF_put_self hil hp).2
      · rw [getF_put_other hil hp e]
        exact hin k nm' hk
    · exact ⟨INL, Or.inl ⟨hi1, rfl⟩, hil, hin⟩
  obtain ⟨hrun, hfin, hneed, hsure⟩ := hone
  have hcsi := csi_gate_scc_one_f_six_B (fun _ => True) tsMapAt_holds cape DATA FOL CODE JETS CALLS JH NR MO SC0 INL SU
    h0 hnr hsu hcalls nm INL' hiok envb hn hax (fun nex => scOrd fuel nex cape)
    (scAt_of_scRet envb nm cape fuel (scRet_of_fixRet envb hn hax cape fuel hfix)) (fun _ _ _ => trivial) hbake
  obtain ⟨NRU, hpn, hmn, -⟩ := putF_spec mugF NR (C (C cape.toNoun DATA) FOL) st.toNoun hnr
  obtain ⟨SUU, hps, hms, -⟩ := putF_spec mugF SU (C (C cape.toNoun DATA) FOL) (sccSur p.1 cape).toNoun hsu
  rw [hrun] at hcsi
  simp only [Option.bind_some, hfin, hpn, hps, Option.map_some] at hcsi
  have hst : slot? 2 st.toNoun = some st.need.toNoun := by simp [Straight.toNoun, nock_exec]
  have hmiss := cccMiss_hit_one h7 hl hj h107 ⟨Sock.mk cape DATA, FOL⟩ st.need (RS := C INL SU) (SO := xs) (SS := xf)
    hsc hcsi hst
  have hBb : ∀ b' : Bell, b'.toNoun = C (C cape.toNoun DATA) FOL → b' = ⟨Sock.mk cape DATA, FOL⟩ := by
    intro b' e
    obtain ⟨l, f⟩ := b'
    cases l <;> simp [Bell.toNoun, Sock.toNoun] at e
    · obtain ⟨⟨h1, h2⟩, h3⟩ := e
      subst h2 h3
      have := congrArg Cape.ofNoun? h1
      simp [Cape.ofNoun?_toNoun] at this
      subst this
      rfl
  refine ⟨cacheN NRU MO SC0 INL' SUU, hmiss, ext_one hnr hsu h0 hsu0 hpn hps, ?_, ?_, ?_⟩
  · refine ⟨fun o => hns o, NRU, MO, SC0, INL', SUU, rfl, hmn, hms, fun b' u hu => ?_, fun b' v hv => ?_⟩
    · rcases getF_put_cases hnr hpn hu with ⟨e, rfl⟩ | ⟨-, hu'⟩
      · obtain rfl := hBb b' e
        exact ⟨⟨st.need, hneed, hst⟩, _, (getF_put_self hsu hps).2⟩
      · obtain ⟨h1, v, hv⟩ := hag b' u hu'
        exact ⟨h1, v, mapSub_put hsu hsu0 hps _ _ hv⟩
    · rcases getF_put_cases hsu hps hv with ⟨e, rfl⟩ | ⟨-, hv'⟩
      · obtain rfl := hBb b' e
        exact ⟨by rw [hsure], _, (getF_put_self hnr hpn).2⟩
      · obtain ⟨h1, u, hu⟩ := hsa b' v hv'
        exact ⟨h1, u, mapSub_put hnr h0 hpn _ _ hu⟩
  · exact ⟨⟨NRU, MO, INL', SUU, rfl, hil', hin'⟩, NRU, by simp [cacheN, nock_exec], sccClosed_put hnr h0 hpn hsc hcl⟩
  · refine ⟨NRU, st.toNoun, ?_, (getF_put_self hnr hpn).2⟩
    show slot? 2 (cacheN NRU MO SC0 INL' SUU) = some NRU
    simp [cacheN, nock_exec]

/-! ## The height of the callee's SCC -/

/-- **The induction on the height of the callee's SCC in the condensation**: if the compile of a
miss at height `h` is `CalleeCompiledP` whenever every miss of smaller height is (at every set
in progress and context: what track I's `MemGate` for the members of `S` takes for the outside
callees of a member, at `P ∪ S`, and `calleeCompiled_scc` turns into this step), every miss is.
The nesting of misses (up to 6 deep in the corpus) is bounded by the height, which is the measure
here; the induction itself lives in the construction of `MemGate`, not in the gate below. -/
theorem calleeCompiledP_rank {env : CallEnv} {R : GenRest → Prop} (ht : Bell → Nat)
    (Good : Bell → (Noun → Prop) → Noun → NeedOrd → Prop)
    (hstep : ∀ b P ctx nb, Good b P ctx nb →
      (∀ b' P' ctx' nb', ht b' < ht b → Good b' P' ctx' nb' → CalleeCompiledP env R P' ctx' b' nb') →
      CalleeCompiledP env R P ctx b nb) :
    ∀ b P ctx nb, Good b P ctx nb → CalleeCompiledP env R P ctx b nb := by
  suffices H : ∀ m b, ht b < m → ∀ P ctx nb, Good b P ctx nb → CalleeCompiledP env R P ctx b nb from
    fun b => H (ht b + 1) b (Nat.lt_succ_self _)
  intro m
  induction m with
  | zero => intro b h; exact absurd h (Nat.not_lt_zero _)
  | succ m ih =>
    intro b hb P ctx nb hg
    exact hstep b P ctx nb hg fun b' P' ctx' nb' hlt hg' => ih b' (by omega) P' ctx' nb' hg'

/-! ## The gate -/

/-- **A callee of an SCC that is not a lone bell without a self call** (README Gaps 19 (g)): its
need, its `sccs` entry `S` with `hnd`, and track I's loop on `S` at every miss rest. -/
def SccCallee (env : CallEnv) (SC0 CODE JETS CALLS JH : Noun) (inl : Noun → Option Nomm) (b : Bell) : Prop :=
  ∃ nb S, env.need b = some nb ∧ getF mugF b.toNoun SC0 = some (C (A 0) S) ∧
    ((∀ n, S ≠ C n (C (A 0) (A 0))) ∨ ∃ n, S = C n (C (A 0) (A 0)) ∧ CalleeIn CALLS n n) ∧
    ∀ x NR CR, SccLoopAt env (RK SC0 inl) (fun _ => False) S CODE JETS CALLS JH x NR CR

/-- **What one callee of the caller takes**: readable at the start (the callees inside the
caller's SCC: `CsiNeeds`, `CsiSures`), or outside the caller's SCC and a one-bell callee or a
callee of any SCC. -/
def AnyCallee (env : CallEnv) (SC0 CODE JETS CALLS JH SCC : Noun) (inl : Noun → Option Nomm) (ctx : Noun)
    (x0 : GenRest) (b : Bell) : Prop :=
  (∃ nb, env.need b = some nb ∧ NeedRead ctx x0 b nb ∧ SureNoun env b x0) ∨
    (hasInF mugF b.toNoun SCC = some false ∧
      (OneCallee env SC0 CODE CALLS inl b ∨ SccCallee env SC0 CODE JETS CALLS JH inl b))

theorem callAt_any {FUNC SCC CODE JETS CALLS JH NM SC0 : Noun} {env : CallEnv} {inl : Noun → Option Nomm}
    {x0 : GenRest} {b : Bell} (hsg : SccsGood SC0) (hcj : IsMap mugF CALLS ∧ ∀ k v, Get CALLS k v → IsSet mugF v)
    (h : AnyCallee env SC0 CODE JETS CALLS JH SCC inl (cuCtx FUNC SCC CODE (C JETS CALLS) JH NM) x0 b) :
    ∃ nb, env.need b = some nb ∧
      CallAt env (RK SC0 inl) (cuCtx FUNC SCC CODE (C JETS CALLS) JH NM) x0 b nb := by
  have h7 : slot? 7 (cuCtx FUNC SCC CODE (C JETS CALLS) JH NM) = some compK := rfl
  have hl : slot? 26 (cuCtx FUNC SCC CODE (C JETS CALLS) JH NM) = some (C CODE (C JETS CALLS)) := by
    simp [cuCtx, nock_exec]
  have h107 : slot? 107 (cuCtx FUNC SCC CODE (C JETS CALLS) JH NM) = some CALLS := by simp [cuCtx, nock_exec]
  have h12 : slot? 12 (cuCtx FUNC SCC CODE (C JETS CALLS) JH NM) = some SCC := by simp [cuCtx, nock_exec]
  rcases h with ⟨nb, hnb, hr, hs⟩ | ⟨hout, hone | ⟨nb, S, hnb, hsc, hnd, hloop⟩⟩
  · exact ⟨nb, hnb, Or.inl ⟨hr, hs⟩⟩
  · obtain ⟨cape, DATA, FOL, nm, fuel, envb, p, st, rfl, hsc, hinl, hcalls, hcode, hn, hax, hfix, hbake, hone⟩ := hone
    refine ⟨st.need, hone.2.2.1, Or.inr ⟨SCC, h12, hout, ?_⟩⟩
    exact calleeCompiled_oneK (CODE := CODE) (JETS := JETS) (CALLS := CALLS) (JH := JH) h7 hl
      (cuCtx_hot _ _ _ _ _ _) h107 env envb cape DATA FOL nm fuel p st inl hsc hinl hcalls hcode hn hax hfix hbake hone
  · refine ⟨nb, hnb, Or.inr ⟨SCC, h12, hout, calleeCompiled_of_P ?_⟩⟩
    exact calleeCompiled_scc h7 hl (cuCtx_hot _ _ _ _ _ _) h107 env inl _ b nb S hsg hcj hsc hnd
      (fun _ _ h => h) hnb hloop

/-- **The gate of `+compile-unary` on `DirOk` with callees in SCCs of any size** (README Gaps
19 (g)).  Hypotheses: the state nouns (`hgot`, `hv`, `hcl`, `hcsi`), the invariants at the cache
`+compile-scc-in` returned (`AgreeE` `hE0`, `RK` `hR0`), the class `DirOk n`, the code table
(`EnvFrom`, `CodeNoRing`, `CodeAna`), the meaning of `sccs` (`SccsGood`), the jug `calls`, and per
callee `AnyCallee`: readable at the start, or outside the caller's SCC and either a one-bell
callee (`OneCallee`: track A's chain) or a callee of any SCC (`SccCallee`: track I's loop, whose
`MemGate` holds the nested misses).  The product carries a cache `CA'` that extends `CA` and keeps
both invariants. -/
theorem cu_gate_dir_scc (FUNC SCC CODE JETS CALLS JH CACHE NM CA V COLE SC0 : Noun) (env : CallEnv)
    (inl : Noun → Option Nomm) (n : Nomm)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun)
    (hcl : slot? 190 (C JETS CALLS) = some COLE)
    (hcsi : nock (cuTC (cuSam FUNC SCC CODE (C JETS CALLS) JH CACHE)) cuCsi = some (C NM CA))
    (hE0 : AgreeE env (cuRest CA)) (hR0 : RK SC0 inl (cuRest CA))
    (hn : DirOk n = true)
    (he : EnvFrom env CODE COLE) (hcr : CodeNoRing CODE COLE n) (hana : CodeAna CODE)
    (hsg : SccsGood SC0) (hcj : IsMap mugF CALLS ∧ ∀ k v, Get CALLS k v → IsSet mugF v)
    (hcal : ∀ b ∈ dirBells n,
      AnyCallee env SC0 CODE JETS CALLS JH SCC inl (cuCtx FUNC SCC CODE (C JETS CALLS) JH NM) (cuRest CA) b) :
    ∃ CA', Ext (cuRest CA) (cuRest CA') ∧ AgreeE env (cuRest CA') ∧ RK SC0 inl (cuRest CA') ∧
      nock (C cuGB (C (cuSam FUNC SCC CODE (C JETS CALLS) JH CACHE) compK)) cuGB
        = (finishLUCM (S := CSet) (Map := TreapMap mugF) env n).map fun st => C (C st.toNoun NM) CA' :=
  cu_gate_dirE FUNC SCC CODE (C JETS CALLS) JH CACHE NM CA V COLE env (RK SC0 inl) n hgot hv hcl hcsi hE0 hR0
    hn he hcr hana fun b hb => callAt_any hsg hcj (hcal b hb)

end Compiler
end Formalization
