import lemmas.Compiler.CompMonoLinkSccs
import lemmas.Compiler.PokeLinkGlue
import lemmas.Compiler.PokeLinkJetsCole

/-!
# The gate's record at `PGood6`, and track P's top over `PGood6` with it (README Gaps 19 (g))

Track P's top `pokeModel_fullReachP6L` (`PokeLinkGlue.lean`) takes the gate `hG` in the old form
`UnaryGateAt`, asked at EVERY bell `b` and set `sc` of a `PGood6` state, plus `UnaryCacheKeeps`
and `UnarySccsIs` (asked at every `PGood3` state, resp. every state).  The model's `%full` calls
`+compile-unary` only at the state of `good6_mid`, on the root bell `r.1` of the poke (a key of
the new table, P's `anaArmP_root`) and the set `q.1` of `+scc-of`, which is `sccSet` of the
table at `r.1` (Q's `sccOfP_is`).  So all three are asked here only there:

* `MonoLinkGood6K`, `UnarySccsIs6`, `UnaryCacheKeeps6`: at a `PGood6` state, a key `b` of the
  table, and `sc = sccSet code b`;
* `midClosedSccs`: the closed table and `SccsIs` before `+scc-of` (lines of P's
  `good6_full_step`); `pokeModel_fullGood6K`, `good3_full_stepK`, `good6_full_stepK`,
  `pokeReachGood6K`, `pokeModel_fullReachP6K` (P's theorems with the restricted links);
* `GateRest6Sw`: `GateRest5Sw` without `got`, `nomm` and `cole`, which are state facts
  (`gateRest5Sw_of_6`: `got` and `nomm` from the code entry by `codeNoun_getF`, `cole` from
  `JetsMaps`, `coleOf_good`);
* **`unarySccsIs6_of_gate`**: `UnarySccsIs6` from the record (`cu_sccs_of_gateS`);
* **`cacheGood_of_gate`**, **`unaryCacheKeeps6_of_gate`**: `UnaryCacheKeeps6` from the record
  and `UnaryRestKeys6`.  What the gate keeps of the cache it returns: `AgreeE` (`nary` and `sure`
  maps; a `nary` key has a `sure` entry; a BELL key of `sure` has a `nary` entry), `RK`
  (`sccs` is the state's, `inl` a map, `nary` closed under SCCs).  What `CacheGood` asks beyond
  that, the leaf `UnaryRestKeys6`: every key of `sure.cache` is a bell, and every entry of
  `inl.cache` is a key of the table with a nomm value (`inlKeys`); the gate's rest predicate
  speaks of `inl` only at the keys `inl` names, and `AgreeE` of `sure` only at bell keys;
* **`pokeModel_fullReachP6U`**: `pokeModel_fullReachP6L` with `hG` replaced by `GateRest6Sw`,
  `UnarySccsIs` gone, and `UnaryCacheKeeps` replaced by `UnaryRestKeys6`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeF SkaModel.PokeM FinMap

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section Defs

variable (fl : Flags) (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
  (Cls : Straight (TreapMap mugF) → Prop)

/-- `MonoLinkGood6` asked only at a key of the table and its SCC. -/
def MonoLinkGood6K : Prop :=
  ∀ (st : PSt) b e, PGood6 Cls st → FinMap.get st.long.code b = some e →
    MonoLinkAt fl Ar st b (sccSet st.long.code b)

/-- **`+compile-unary` keeps `SccsIs` and `SccsGoodM`**, at a `PGood6` state, a key and its SCC. -/
def UnarySccsIs6 : Prop :=
  ∀ (st : PSt) b e r, PGood6 Cls st → FinMap.get st.long.code b = some e →
    Ar.compileUnary b (sccSet st.long.code b) st.long st.jets st.hot st.cache = some r →
    SccsIs st.long.code r.2.sccs ∧ SccsGoodM r.2.sccs

/-- **`+compile-unary` keeps `CacheGood`**, at a `PGood6` state, a key and its SCC. -/
def UnaryCacheKeeps6 : Prop :=
  ∀ (st : PSt) b e r, PGood6 Cls st → FinMap.get st.long.code b = some e →
    Ar.compileUnary b (sccSet st.long.code b) st.long st.jets st.hot st.cache = some r →
    CacheGood st.long.code r.2

/-- **The leaf of `CacheGood` the gate does not keep** (K): on the pill's `+compile-unary` at a
`PGood6` state, a key and its SCC, every key of `sure.cache` is a bell, and every entry of
`inl.cache` is a key of the table with a nomm value. -/
def UnaryRestKeys6 : Prop :=
  ∀ (st : PSt) b e r, PGood6 Cls st → FinMap.get st.long.code b = some e →
    compileUnaryP fl b (sccSet st.long.code b) st.long st.jets st.hot st.cache = some r →
    (∀ kn v, Get r.2.rest.2 kn v → ∃ b' : Bell, kn = b'.toNoun) ∧
    (∀ kn v, Get r.2.rest.1 kn v → ∃ (b' : Bell) (e' : VarEntry FinMap) (nm : Nomm),
      kn = b'.toNoun ∧ FinMap.get st.long.code b' = some e' ∧ v = nm.toNoun)

end Defs

/-! ## The record at `PGood6` -/

/-- **`GateRest5Sw` without the state facts `got`, `nomm`, `cole`**: asked at a key `b` with
entry `e` (its nomm `e.nomm`, its code noun `[e.nomm flags]`), its SCC `sccSet code b`, and the
`COLE` of the state's jets.  Each field with its owner, as in `GateRest5Sw`. -/
structure GateRest6Sw (fl : Flags) (st : PSt) (b : Bell) (e : VarEntry FinMap) (NM CA COLE : Noun)
    (env : Comp.CallEnv) (inl : Noun → Option Nomm) (D : Bell → Prop) : Prop where
  /-- the poke's `+compile-scc-in` on `b`'s SCC inside `+compile-unary` (I) -/
  csi : nock (cuTC (cuSam b.toNoun (FinMap.setNoun (sccSet st.long.code b)) (codeNoun fl st.long.code)
    (C st.jets (callsNoun st.long)) st.hot (cacheNoun st.cache))) cuCsi = some (C NM CA)
  /-- the invariants at the cache after it (P/I) -/
  agree : AgreeE env (cuRest CA)
  rest : RK (sccsNoun st.cache.sccs) inl (cuRest CA)
  dec : CacheDec (st.cache.mono.toNoun Straight.toNoun) CA
  /-- the top loop's data with its gates proved (I, A) -/
  top : TopDecSh (FinMap.setNoun (sccSet st.long.code b)) (codeNoun fl st.long.code) st.jets (callsNoun st.long)
    st.hot (cacheNoun st.cache)
  /-- the class of `b`'s nomm (K) -/
  dir : DirOk e.nomm = true
  /-- the code table (no ring: K's link covers callees without a `call.cole` entry; `ana`: P) -/
  noRing : CodeNoRing (codeNoun fl st.long.code) COLE e.nomm
  ana : CodeAna (codeNoun fl st.long.code)
  /-- the table of callees (A, I, K) -/
  table : ∀ ht, HtRank (sccsNoun st.cache.sccs) (callsNoun st.long) ht → HtScc (sccsNoun st.cache.sccs) ht →
    ∀ b', D b' → CalleeHSDSw env (sccsNoun st.cache.sccs) (st.cache.mono.toNoun Straight.toNoun)
      (codeNoun fl st.long.code) st.jets (callsNoun st.long) st.hot inl ht D b'
  /-- each callee readable at the start or outside, in `D`, with a need (P/I) -/
  callees : ∀ b' ∈ dirBells e.nomm, AnyCalleeH env (FinMap.setNoun (sccSet st.long.code b)) D
    (cuCtx b.toNoun (FinMap.setNoun (sccSet st.long.code b)) (codeNoun fl st.long.code) (C st.jets (callsNoun st.long))
      st.hot NM)
    (cuRest CA) b'

/-- **`GateRest5Sw` from `GateRest6Sw`** and the state facts. -/
theorem gateRest5Sw_of_6 {fl : Flags} {st : PSt} {b : Bell} {e : VarEntry FinMap} {NM CA COLE : Noun}
    {need : Bell → Option SkaModel.NeedOrd} {sure : Bell → SkaModel.NeedOrd} {sof : Nomm → Nomm → Nomm → Bell → SkaModel.NeedOrd → Bool}
    {inl : Noun → Option Nomm} {D : Bell → Prop} (he : FinMap.get st.long.code b = some e)
    (hcole : slot? 190 (C st.jets (callsNoun st.long)) = some COLE)
    (H : GateRest6Sw fl st b e NM CA COLE (envOf (codeNoun fl st.long.code) COLE need sure sof) inl D) :
    GateRest5Sw fl st b (sccSet st.long.code b) NM CA (C e.nomm.toNoun (fl st.long.code b)) COLE
      (envOf (codeNoun fl st.long.code) COLE need sure sof) inl e.nomm D :=
  ⟨(gateGot_of_key fl st b e he).1, (gateGot_of_key fl st b e he).2, hcole, H.csi, H.agree, H.rest, H.dec, H.top,
    H.dir, envOf_from _ _ need sure sof, H.noRing, H.ana, H.table, H.callees⟩

/-- The record asked at every `PGood6` state, key, entry and `COLE`. -/
def GateRest6All (fl : Flags) (Cls : Straight (TreapMap mugF) → Prop) : Prop :=
  ∀ st b e COLE, PGood6 Cls st → FinMap.get st.long.code b = some e →
    slot? 190 (C st.jets (callsNoun st.long)) = some COLE →
    ∃ (NM CA : Noun) (need : Bell → Option SkaModel.NeedOrd) (sure : Bell → SkaModel.NeedOrd)
      (sof : Nomm → Nomm → Nomm → Bell → SkaModel.NeedOrd → Bool) (inl : Noun → Option Nomm) (D : Bell → Prop),
      GateRest6Sw fl st b e NM CA COLE (envOf (codeNoun fl st.long.code) COLE need sure sof) inl D

/-- **The gate `UnaryGateAtS` from the record** at a key of a `PGood6` state. -/
theorem unaryGateAtS_of_6 {fl : Flags} {Cls : Straight (TreapMap mugF) → Prop} (hGR : GateRest6All fl Cls)
    {st : PSt} {b : Bell} {e : VarEntry FinMap} (hg : PGood6 Cls st) (he : FinMap.get st.long.code b = some e) :
    ∃ (NM CA V COLE : Noun) (envK : Comp.CallEnv) (inl : Noun → Option Nomm) (ht : Noun → Nat) (D : Bell → Prop),
      UnaryGateAtS fl st b (sccSet st.long.code b) NM CA V COLE (sccsNoun st.cache.sccs) envK inl e.nomm ht D := by
  obtain ⟨-, -, -, -, -, COLE, -, -, -, hcole⟩ := gateCole_of_good hg
  obtain ⟨NM, CA, need, sure, sof, inl, D, H⟩ := hGR st b e COLE hg he hcole
  obtain ⟨ht, H'⟩ := unaryGateAtS_of_good5 hg.good5 (gateRest5_of_Sw hg.good5 (gateRest5Sw_of_6 he hcole H))
  exact ⟨NM, CA, _, COLE, _, inl, ht, D, H'⟩

/-- **`MonoLinkGood6K` from the record.** -/
theorem monoLinkGood6K_of_gate (fl : Flags) (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
    (Cls : Straight (TreapMap mugF) → Prop) (hUA : Ar.compileUnary = compileUnaryP fl) (hGR : GateRest6All fl Cls) :
    MonoLinkGood6K fl Ar Cls := by
  intro st b e hg he
  obtain ⟨NM, CA, V, COLE, envK, inl, ht, D, H⟩ := unaryGateAtS_of_6 hGR hg he
  exact monoLinkAt_of fl Ar hUA st b _ (unaryImageAt_of_gateDS H) (monoMissAt_of fl st b _)

/-- **`UnarySccsIs6` from the record** (`cu_sccs_of_gateS`). -/
theorem unarySccsIs6_of_gate {fl : Flags} {Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)}
    {Cls : Straight (TreapMap mugF) → Prop} (hUA : Ar.compileUnary = compileUnaryP fl) (hGR : GateRest6All fl Cls) :
    UnarySccsIs6 Ar Cls := by
  intro st b e r hg he hr
  rw [hUA] at hr
  obtain ⟨NM, CA, V, COLE, envK, inl, ht, D, H⟩ := unaryGateAtS_of_6 hGR hg he
  rw [cu_sccs_of_gateS H hr]
  exact ⟨hg.good5.sccsIs, hg.good5.good4.good3.good2.cache.sccs⟩

/-! ## The cache the gate returns -/

/-- **What the gate keeps of the cache it returns**: `AgreeE` and `RK` at the noun of `r.2`. -/
theorem cu_cache_of_gateS {fl : Flags} {st : PSt} {b : Bell} {sc : FinMap Bell Unit} {NM CA V COLE SC0 : Noun}
    {env : Comp.CallEnv} {inl : Noun → Option Nomm} {n : Nomm} {ht : Noun → Nat} {D : Bell → Prop}
    (H : UnaryGateAtS fl st b sc NM CA V COLE SC0 env inl n ht D)
    {r : (Straight (TreapMap mugF) × FinMap Bell (Straight (TreapMap mugF))) × Cache FinMap (TreapMap mugF) (Noun × Noun)}
    (hr : compileUnaryP fl b sc st.long st.jets st.hot st.cache = some r) :
    AgreeE env (cuRest (cacheNoun r.2)) ∧ RK SC0 inl (cuRest (cacheNoun r.2)) := by
  obtain ⟨CA', -, hA, hR, -, hg⟩ := cu_gate_dir_sccDS b.toNoun (FinMap.setNoun sc) (codeNoun fl st.long.code)
    st.jets (callsNoun st.long) st.hot (cacheNoun st.cache) NM CA V COLE SC0 (st.cache.mono.toNoun Straight.toNoun)
    env inl n ht D H.got H.nomm H.cole H.csi H.agree H.rest H.dec H.dir H.envFrom H.noRing H.ana H.sccsGood H.jug
    H.heights H.table H.callees
  unfold compileUnaryP at hr
  split at hr
  · rename_i hx
    have hspec := Classical.choose_spec hx
    cases hr
    have hspec' : nock (C cuGB (C (cuSam b.toNoun (FinMap.setNoun sc) (codeNoun fl st.long.code)
        (C st.jets (callsNoun st.long)) st.hot (cacheNoun st.cache)) compK)) cuGB = some (cuResNoun (Classical.choose hx)) :=
      hspec
    rw [hg] at hspec'
    obtain ⟨s, -, e⟩ := Option.map_eq_some_iff.1 hspec'
    have eCA : CA' = cacheNoun (Classical.choose hx).2 := (Noun.cell.inj e).2
    rw [eCA] at hA hR
    exact ⟨hA, hR⟩
  · cases hr

/-- **`CacheGood` from what the gate keeps and the leaf's two key clauses.** -/
theorem cacheGood_of_gate {code : FinMap Bell (VarEntry FinMap)} {c : Cache FinMap (TreapMap mugF) (Noun × Noun)}
    {env : Comp.CallEnv} {inl : Noun → Option Nomm}
    (hA : AgreeE env (cuRest (cacheNoun c))) (hR : RK (sccsNoun c.sccs) inl (cuRest (cacheNoun c)))
    (hsg : SccsGoodM c.sccs)
    (hsu : ∀ kn v, Get c.rest.2 kn v → ∃ b' : Bell, kn = b'.toNoun)
    (hin : ∀ kn v, Get c.rest.1 kn v → ∃ (b' : Bell) (e' : VarEntry FinMap) (nm : Nomm),
      kn = b'.toNoun ∧ FinMap.get code b' = some e' ∧ v = nm.toNoun) :
    CacheGood code c := by
  obtain ⟨-, NR, MO, SC, INL, SU, hc, hNR, hSU, h1, h2⟩ := hA
  change cacheNoun c = cacheN NR MO SC INL SU at hc
  simp only [cacheNoun, cacheN, Noun.cell.injEq] at hc
  obtain ⟨rfl, -, -, rfl, rfl⟩ := hc
  obtain ⟨⟨NR', MO', INL', SU', hc', hINL, -⟩, NR2, hNR2, hcl⟩ := hR
  change cacheNoun c = cacheN NR' MO' (sccsNoun c.sccs) INL' SU' at hc'
  simp only [cacheNoun, cacheN, Noun.cell.injEq] at hc'
  obtain ⟨-, -, -, rfl, -⟩ := hc'
  have eNR2 : NR2 = c.nary.toNoun Straight.toNoun := by
    have : slot? 2 (cacheNoun c) = some (c.nary.toNoun Straight.toNoun) := by
      simp only [cacheNoun]; rw [slot?_step 2 (by omega)]; simp [child]
    exact Option.some.inj (hNR2.symm.trans this)
  subst eNR2
  -- a key of `nary` from a `getF` hit on its noun
  have naryOf : ∀ (k : Bell) u, getF mugF k.toNoun (c.nary.toNoun Straight.toNoun) = some (C (A 0) u) →
      ∃ s, FinMap.get c.nary k = some s := by
    intro k u hk
    obtain ⟨b', x, hb', hkb, -⟩ := getF_toNoun_some Straight.toNoun c.nary k.toNoun u hk
    have : k = b' := TKey.enc_inj _ _ hkb
    subst this
    exact ⟨x, hb'⟩
  have naryNoun : ∀ (k : Bell) s, FinMap.get c.nary k = some s →
      getF mugF k.toNoun (c.nary.toNoun Straight.toNoun) = some (C (A 0) s.toNoun) := by
    intro k s hk
    have e := FinMap.getF_toNoun Straight.toNoun c.nary k
    rw [show c.nary.get k = some s from hk] at e
    exact e
  refine ⟨hSU, fun kn => ⟨fun ⟨v, hv⟩ => ?_, fun ⟨b', s, hkn, hb'⟩ => ?_⟩, hINL, hin, hsg, ?_⟩
  · obtain ⟨b', rfl⟩ := hsu kn v hv
    obtain ⟨-, u, hu⟩ := h2 b' v (getF_some hSU hv)
    obtain ⟨s, hs⟩ := naryOf b' u hu
    exact ⟨b', s, rfl, hs⟩
  · subst hkn
    obtain ⟨-, v, hv⟩ := h1 b' s.toNoun (naryNoun b' s hb')
    exact ⟨v, get_of_getF hSU hv⟩
  · intro k s hk
    obtain ⟨S, hS, hall⟩ := hcl k.toNoun s.toNoun (naryNoun k s hk)
    obtain ⟨b', S', hb', hkb, rfl⟩ := getF_toNoun_some FinMap.setNoun c.sccs k.toNoun S hS
    have : k = b' := TKey.enc_inj _ _ hkb
    subst this
    refine ⟨S', hb', fun k' hk' => ?_⟩
    have hm : k'.toNoun ∈ tapList (FinMap.setNoun S') :=
      (mem_tapList_set (isSet_setNoun S') _).2 ((has_setNoun_enc S' k').2 hk')
    obtain ⟨u', hu'⟩ := hall k'.toNoun hm
    exact naryOf k' u' hu'

/-- **`UnaryCacheKeeps6` from the record and the leaf `UnaryRestKeys6`.** -/
theorem unaryCacheKeeps6_of_gate {fl : Flags} {Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)}
    {Cls : Straight (TreapMap mugF) → Prop} (hUA : Ar.compileUnary = compileUnaryP fl) (hGR : GateRest6All fl Cls)
    (hRK : UnaryRestKeys6 fl Cls) : UnaryCacheKeeps6 Ar Cls := by
  intro st b e r hg he hr
  rw [hUA] at hr
  obtain ⟨NM, CA, V, COLE, envK, inl, ht, D, H⟩ := unaryGateAtS_of_6 hGR hg he
  obtain ⟨hA, hR⟩ := cu_cache_of_gateS H hr
  have hs : r.2.sccs = st.cache.sccs := cu_sccs_of_gateS H hr
  rw [← hs] at hR
  obtain ⟨hsu, hin⟩ := hRK st b e r hg he hr
  exact cacheGood_of_gate hA hR (hs ▸ hg.good5.good4.good3.good2.cache.sccs) hsu hin

/-! ## Track P's theorems with the restricted links -/

section Keep

variable {Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)} {Cls : Straight (TreapMap mugF) → Prop}
  {R : Type} {envR : Env R}
  {jet : Noun → Noun → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
  {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → R}
  {jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun} {newOf : R → Noun}

/-- **The closed table and `SccsIs` before `+scc-of`** (the lines of P's `good6_full_step`). -/
theorem midClosedSccs (hA : Ar.skaPoke = anaArmP envR jet fold frozen fuel bf regOf jetsOf newOf)
    (st : PSt) (s f : Noun) (hg : PGood5 Cls st) (r : Bell × LongB FinMap × Noun × Noun)
    (e1 : Ar.skaPoke s f st.long st.jets st.hot = some r) :
    CodeClosed r.2.1.code ∧ SccsIs r.2.1.code st.cache.sccs := by
  have e1' := e1
  rw [hA] at e1'
  obtain ⟨E, n, bg, reg', hbg, hEv, hcode, -⟩ := anaArmP_bake e1'
  have hc := hg.good4.good3.good2.closed
  have hv : VarsKeys E.vars st.long.code := hEv ▸ hg.good4.good3.vars
  have hc' := (addCode_closed hc hv hbg).1
  have hsc := sccsIs_addCode (addsTo_addCode st.long.code bg.1) hc hg.sccsIs hg.good4.good3.good2.cache.sccs
  rw [← hcode] at hc' hsc
  exact ⟨hc', hsc⟩

/-- **The mid state's call**: the root is a key of the new table and `q.1` is its `sccSet`. -/
theorem mid_key (hA : Ar.skaPoke = anaArmP envR jet fold frozen fuel bf regOf jetsOf newOf)
    (hSA : Ar.sccOf = sccOfP) (st : PSt) (s f : Noun) (hg : PGood5 Cls st) (r : Bell × LongB FinMap × Noun × Noun)
    (e1 : Ar.skaPoke s f st.long st.jets st.hot = some r)
    (q : FinMap Bell Unit × FinMap Bell (FinMap Bell Unit)) (e3 : Ar.sccOf r.1 r.2.1 st.cache.sccs = some q) :
    (∃ e, FinMap.get r.2.1.code r.1 = some e) ∧ q.1 = sccSet r.2.1.code r.1 := by
  have e1' := e1
  rw [hA] at e1'
  have hb := anaArmP_root e1'
  obtain ⟨hc', hsc⟩ := midClosedSccs hA st s f hg r e1
  rw [hSA] at e3
  exact ⟨hb, (sccOfP_is hc' hsc hg.good4.good3.good2.cache.sccs hb e3).2⟩

/-- **The model's `%full` keeps `PGood3`**, with the cache fact asked at the mid state's call
only (P's `good3_full_step`, the last line changed). -/
theorem good3_full_stepK (hK : SkaKeeps Ar) (hU : UnaryKeeps Ar Cls) (hS : SkaCodeKeeps Ar) (hO : SccOfKeeps Ar)
    (st : PSt) (s f : Noun) (pr : SkaModel.Prod (TreapMap mugF)) (st' : PSt)
    (hC : ∀ r (q : FinMap Bell Unit × FinMap Bell (FinMap Bell Unit)) r', Ar.skaPoke s f st.long st.jets st.hot = some r →
      Ar.sccOf r.1 r.2.1 st.cache.sccs = some q →
      Ar.compileUnary r.1 q.1 r.2.1 r.2.2.1 st.hot { st.cache with sccs := q.2 } = some r' →
      CacheGood r.2.1.code r'.2)
    (hg : PGood3 Cls st) (h : pokeS Ar st (Ovum.full s f) = some (pr, st')) : PGood3 Cls st' := by
  have hgood := good_full_step hK hU st s f pr st' hg.good2.good h
  simp only [pokeS] at h
  obtain ⟨r, e1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨hc', hv', hold⟩ := hS st s f r hg.good2.closed hg.vars e1
  split at h
  · cases h
    exact ⟨⟨hgood, hc', cacheGood_code hg.good2.cache hold⟩, hv'⟩
  · obtain ⟨p, hp, e⟩ := Option.map_eq_some_iff.1 h
    cases e
    unfold compileStep at hp
    obtain ⟨q, e3, hp⟩ := Option.bind_eq_some_iff.1 hp
    obtain ⟨p', hp', e⟩ := Option.map_eq_some_iff.1 hp
    cases e
    simp only [if_true] at hp'
    have hmid := good3_mid hK hS hO st s f hg r e1 q e3
    refine ⟨⟨hgood, hc', ?_⟩, hv'⟩
    unfold compiledMono at hp'
    split at hp'
    · cases hp'; exact hmid.good2.cache
    · obtain ⟨r', hr', e⟩ := Option.map_eq_some_iff.1 hp'
      cases e
      exact cacheGood_mono _ (hC r q r' e1 e3 hr')

/-- **The model's `%full` keeps `PGood6`**, with `UnaryCacheKeeps6` and `UnarySccsIs6` (P's
`good6_full_step`; the two calls at the mid state through `mid_key`). -/
theorem good6_full_stepK (hA : Ar.skaPoke = anaArmP envR jet fold frozen fuel bf regOf jetsOf newOf)
    (hSA : Ar.sccOf = sccOfP)
    (hK : SkaKeeps Ar) (hU : UnaryKeeps Ar Cls) (hO : SccOfKeeps Ar) (hC : UnaryCacheKeeps6 Ar Cls)
    (hSI : SccOfIsK Ar) (hUS : UnarySccsIs6 Ar Cls) (hTE : TarjanExists) (hJC : JetsOfCole6 jetsOf)
    (st : PSt) (s f : Noun) (pr : SkaModel.Prod (TreapMap mugF)) (st' : PSt)
    (hg : PGood6 Cls st) (h : pokeS Ar st (Ovum.full s f) = some (pr, st')) : PGood6 Cls st' := by
  have hg3 := good3_full_stepK hK hU (skaCodeKeeps_of_armP Ar hA) hO st s f pr st'
    (fun r q r' e1 e3 hr' => by
      obtain ⟨⟨eb, heb⟩, hq⟩ := mid_key hA hSA st s f hg.good5 r e1 q e3
      have hm := good6_mid hA hK hO hSI hTE hJC st s f hg r e1 q e3
      rw [hq] at hr'
      exact hC { st with long := r.2.1, jets := r.2.2.1, cache := { st.cache with sccs := q.2 } } r.1 eb r' hm heb hr')
    hg.good5.good4.good3 h
  simp only [pokeS] at h
  obtain ⟨r, e1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨hcole, hdom⟩ := cole_poke hA hJC st s f hg r e1
  have e1' := e1
  rw [hA] at e1'
  obtain ⟨E, n, bg, reg', hbg, hEv, hcode, -⟩ := anaArmP_bake e1'
  obtain ⟨lib, hInv⟩ := hg.good5.invB
  have hInv' : InvB lib r.2.1 := ((anaHyp_of_armP (lib := lib) Ar hA).ana s f st.long st.jets st.hot r e1 hInv).1
  have hc := hg.good5.good4.good3.good2.closed
  have hv : VarsKeys E.vars st.long.code := hEv ▸ hg.good5.good4.good3.vars
  have hi := hg.good5.good4.info
  obtain ⟨F, hF, hFt⟩ := hg.good5.good4.flags
  obtain ⟨L, hL⟩ := hTE (newCode st.long.code bg.1)
  obtain ⟨G, hG⟩ := loopTotal_poke hc hv hi hbg hFt hInv' hcode L hL
  obtain ⟨hi', hG1, hG2⟩ := flags_poke hc hv hi hbg hL hF hFt hG
  have hc' := (addCode_closed hc hv hbg).1
  have hsc := sccsIs_addCode (addsTo_addCode st.long.code bg.1) hc hg.good5.sccsIs
    hg.good5.good4.good3.good2.cache.sccs
  rw [← hcode] at hi' hG1 hG2 hc' hsc
  have key : ∀ st'' : PSt, st''.long = r.2.1 → st''.jets = r.2.2.1 → SccsIs r.2.1.code st''.cache.sccs →
      PGood3 Cls st'' → PGood6 Cls st'' := fun st'' hl hj hs h3 =>
    ⟨⟨⟨h3, hl ▸ hi', ⟨G, hl ▸ hG1, hl ▸ hG2⟩⟩, ⟨lib, hl ▸ hInv'⟩, hl ▸ hs, hj ▸ hcole⟩, hj ▸ hl ▸ hdom⟩
  split at h
  · cases h
    exact key _ rfl rfl hsc hg3
  · obtain ⟨p, hp, e⟩ := Option.map_eq_some_iff.1 h
    cases e
    unfold compileStep at hp
    obtain ⟨q, e3, hp⟩ := Option.bind_eq_some_iff.1 hp
    obtain ⟨p', hp', e⟩ := Option.map_eq_some_iff.1 hp
    cases e
    simp only [if_true] at hp'
    have hsq : SccsIs r.2.1.code q.2 :=
      hSI _ _ _ q hc' hsc hg.good5.good4.good3.good2.cache.sccs (anaArmP_root e1') e3
    refine key _ rfl rfl ?_ hg3
    unfold compiledMono at hp'
    split at hp'
    · cases hp'; exact hsq
    · obtain ⟨r', hr', e⟩ := Option.map_eq_some_iff.1 hp'
      cases e
      obtain ⟨⟨eb, heb⟩, hq⟩ := mid_key hA hSA st s f hg.good5 r e1 q e3
      rw [hq] at hr'
      exact (hUS { st with long := r.2.1, jets := r.2.2.1, cache := { st.cache with sccs := q.2 } } r.1 eb r'
        (good6_mid hA hK hO hSI hTE hJC st s f hg r e1 q e3) heb hr').1

end Keep

section Links

variable (fl : Flags) (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
  (Cls : Straight (TreapMap mugF) → Prop)

variable {R : Type} {envR : Env R}
  {jet : Noun → Noun → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
  {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → R}
  {jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun} {newOf : R → Noun}

/-- **`pokeModel` on every `%full` at a `PGood6` state**, with `MonoLinkGood6K` (P's
`pokeModel_fullGood6`, the `+compiled-mono` link at the mid state through `mid_key`). -/
theorem pokeModel_fullGood6K (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP)
    (hA : Ar.skaPoke = anaArmP envR jet fold frozen fuel bf regOf jetsOf newOf) (hSA : Ar.sccOf = sccOfP)
    (hJA : Ar.jetRoot = jetRootP) (hR : SpRestGood6 fl Ar Cls env) (hC : SccLink fl Ar sccP)
    (hM : MonoLinkGood6K fl Ar Cls) (hO : OptLinkOn Cls Ar optP) (hK : SkaKeeps Ar) (hU : UnaryKeeps Ar Cls)
    (hSc : SccOfKeeps Ar) (hSI : SccOfIsK Ar) (hTE : TarjanExists) (hJC : JetsOfCole6 jetsOf)
    (hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none) (st : PSt) (hg : PGood6 Cls st) (s f : Noun) :
    pokeN (enc fl st) (Ovum.full s f).toNoun =
      (liftPoke (enc fl) (pokeS Ar) (enc fl st) (Ovum.full s f)).map fun r => C r.1.toNoun r.2 := by
  have hg2 := hg.good5.good4.good3.good2
  cases f with
  | atom a => rw [pokeN_full_atom, liftPoke_enc_fl]; simp [pokeS, hAt]
  | cell f₁ f₂ =>
    refine pokeN_fullAt4 fl Ar Cls hC hO st s f₁ f₂ ?_ (fun r e => ?_) (fun r q e e3 => ?_)
      (optInAt_of_good hK hU st s _ hg2.good)
    · obtain ⟨r1, r2, r3, r4, pd, ca, bk, hj, -⟩ := hg2.good.maps
      obtain ⟨key, hk, -, -⟩ := keyRaw_enc fl st hg2.good.jets.2
      exact skaLinkAt_of fl Ar env hhe hth hsoft hrf st s (C f₁ f₂) r1 r2 r3 r4 (C pd (C ca bk)) key hj hk
        (hR st s f₁ f₂ r1 r2 r3 r4 _ key hg hj hk)
    · obtain ⟨_, hj'⟩ := hK st s _ r hg2.good.maps hg2.good.jets e
      exact jetRootLinkG_of fl Ar hJA st s _ r e hj'
    · obtain ⟨⟨eb, heb⟩, hq⟩ := mid_key hA hSA st s _ hg.good5 r e q e3
      rw [hq]
      exact hM _ r.1 eb (good6_mid hA hK hSc hSI hTE hJC st s _ hg r e q e3) heb

/-- **Every core the pill reaches is an encoded `PGood6` state**, with the restricted links (P's
`pokeReachGood6`). -/
theorem pokeReachGood6K (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP) (lib : Lib)
    (hA : Ar.skaPoke = anaArmP envR jet fold frozen fuel bf regOf jetsOf newOf) (hSA : Ar.sccOf = sccOfP)
    (hJA : Ar.jetRoot = jetRootP) (hR : SpRestGood6 fl Ar Cls env) (hC : SccLink fl Ar sccP)
    (hM : MonoLinkGood6K fl Ar Cls) (hO : OptLinkOn Cls Ar optP) (hK : SkaKeeps Ar) (hU : UnaryKeeps Ar Cls)
    (hSc : SccOfKeeps Ar) (hCK : UnaryCacheKeeps6 Ar Cls) (hSI : SccOfIsK Ar) (hUS : UnarySccsIs6 Ar Cls)
    (hTE : TarjanExists) (hJC : JetsOfCole6 jetsOf)
    (hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none) (hX : OtherKeeps6 fl Cls) :
    ∀ cr, PokeReach cr → ∃ st, PGood6 Cls st ∧ enc fl st = cr := by
  intro cr h
  induction h with
  | start => exact ⟨emptySt, good6_empty Cls lib, (cor_enc fl).symm⟩
  | @poke c ovo p c' _ hp hh ih =>
    obtain ⟨st, hg, rfl⟩ := ih
    by_cases e : ∃ s f, ovo = (Ovum.full s f).toNoun
    · obtain ⟨s, f, rfl⟩ := e
      rw [pokeModel_fullGood6K fl Ar Cls env hhe hth hsoft hrf hA hSA hJA hR hC hM hO hK hU hSc hSI hTE hJC hAt st hg
        s f, liftPoke_enc_fl] at hp
      cases e' : pokeS Ar st (Ovum.full s f) with
      | none => rw [e'] at hp; cases hp
      | some q =>
        rw [e'] at hp
        simp only [Option.map_some, Option.some.injEq, Noun.cell.injEq] at hp
        exact ⟨q.2, good6_full_stepK hA hSA hK hU hSc hCK hSI hUS hTE hJC st s f q.1 q.2 hg e', hp.2⟩
    · exact hX st ovo p c' hg hp hh fun s f h => e ⟨s, f, h⟩

end Links

/-- **`pokeModel` on `%full` at every reachable core, over `PGood6`, with the restricted links**
(P's `pokeModel_fullReachP6` with `MonoLinkGood6K`, `UnaryCacheKeeps6`, `UnarySccsIs6`). -/
theorem pokeModel_fullReachP6K (fl : Flags) (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
    (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP) (lib : Lib)
    {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → Noun}
    {jetsOf : Noun → Noun → Noun → LongB FinMap → LongB FinMap → Noun} {newOf : Noun → Noun}
    (hA : Ar.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf)
    (hJA : Ar.jetRoot = jetRootP) (hOA : Ar.optimize = optimizeP) (hSA : Ar.sccOf = sccOfP)
    (hR : SpRestGood6 fl Ar OptTotal env) (hM : MonoLinkGood6K fl Ar OptTotal)
    (hJ : JetsOfGood jetsOf) (hJC : JetsOfCole6 jetsOf)
    (hU : UnaryKeeps Ar OptTotal) (hCK : UnaryCacheKeeps6 Ar OptTotal) (hUS : UnarySccsIs6 Ar OptTotal)
    (hX : OtherKeeps6 fl OptTotal) :
    ∀ cr, CorIn cr → ∀ s f, pokeN cr (Ovum.full s f).toNoun =
      (liftPoke (enc fl) (pokeS Ar) cr (Ovum.full s f)).map fun r => C r.1.toNoun r.2 := by
  have hI : SccImage := sccImage
  have hSc : SccOfKeeps Ar := sccOfKeeps_of hSA
  have hSI : SccOfIsK Ar := sccOfIsK_of hSA
  have hTE : TarjanExists := tarjanExists
  have hK := skaKeeps_of_armP Ar hA hJ
  have hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none := fun s a L j h => by
    rw [hA]; exact anaArmP_atom env jet fold frozen fuel bf regOf jetsOf newOf s a L j h
  intro cr hc s f
  obtain ⟨st, hg, rfl⟩ := pokeReachGood6K fl Ar OptTotal env hhe hth hsoft hrf lib hA hSA hJA hR (sccLink_of fl hSA hI)
    hM (optLinkOn_optimizeP hOA) hK hU hSc hCK hSI hUS hTE hJC hAt hX cr hc.2.2
  exact pokeModel_fullGood6K fl Ar OptTotal env hhe hth hsoft hrf hA hSA hJA hR (sccLink_of fl hSA hI) hM
    (optLinkOn_optimizeP hOA) hK hU hSc hSI hTE hJC hAt st hg s f

/-- **THE TOP: `pokeModel` on `%full` at every reachable core, over `PGood6`, at the flags
`flagsOf`, with track K's record `GateRest6Sw`**: track P's `pokeModel_fullReachP6L` with `hG`
replaced by `GateRest6All` (no `got`, `nomm`, `cole`: state facts), `UnarySccsIs` gone
(`unarySccsIs6_of_gate`), and `UnaryCacheKeeps` replaced by the leaf `UnaryRestKeys6`
(`unaryCacheKeeps6_of_gate`). -/
theorem pokeModel_fullReachP6U (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
    (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP) (lib : Lib)
    {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → Noun}
    {jetsOf : Noun → Noun → Noun → LongB FinMap → LongB FinMap → Noun} {newOf : Noun → Noun}
    (hA : Ar.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf)
    (hJA : Ar.jetRoot = jetRootP) (hOA : Ar.optimize = optimizeP) (hSA : Ar.sccOf = sccOfP)
    (hUA : Ar.compileUnary = compileUnaryP flagsOf)
    (hF : FuelOK env regOf fuel)
    (hreg : ∀ r1 r2 r3 r4 jRest, regOf (C r1 (C r2 (C r3 (C r4 jRest)))) = C r1 (C r2 (C r3 (C r4 (A 0)))))
    (hL : SpLeavesGood OptTotal env jet fold frozen bf jetsOf newOf)
    (hGR : GateRest6All flagsOf OptTotal) (hRK : UnaryRestKeys6 flagsOf OptTotal)
    (hJ : JetsOfGood jetsOf) (hJC : JetsOfCole6 jetsOf)
    (hU : UnaryKeeps Ar OptTotal) (hX : OtherKeeps6 flagsOf OptTotal) :
    ∀ cr, CorIn cr → ∀ s f, pokeN cr (Ovum.full s f).toNoun =
      (liftPoke (enc flagsOf) (pokeS Ar) cr (Ovum.full s f)).map fun r => C r.1.toNoun r.2 :=
  pokeModel_fullReachP6K flagsOf Ar env hhe hth hsoft hrf lib hA hJA hOA hSA
    (spRestGood6_of_leaves Ar OptTotal env hA hF hreg hL) (monoLinkGood6K_of_gate flagsOf Ar OptTotal hUA hGR)
    hJ hJC hU (unaryCacheKeeps6_of_gate hUA hGR hRK) (unarySccsIs6_of_gate hUA hGR) hX

/-- **THE TOP at track P's concrete route: `pokeModel_fullReachP9` with track K's record**:
`pokeModel_fullReachP6U` at `jetsOfP`, `newOfP`, `regOfP`, the fuel `anaFuel env regOfP`
(P's `fuelOK_anaFuel`, `regOfP_shape`, `jetsOfGood_P`, `jetsOfCole6_P`). -/
theorem pokeModel_fullReachP9U (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
    (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP) (lib : Lib)
    {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool}
    {bf : BEnv FinMap → Nat}
    (hA : Ar.skaPoke = anaArmP env jet fold frozen (anaFuel env regOfP) bf regOfP jetsOfP newOfP)
    (hJA : Ar.jetRoot = jetRootP) (hOA : Ar.optimize = optimizeP) (hSA : Ar.sccOf = sccOfP)
    (hUA : Ar.compileUnary = compileUnaryP flagsOf)
    (hL : SpLeavesGood OptTotal env jet fold frozen bf jetsOfP newOfP)
    (hGR : GateRest6All flagsOf OptTotal) (hRK : UnaryRestKeys6 flagsOf OptTotal)
    (hU : UnaryKeeps Ar OptTotal) (hX : OtherKeeps6 flagsOf OptTotal) :
    ∀ cr, CorIn cr → ∀ s f, pokeN cr (Ovum.full s f).toNoun =
      (liftPoke (enc flagsOf) (pokeS Ar) cr (Ovum.full s f)).map fun r => C r.1.toNoun r.2 :=
  pokeModel_fullReachP6U Ar env hhe hth hsoft hrf lib hA hJA hOA hSA hUA (fuelOK_anaFuel env regOfP) regOfP_shape hL
    hGR hRK jetsOfGood_P jetsOfCole6_P hU hX

end Compiler
end Formalization
