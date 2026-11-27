import lemmas.Compiler.CompMonoLinkTop5Sw
import lemmas.Compiler.CompSccOfMissImg

/-!
# `+compile-unary` keeps `sccs.cache`, from the gate (README Gaps 19 (g), `UnarySccsIs`)

Track P's `UnarySccsIs` (`PokeLinkGood5.lean`) is asked at EVERY state (`CodeClosed` and `SccsIs`
only).  It has the shape of `SccOfIs`, which track Q showed false as stated (`sccOfIs_needs_key`,
`sccOfIs_needs_good`), and nothing here proves it at an arbitrary state: that would need the link
of the pill's `+compile-unary` where its `+scc-of`s miss, which the gate does not cover.

Under the gate's record the question is simpler: every callee the gate compiles has an entry in
`sccs` (`CalleeHSDS` and `OneCalleeA` carry it), so every `+scc-of` of `+callee-compiled` hits
(`ccc_scc_hit`), and the rest predicate `RK SC0 inl` (`RInl`: `sccs.cache` is `SC0`) holds at the
cache the gate returns.  So `+compile-unary` returns the state's own `sccs`:

* **`cu_sccs_of_gateS`**: at a state with `UnaryGateAtS`, a result `r` of `compileUnaryP` has
  `r.2.sccs = st.cache.sccs`;
* `UnarySccsIs5`: `UnarySccsIs` at `PGood5` states, with `SccsGoodM` added to the conclusion (the
  form `good5_full_step` can use: its call is at the state of `good5_mid`, which is `PGood5`);
* **`unarySccsIs5_of_gate`**: `UnarySccsIs5` from `GateRest5Sw` at every `PGood5` state;
* `good5_full_stepU`, `pokeReachGood5U` (track P's `good5_full_step`, `pokeReachGood5` with
  `UnarySccsIs5` and `good5_mid` at the call; the proofs copied, one line changed);
* **`pokeModel_fullReachP5U`**: `pokeModel_fullReachP5Sw` without `UnarySccsIs`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeF SkaModel.PokeM FinMap

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **`+compile-unary` returns the state's `sccs`** at a state with the gate's record: the gate's
cache `CA'` has `RK SC0 inl`, so its `sccs` is `SC0 = sccsNoun st.cache.sccs`. -/
theorem cu_sccs_of_gateS {fl : Flags} {st : PSt} {b : Bell} {sc : FinMap Bell Unit} {NM CA V COLE SC0 : Noun}
    {env : Comp.CallEnv} {inl : Noun → Option Nomm} {n : Nomm} {ht : Noun → Nat} {D : Bell → Prop}
    (H : UnaryGateAtS fl st b sc NM CA V COLE SC0 env inl n ht D)
    {r : (Straight (TreapMap mugF) × FinMap Bell (Straight (TreapMap mugF))) × Cache FinMap (TreapMap mugF) (Noun × Noun)}
    (hr : compileUnaryP fl b sc st.long st.jets st.hot st.cache = some r) : r.2.sccs = st.cache.sccs := by
  obtain ⟨CA', -, -, hR, -, hg⟩ := cu_gate_dir_sccDS b.toNoun (FinMap.setNoun sc) (codeNoun fl st.long.code)
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
    obtain ⟨⟨NR, MO, INL, SU, hc, -⟩, -⟩ := hR
    change CA' = cacheN NR MO SC0 INL SU at hc
    rw [eCA] at hc
    simp only [cacheNoun, cacheN, Noun.cell.injEq] at hc
    obtain ⟨-, -, hs, -⟩ := hc
    rw [H.sccs] at hs
    exact sccsNoun_inj hs
  · cases hr

/-- **`UnarySccsIs` at `PGood5` states**, with `SccsGoodM` in the conclusion. -/
def UnarySccsIs5 (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)) (Cls : Straight (TreapMap mugF) → Prop) :
    Prop :=
  ∀ (st : PSt) b scc r, PGood5 Cls st → Ar.compileUnary b scc st.long st.jets st.hot st.cache = some r →
    SccsIs st.long.code r.2.sccs ∧ SccsGoodM r.2.sccs

/-- **`UnarySccsIs5` from the gate's record at every `PGood5` state** (`cu_sccs_of_gateS`; `SccsIs`
and `SccsGoodM` of the state's `sccs` from `PGood5`). -/
theorem unarySccsIs5_of_gate {fl : Flags} {Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)}
    {Cls : Straight (TreapMap mugF) → Prop} (hUA : Ar.compileUnary = compileUnaryP fl)
    (hGR : ∀ st b sc, PGood5 Cls st → ∃ (NM CA V COLE : Noun) (envK : Comp.CallEnv) (inl : Noun → Option Nomm)
      (n : Nomm) (D : Bell → Prop), GateRest5Sw fl st b sc NM CA V COLE envK inl n D) :
    UnarySccsIs5 Ar Cls := by
  intro st b scc r hg hr
  rw [hUA] at hr
  obtain ⟨NM, CA, V, COLE, envK, inl, n, D, H⟩ := hGR st b scc hg
  obtain ⟨ht, H'⟩ := unaryGateAtS_of_good5 hg (gateRest5_of_Sw hg H)
  rw [cu_sccs_of_gateS H' hr]
  exact ⟨hg.sccsIs, hg.good4.good3.good2.cache.sccs⟩

section Keep

variable {Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)} {Cls : Straight (TreapMap mugF) → Prop}

/-- **The model's `%full` keeps `PGood5`**, with `UnarySccsIs5` (track P's `good5_full_step`, the
call of `UnarySccsIs` at the state of `good5_mid`, which is `PGood5`). -/
theorem good5_full_stepU {R : Type} {env : Env R}
    {jet : Noun → Noun → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → R}
    {jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun} {newOf : R → Noun}
    (hA : Ar.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf)
    (hK : SkaKeeps Ar) (hU : UnaryKeeps Ar Cls) (hO : SccOfKeeps Ar) (hC : UnaryCacheKeeps Ar Cls)
    (hSI : SccOfIs Ar) (hUS : UnarySccsIs5 Ar Cls) (hTE : TarjanExists)
    (hJC : ∀ hot j reg L L', ColeCoh j → ColeCoh (jetsOf hot j reg L L'))
    (st : PSt) (s f : Noun) (pr : SkaModel.Prod (TreapMap mugF)) (st' : PSt)
    (hg : PGood5 Cls st) (h : pokeS Ar st (Ovum.full s f) = some (pr, st')) : PGood5 Cls st' := by
  have hg3 := good3_full_step hK hU (skaCodeKeeps_of_armP Ar hA) hO hC st s f pr st' hg.good4.good3 h
  simp only [pokeS] at h
  obtain ⟨r, e1, h⟩ := Option.bind_eq_some_iff.1 h
  have e1' := e1
  rw [hA] at e1'
  obtain ⟨E, n, bg, reg', hbg, hEv, hcode, hjets⟩ := anaArmP_bake e1'
  obtain ⟨lib, hInv⟩ := hg.invB
  have hInv' : InvB lib r.2.1 := ((anaHyp_of_armP (lib := lib) Ar hA).ana s f st.long st.jets st.hot r e1 hInv).1
  have hc := hg.good4.good3.good2.closed
  have hv : VarsKeys E.vars st.long.code := hEv ▸ hg.good4.good3.vars
  have hi := hg.good4.info
  obtain ⟨F, hF, hFt⟩ := hg.good4.flags
  obtain ⟨L, hL⟩ := hTE (newCode st.long.code bg.1)
  obtain ⟨G, hG⟩ := loopTotal_poke hc hv hi hbg hFt hInv' hcode L hL
  obtain ⟨hi', hG1, hG2⟩ := flags_poke hc hv hi hbg hL hF hFt hG
  have hc' := (addCode_closed hc hv hbg).1
  have hsc := sccsIs_addCode (addsTo_addCode st.long.code bg.1) hc hg.sccsIs hg.good4.good3.good2.cache.sccs
  rw [← hcode] at hi' hG1 hG2 hc' hsc
  have hcole : ColeCoh r.2.2.1 := by rw [hjets]; exact hJC _ _ _ _ _ hg.cole
  have key : ∀ st'' : PSt, st''.long = r.2.1 → st''.jets = r.2.2.1 → SccsIs r.2.1.code st''.cache.sccs →
      PGood3 Cls st'' → PGood5 Cls st'' := fun st'' hl hj hs h3 =>
    ⟨⟨h3, hl ▸ hi', ⟨G, hl ▸ hG1, hl ▸ hG2⟩⟩, ⟨lib, hl ▸ hInv'⟩, hl ▸ hs, hj ▸ hcole⟩
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
    have hsq : SccsIs r.2.1.code q.2 := hSI _ _ _ q hc' hsc e3
    refine key _ rfl rfl ?_ hg3
    unfold compiledMono at hp'
    split at hp'
    · cases hp'; exact hsq
    · obtain ⟨r', hr', e⟩ := Option.map_eq_some_iff.1 hp'
      cases e
      exact (hUS { st with long := r.2.1, jets := r.2.2.1, cache := { st.cache with sccs := q.2 } } r.1 q.1 r'
        (good5_mid hA hK hO hSI hTE hJC st s f hg r e1 q e3) hr').1

end Keep

section Links

variable (fl : Flags) (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)) (Cls : Straight (TreapMap mugF) → Prop)

variable {R : Type} {envR : Env R}
  {jet : Noun → Noun → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
  {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → R}
  {jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun} {newOf : R → Noun}

/-- **Every core the pill reaches is an encoded `PGood5` state**, with `UnarySccsIs5` (track P's
`pokeReachGood5`, the step by `good5_full_stepU`). -/
theorem pokeReachGood5U (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP) (lib : Lib)
    (hA : Ar.skaPoke = anaArmP envR jet fold frozen fuel bf regOf jetsOf newOf)
    (hJA : Ar.jetRoot = jetRootP) (hR : SpRestGood5 fl Ar Cls env) (hC : SccLink fl Ar sccP)
    (hM : MonoLinkGood5 fl Ar Cls) (hO : OptLinkOn Cls Ar optP) (hK : SkaKeeps Ar) (hU : UnaryKeeps Ar Cls)
    (hSc : SccOfKeeps Ar) (hCK : UnaryCacheKeeps Ar Cls) (hSI : SccOfIs Ar) (hUS : UnarySccsIs5 Ar Cls)
    (hTE : TarjanExists) (hJC : ∀ hot j reg L L', ColeCoh j → ColeCoh (jetsOf hot j reg L L'))
    (hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none) (hX : OtherKeeps5 fl Cls) :
    ∀ cr, PokeReach cr → ∃ st, PGood5 Cls st ∧ enc fl st = cr := by
  intro cr h
  induction h with
  | start => exact ⟨emptySt, good5_empty Cls lib, (cor_enc fl).symm⟩
  | @poke c ovo p c' _ hp hh ih =>
    obtain ⟨st, hg, rfl⟩ := ih
    by_cases e : ∃ s f, ovo = (Ovum.full s f).toNoun
    · obtain ⟨s, f, rfl⟩ := e
      rw [pokeModel_fullGood5 fl Ar Cls env hhe hth hsoft hrf hA hJA hR hC hM hO hK hU hSc hSI hTE hJC hAt st hg s f,
        liftPoke_enc_fl] at hp
      cases e' : pokeS Ar st (Ovum.full s f) with
      | none => rw [e'] at hp; cases hp
      | some q =>
        rw [e'] at hp
        simp only [Option.map_some, Option.some.injEq, Noun.cell.injEq] at hp
        exact ⟨q.2, good5_full_stepU hA hK hU hSc hCK hSI hUS hTE hJC st s f q.1 q.2 hg e', hp.2⟩
    · exact hX st ovo p c' hg hp hh fun s f h => e ⟨s, f, h⟩

end Links

/-- **`pokeModel` on `%full` at every reachable core, with no member gate and no `UnarySccsIs`
as a hypothesis**: `pokeModel_fullReachP5Sw` with `UnarySccsIs` replaced by
`unarySccsIs5_of_gate` (from `hGR` itself). -/
theorem pokeModel_fullReachP5U (fl : Flags) (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
    (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP) (lib : Lib)
    {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → Noun}
    {jetsOf : Noun → Noun → Noun → LongB FinMap → LongB FinMap → Noun} {newOf : Noun → Noun}
    (hA : Ar.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf)
    (hJA : Ar.jetRoot = jetRootP) (hOA : Ar.optimize = optimizeP) (hSA : Ar.sccOf = sccOfP)
    (hUA : Ar.compileUnary = compileUnaryP fl)
    (hR : SpRestGood5 fl Ar OptTotal env) (hI : SccImage) (hSc : SccOfKeeps Ar) (hSI : SccOfIs Ar)
    (hTE : TarjanExists)
    (hGR : ∀ st b sc, PGood5 OptTotal st → ∃ (NM CA V COLE : Noun) (envK : Comp.CallEnv) (inl : Noun → Option Nomm)
      (n : Nomm) (D : Bell → Prop), GateRest5Sw fl st b sc NM CA V COLE envK inl n D)
    (hJ : JetsOfGood jetsOf) (hJC : ∀ hot j reg L L', ColeCoh j → ColeCoh (jetsOf hot j reg L L'))
    (hU : UnaryKeeps Ar OptTotal) (hCK : UnaryCacheKeeps Ar OptTotal)
    (hX : OtherKeeps5 fl OptTotal) :
    ∀ cr, CorIn cr → ∀ s f, pokeN cr (Ovum.full s f).toNoun =
      (liftPoke (enc fl) (pokeS Ar) cr (Ovum.full s f)).map fun r => C r.1.toNoun r.2 := by
  have hGR' : ∀ st b sc, PGood5 OptTotal st → ∃ (NM CA V COLE : Noun) (envK : Comp.CallEnv)
      (inl : Noun → Option Nomm) (n : Nomm) (D : Bell → Prop), GateRest5 fl st b sc NM CA V COLE envK inl n D :=
    fun st b sc hg => by
      obtain ⟨NM, CA, V, COLE, envK, inl, n, D, H⟩ := hGR st b sc hg
      exact ⟨NM, CA, V, COLE, envK, inl, n, D, gateRest5_of_Sw hg H⟩
  have hM := monoLinkGood5_of_gateS fl Ar OptTotal hUA fun st b sc hg => by
    obtain ⟨NM, CA, V, COLE, envK, inl, n, D, H⟩ := hGR' st b sc hg
    obtain ⟨ht, H'⟩ := unaryGateAtS_of_good5 hg H
    exact ⟨NM, CA, V, COLE, _, envK, inl, n, ht, D, H'⟩
  have hUS := unarySccsIs5_of_gate hUA hGR
  have hK := skaKeeps_of_armP Ar hA hJ
  have hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none := fun s a L j h => by
    rw [hA]; exact anaArmP_atom env jet fold frozen fuel bf regOf jetsOf newOf s a L j h
  intro cr hc s f
  obtain ⟨st, hg, rfl⟩ := pokeReachGood5U fl Ar OptTotal env hhe hth hsoft hrf lib hA hJA hR (sccLink_of fl hSA hI)
    hM (optLinkOn_optimizeP hOA) hK hU hSc hCK hSI hUS hTE hJC hAt hX cr hc.2.2
  exact pokeModel_fullGood5 fl Ar OptTotal env hhe hth hsoft hrf hA hJA hR (sccLink_of fl hSA hI) hM
    (optLinkOn_optimizeP hOA) hK hU hSc hSI hTE hJC hAt st hg s f

end Compiler
end Formalization
