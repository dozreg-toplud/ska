import lemmas.Compiler.PokeLinkTop5
import lemmas.Compiler.CompMonoLinkSoft

/-!
# The gate's record at a `PGood5` state, and track P's top with it (README Gaps 19 (g))

Track P's `pokeModel_fullReachP5` takes the gate in the old form `UnaryGateAt` (`hG`), whose
fields `nmDec` (decoding of the top loop's map) and `table` (with `CsiDec`) the newer records
`UnaryGateAtStr` / `UnaryGateAtS` no longer have: `top : TopDec` replaces `nmDec`
(`nmDec_of_top`), and the table is `CalleeHSDStr` / `CalleeHSDS` (no `CsiDec`; soft members
admitted in the second).  There is no map from the new records to the old one, so the corollary
here re-derives `MonoLinkGood5` from `UnaryGateAtS` and repeats P's proof (it is two lines).

* `monoLinkGood5_of_gateS`: `MonoLinkGood5` from `UnaryGateAtS` at `PGood5` states;
* `GateRest5`: what the record still takes at a `PGood5` state, each field with its owner;
* **`unaryGateAtS_of_good5`**: the record from `PGood5` (`heights_good5`, i.e. `htRank_of`;
  `pgoodK_state_of` for `sccsGood` and `jug`; `sccs` by definition) and `GateRest5`;
* **`pokeModel_fullReachP5S`**: `pokeModel_fullReachP5` with `GateRest5` in place of `hG`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeF SkaModel.PokeM FinMap

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **`MonoLinkGood5` from the gate with soft members admitted** (`monoLinkGood5_of_gate` with
`UnaryGateAtS`). -/
theorem monoLinkGood5_of_gateS (fl : Flags) (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
    (Cls : Straight (TreapMap mugF) → Prop) (hA : Ar.compileUnary = compileUnaryP fl)
    (hG : ∀ st b sc, PGood5 Cls st → ∃ (NM CA V COLE SC0 : Noun) (env : Comp.CallEnv) (inl : Noun → Option Nomm)
      (n : Nomm) (ht : Noun → Nat) (D : Bell → Prop), UnaryGateAtS fl st b sc NM CA V COLE SC0 env inl n ht D) :
    MonoLinkGood5 fl Ar Cls := by
  intro st b sc hg
  obtain ⟨NM, CA, V, COLE, SC0, env, inl, n, ht, D, H⟩ := hG st b sc hg
  exact monoLinkAt_of fl Ar hA st b sc (unaryImageAt_of_gateDS H) (monoMissAt_of fl st b sc)

/-- **What `UnaryGateAtS` still takes at a `PGood5` state**, with `SC0` the state's `sccs`: the
fields that `PGood5` does not give (`heights`, `sccs`, `sccsGood`, `jug` are given), the table
asked at every height `ht` with P's `HtRank` and `HtScc`. -/
structure GateRest5 (fl : Flags) (st : PSt) (b : Bell) (sc : FinMap Bell Unit) (NM CA V COLE : Noun)
    (env : Comp.CallEnv) (inl : Noun → Option Nomm) (n : Nomm) (D : Bell → Prop) : Prop where
  /-- the code entry of `b` and its nomm (P: the code table) -/
  got : getF mugF b.toNoun (codeNoun fl st.long.code) = some (C (A 0) V)
  nomm : slot? 2 V = some n.toNoun
  /-- `call.cole` (P) -/
  cole : slot? 190 (C st.jets (callsNoun st.long)) = some COLE
  /-- the poke's `+compile-scc-in` on `b`'s SCC inside `+compile-unary` (I) -/
  csi : nock (cuTC (cuSam b.toNoun (FinMap.setNoun sc) (codeNoun fl st.long.code) (C st.jets (callsNoun st.long))
    st.hot (cacheNoun st.cache))) cuCsi = some (C NM CA)
  /-- the invariants at the cache after it (P/I) -/
  agree : AgreeE env (cuRest CA)
  rest : RK (sccsNoun st.cache.sccs) inl (cuRest CA)
  dec : CacheDec (st.cache.mono.toNoun Straight.toNoun) CA
  /-- the top loop's data (I: `TopLoopS`; A: `TopOneS`) -/
  top : TopDec (FinMap.setNoun sc) (codeNoun fl st.long.code) st.jets (callsNoun st.long) st.hot (cacheNoun st.cache)
  /-- the class of `b`'s nomm (K) -/
  dir : DirOk n = true
  /-- the code table (C/J/P) -/
  envFrom : EnvFrom env (codeNoun fl st.long.code) COLE
  noRing : CodeNoRing (codeNoun fl st.long.code) COLE n
  ana : CodeAna (codeNoun fl st.long.code)
  /-- the table of callees at every height with P's rank (A: one-bell; I/A: the loop gates; K:
  `MemDoneRestSDStr` / `MemRunS`) -/
  table : ∀ ht, HtRank (sccsNoun st.cache.sccs) (callsNoun st.long) ht → HtScc (sccsNoun st.cache.sccs) ht →
    ∀ b', D b' → CalleeHSDS env (sccsNoun st.cache.sccs) (st.cache.mono.toNoun Straight.toNoun)
      (codeNoun fl st.long.code) st.jets (callsNoun st.long) st.hot inl ht D b'
  /-- each callee readable at the start or outside, in `D`, with a need (P/I) -/
  callees : ∀ b' ∈ dirBells n, AnyCalleeH env (FinMap.setNoun sc) D
    (cuCtx b.toNoun (FinMap.setNoun sc) (codeNoun fl st.long.code) (C st.jets (callsNoun st.long)) st.hot NM)
    (cuRest CA) b'

/-- **The gate's record at a `PGood5` state**: `heights` from `heights_good5` (P's `htRank_of`),
`sccsGood` and `jug` from `pgoodK_state_of`, `sccs` by definition, the rest from `GateRest5`. -/
theorem unaryGateAtS_of_good5 {Cls : Straight (TreapMap mugF) → Prop} {fl : Flags} {st : PSt} {b : Bell}
    {sc : FinMap Bell Unit} {NM CA V COLE : Noun} {env : Comp.CallEnv} {inl : Noun → Option Nomm} {n : Nomm}
    {D : Bell → Prop} (hg : PGood5 Cls st) (H : GateRest5 fl st b sc NM CA V COLE env inl n D) :
    ∃ ht, UnaryGateAtS fl st b sc NM CA V COLE (sccsNoun st.cache.sccs) env inl n ht D := by
  obtain ⟨ht, hR, hS⟩ := heights_good5 hg
  obtain ⟨hsg, hcj, -⟩ := pgoodK_state_of hg.good4.good3
  exact ⟨ht, H.got, H.nomm, H.cole, H.csi, H.agree, H.rest, H.dec, H.top, rfl, H.dir, H.envFrom, H.noRing, H.ana, hsg,
    hcj, hS, H.table ht hR hS, H.callees⟩

/-- **`pokeModel` on `%full` at every reachable core, over `PGood5`, with the gate's record built
from `PGood5`**: `pokeModel_fullReachP5` with `hG` replaced by `GateRest5` at every `PGood5`
state, bell and SCC (the table with soft members admitted). -/
theorem pokeModel_fullReachP5S (fl : Flags) (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
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
      (n : Nomm) (D : Bell → Prop), GateRest5 fl st b sc NM CA V COLE envK inl n D)
    (hJ : JetsOfGood jetsOf) (hJC : ∀ hot j reg L L', ColeCoh j → ColeCoh (jetsOf hot j reg L L'))
    (hU : UnaryKeeps Ar OptTotal) (hCK : UnaryCacheKeeps Ar OptTotal) (hUS : UnarySccsIs Ar)
    (hX : OtherKeeps5 fl OptTotal) :
    ∀ cr, CorIn cr → ∀ s f, pokeN cr (Ovum.full s f).toNoun =
      (liftPoke (enc fl) (pokeS Ar) cr (Ovum.full s f)).map fun r => C r.1.toNoun r.2 := by
  have hM := monoLinkGood5_of_gateS fl Ar OptTotal hUA fun st b sc hg => by
    obtain ⟨NM, CA, V, COLE, envK, inl, n, D, H⟩ := hGR st b sc hg
    obtain ⟨ht, H'⟩ := unaryGateAtS_of_good5 hg H
    exact ⟨NM, CA, V, COLE, _, envK, inl, n, ht, D, H'⟩
  have hK := skaKeeps_of_armP Ar hA hJ
  have hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none := fun s a L j h => by
    rw [hA]; exact anaArmP_atom env jet fold frozen fuel bf regOf jetsOf newOf s a L j h
  intro cr hc s f
  obtain ⟨st, hg, rfl⟩ := pokeReachGood5 fl Ar OptTotal env hhe hth hsoft hrf lib hA hJA hR (sccLink_of fl hSA hI)
    hM (optLinkOn_optimizeP hOA) hK hU hSc hCK hSI hUS hTE hJC hAt hX cr hc.2.2
  exact pokeModel_fullGood5 fl Ar OptTotal env hhe hth hsoft hrf hA hJA hR (sccLink_of fl hSA hI) hM
    (optLinkOn_optimizeP hOA) hK hU hSc hSI hTE hJC hAt st hg s f

end Compiler
end Formalization
