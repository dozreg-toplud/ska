import lemmas.Compiler.CompMonoLinkTop5
import lemmas.Compiler.CompSccOfSweep

/-!
# Track P's top with the sweeps' gates proved (README Gaps 19 (g), the sweeps)

`GateRest5` (`CompMonoLinkTop5.lean`) with the loop data of `CompSccOfSweep.lean`: the table at
`CalleeHSDSw` (each nested loop's `%may` / `%must` gates replaced by `MemSweepCallK` at every
call) and the top loop's data at `TopDecSh` (track I's `csi_gate_ranked_shape` hypotheses, with
`MemSweepCallK`).  No member gate is a hypothesis any more.

* `GateRest5Sw`, **`gateRest5_of_Sw`** (at a `PGood5` state: `SccsGood` of its `sccs` from
  `pgoodK_state_of`);
* **`pokeModel_fullReachP5Sw`**: `pokeModel_fullReachP5S` with `GateRest5Sw`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeF SkaModel.PokeM FinMap

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **`GateRest5` with the sweeps' gates proved**: `top` at `TopDecSh`, the table at
`CalleeHSDSw`; the other fields as in `GateRest5`, each with its owner. -/
structure GateRest5Sw (fl : Flags) (st : PSt) (b : Bell) (sc : FinMap Bell Unit) (NM CA V COLE : Noun)
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
  /-- the top loop's data with its gates proved (I: `MemDoneCallStr`, the sample facts; A:
  `MemShapeBranch` and `InlKeep` in `MemSweepCallK`, or `TopOneS`) -/
  top : TopDecSh (FinMap.setNoun sc) (codeNoun fl st.long.code) st.jets (callsNoun st.long) st.hot (cacheNoun st.cache)
  /-- the class of `b`'s nomm (K) -/
  dir : DirOk n = true
  /-- the code table (C/J/P) -/
  envFrom : EnvFrom env (codeNoun fl st.long.code) COLE
  noRing : CodeNoRing (codeNoun fl st.long.code) COLE n
  ana : CodeAna (codeNoun fl st.long.code)
  /-- the table of callees at every height with P's rank (A: one-bell, and `MemShapeBranch` /
  `InlKeep` of `MemSweepCallK`; I: `Ranked`, `CfgOf`, `henv`; K: `MemDoneRestSDStr` / `MemRunS`) -/
  table : ∀ ht, HtRank (sccsNoun st.cache.sccs) (callsNoun st.long) ht → HtScc (sccsNoun st.cache.sccs) ht →
    ∀ b', D b' → CalleeHSDSw env (sccsNoun st.cache.sccs) (st.cache.mono.toNoun Straight.toNoun)
      (codeNoun fl st.long.code) st.jets (callsNoun st.long) st.hot inl ht D b'
  /-- each callee readable at the start or outside, in `D`, with a need (P/I) -/
  callees : ∀ b' ∈ dirBells n, AnyCalleeH env (FinMap.setNoun sc) D
    (cuCtx b.toNoun (FinMap.setNoun sc) (codeNoun fl st.long.code) (C st.jets (callsNoun st.long)) st.hot NM)
    (cuRest CA) b'

/-- **`GateRest5` from `GateRest5Sw`** at a `PGood5` state (`topDec_of_Sh`, `calleeHSDS_of_Sw`
with `SccsGood` from `pgoodK_state_of`). -/
theorem gateRest5_of_Sw {Cls : Straight (TreapMap mugF) → Prop} {fl : Flags} {st : PSt} {b : Bell}
    {sc : FinMap Bell Unit} {NM CA V COLE : Noun} {env : Comp.CallEnv} {inl : Noun → Option Nomm} {n : Nomm}
    {D : Bell → Prop} (hg : PGood5 Cls st) (H : GateRest5Sw fl st b sc NM CA V COLE env inl n D) :
    GateRest5 fl st b sc NM CA V COLE env inl n D := by
  obtain ⟨hsg, -, -⟩ := pgoodK_state_of hg.good4.good3
  exact ⟨H.got, H.nomm, H.cole, H.csi, H.agree, H.rest, H.dec, topDec_of_Sh H.top, H.dir, H.envFrom, H.noRing, H.ana,
    fun ht hR hS b' hD => calleeHSDS_of_Sw hsg hS (H.table ht hR hS b' hD), H.callees⟩

/-- **`pokeModel` on `%full` at every reachable core, with no member gate as a hypothesis**:
`pokeModel_fullReachP5S` with `GateRest5Sw` in place of `GateRest5`. -/
theorem pokeModel_fullReachP5Sw (fl : Flags) (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
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
    (hU : UnaryKeeps Ar OptTotal) (hCK : UnaryCacheKeeps Ar OptTotal) (hUS : UnarySccsIs Ar)
    (hX : OtherKeeps5 fl OptTotal) :
    ∀ cr, CorIn cr → ∀ s f, pokeN cr (Ovum.full s f).toNoun =
      (liftPoke (enc fl) (pokeS Ar) cr (Ovum.full s f)).map fun r => C r.1.toNoun r.2 :=
  pokeModel_fullReachP5S fl Ar env hhe hth hsoft hrf lib hA hJA hOA hSA hUA hR hI hSc hSI hTE
    (fun st b sc hg => by
      obtain ⟨NM, CA, V, COLE, envK, inl, n, D, H⟩ := hGR st b sc hg
      exact ⟨NM, CA, V, COLE, envK, inl, n, D, gateRest5_of_Sw hg H⟩)
    hJ hJC hU hCK hUS hX

end Compiler
end Formalization
