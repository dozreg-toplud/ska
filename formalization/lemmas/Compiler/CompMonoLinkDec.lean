import lemmas.Compiler.CompSccOfDecH
import lemmas.Compiler.CompMonoLinkMiss
import lemmas.Compiler.PokeLinkGood3

/-!
# `MonoLinkGood3` from the gate, the unary image decoded (README Gaps 19 (g))

* **`cu_gate_dir_sccD`**: `cu_gate_dir_sccH` at the rest predicate `RKD` (the cache decoded):
  from `CacheDec MO0 CA` at the start, the gate's cache `CA'` has `CacheDec MO0 CA'` too;
* `cacheNoun_of_dec`: a cache with `CacheDec` (`mono` the noun of a map) and `RInl` at a
  `sccsNoun` is `cacheNoun c`;
* `UnaryGateAt`: what `cu_gate_dir_sccD` takes at the encoded sample of `+compiled-mono`, one
  field per hypothesis (owners in the field comments), with decoding (a) `nmDec`;
* **`unaryImageAt_of_gateD`**: `UnaryImageAt` from `UnaryGateAt` (decoding (b) is proved);
* **`monoLinkGood3_of_gate`**: track P's `MonoLinkGood3` from `Ar.compileUnary = compileUnaryP fl`
  and `UnaryGateAt` at every `PGood3` state.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.Comp SkaModel.SccLoop SkaModel.PokeM

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **The gate of `+compile-unary` with the cache decoded** (`cu_gate_dir_sccH` at `RKD`): the
cache `CA'` the gate returns keeps `mono` at `MO0` and its `nary` is the noun of a map of
straights, when `CA` (after the poke's `+compile-scc-in`) has both and the loop data
`CalleeHSD` carry decoding (a) at every nested loop. -/
theorem cu_gate_dir_sccD (FUNC SCC CODE JETS CALLS JH CACHE NM CA V COLE SC0 MO0 : Noun) (env : CallEnv)
    (inl : Noun → Option Nomm) (n : Nomm) (ht : Noun → Nat) (D : Bell → Prop)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun)
    (hcl : slot? 190 (C JETS CALLS) = some COLE)
    (hcsi : nock (cuTC (cuSam FUNC SCC CODE (C JETS CALLS) JH CACHE)) cuCsi = some (C NM CA))
    (hE0 : AgreeE env (cuRest CA)) (hR0 : RK SC0 inl (cuRest CA)) (hD0 : CacheDec MO0 CA)
    (hn : DirOk n = true)
    (he : EnvFrom env CODE COLE) (hcr : CodeNoRing CODE COLE n) (hana : CodeAna CODE)
    (hsg : SccsGood SC0) (hcj : IsMap mugF CALLS ∧ ∀ k v, Get CALLS k v → IsSet mugF v)
    (hht : HtScc SC0 ht) (hT : ∀ b, D b → CalleeHSD env SC0 MO0 CODE JETS CALLS JH inl ht D b)
    (hcal : ∀ b ∈ dirBells n, AnyCalleeH env SCC D (cuCtx FUNC SCC CODE (C JETS CALLS) JH NM) (cuRest CA) b) :
    ∃ CA', Ext (cuRest CA) (cuRest CA') ∧ AgreeE env (cuRest CA') ∧ RK SC0 inl (cuRest CA') ∧ CacheDec MO0 CA' ∧
      nock (C cuGB (C (cuSam FUNC SCC CODE (C JETS CALLS) JH CACHE) compK)) cuGB
        = (finishLUCM (S := CSet) (Map := TreapMap mugF) env n).map fun st => C (C st.toNoun NM) CA' := by
  obtain ⟨CA', h1, h2, h3, h4⟩ := cu_gate_dirE FUNC SCC CODE (C JETS CALLS) JH CACHE NM CA V COLE env
    (RKD SC0 MO0 inl (fun _ => False)) n hgot hv hcl hcsi hE0 ⟨rKP_empty.2 hR0, hD0⟩ hn he hcr hana fun b hb => by
    rcases hcal b hb with ⟨nb, hnb, hr, hs⟩ | ⟨hout, hD, nb, hnb⟩
    · exact ⟨nb, hnb, Or.inl ⟨hr, hs⟩⟩
    · exact ⟨nb, hnb, Or.inr ⟨SCC, by simp [cuCtx, nock_exec], hout,
        calleeCompiled_heights0D hsg hcj hht (fun b' hD' => calleeH_of_SD hsg hht (hT b' hD')) hD
          (ctxK_cu _ _ _ _ _ _ _) hnb⟩⟩
  exact ⟨CA', h1, h2, rKP_empty.1 h3.1, h3.2, h4⟩

/-- **A decoded cache is the noun of a model cache**: `mono` the noun of `m0`, `nary` that of a
map of straights (`CacheDec`), `sccs` the noun of `sc` (`RInl` at `sccsNoun sc`). -/
theorem cacheNoun_of_dec {m0 : FinMap Bell (Straight (TreapMap mugF))} {sc : FinMap Bell (FinMap Bell Unit)}
    {inl : Noun → Option Nomm} {CA : Noun} (hD : CacheDec (m0.toNoun Straight.toNoun) CA)
    (hR : RInl (sccsNoun sc) inl (cuRest CA)) :
    ∃ c : Cache FinMap (TreapMap mugF) (Noun × Noun), CA = cacheNoun c := by
  obtain ⟨NR, MO, INL, SU, hc, -, -⟩ := hR
  change CA = cacheN NR MO (sccsNoun sc) INL SU at hc
  subst hc
  obtain ⟨h6, m, h2⟩ := hD
  have e1 : NR = m.toNoun Straight.toNoun := by simpa [cacheN, nock_exec] using h2
  have e2 : MO = m0.toNoun Straight.toNoun := by simpa [cacheN, nock_exec] using h6
  subst e1 e2
  exact ⟨⟨m0, m, sc, (INL, SU)⟩, rfl⟩

/-- **What `cu_gate_dir_sccD` takes at the encoded sample of `+compiled-mono`** (the bell `b`,
the SCC `sc`, the state `st`), one field per hypothesis, its owner in the comment. -/
structure UnaryGateAt (fl : Flags) (st : PSt) (b : Bell) (sc : FinMap Bell Unit)
    (NM CA V COLE SC0 : Noun) (env : CallEnv) (inl : Noun → Option Nomm) (n : Nomm) (ht : Noun → Nat)
    (D : Bell → Prop) : Prop where
  /-- the code entry of `b` and its nomm (track P: the code table) -/
  got : getF mugF b.toNoun (codeNoun fl st.long.code) = some (C (A 0) V)
  nomm : slot? 2 V = some n.toNoun
  /-- `call.cole` (track P) -/
  cole : slot? 190 (C st.jets (callsNoun st.long)) = some COLE
  /-- the poke's `+compile-scc-in` on `b`'s SCC inside `+compile-unary` (track I) -/
  csi : nock (cuTC (cuSam b.toNoun (FinMap.setNoun sc) (codeNoun fl st.long.code) (C st.jets (callsNoun st.long))
    st.hot (cacheNoun st.cache))) cuCsi = some (C NM CA)
  /-- the invariants at the cache after it (tracks P/I: `PGoodK` carried by the loop) -/
  agree : AgreeE env (cuRest CA)
  rest : RK SC0 inl (cuRest CA)
  /-- NEW, tracks P/I: the cache after it keeps `mono` and its `nary` decodes (the `nary` part
  follows from `nmDec` and the `UniSpec` of the loop's `+uni:by`, `cacheDec_uni`) -/
  dec : CacheDec (st.cache.mono.toNoun Straight.toNoun) CA
  /-- decoding (a) at the top loop (track I) -/
  nmDec : ∃ m : FinMap Bell (Straight (TreapMap mugF)), NM = m.toNoun Straight.toNoun
  /-- `sccs` is the state's (track P: `PGoodK.rest` is at `sccsNoun st.cache.sccs`) -/
  sccs : SC0 = sccsNoun st.cache.sccs
  /-- the class of `b`'s nomm (track K) -/
  dir : DirOk n = true
  /-- the code table (tracks C/J/P) -/
  envFrom : EnvFrom env (codeNoun fl st.long.code) COLE
  noRing : CodeNoRing (codeNoun fl st.long.code) COLE n
  ana : CodeAna (codeNoun fl st.long.code)
  /-- `sccs` is `+tarjan`'s partition and `calls` a jug (track P) -/
  sccsGood : SccsGood SC0
  jug : IsMap mugF (callsNoun st.long) ∧ ∀ k v, Get (callsNoun st.long) k v → IsSet mugF v
  /-- heights constant on SCCs (tracks P/Q) -/
  heights : HtScc SC0 ht
  /-- the table of callees: one-bell (track A) or an SCC with the loop data (tracks I/A, with
  `CsiDec` (a) at each loop) -/
  table : ∀ b', D b' → CalleeHSD env SC0 (st.cache.mono.toNoun Straight.toNoun) (codeNoun fl st.long.code) st.jets
    (callsNoun st.long) st.hot inl ht D b'
  /-- each callee readable at the start or outside, in `D`, with a need (tracks P/I) -/
  callees : ∀ b' ∈ dirBells n, AnyCalleeH env (FinMap.setNoun sc) D
    (cuCtx b.toNoun (FinMap.setNoun sc) (codeNoun fl st.long.code) (C st.jets (callsNoun st.long)) st.hot NM)
    (cuRest CA) b'

/-- **`UnaryImageAt` from the gate** (`cu_gate_dir_sccD` at the encoded sample): decoding (b) is
proved (`cacheNoun_of_dec`); decoding (a) is the field `nmDec`. -/
theorem unaryImageAt_of_gateD {fl : Flags} {st : PSt} {b : Bell} {sc : FinMap Bell Unit} {NM CA V COLE SC0 : Noun}
    {env : CallEnv} {inl : Noun → Option Nomm} {n : Nomm} {ht : Noun → Nat} {D : Bell → Prop}
    (H : UnaryGateAt fl st b sc NM CA V COLE SC0 env inl n ht D) : UnaryImageAt fl st b sc := by
  obtain ⟨CA', -, -, hR, hD, hg⟩ := cu_gate_dir_sccD b.toNoun (FinMap.setNoun sc) (codeNoun fl st.long.code) st.jets
    (callsNoun st.long) st.hot (cacheNoun st.cache) NM CA V COLE SC0 (st.cache.mono.toNoun Straight.toNoun) env inl n
    ht D H.got H.nomm H.cole H.csi H.agree H.rest H.dec H.dir H.envFrom H.noRing H.ana H.sccsGood H.jug H.heights
    H.table H.callees
  refine unaryImageAt_of_gate fl st b sc env n NM
    (fun CA'' => RK SC0 inl (cuRest CA'') ∧ CacheDec (st.cache.mono.toNoun Straight.toNoun) CA'')
    ⟨CA', ⟨hR, hD⟩, hg⟩ H.nmDec fun CA'' h => ?_
  rw [H.sccs] at h
  exact cacheNoun_of_dec h.2 h.1.1

/-- **`MonoLinkGood3` from the gate** (README Gaps 19 (g)): track P's hypothesis, from `Ar`
reading `+compile-unary` back (`hA`) and the gate's data `UnaryGateAt` at every `PGood3` state,
bell and SCC. -/
theorem monoLinkGood3_of_gate (fl : Flags) (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
    (Cls : Straight (TreapMap mugF) → Prop) (hA : Ar.compileUnary = compileUnaryP fl)
    (hG : ∀ st b sc, PGood3 Cls st → ∃ (NM CA V COLE SC0 : Noun) (env : CallEnv) (inl : Noun → Option Nomm) (n : Nomm)
      (ht : Noun → Nat) (D : Bell → Prop), UnaryGateAt fl st b sc NM CA V COLE SC0 env inl n ht D) :
    MonoLinkGood3 fl Ar Cls := by
  intro st b sc hg
  obtain ⟨NM, CA, V, COLE, SC0, env, inl, n, ht, D, H⟩ := hG st b sc hg
  exact monoLinkAt_of fl Ar hA st b sc (unaryImageAt_of_gateD H) (monoMissAt_of fl st b sc)

end Compiler
end Formalization
