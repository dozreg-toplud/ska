import lemmas.Compiler.CompSccOfSoft
import lemmas.Compiler.CompMonoLinkStr

/-!
# The gate of `+compile-unary` with soft members admitted (README Gaps 19 (g))

`cu_gate_dir_sccDStr` with the table `CalleeHSDS` (`CompSccOfSoft.lean`): a callee SCC whose
members make soft calls has its loop data at track I's `cfgRealS` (`SccLoopDataDS`, each member
`SoftChainOk` or `DirOk`, `MemRunS`); an SCC without soft calls keeps the data of
`CompSccOfStr.lean`.

* **`cu_gate_dir_sccDS`**; `UnaryGateAtS` (`UnaryGateAtStr` with the table at `CalleeHSDS`),
  `unaryGateAtS_of_Str`, **`unaryImageAt_of_gateDS`**, **`monoLinkGood3_of_gateS`**.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.Comp SkaModel.SccLoop SkaModel.PokeM

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **The gate of `+compile-unary` with soft members admitted** (`cu_gate_dir_sccDStr` with the
table `CalleeHSDS`). -/
theorem cu_gate_dir_sccDS (FUNC SCC CODE JETS CALLS JH CACHE NM CA V COLE SC0 MO0 : Noun) (env : CallEnv)
    (inl : Noun → Option Nomm) (n : Nomm) (ht : Noun → Nat) (D : Bell → Prop)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun)
    (hcl : slot? 190 (C JETS CALLS) = some COLE)
    (hcsi : nock (cuTC (cuSam FUNC SCC CODE (C JETS CALLS) JH CACHE)) cuCsi = some (C NM CA))
    (hE0 : AgreeE env (cuRest CA)) (hR0 : RK SC0 inl (cuRest CA)) (hD0 : CacheDec MO0 CA)
    (hn : DirOk n = true)
    (he : EnvFrom env CODE COLE) (hcr : CodeNoRing CODE COLE n) (hana : CodeAna CODE)
    (hsg : SccsGood SC0) (hcj : IsMap mugF CALLS ∧ ∀ k v, Get CALLS k v → IsSet mugF v)
    (hht : HtScc SC0 ht) (hT : ∀ b, D b → CalleeHSDS env SC0 MO0 CODE JETS CALLS JH inl ht D b)
    (hcal : ∀ b ∈ dirBells n, AnyCalleeH env SCC D (cuCtx FUNC SCC CODE (C JETS CALLS) JH NM) (cuRest CA) b) :
    ∃ CA', Ext (cuRest CA) (cuRest CA') ∧ AgreeE env (cuRest CA') ∧ RK SC0 inl (cuRest CA') ∧ CacheDec MO0 CA' ∧
      nock (C cuGB (C (cuSam FUNC SCC CODE (C JETS CALLS) JH CACHE) compK)) cuGB
        = (finishLUCM (S := CSet) (Map := TreapMap mugF) env n).map fun st => C (C st.toNoun NM) CA' := by
  obtain ⟨CA', h1, h2, h3, h4⟩ := cu_gate_dirE FUNC SCC CODE (C JETS CALLS) JH CACHE NM CA V COLE env
    (RKD SC0 MO0 inl (fun _ => False)) n hgot hv hcl hcsi hE0 ⟨rKP_empty.2 hR0, hD0⟩ hn he hcr hana fun b hb => by
    rcases hcal b hb with ⟨nb, hnb, hr, hs⟩ | ⟨hout, hD, nb, hnb⟩
    · exact ⟨nb, hnb, Or.inl ⟨hr, hs⟩⟩
    · exact ⟨nb, hnb, Or.inr ⟨SCC, by simp [cuCtx, nock_exec], hout,
        calleeCompiled_heights0DS hsg hcj hht (fun b' hD' => calleeH_of_SDS hsg hht (hT b' hD')) hD
          (ctxK_cu _ _ _ _ _ _ _) hnb⟩⟩
  exact ⟨CA', h1, h2, rKP_empty.1 h3.1, h3.2, h4⟩

/-- **What `cu_gate_dir_sccDS` takes at the encoded sample of `+compiled-mono`**: the fields of
`UnaryGateAtStr` with the table at `CalleeHSDS` (soft members admitted). -/
structure UnaryGateAtS (fl : Flags) (st : PSt) (b : Bell) (sc : FinMap Bell Unit)
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
  /-- tracks P/I: the cache after it keeps `mono` and its `nary` decodes -/
  dec : CacheDec (st.cache.mono.toNoun Straight.toNoun) CA
  /-- the top loop's data (track I: its member gates at `LoopRS`; a lone bell: track A) -/
  top : TopDec (FinMap.setNoun sc) (codeNoun fl st.long.code) st.jets (callsNoun st.long) st.hot (cacheNoun st.cache)
  /-- `sccs` is the state's (track P) -/
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
  /-- the table of callees: one-bell (track A), an SCC without soft calls (tracks I/A), or an SCC
  with soft members at `cfgRealS` (tracks I/A for the gates, K for `MemRunS`) -/
  table : ∀ b', D b' → CalleeHSDS env SC0 (st.cache.mono.toNoun Straight.toNoun) (codeNoun fl st.long.code) st.jets
    (callsNoun st.long) st.hot inl ht D b'
  /-- each callee readable at the start or outside, in `D`, with a need (tracks P/I) -/
  callees : ∀ b' ∈ dirBells n, AnyCalleeH env (FinMap.setNoun sc) D
    (cuCtx b.toNoun (FinMap.setNoun sc) (codeNoun fl st.long.code) (C st.jets (callsNoun st.long)) st.hot NM)
    (cuRest CA) b'

/-- The record without soft members is one with them admitted. -/
theorem unaryGateAtS_of_Str {fl : Flags} {st : PSt} {b : Bell} {sc : FinMap Bell Unit} {NM CA V COLE SC0 : Noun}
    {env : CallEnv} {inl : Noun → Option Nomm} {n : Nomm} {ht : Noun → Nat} {D : Bell → Prop}
    (H : UnaryGateAtStr fl st b sc NM CA V COLE SC0 env inl n ht D) : UnaryGateAtS fl st b sc NM CA V COLE SC0 env inl n ht D :=
  ⟨H.got, H.nomm, H.cole, H.csi, H.agree, H.rest, H.dec, H.top, H.sccs, H.dir, H.envFrom, H.noRing, H.ana, H.sccsGood,
    H.jug, H.heights, fun b' hD => calleeHSDS_of_Str (H.table b' hD), H.callees⟩

/-- **`UnaryImageAt` from the gate with soft members admitted** (`cu_gate_dir_sccDS`,
`nmDec_of_top`, `cacheNoun_of_dec`). -/
theorem unaryImageAt_of_gateDS {fl : Flags} {st : PSt} {b : Bell} {sc : FinMap Bell Unit} {NM CA V COLE SC0 : Noun}
    {env : CallEnv} {inl : Noun → Option Nomm} {n : Nomm} {ht : Noun → Nat} {D : Bell → Prop}
    (H : UnaryGateAtS fl st b sc NM CA V COLE SC0 env inl n ht D) : UnaryImageAt fl st b sc := by
  obtain ⟨CA', -, -, hR, hD, hg⟩ := cu_gate_dir_sccDS b.toNoun (FinMap.setNoun sc) (codeNoun fl st.long.code)
    st.jets (callsNoun st.long) st.hot (cacheNoun st.cache) NM CA V COLE SC0 (st.cache.mono.toNoun Straight.toNoun)
    env inl n ht D H.got H.nomm H.cole H.csi H.agree H.rest H.dec H.dir H.envFrom H.noRing H.ana H.sccsGood H.jug
    H.heights H.table H.callees
  refine unaryImageAt_of_gate fl st b sc env n NM
    (fun CA'' => RK SC0 inl (cuRest CA'') ∧ CacheDec (st.cache.mono.toNoun Straight.toNoun) CA'')
    ⟨CA', ⟨hR, hD⟩, hg⟩ (nmDec_of_top H.csi H.top) fun CA'' h => ?_
  rw [H.sccs] at h
  exact cacheNoun_of_dec h.2 h.1.1

/-- **`MonoLinkGood3` from the gate with soft members admitted**, `UnaryGateAtS` at every
`PGood3` state, bell and SCC. -/
theorem monoLinkGood3_of_gateS (fl : Flags) (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
    (Cls : Straight (TreapMap mugF) → Prop) (hA : Ar.compileUnary = compileUnaryP fl)
    (hG : ∀ st b sc, PGood3 Cls st → ∃ (NM CA V COLE SC0 : Noun) (env : CallEnv) (inl : Noun → Option Nomm) (n : Nomm)
      (ht : Noun → Nat) (D : Bell → Prop), UnaryGateAtS fl st b sc NM CA V COLE SC0 env inl n ht D) :
    MonoLinkGood3 fl Ar Cls := by
  intro st b sc hg
  obtain ⟨NM, CA, V, COLE, SC0, env, inl, n, ht, D, H⟩ := hG st b sc hg
  exact monoLinkAt_of fl Ar hA st b sc (unaryImageAt_of_gateDS H) (monoMissAt_of fl st b sc)

end Compiler
end Formalization
