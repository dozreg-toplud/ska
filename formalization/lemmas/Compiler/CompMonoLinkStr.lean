import lemmas.Compiler.CompSccOfStr
import lemmas.Compiler.CompMonoLinkDec
import lemmas.Compiler.GitG

/-!
# `MonoLinkGood3` from the gate with track I's decoding (README Gaps 19 (g), the switch)

* `csiDecI_iff`: track I's `CsiDecI` is this track's `CsiDec` (`Iff.rfl`);
* `TopLoopS` (the hypotheses of track I's `csiDec_of_loop` at the top loop: the member gates at
  `LoopRS`), `TopOneS` (a lone bell without a self call: the top `+compile-scc-in` returns one
  straight, the shape of track A's `csi_gate_scc_one_f_six_B_any`), `TopDec` (one of the two),
  **`nmDec_of_top`**: decoding (a) of the top loop's map from `TopDec` (`cu_csi_eq`,
  `csiDec_of_loop`, `single_toNoun`);
* **`cu_gate_dir_sccDStr`**: `cu_gate_dir_sccD` with the table `CalleeHSDStr` (the nested loops at
  `LoopRS`, no `CsiDec`);
* `UnaryGateAtStr`: `UnaryGateAt` without `nmDec` (in its place `top : TopDec ..`), the table at
  `CalleeHSDStr`; **`unaryImageAt_of_gateDStr`**, **`monoLinkGood3_of_gateStr`**.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.Comp SkaModel.SccLoop SkaModel.PokeM

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **Track I's `CsiDecI` is `CsiDec`.** -/
theorem csiDecI_iff (S CODE JETS CALLS JH NR CR : Noun) :
    CsiDecI S CODE JETS CALLS JH NR CR ↔ CsiDec S CODE JETS CALLS JH NR CR := Iff.rfl

/-- **The top loop's data at `LoopRS`** (track I): the hypotheses of `csiDec_of_loop` on the SCC
`SCC` at the cache `[NARY CR]`. -/
def TopLoopS (SCC CODE JETS CALLS JH NARY CR : Noun) : Prop :=
  ∃ (c : Cfg Noun NeedOrd) (r : Ranked c) (bs : List Noun) (outC : Noun → List Noun) (nout : Noun → NeedOrd)
    (Q : Noun → Prop) (st0 : St Noun NeedOrd),
    SamOK SCC CALLS NARY ∧ (∃ b ∈ tapList SCC, getF mugF b NARY = some (A 0)) ∧
    ((∀ n, SCC ≠ C n (C (A 0) (A 0))) ∨ ∃ n, SCC = C n (C (A 0) (A 0)) ∧ CalleeIn CALLS n n) ∧
    CfgOf c SCC (kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR)) ∧
    (∀ k ∈ tapList SCC, ∃ b' : Bell, b'.toNoun = k) ∧
    MemGate c (LoopRS bs outC nout Q) (csiCtx (A 1) (kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR))
      SCC (C CODE (C JETS CALLS)) JH (C NARY CR)) (fun _ => c.none) (A 0) Mode.may (A 0x79616d) ∧
    MemGate c (LoopRS bs outC nout Q) (csiCtx (A 1) (kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR))
      SCC (C CODE (C JETS CALLS)) JH (C NARY CR)) (fun _ => c.none) (A 0) Mode.done (A 0x656e6f64) ∧
    (∀ TOP, TopN (maySweep c st0).ml TOP → MemGate c (LoopRS bs outC nout Q)
      (csiCtx (A 1) (kidsOf SCC (C CODE (C JETS CALLS)) JH (C NARY CR)) SCC (C CODE (C JETS CALLS)) JH (C NARY CR))
      (topOf c (maySweep c st0)) TOP Mode.must (A 0x7473756d)) ∧
    (∀ CA, Q CA → ∃ NR REST, CA = C NR REST ∧ IsMap mugF NR) ∧
    (∀ b, st0.ml b = none) ∧ SureHolds bs st0.sure (C NARY CR) ∧ Q (C NARY CR)

/-- **The top `+compile-scc-in` on a lone bell** (no self call, track A's
`csi_gate_scc_one_f_six_B_any`): its map is one straight. -/
def TopOneS (SCC CODE JETS CALLS JH CACHE : Noun) : Prop :=
  ∀ M T, nock (C csiBody (C (csiSam SCC (C CODE (C JETS CALLS)) JH CACHE) compK)) csiBody = some (C M T) →
    ∃ (B : Bell) (s : Straight (TreapMap mugF)), M = C (C B.toNoun s.toNoun) (C (A 0) (A 0))

/-- What decodes the top loop's map: a loop at `LoopRS`, or a lone bell. -/
def TopDec (SCC CODE JETS CALLS JH CACHE : Noun) : Prop :=
  (∃ NARY CR, CACHE = C NARY CR ∧ TopLoopS SCC CODE JETS CALLS JH NARY CR) ∨ TopOneS SCC CODE JETS CALLS JH CACHE

/-- The map of one straight is a `FinMap.toNoun`. -/
theorem single_toNoun (B : Bell) (s : Straight (TreapMap mugF)) :
    ∃ m : FinMap Bell (Straight (TreapMap mugF)), C (C B.toNoun s.toNoun) (C (A 0) (A 0)) = m.toNoun Straight.toNoun := by
  have h := FinMap.putF_toNoun Straight.toNoun (FinMap.empty : FinMap Bell (Straight (TreapMap mugF))) B s
  rw [FinMap.toNoun_empty] at h
  refine ⟨FinMap.empty.put B s, ?_⟩
  have h0 : putF mugF B.toNoun s.toNoun (A 0) = some (C (C B.toNoun s.toNoun) (C (A 0) (A 0))) := by
    simp [putF]
  have h' : putF mugF B.toNoun s.toNoun (A 0) = some ((FinMap.empty.put B s).toNoun Straight.toNoun) := h
  rw [h0] at h'
  exact Option.some.inj h'

/-- **Decoding (a) at the top loop** (`nmDec` of `UnaryGateAt`) from `TopDec`. -/
theorem nmDec_of_top {FUNC SCC CODE JETS CALLS JH CACHE NM CA : Noun}
    (hcsi : nock (cuTC (cuSam FUNC SCC CODE (C JETS CALLS) JH CACHE)) cuCsi = some (C NM CA))
    (ht : TopDec SCC CODE JETS CALLS JH CACHE) :
    ∃ m : FinMap Bell (Straight (TreapMap mugF)), NM = m.toNoun Straight.toNoun := by
  rw [cu_csi_eq] at hcsi
  rcases ht with ⟨NARY, CR, rfl, c, r, bs, outC, nout, Q, st0, hsam, hmiss, hnd, hcfg, hbell, hmay, hdone, hmust, hQ,
    hml0, hsu0, hq0⟩ | hone
  · exact (csiDecI_iff _ _ _ _ _ _ _).1 (csiDec_of_loop c r bs outC nout Q SCC CODE JETS CALLS JH NARY CR hsam hmiss
      hnd hcfg hbell hmay hdone st0 hmust hQ hml0 hsu0 hq0) NM CA hcsi
  · obtain ⟨B, s, rfl⟩ := hone NM CA hcsi
    exact single_toNoun B s

/-- **The gate of `+compile-unary` with the nested loops at `LoopRS`** (`cu_gate_dir_sccD` with the
table `CalleeHSDStr`: no `CsiDec` asked of the loops). -/
theorem cu_gate_dir_sccDStr (FUNC SCC CODE JETS CALLS JH CACHE NM CA V COLE SC0 MO0 : Noun) (env : CallEnv)
    (inl : Noun → Option Nomm) (n : Nomm) (ht : Noun → Nat) (D : Bell → Prop)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun)
    (hcl : slot? 190 (C JETS CALLS) = some COLE)
    (hcsi : nock (cuTC (cuSam FUNC SCC CODE (C JETS CALLS) JH CACHE)) cuCsi = some (C NM CA))
    (hE0 : AgreeE env (cuRest CA)) (hR0 : RK SC0 inl (cuRest CA)) (hD0 : CacheDec MO0 CA)
    (hn : DirOk n = true)
    (he : EnvFrom env CODE COLE) (hcr : CodeNoRing CODE COLE n) (hana : CodeAna CODE)
    (hsg : SccsGood SC0) (hcj : IsMap mugF CALLS ∧ ∀ k v, Get CALLS k v → IsSet mugF v)
    (hht : HtScc SC0 ht) (hT : ∀ b, D b → CalleeHSDStr env SC0 MO0 CODE JETS CALLS JH inl ht D b)
    (hcal : ∀ b ∈ dirBells n, AnyCalleeH env SCC D (cuCtx FUNC SCC CODE (C JETS CALLS) JH NM) (cuRest CA) b) :
    ∃ CA', Ext (cuRest CA) (cuRest CA') ∧ AgreeE env (cuRest CA') ∧ RK SC0 inl (cuRest CA') ∧ CacheDec MO0 CA' ∧
      nock (C cuGB (C (cuSam FUNC SCC CODE (C JETS CALLS) JH CACHE) compK)) cuGB
        = (finishLUCM (S := CSet) (Map := TreapMap mugF) env n).map fun st => C (C st.toNoun NM) CA' := by
  obtain ⟨CA', h1, h2, h3, h4⟩ := cu_gate_dirE FUNC SCC CODE (C JETS CALLS) JH CACHE NM CA V COLE env
    (RKD SC0 MO0 inl (fun _ => False)) n hgot hv hcl hcsi hE0 ⟨rKP_empty.2 hR0, hD0⟩ hn he hcr hana fun b hb => by
    rcases hcal b hb with ⟨nb, hnb, hr, hs⟩ | ⟨hout, hD, nb, hnb⟩
    · exact ⟨nb, hnb, Or.inl ⟨hr, hs⟩⟩
    · exact ⟨nb, hnb, Or.inr ⟨SCC, by simp [cuCtx, nock_exec], hout,
        calleeCompiled_heights0DStr hsg hcj hht (fun b' hD' => calleeH_of_SDStr hsg hht (hT b' hD')) hD
          (ctxK_cu _ _ _ _ _ _ _) hnb⟩⟩
  exact ⟨CA', h1, h2, rKP_empty.1 h3.1, h3.2, h4⟩

/-- **What `cu_gate_dir_sccDStr` takes at the encoded sample of `+compiled-mono`**: the fields
of `UnaryGateAt` with `nmDec` replaced by `top` (the data that decode the top loop's map) and the
table at `CalleeHSDStr` (no `CsiDec`). -/
structure UnaryGateAtStr (fl : Flags) (st : PSt) (b : Bell) (sc : FinMap Bell Unit)
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
  /-- the table of callees: one-bell (track A) or an SCC with the loop data at `LoopRS` (tracks I/A) -/
  table : ∀ b', D b' → CalleeHSDStr env SC0 (st.cache.mono.toNoun Straight.toNoun) (codeNoun fl st.long.code) st.jets
    (callsNoun st.long) st.hot inl ht D b'
  /-- each callee readable at the start or outside, in `D`, with a need (tracks P/I) -/
  callees : ∀ b' ∈ dirBells n, AnyCalleeH env (FinMap.setNoun sc) D
    (cuCtx b.toNoun (FinMap.setNoun sc) (codeNoun fl st.long.code) (C st.jets (callsNoun st.long)) st.hot NM)
    (cuRest CA) b'

/-- **`UnaryImageAt` from the gate, both decodings proved** (`cu_gate_dir_sccDStr`,
`nmDec_of_top`, `cacheNoun_of_dec`). -/
theorem unaryImageAt_of_gateDStr {fl : Flags} {st : PSt} {b : Bell} {sc : FinMap Bell Unit} {NM CA V COLE SC0 : Noun}
    {env : CallEnv} {inl : Noun → Option Nomm} {n : Nomm} {ht : Noun → Nat} {D : Bell → Prop}
    (H : UnaryGateAtStr fl st b sc NM CA V COLE SC0 env inl n ht D) : UnaryImageAt fl st b sc := by
  obtain ⟨CA', -, -, hR, hD, hg⟩ := cu_gate_dir_sccDStr b.toNoun (FinMap.setNoun sc) (codeNoun fl st.long.code)
    st.jets (callsNoun st.long) st.hot (cacheNoun st.cache) NM CA V COLE SC0 (st.cache.mono.toNoun Straight.toNoun)
    env inl n ht D H.got H.nomm H.cole H.csi H.agree H.rest H.dec H.dir H.envFrom H.noRing H.ana H.sccsGood H.jug
    H.heights H.table H.callees
  refine unaryImageAt_of_gate fl st b sc env n NM
    (fun CA'' => RK SC0 inl (cuRest CA'') ∧ CacheDec (st.cache.mono.toNoun Straight.toNoun) CA'')
    ⟨CA', ⟨hR, hD⟩, hg⟩ (nmDec_of_top H.csi H.top) fun CA'' h => ?_
  rw [H.sccs] at h
  exact cacheNoun_of_dec h.2 h.1.1

/-- **`MonoLinkGood3` from the gate** with `UnaryGateAtStr` (no decoding field) at every `PGood3`
state, bell and SCC. -/
theorem monoLinkGood3_of_gateStr (fl : Flags) (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
    (Cls : Straight (TreapMap mugF) → Prop) (hA : Ar.compileUnary = compileUnaryP fl)
    (hG : ∀ st b sc, PGood3 Cls st → ∃ (NM CA V COLE SC0 : Noun) (env : CallEnv) (inl : Noun → Option Nomm) (n : Nomm)
      (ht : Noun → Nat) (D : Bell → Prop), UnaryGateAtStr fl st b sc NM CA V COLE SC0 env inl n ht D) :
    MonoLinkGood3 fl Ar Cls := by
  intro st b sc hg
  obtain ⟨NM, CA, V, COLE, SC0, env, inl, n, ht, D, H⟩ := hG st b sc hg
  exact monoLinkAt_of fl Ar hA st b sc (unaryImageAt_of_gateDStr H) (monoMissAt_of fl st b sc)

end Compiler
end Formalization
