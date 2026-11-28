import lemmas.Compiler.CompMonoLinkTop6

/-!
# The field `noRing` of the gate's record, split (track K, README Gaps 19 (g))

`CodeNoRing CODE COLE n` (`CompUnaryDir.lean`) asks two things of every direct callee `b` of
`n`: a code entry with a loobean `pure` (`codeOf CODE b = some c`), and NO `call.cole` entry.

**The check on the real compiler** (`tools/hoon/ringcall.hoon`, 2026-11-28).  The core
`[[ma mb] 1 2 3 4 5 6 0]` is registered by `%fast` (`/mm`) before the first `%full`; the root
`[9 4 0 1]` calls its arm `ma` directly (`ma`, `mb` call each other):
* with `jets-hot` empty, the `%full` gives `ma` and `mb` the rings `[/mm 4]`, `[/mm 5]` in
  `call.cole` (`+ska-cole-update`), both get a `nary.cache` entry (compiled normally through
  `+callee-compiled`), and the root compiles normally, but its call is the op `%jsf` / `%jmf`
  (`%caf` / `%csf` under `%next`), the call THROUGH the ring, not `%jsp` / `%jmp`;
* after a `%jets` that makes both rings hot, all three bells are dropped, and the same `%full`
  compiles only the root: `+callee-need` returns the driver's need `need.u.j`, the callee is not
  compiled (`%.n`), and the root's one block ends in `%jmf`.

So the second half of `CodeNoRing` is not an invariant of the compiler, and "no hot driver" is
what `+callee-need` and the `sur` of `+run` / `+run-shape` really read (`CodeNoHot`).  BUT the
model of the call, `callL` / `callLM` (`Ska/CompCall.lean`, `Ska/CompDirectM.lean`, line
`| _, _, _ => fun _ => Option.none`), has no case for `env.ring b = some r`: on a ringed callee
without a hot driver the model fails where the pill emits `%caf` / `%jmf`.  The restatement on
"no hot driver" therefore needs that model case first (its owner: the call model, README Gaps
12.9 / 18.8); until then the gate can only ask `CodeRingFree`, the model's fragment, which is
false at a reachable state (the witness above) and is therefore a SCOPE hypothesis.

*Proved here*: the first half of `CodeNoRing` from the state (`codeKeys_of_closed`: `CodeClosed`
of `PGood2` and `FlagsLoob`); `GateRest7Sw` (the record with `noRing` replaced by
`ringFree : CodeRingFree`), `gateRest6Sw_of_7`, `gateRest6All_of_7`; `flagsLoob_flagsOf`; the top
`pokeModel_fullReachP9V`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeF SkaModel.PokeM FinMap

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## The two halves of `CodeNoRing`, and the true restriction -/

/-- **The model's fragment** (`callL` has no ring case): no direct callee of `n` has a
`call.cole` entry.  NOT an invariant of the compiler (`tools/hoon/ringcall.hoon`). -/
def CodeRingFree (COLE : Noun) (n : Nomm) : Prop :=
  ∀ b ∈ dirBells n, getF mugF b.toNoun COLE = some (A 0)

/-- **What `+callee-need` reads** (lines 4605 to 4609, and the `sur` of `+run` line 3971 and of
`+run-shape` line 4465): no direct callee's ring has a `jets-hot` entry (`JH` the noun of
`jets-hot`).  The restriction under which the callee is compiled and its own need is used. -/
def CodeNoHot (CODE COLE JH : Noun) (n : Nomm) : Prop :=
  ∀ b ∈ dirBells n, (∃ c, codeOf CODE b = some c) ∧
    ∀ r, getF mugF b.toNoun COLE = some (C (A 0) r) → getF mugF r JH = some (A 0)

/-- The two halves give `CodeNoRing`. -/
theorem codeNoRing_of {CODE COLE : Noun} {n : Nomm} (hk : ∀ b ∈ dirBells n, ∃ c, codeOf CODE b = some c)
    (hr : CodeRingFree COLE n) : CodeNoRing CODE COLE n :=
  fun b hb => ⟨hk b hb, hr b hb⟩

/-- `CodeNoRing` is the stronger: with no ring there is no hot driver. -/
theorem codeNoHot_of_noRing {CODE COLE JH : Noun} {n : Nomm} (h : CodeNoRing CODE COLE n) :
    CodeNoHot CODE COLE JH n :=
  fun b hb => ⟨(h b hb).1, fun r hr => by rw [(h b hb).2] at hr; cases hr⟩

/-! ## The first half from the state -/

/-- Every direct callee is a `%2` info bell. -/
theorem dirBells_sub_infos : ∀ (n : Nomm) (b : Bell), b ∈ dirBells n → b ∈ nommInfos n
  | Nomm.cons p q, b, h => by
    simp only [dirBells, nommInfos, List.mem_append] at h ⊢
    rcases h with h | h
    · exact Or.inl (dirBells_sub_infos p b h)
    · exact Or.inr (dirBells_sub_infos q b h)
  | Nomm.n2 p q Option.none, b, h => by
    simp only [dirBells, nommInfos, List.mem_append] at h ⊢
    rcases h with h | h
    · exact Or.inl (Or.inl (dirBells_sub_infos p b h))
    · exact Or.inl (Or.inr (dirBells_sub_infos q b h))
  | Nomm.n2 p q (some (c, k)), b, h => by
    simp only [dirBells, nommInfos, List.mem_append, List.mem_cons] at h ⊢
    rcases h with h | h | h
    · exact Or.inr (by simp [h])
    · exact Or.inl (Or.inl (dirBells_sub_infos p b h))
    · exact Or.inl (Or.inr (dirBells_sub_infos q b h))
  | Nomm.n3 p, b, h => by
    simp only [dirBells, nommInfos] at h ⊢; exact dirBells_sub_infos p b h
  | Nomm.n4 p, b, h => by
    simp only [dirBells, nommInfos] at h ⊢; exact dirBells_sub_infos p b h
  | Nomm.n5 p q, b, h => by
    simp only [dirBells, nommInfos, List.mem_append] at h ⊢
    rcases h with h | h
    · exact Or.inl (dirBells_sub_infos p b h)
    · exact Or.inr (dirBells_sub_infos q b h)
  | Nomm.n6 p q r, b, h => by
    simp only [dirBells, nommInfos, List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · exact Or.inl (Or.inl (dirBells_sub_infos p b h))
    · exact Or.inl (Or.inr (dirBells_sub_infos q b h))
    · exact Or.inr (dirBells_sub_infos r b h)
  | Nomm.n7 p q, b, h => by
    simp only [dirBells, nommInfos, List.mem_append] at h ⊢
    rcases h with h | h
    · exact Or.inl (dirBells_sub_infos p b h)
    · exact Or.inr (dirBells_sub_infos q b h)
  | Nomm.n10 a v q, b, h => by
    simp only [dirBells, nommInfos, List.mem_append] at h ⊢
    rcases h with h | h
    · exact Or.inl (dirBells_sub_infos v b h)
    · exact Or.inr (dirBells_sub_infos q b h)
  | Nomm.n0 _, b, h => by simp [dirBells] at h
  | Nomm.n1 _, b, h => by simp [dirBells] at h
  | Nomm.n11s _ _ _, b, h => by simp [dirBells] at h
  | Nomm.n11d _ _ _ _, b, h => by simp [dirBells] at h
  | Nomm.n12 _ _, b, h => by simp [dirBells] at h
  | Nomm.mean _ _ _ _ _, b, h => by simp [dirBells] at h

/-- **The flags of every key start with a loobean** (`pure`): what `codeOf` reads at axis `6` of
`[nomm flags]`.  P: for `flagsOf` it is `flagsLoob_flagsOf`. -/
def FlagsLoob (fl : Flags) (code : FinMap Bell (VarEntry FinMap)) : Prop :=
  ∀ b e, FinMap.get code b = some e → ∃ c, (slot? 2 (fl code b)).bind unLoob = some c

/-- `FlagsLoob` of a flags function that gives `flagNoun` of a pair at every key. -/
theorem flagsLoob_of_noun {fl : Flags} {code : FinMap Bell (VarEntry FinMap)}
    (h : ∀ b e, FinMap.get code b = some e → ∃ p, fl code b = flagNoun p) : FlagsLoob fl code := by
  intro b e hb
  obtain ⟨⟨p1, p2⟩, hp⟩ := h b e hb
  refine ⟨p1, ?_⟩
  rw [hp]
  cases p1 <;> simp [flagNoun, nock_exec, unLoob]

/-- **`FlagsLoob flagsOf T`** when the SCC loop has a solution on `T` and every solution gives
every key flags. -/
theorem flagsLoob_flagsOf {T : FinMap Bell (VarEntry FinMap)} (hex : ∃ F, FlagSol T F)
    (hall : ∀ G, FlagSol T G → ∀ b e, FinMap.get T b = some e → ∃ p, G b = some p) : FlagsLoob flagsOf T := by
  apply flagsLoob_of_noun
  intro b e hb
  have hs := Classical.epsilon_spec (p := FlagSol T) hex
  obtain ⟨p, hp⟩ := hall _ hs b e hb
  exact ⟨p, by simp only [flagsOf, hp]⟩

/-- **The first half of `CodeNoRing` from the state**: in a closed table whose flags start with a
loobean, every direct callee of an entry has a code entry with its `pure`. -/
theorem codeKeys_of_closed {fl : Flags} {code : FinMap Bell (VarEntry FinMap)} (hc : CodeClosed code)
    (hfl : FlagsLoob fl code) {b : Bell} {e : VarEntry FinMap} (he : FinMap.get code b = some e) :
    ∀ b' ∈ dirBells e.nomm, ∃ c, codeOf (codeNoun fl code) b' = some c := by
  intro b' hb'
  obtain ⟨e', he'⟩ := (hc b e he).2 b' (dirBells_sub_infos e.nomm b' hb')
  obtain ⟨c, hcv⟩ := hfl b' e' he'
  have hg : getF mugF b'.toNoun (codeNoun fl code) = some (C (A 0) (C e'.nomm.toNoun (fl code b'))) := by
    have hc := codeNoun_getF fl code b'
    rw [he'] at hc
    exact hc
  refine ⟨c, ?_⟩
  unfold codeOf
  rw [hg]
  simpa [nock_exec] using hcv

/-! ## The record with `noRing` split -/

/-- **`GateRest6Sw` with `noRing` replaced by `ringFree`** (the key half is a state fact,
`codeKeys_of_closed`).  `ringFree` is the model's fragment (no `call.cole` entry at a direct
callee): a scope hypothesis until `callL` models `%caf` / `%jmf`, then `CodeNoHot`. -/
structure GateRest7Sw (fl : Flags) (st : PSt) (b : Bell) (e : VarEntry FinMap) (NM CA COLE : Noun)
    (env : Comp.CallEnv) (inl : Noun → Option Nomm) (D : Bell → Prop) : Prop where
  csi : nock (cuTC (cuSam b.toNoun (FinMap.setNoun (sccSet st.long.code b)) (codeNoun fl st.long.code)
    (C st.jets (callsNoun st.long)) st.hot (cacheNoun st.cache))) cuCsi = some (C NM CA)
  agree : AgreeE env (cuRest CA)
  rest : RK (sccsNoun st.cache.sccs) inl (cuRest CA)
  dec : CacheDec (st.cache.mono.toNoun Straight.toNoun) CA
  top : TopDecSh (FinMap.setNoun (sccSet st.long.code b)) (codeNoun fl st.long.code) st.jets (callsNoun st.long)
    st.hot (cacheNoun st.cache)
  dir : DirOk e.nomm = true
  /-- the model's fragment: no direct callee has a ring (scope; see the header) -/
  ringFree : CodeRingFree COLE e.nomm
  ana : CodeAna (codeNoun fl st.long.code)
  table : ∀ ht, HtRank (sccsNoun st.cache.sccs) (callsNoun st.long) ht → HtScc (sccsNoun st.cache.sccs) ht →
    ∀ b', D b' → CalleeHSDSw env (sccsNoun st.cache.sccs) (st.cache.mono.toNoun Straight.toNoun)
      (codeNoun fl st.long.code) st.jets (callsNoun st.long) st.hot inl ht D b'
  callees : ∀ b' ∈ dirBells e.nomm, AnyCalleeH env (FinMap.setNoun (sccSet st.long.code b)) D
    (cuCtx b.toNoun (FinMap.setNoun (sccSet st.long.code b)) (codeNoun fl st.long.code) (C st.jets (callsNoun st.long))
      st.hot NM)
    (cuRest CA) b'

/-- **`GateRest6Sw` from `GateRest7Sw`**, the closed table and `FlagsLoob`. -/
theorem gateRest6Sw_of_7 {fl : Flags} {st : PSt} {b : Bell} {e : VarEntry FinMap} {NM CA COLE : Noun}
    {env : Comp.CallEnv} {inl : Noun → Option Nomm} {D : Bell → Prop}
    (hc : CodeClosed st.long.code) (hfl : FlagsLoob fl st.long.code) (he : FinMap.get st.long.code b = some e)
    (H : GateRest7Sw fl st b e NM CA COLE env inl D) : GateRest6Sw fl st b e NM CA COLE env inl D :=
  ⟨H.csi, H.agree, H.rest, H.dec, H.top, H.dir, codeNoRing_of (codeKeys_of_closed hc hfl he) H.ringFree,
    H.ana, H.table, H.callees⟩

/-- The record `GateRest7Sw` asked at every `PGood6` state, key, entry and `COLE`. -/
def GateRest7All (fl : Flags) (Cls : Straight (TreapMap mugF) → Prop) : Prop :=
  ∀ st b e COLE, PGood6 Cls st → FinMap.get st.long.code b = some e →
    slot? 190 (C st.jets (callsNoun st.long)) = some COLE →
    ∃ (NM CA : Noun) (need : Bell → Option SkaModel.NeedOrd) (sure : Bell → SkaModel.NeedOrd)
      (sof : Nomm → Nomm → Nomm → Bell → SkaModel.NeedOrd → Bool) (inl : Noun → Option Nomm) (D : Bell → Prop),
      GateRest7Sw fl st b e NM CA COLE (envOf (codeNoun fl st.long.code) COLE need sure sof) inl D

/-- **`GateRest6All` from `GateRest7All`** and `FlagsLoob` at every `PGood6` state. -/
theorem gateRest6All_of_7 {fl : Flags} {Cls : Straight (TreapMap mugF) → Prop}
    (hFL : ∀ st, PGood6 Cls st → FlagsLoob fl st.long.code) (H : GateRest7All fl Cls) : GateRest6All fl Cls := by
  intro st b e COLE hg he hcole
  obtain ⟨NM, CA, need, sure, sof, inl, D, H7⟩ := H st b e COLE hg he hcole
  exact ⟨NM, CA, need, sure, sof, inl, D, gateRest6Sw_of_7 hg.good5.good4.good3.good2.closed (hFL st hg) he H7⟩

/-- **THE TOP with the key half of `noRing` discharged**: `pokeModel_fullReachP9U` with the
record `GateRest7All` (its `ringFree` the model's fragment) and `FlagsLoob flagsOf` at every
`PGood6` state (P: `flagsLoob_flagsOf` from a solution of the SCC loop that flags every key). -/
theorem pokeModel_fullReachP9V (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
    (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP) (lib : Lib)
    {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool}
    {bf : BEnv FinMap → Nat}
    (hA : Ar.skaPoke = anaArmP env jet fold frozen (anaFuel env regOfP) bf regOfP jetsOfP newOfP)
    (hJA : Ar.jetRoot = jetRootP) (hOA : Ar.optimize = optimizeP) (hSA : Ar.sccOf = sccOfP)
    (hUA : Ar.compileUnary = compileUnaryP flagsOf)
    (hL : SpLeavesGood OptTotal env jet fold frozen bf jetsOfP newOfP)
    (hGR : GateRest7All flagsOf OptTotal) (hFL : ∀ st, PGood6 OptTotal st → FlagsLoob flagsOf st.long.code)
    (hRK : UnaryRestKeys6 flagsOf OptTotal)
    (hU : UnaryKeeps Ar OptTotal) (hX : OtherKeeps6 flagsOf OptTotal) :
    ∀ cr, CorIn cr → ∀ s f, pokeN cr (Ovum.full s f).toNoun =
      (liftPoke (enc flagsOf) (pokeS Ar) cr (Ovum.full s f)).map fun r => C r.1.toNoun r.2 :=
  pokeModel_fullReachP9U Ar env hhe hth hsoft hrf lib hA hJA hOA hSA hUA hL (gateRest6All_of_7 hFL hGR) hRK hU hX

end Compiler
end Formalization
