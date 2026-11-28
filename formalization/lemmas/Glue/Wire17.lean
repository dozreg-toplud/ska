import lemmas.Glue.Assemble16
import lemmas.Compiler.PokeLinkHotTop
import lemmas.Ska.BakeHaltTie
import lemmas.Ska.CompHintWGlue
import lemmas.Glue.GlueConsFragC

/-!
# The wiring of the seventeenth pass (track G): what the other tracks proved, as `gap17` uses it

Each item is a small lemma; `Assemble17.lean` puts them together.

* **The invariant on P's `PGood9`** (track P, `PokeLinkHot*.lean`): `I17 := I14 ∧ PGood9 OptTotal`
  and `Rd17 := Rd14 ∧ jets-hot = ~`; `invStart17` (`good9_empty`); the poke record
  `PokeLeaves17` (`model`, `good9`: every reached state is `PGood9`, the second half of P's
  `pokeModel_fullReachP14`); `reachOn17`.  At every place the compile runs, `jets-hot = ~`
  (`Rd17`), and at every `PGood6` state the values of `call.cole` are ring nouns
  (`ringVals_of_good6`, the path of P's `reach_ringVals`).  So the `+compile-unary` leaves are
  asked only where `jets-hot = ~`: `UnaryOutR9`, `UnaryEnvIsR9`, `UnaryCacheOKR9`, `UnaryAtR9`,
  `unaryAtR9_of`, each implied by its `gap16` form (`unaryOutR9_of` and the rest).
* `pokeLeaves17_of_P14`: the record from P's top as P states it.  NOT used by `gap17`: P's top
  takes the gate in the OLD record `UnaryGateAt`, whose fields `noRing : CodeNoRing` and
  `dir : DirOk` are false on the real compiler (ring code; hinted keys), and P's chain is over
  `MonoLinkGood6` (every `sc`) where K's is over `MonoLinkGood6K` (keys).  So `good9` stays K's
  leaf: P's proof of `pokeModel_fullReachP14` with K's `GateRest8` link forms.
* **The bake leaf with ties** (track Q, `BakeHaltTie.lean`): `bake17_of_dropsT` (Q's
  `bakeEnds_of_dropsT` at `bakeFuel`); `BakeDrops`'s "no tie" is FALSE on the real compiler, so
  the leaf is `BakeDropsT`.
* **J's wider hinted class** (`CompHintWGlue.lean`): `HintLeavesW` (the three model leaves on
  `HintClsBW`), `classLeavesH_hintW` (the raw contract is J's `rawMonoH_hintClsW`, no premise).
* **C's `ConsFragB`** (`GlueConsFragC.lean`): `consFragB_fragX`: it lies in `FragX`, so it adds
  nothing to the class (recorded only).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Ana Bake PokeM Compiler Pill Hoon AnnotSF

/-! ## The invariant on `PGood9` -/

/-- **The invariant of reached states, seventeenth pass**: `I14` and P's `PGood9` (so
`jets-hot = ~` and the ring values of `call.cole`). -/
def I17 (st : PSt) : Prop := I14 st ∧ PGood9 OptTotal st

/-- **Where the compile step runs**: `Rd14`, and `jets-hot = ~`. -/
def Rd17 (Ar : ArmsP) (st : PSt) (b : Bell) : Prop := Rd14 Ar st b ∧ st.hot = A 0

theorem invStart17 : I17 emptySt := ⟨invStart14, good9_empty OptTotal libP⟩

/-- **The leaves of the poke side, on `PGood9`** (K): `model` as `gap16`, and every reached
state is `PGood9` (the second half of P's `pokeModel_fullReachP14`, once K's gate record is in
the form P's chain takes). -/
structure PokeLeaves17 (Ar : ArmsP) : Prop where
  /-- K: `pokeModel_fullReachP9W` (from `GateRest8All`) with P's `PokeOther13`. -/
  model : Assembly.PokeModel (liftPoke (enc flagsOf) (pokeS Ar))
  /-- K (P's chain): every reached state is `PGood9`. -/
  good9 : ∀ st : PSt, PokeReach (enc flagsOf st) → PGood9 OptTotal st

/-- `PokeLeaves17` gives `gap16`'s record. -/
theorem pokeLeaves16_of_17 {Ar : ArmsP} (h : PokeLeaves17 Ar) : PokeLeaves16 Ar :=
  ⟨h.model, fun st hst => (h.good9 st hst).good8.good7.good6⟩

/-- **`PokeLeaves17` from P's top as P states it** (NOT used by `gap17`: `hG` is the old record
`UnaryGateAt`, with `noRing : CodeNoRing` and `dir : DirOk`, false on the real compiler at ring
code and at hinted keys). -/
theorem pokeLeaves17_of_P14 {Ar : ArmsP} {env : Env Noun} {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool}
    {fold frozen : Bool} {bf : BEnv FinMap → Nat} (hR : Route14 Ar env jet fold frozen bf)
    (hL : SpLeavesGood9 OptTotal env jet fold frozen bf jetsOfP newOfP) (hRG : AnaRegsGood env)
    (hG : ∀ st b sc, PGood6 OptTotal st → ∃ (NM CA V COLE SC0 : Noun) (env : Comp.CallEnv) (inl : Noun → Option Nomm)
      (n : Nomm) (ht : Noun → Nat) (D : Bell → Prop), UnaryGateAt flagsOf st b sc NM CA V COLE SC0 env inl n ht D)
    (hU : UnaryKeeps Ar OptTotal) (hCK : UnaryCacheKeeps Ar OptTotal) (hUS : UnarySccsIs Ar)
    (hX : OtherKeeps9 flagsOf OptTotal) (hO : PokeOther13 Ar) : PokeLeaves17 Ar :=
  have H := pokeModel_fullReachP14 Ar env hR.he hR.threshold hR.softSpot hR.registerFast libP hR.skaPoke
    hR.jetRoot hR.optimize hR.sccOf hR.compileUnary hL hRG hG hU hCK hUS hX
  ⟨pokeModel_of_fullOther H.1 hO, H.2⟩

/-- **The reached states on `PGood9`**, as `ReachOn` asks. -/
theorem reachOn17 {Ar : ArmsP} {env : Env Noun} {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool}
    {fold frozen : Bool} {bf : BEnv FinMap → Nat} (hR : Route14 Ar env jet fold frozen bf)
    (hP : PokeLeaves17 Ar) : ReachOn Ar I17 (Rd17 Ar) where
  now := fun st b hi => ⟨(reachOn16 hR (pokeLeaves16_of_17 hP)).now st b hi.1, hi.2.hot⟩
  ana := fun st s f r hi hr => ⟨(reachOn16 hR (pokeLeaves16_of_17 hP)).ana st s f r hi.1 hr, hi.2.hot⟩
  kept := by
    intro st ov p st' hi hh h
    have h1 := (reachOn16 hR (pokeLeaves16_of_17 hP)).kept st ov p st' hi.1 hh h
    exact ⟨h1, hP.good9 st' h1.1⟩

/-- **The values of `call.cole` are ring nouns at every `PGood6` state** (the clause P's
`reach_ringVals` reads, available below `PGood9`). -/
theorem ringVals_of_good6 {st : PSt} (hg : PGood6 OptTotal st) :
    ∃ cm, slot? 126 st.jets = some cm ∧ IsMap mugF cm ∧ ∀ k v, Get cm k v → ∃ n : Ring, v = n.toNoun :=
  hg.good5.good4.good3.good2.good.jets.1

/-! ## The `+compile-unary` leaves where `jets-hot = ~` -/

/-- `UnaryOutR` asked only where `jets-hot = ~` (what K's `GateRest8` must give; with
`ringVals_of_good6`, the `RingNoun` of the `call.cole` values is free). -/
def UnaryOutR9 (Ar : ArmsP) : Prop :=
  ∀ (st : PSt) b (e : VarEntry FinMap) r, PGood6 OptTotal st → st.hot = A 0 → FinMap.get st.long.code b = some e →
    Ar.compileUnary b (sccSet st.long.code b) st.long st.jets st.hot st.cache = some r →
    ∃ (COLE : Noun) (need : Bell → Option NeedOrd) (sure : Bell → NeedOrd)
      (sof : Nomm → Nomm → Nomm → Bell → NeedOrd → Bool),
      slot? 190 (C st.jets (callsNoun st.long)) = some COLE ∧
      (e.nomm.noHint = true →
        Comp.finishLUCMR (S := CSet) (envOf (codeNoun flagsOf st.long.code) COLE need sure sof) e.nomm = some r.1.1) ∧
      (e.nomm.noHint = false → ∃ s', RingSameN r.1.1 s' ∧ RingUniform r.1.1 ∧ RingUniform s' ∧
        Comp.finishLUCH (S := CSet) (envOf (codeNoun flagsOf st.long.code) COLE need sure sof).noRing (snP st.long)
          e.nomm = some s')

/-- `UnaryEnvIsR` asked only where `jets-hot = ~`. -/
def UnaryEnvIsR9 (D : CompData FinMap (TreapMap mugF) Noun Noun) : Prop :=
  ∀ (st : PSt) b (e : VarEntry FinMap) COLE (need : Bell → Option NeedOrd) (sure : Bell → NeedOrd)
    (sof : Nomm → Nomm → Nomm → Bell → NeedOrd → Bool) (s : Straight (TreapMap mugF)),
    PGood6 OptTotal st → st.hot = A 0 → FinMap.get st.long.code b = some e →
    slot? 190 (C st.jets (callsNoun st.long)) = some COLE →
    (e.nomm.noHint = true →
      Comp.finishLUCMR (S := CSet) (envOf (codeNoun flagsOf st.long.code) COLE need sure sof) e.nomm = some s →
      Comp.finishLUCMR (S := CSet) (D.env st.long st.jets st.hot b true) e.nomm = some s) ∧
    (e.nomm.noHint = false →
      Comp.finishLUCH (S := CSet) (envOf (codeNoun flagsOf st.long.code) COLE need sure sof).noRing (snP st.long)
        e.nomm = some s →
      Comp.finishLUCH (S := CSet) (D.env st.long st.jets st.hot b true).noRing (snP st.long) e.nomm = some s)

/-- `UnaryCacheOKR` asked only where `jets-hot = ~`. -/
def UnaryCacheOKR9 (Ar : ArmsP) (ref : Ref FinMap (TreapMap mugF) Noun Noun) : Prop :=
  ∀ (st : PSt) b (e : VarEntry FinMap) r, PGood6 OptTotal st → st.hot = A 0 → FinMap.get st.long.code b = some e →
    Ar.compileUnary b (sccSet st.long.code b) st.long st.jets st.hot st.cache = some r →
    CacheOKR Ar ref st.long st.jets st.hot st.cache → CacheOKR Ar ref st.long st.jets st.hot r.2

/-- `UnaryAtR` asked only where `jets-hot = ~`. -/
def UnaryAtR9 (Ar : ArmsP) (ref : Ref FinMap (TreapMap mugF) Noun Noun) : Prop :=
  ∀ (st : PSt) b (e : VarEntry FinMap) r, PGood6 OptTotal st → st.hot = A 0 → FinMap.get st.long.code b = some e →
    Ar.compileUnary b (sccSet st.long.code b) st.long st.jets st.hot st.cache = some r →
    (∃ s', ref st.long st.jets st.hot b true = some s' ∧ SameO Ar r.1.1 s') ∧
      (CacheOKR Ar ref st.long st.jets st.hot st.cache → CacheOKR Ar ref st.long st.jets st.hot r.2)

theorem unaryOutR9_of {Ar : ArmsP} (h : UnaryOutR Ar) : UnaryOutR9 Ar :=
  fun st b e r hg _ he hu => h st b e r hg he hu

theorem unaryEnvIsR9_of {D : CompData FinMap (TreapMap mugF) Noun Noun} (h : UnaryEnvIsR D) : UnaryEnvIsR9 D :=
  fun st b e COLE need sure sof s hg _ he hc => h st b e COLE need sure sof s hg he hc

theorem unaryCacheOKR9_of {Ar : ArmsP} {ref : Ref FinMap (TreapMap mugF) Noun Noun} (h : UnaryCacheOKR Ar ref) :
    UnaryCacheOKR9 Ar ref :=
  fun st b e r hg _ he hu => h st b e r hg he hu

theorem unaryAtR9_of_R {Ar : ArmsP} {ref : Ref FinMap (TreapMap mugF) Noun Noun} (h : UnaryAtR Ar ref) :
    UnaryAtR9 Ar ref :=
  fun st b e r hg _ he hu => h st b e r hg he hu

/-- **`UnaryAtR9` from `UnaryOutR9`, `UnaryEnvIsR9`, `UnaryCacheOKR9`** (and `OptRing` for the
hinted keys): `unaryAtR_of` where `jets-hot = ~`. -/
theorem unaryAtR9_of {Ar : ArmsP} {D : CompData FinMap (TreapMap mugF) Noun Noun} (hO : OptRing Ar)
    (hK : UnaryOutR9 Ar) (hE : UnaryEnvIsR9 D) (hC : UnaryCacheOKR9 Ar (refDHR CSet D snP)) :
    UnaryAtR9 Ar (refDHR CSet D snP) := by
  intro st b e r hg hh he hu
  refine ⟨?_, hC st b e r hg hh he hu⟩
  obtain ⟨COLE, need, sure, sof, hcole, h1, h2⟩ := hK st b e r hg hh he hu
  obtain ⟨hE1, -⟩ := hE st b e COLE need sure sof r.1.1 hg hh he hcole
  have he' : Treap.get st.long.code b = some e := he
  simp only [refDHR, if_true, realOf, he', Option.map_some, Option.bind_some]
  by_cases hn : e.nomm.noHint = true
  · rw [if_pos hn]
    exact ⟨r.1.1, hE1 hn (h1 hn), sameO_refl Ar _⟩
  · rw [if_neg hn]
    have hf : e.nomm.noHint = false := by simpa using hn
    obtain ⟨s', hs, hu1, hu2, hl⟩ := h2 hf
    obtain ⟨-, hE2'⟩ := hE st b e COLE need sure sof s' hg hh he hcole
    exact ⟨s', hE2' hf hl, hO _ _ hu1 hu2 hs⟩

/-- **`unary` on the `%full` path where `jets-hot = ~`.** -/
theorem unaryMid17 {Ar : ArmsP} {env : Env Noun} {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool}
    {fold frozen : Bool} {bf : BEnv FinMap → Nat} {ref : Ref FinMap (TreapMap mugF) Noun Noun}
    (hR : Route14 Ar env jet fold frozen bf) (hU : UnaryAtR9 Ar ref) {st0 : PSt} {s f : Noun}
    {r : Bell × LongB FinMap × Noun × Noun} (hg : PGood6 OptTotal st0) (hh : st0.hot = A 0)
    (e1 : Ar.skaPoke s f st0.long st0.jets st0.hot = some r) {q : FinMap Bell Unit × FinMap Bell (FinMap Bell Unit)}
    (e3 : Ar.sccOf r.1 r.2.1 st0.cache.sccs = some q) {s' : Straight (TreapMap mugF)}
    {n : FinMap Bell (Straight (TreapMap mugF))} {c' : Cache FinMap (TreapMap mugF) (Noun × Noun)}
    (hu : Ar.compileUnary r.1 q.1 r.2.1 r.2.2.1 st0.hot { st0.cache with sccs := q.2 } = some ((s', n), c')) :
    (∃ x, ref r.2.1 r.2.2.1 st0.hot r.1 true = some x ∧ SameO Ar s' x) ∧
      (CacheOKR Ar ref r.2.1 r.2.2.1 st0.hot st0.cache → CacheOKR Ar ref r.2.1 r.2.2.1 st0.hot c') := by
  have hK := skaKeeps_of_armP Ar hR.skaPoke jetsOfGood_P
  obtain ⟨⟨eb, heb⟩, hq⟩ := mid_key hR.skaPoke hR.sccOf st0 s f hg.good5 r e1 q e3
  have hm := good6_mid hR.skaPoke hK (sccOfKeeps_of hR.sccOf) (sccOfIsK_of hR.sccOf) tarjanExists jetsOfCole6_P
    st0 s f hg r e1 q e3
  rw [hq] at hu
  exact hU _ r.1 eb _ hm hh heb hu

/-- **`unary` on the `%dire` path where `jets-hot = ~`**, from P's `DireGood6`. -/
theorem unaryDireR17_of {Ar : ArmsP} {ref : Ref FinMap (TreapMap mugF) Noun Noun} (hDG : DireGood6 Ar)
    (hU : UnaryAtR9 Ar ref) :
    ∀ (st : PSt) b q s n c', PGood6 OptTotal st → st.hot = A 0 → InvK libP st.long →
      Ar.sccOf b st.long st.cache.sccs = some q →
      Ar.compileUnary b q.1 st.long st.jets st.hot { st.cache with sccs := q.2 } = some ((s, n), c') →
      (∃ x, ref st.long st.jets st.hot b true = some x ∧ SameO Ar s x) ∧
        (CacheOKR Ar ref st.long st.jets st.hot st.cache → CacheOKR Ar ref st.long st.jets st.hot c') := by
  intro st b q s n c' hg hh hk hq hu
  obtain ⟨⟨eb, heb⟩, hq1, hm⟩ := hDG st b q _ hg hk hq hu
  have hu' : Ar.compileUnary b (sccSet st.long.code b) st.long st.jets st.hot { st.cache with sccs := q.2 } =
      some ((s, n), c') := by rw [← hq1]; exact hu
  exact hU _ b eb _ hm hh heb hu'

/-! ## The bake leaf with ties (Q) -/

/-- **The bake leaf from Q's tie-tolerant measure** (`bakeEnds_of_dropsT` at `bakeFuel`). -/
theorem bake17_of_dropsT {env : Env Noun} {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool}
    {fold frozen : Bool} (h : BakeDropsT (M := FinMap) libP env jet fold frozen (anaFuel env regOfP) regOfP) :
    BakeEnds libP env jet fold frozen (anaFuel env regOfP) (bakeFuel (M := FinMap)) regOfP :=
  bakeEnds_of_dropsT h

/-! ## J's wider hinted class -/

variable {S : Type} [Comp.HoonSet S]

/-- **The model leaves of J's wider hinted class** (D: `OptIn`; G / D: the entry; H / O: the
totality of the pill's `+optimize`), at `finishLUCH`. -/
structure HintLeavesW (S : Type) [Comp.HoonSet S] (lib : Lib) : Prop where
  optIn : ∀ snd, OptInMonoH S (TreapMap mugF) snd (HintClsBW snd lib)
  entry : ∀ snd, EntryMonoH S (TreapMap mugF) lib snd (HintClsBW snd lib)
  total : ∀ snd, OptTotalMonoH S snd (HintClsBW snd lib)

/-- **J's wider hinted class as a `ClassLeavesH` class**: the raw contract is J's
`rawMonoH_hintClsW` (no premise), the n-ary side empty. -/
theorem classLeavesH_hintW {lib : Lib} (h : HintLeavesW S lib) :
    ClassLeavesH S lib (fun snd => HintClsBW snd lib) NoNary where
  rawMono := fun snd => rawMonoH_hintClsW lib snd
  rawNary := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hf => hf.elim
  optInMono := h.optIn
  optInNary := fun _ _ _ _ _ _ _ _ hf => hf.elim
  entryMono := h.entry
  entryNary := fun _ _ _ _ _ _ _ _ hf => hf.elim
  totalMono := h.total
  totalNary := fun _ _ _ _ _ _ _ _ hf => hf.elim

/-! ## C's `ConsFragB`: inside `FragX` -/

/-- **`ConsFragB` lies in `FragX`** (C's `consFragM_fragXM`): the class of C's new contract adds
no member to `gap17`'s class, which has `FragX` already. -/
theorem consFragB_fragX {env : Comp.CallEnv} {N : Needs} {bl : Bell} {nm : Nomm} (h : ConsFragB env N bl nm) :
    liftMC (FragXM S) env N bl nm :=
  consFragM_fragXM ⟨bl.fol, h⟩

end Glue
end SkaModel
end Formalization
