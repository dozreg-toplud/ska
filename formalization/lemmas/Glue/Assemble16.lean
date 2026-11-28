import lemmas.Glue.Assemble15
import lemmas.Glue.RefSideR
import lemmas.Ska.BakeHalt

/-!
# The assembly, sixteenth pass (track G): the real compiler with rings

ONE theorem, `gap16`: all eight fields of `Assembly.Gap` (hence `Full`, `full16`) for

* `lib := libP`, `pk := liftPoke (enc flagsOf) (pokeS Ar)` (as `gap15`),
* the reference compiler `refDHR CSet D snP`: track K's RING MODEL (`finishLUCMR` of the
  table's hint-free nomm, `finishLFCR` of `D.inl`; a hinted nomm through `finishLUCH` with the
  rings dropped),
* `InvC := liftInv (enc flagsOf) (InvSMIR Ar libP (refDHR CSet D snP) I14)`: the cache compared
  UP TO RINGS (`CacheOKR`: misfit 11 gone; K's finding that a cached caller keeps `%jmp` while a
  fresh compile emits `%jmf` after a `%jets ~` is inside the invariant),

from `Route14` at `bf := bakeFuel`, `PokeLeaves16` (K's top and reached-state goodness, with NO
`ringFree` / `CodeNoRing`: misfit 9 gone), `CompLeaves16`, `ClassLeavesH` (unchanged: at the
no-ring reference `refDH CSet (noRingD D) snP`), `HaltLeaves16`, `FormatLeaves13`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Ana Bake PokeM Compiler Pill Hoon AnnotSF

/-! ## The poke side, with no ring-free record -/

/-- **The leaves of the poke side (owner K)**: what K's running step gives once `GateRest8`
(the record of `+compile-unary` with `env.ring b = ringOf COLE b` and no `ringFree` field)
replaces `GateRest6All`. -/
structure PokeLeaves16 (Ar : ArmsP) : Prop where
  /-- K: `pokeModel_fullReachP9W` (from `spLeaves`, `GateRest8All`, `restKeys`, `unaryKeeps`,
  `otherKeeps` and P's `PokeOther13`). -/
  model : Assembly.PokeModel (liftPoke (enc flagsOf) (pokeS Ar))
  /-- K: `pokeReachGood6K` with `monoLinkGood6K_of_gate8`: every reached state is `PGood6`. -/
  good : ∀ st : PSt, PokeReach (enc flagsOf st) → PGood6 OptTotal st

/-- **The reached states, as `ReachOn` asks**, from `PokeLeaves16`. -/
theorem reachOn16 {Ar : ArmsP} {env : Env Noun} {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool}
    {fold frozen : Bool} {bf : BEnv FinMap → Nat} (hR : Route14 Ar env jet fold frozen bf)
    (hP : PokeLeaves16 Ar) : ReachOn Ar I14 (Rd14 Ar) where
  now := fun st _ hi => ⟨hi.2, Or.inl (hP.good st hi.1)⟩
  ana := fun st s f r hi hr =>
    ⟨invK_ana14 hR.skaPoke s f _ _ _ r hi.2 hr, Or.inr ⟨st, s, f, r, hP.good st hi.1, hr, rfl, rfl⟩⟩
  kept := by
    intro st ov p st' hi hh h
    refine ⟨?_, pokeS_invK hR.skaPoke st ov p st' hi.2 h⟩
    have hc : CorIn (enc flagsOf st) :=
      corIn_of_tail Assembly.corIn_cor (by simp only [cor_enc flagsOf, enc_slot15]) hi.1
    have hn := not_hot_noun hh
    have hpk := hP.model (enc flagsOf st) hc ov hn
    rw [liftPoke_enc (enc_inj flagsOf), h] at hpk
    exact PokeReach.poke hi.1 hpk hn

/-! ## `+compile-unary` up to rings -/

/-- **Leaf (K, I): `+compile-unary` at a key of a `PGood6` state gives the reference form up to
rings, and keeps the cache up to rings.**  K's `GateRest8` gives "+compile-unary IS
`finishLUCMR (envOf CODE COLE ..)` of the key's nomm" at hint-free keys (its hinted twin at
hinted keys, misfit 10); `UnaryEnvIsR` (K, I) carries `envOf` to `D.env`; `UnaryCacheOKR` (I, K)
is the second half. -/
def UnaryAtR (Ar : ArmsP) (ref : Ref FinMap (TreapMap mugF) Noun Noun) : Prop :=
  ∀ (st : PSt) b (e : VarEntry FinMap) r, PGood6 OptTotal st → FinMap.get st.long.code b = some e →
    Ar.compileUnary b (sccSet st.long.code b) st.long st.jets st.hot st.cache = some r →
    (∃ s', ref st.long st.jets st.hot b true = some s' ∧ SameO Ar r.1.1 s') ∧
      (CacheOKR Ar ref st.long st.jets st.hot st.cache → CacheOKR Ar ref st.long st.jets st.hot r.2)

/-- **`unary` on the `%full` path, up to rings.** -/
theorem unaryMid16 {Ar : ArmsP} {env : Env Noun} {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool}
    {fold frozen : Bool} {bf : BEnv FinMap → Nat} {ref : Ref FinMap (TreapMap mugF) Noun Noun}
    (hR : Route14 Ar env jet fold frozen bf) (hU : UnaryAtR Ar ref) {st0 : PSt} {s f : Noun}
    {r : Bell × LongB FinMap × Noun × Noun} (hg : PGood6 OptTotal st0)
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
  exact hU _ r.1 eb _ hm heb hu

/-- **`unary` on the `%dire` path, up to rings**, from P's `DireGood6`. -/
theorem unaryDireR_of {Ar : ArmsP} {ref : Ref FinMap (TreapMap mugF) Noun Noun} (hDG : DireGood6 Ar)
    (hU : UnaryAtR Ar ref) :
    ∀ (st : PSt) b q s n c', PGood6 OptTotal st → InvK libP st.long →
      Ar.sccOf b st.long st.cache.sccs = some q →
      Ar.compileUnary b q.1 st.long st.jets st.hot { st.cache with sccs := q.2 } = some ((s, n), c') →
      (∃ x, ref st.long st.jets st.hot b true = some x ∧ SameO Ar s x) ∧
        (CacheOKR Ar ref st.long st.jets st.hot st.cache → CacheOKR Ar ref st.long st.jets st.hot c') := by
  intro st b q s n c' hg hk hq hu
  obtain ⟨⟨eb, heb⟩, hq1, hm⟩ := hDG st b q _ hg hk hq hu
  have hu' : Ar.compileUnary b (sccSet st.long.code b) st.long st.jets st.hot { st.cache with sccs := q.2 } =
      some ((s, n), c') := by rw [← hq1]; exact hu
  exact hU _ b eb _ hm heb hu'

/-! ## The leaves of `CompHypOnR` at `refDHR` -/

/-- The reference compiler of `gap16`. -/
noncomputable abbrev refR (D : CompData FinMap (TreapMap mugF) Noun Noun) : Ref FinMap (TreapMap mugF) Noun Noun :=
  refDHR CSet D snP

/-- The no-ring reference of `gap16`'s class leaves (`gap15`'s `refDH`, at `noRingD D`). -/
noncomputable abbrev ref0 (D : CompData FinMap (TreapMap mugF) Noun Noun) : Ref FinMap (TreapMap mugF) Noun Noun :=
  refDH CSet (noRingD D) snP

/-- **The compile leaves of `gap16`**: the state leaves up to rings at `refDHR`, the
contract-side leaves at the no-ring reference, the ring leaves (K) and the optimizer leaf (H). -/
structure CompLeaves16 (Ar : ArmsP) (D : CompData FinMap (TreapMap mugF) Noun Noun) (FM : MonoClassH) (FN : NaryClass) :
    Prop where
  /-- K (`GateRest8`), K / I (env), I / K (cache): `+compile-unary` up to rings. -/
  unaryAt : UnaryAtR Ar (refR D)
  /-- P: `%dire` at a `PGood6` state (the `%dire` twin of `mid_key`, `good6_mid`). -/
  direGood : DireGood6 Ar
  /-- I: `+compile-scc` on the `%dire` path, up to rings. -/
  scc : ∀ (st : PSt) b q m c', I14 st → Ar.sccOf b st.long st.cache.sccs = some q →
    Ar.compileScc q.1 st.long st.jets st.hot { st.cache with sccs := q.2 } = some (m, c') →
    (∀ b' s, Treap.get m b' = some s → ∃ s', refR D st.long st.jets st.hot b' false = some s' ∧ SameO Ar s s') ∧
      (CacheOKR Ar (refR D) st.long st.jets st.hot st.cache → CacheOKR Ar (refR D) st.long st.jets st.hot c')
  /-- I + no owner: the compile returns where it runs. -/
  answers : ∀ (st : PSt) b m s, Rd14 Ar st b → InvSR Ar libP (refR D) st →
    refR D st.long st.jets st.hot b m = some s → (compileStep Ar st b m).isSome
  /-- no owner: what is compiled holds across `+ska-poke` up to rings, at reached states. -/
  stable : ∀ (st : PSt) s f r b m x, I14 st → Ar.skaPoke s f st.long st.jets st.hot = some r →
    InvB libP st.long → refR D st.long st.jets st.hot b m = some x →
      ∃ x', refR D r.2.1 r.2.2.1 st.hot b m = some x' ∧ SameO Ar x x'
  /-- no owner: the jetted root, at reached states. -/
  jetRoot : ∀ (st : PSt) s f r out, I14 st → Ar.skaPoke s f st.long st.jets st.hot = some r →
    InvB libP st.long → Ar.jetRoot r.2.2.1 st.hot r.1 = some out →
    out.nargs = 1 ∧ out.need = NeedOrd.this ∧
      ContractFwd libP (refN Ar (refR D) r.2.1 r.2.2.1 st.hot) s f [s] out ∧
      ContractBwd libP (refN Ar (refR D) r.2.1 r.2.2.1 st.hot) s f [s] out
  /-- no owner: `%jets ~` keeps the cache UP TO RINGS (K's finding is inside), at reached states. -/
  jets : ∀ st p r, I14 st → ¬ HotOvum (Ovum.jets p) → Ar.jetsPoke st p = some r →
    CacheOKR Ar (refR D) st.long st.jets st.hot st.cache → CacheOKR Ar (refR D) st.long r.2.1 r.2.2.1 r.2.2.2
  /-- no owner: `%fast` keeps the cache up to rings, at reached states. -/
  fast : ∀ st rs p r, I14 st → Ar.fastPoke st rs p = some r →
    CacheOKR Ar (refR D) st.long st.jets st.hot st.cache → CacheOKR Ar (refR D) st.long r.1 st.hot r.2
  /-- C, J, K, A: every compiled nomm of a reached table is in the class, at the no-ring
  reference (as `gap15`, at `noRingD D`). -/
  inFrag : InFragOnH CSet Ar libP (noRingD D) snP FM FN Tr14
  /-- P: the pill's `+optimize` on the no-ring reference forms of reached tables. -/
  optPill : ∀ long jets hot b m s, InvB libP long → Tr14 long jets hot → ref0 D long jets hot b m = some s →
    nock (C optBody (C s.toNoun optC)) optBody = some (Ar.optimize s).toNoun
  /-- Q (no owner: the pill half): `+inlined` is `inlinedM`. -/
  inlPill : InlPill libP D
  /-- I, J: the needs the compile reads of the callees (`env.noRing` keeps `need`). -/
  callee : ∀ long jets hot b m, InvB libP long → Tr14 long jets hot →
    Comp.CalleeNeeds (D.env long jets hot b m) (refN Ar (ref0 D) long jets hot)
  /-- K: `RingEraseU` / `RingEraseF` at the reached tables' nomms. -/
  ring : RingLeaves CSet libP D Tr14
  /-- H: `+optimize` keeps `RingSameN`. -/
  optRing : OptRing Ar

/-- **The state half of `CompHypOnR` at `refDHR`.** -/
theorem compState16 {Ar : ArmsP} {env : Env Noun} {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool}
    {fold frozen : Bool} {bf : BEnv FinMap → Nat} {D : CompData FinMap (TreapMap mugF) Noun Noun} {FM : MonoClassH}
    {FN : NaryClass} (hR : Route14 Ar env jet fold frozen bf) (hC : CompLeaves16 Ar D FM FN) :
    CompStateOnR Ar libP (refR D) I14 (Rd14 Ar) where
  unary := by
    intro st b q s n c' hrd hq hu
    rcases hrd.2 with hg | ⟨st0, s0, f0, r, hg, e1, rfl, rfl⟩
    · exact unaryDireR_of hC.direGood hC.unaryAt st b q s n c' hg hrd.1 hq hu
    · exact unaryMid16 hR hC.unaryAt hg e1 hq hu
  scc := hC.scc
  answers := hC.answers
  stable := hC.stable
  jetRoot := hC.jetRoot
  jets := hC.jets
  fast := hC.fast

/-- **The contract-side leaves at the no-ring reference.** -/
theorem contractLeaves16 {Ar : ArmsP} {D : CompData FinMap (TreapMap mugF) Noun Noun} {FM : MonoClassH}
    {FN : NaryClass} (hC : CompLeaves16 Ar D FM FN) :
    ContractLeavesOnH CSet Ar libP (ref0 D) (noRingD D) snP FM FN Tr14 where
  toRefSideMOnH := refSideMOnH_refDH hC.inFrag
  optPill := hC.optPill
  inlAnnot := fun long jets hot b nm _ hT hinl => inlAnnot_of_invK hC.inlPill long jets hot b nm hT hinl
  callee := hC.callee

/-- **`CompHypOnR` at the reached states, on the ring model.** -/
theorem compHyp16 {Ar : ArmsP} {env : Env Noun} {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool}
    {fold frozen : Bool} {bf : BEnv FinMap → Nat} {D : CompData FinMap (TreapMap mugF) Noun Noun} {FM : MonoClassH}
    {FN : NaryClass} (hR : Route14 Ar env jet fold frozen bf) (hC : CompLeaves16 Ar D FM FN)
    (hK : ClassLeavesH CSet libP FM FN) : CompHypOnR Ar libP (refR D) I14 (Rd14 Ar) :=
  compHypOnR_of (compState16 hR hC) (contractLeaves16 hC) hK hC.optRing hC.ring fun _ _ hrd => hrd.1

/-! ## THE ASSEMBLY -/

/-- **The leaves of `halting`** at `refDHR`, the bake fuel fixed to Q's `bakeFuel`. -/
structure HaltLeaves16 (Ar : ArmsP) (D : CompData FinMap (TreapMap mugF) Noun Noun) (env : Env Noun)
    (jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool) (fold frozen : Bool) : Prop where
  /-- F: the call graph's pass loop ends (`passLoop_returns_wc`, the width open). -/
  cg : CgHalts (M := FinMap) libP env regOfP
  /-- Q: the worklist of `+bake-graph` ends within `bakeFuel` (`bakeEnds_of_dropsT`, BakeHaltTie). -/
  bake : BakeEnds libP env jet fold frozen (anaFuel env regOfP) (bakeFuel (M := FinMap)) regOfP
  /-- no owner: the root bell has a whole-subject form, at reached states. -/
  root : RootAnswersOnR Ar libP (refR D) I14

/-- **`Gap` from the named leaves, over the reached states, on the ring model, the cache up to
rings.** -/
theorem gap16 (Ar : ArmsP) (D : CompData FinMap (TreapMap mugF) Noun Noun) {FM : MonoClassH} {FN : NaryClass}
    {env : Env Noun} {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool}
    (hR : Route14 Ar env jet fold frozen bakeFuel) (hP : PokeLeaves16 Ar)
    (hC : CompLeaves16 Ar D FM FN) (hK : ClassLeavesH CSet libP FM FN)
    (hH : HaltLeaves16 Ar D env jet fold frozen) (hF : FormatLeaves13) :
    Assembly.Gap libP (liftPoke (enc flagsOf) (pokeS Ar))
      (liftInv (enc flagsOf) (InvSMIR Ar libP (refR D) I14)) := by
  have hCH := compHyp16 hR hC hK
  have hRO := reachOn16 hR hP
  have hG := gap_of_armPMOnR Ar hCH hRO invStart14 hR.skaPoke flagsOf
  exact
    { pokeModel := hP.model
      contract := hG.1
      halting := halting_of_cgMPOnR Ar hCH hRO hR.skaPoke hH.cg hH.bake hH.root flagsOf
      invStart := hG.2.2
      invKept := hG.2.1
      libSlam := libP_slam
      libFormat := libP_format hF.rendRest hF.softTank hF.skipMsg
      mookFormat := libP_evalMook hF.evalMook hF.skipMsg }

/-- **`Full` from the named leaves** (`gap16`). -/
theorem full16 (Ar : ArmsP) (D : CompData FinMap (TreapMap mugF) Noun Noun) {FM : MonoClassH} {FN : NaryClass}
    {env : Env Noun} {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool}
    (hR : Route14 Ar env jet fold frozen bakeFuel) (hP : PokeLeaves16 Ar)
    (hC : CompLeaves16 Ar D FM FN) (hK : ClassLeavesH CSet libP FM FN)
    (hH : HaltLeaves16 Ar D env jet fold frozen) (hF : FormatLeaves13) : Ska.Full :=
  Assembly.full_of (gap16 Ar D hR hP hC hK hH hF)

/-- **The assembly on `gap15`'s classes** (hint-free `FragX` ∪ `PlainCalls` ∪ `PlainCallsDM`
and J's hinted class; the class leaves `ClassLeaves15`, unchanged). -/
theorem gap16_plainH (Ar : ArmsP) (D : CompData FinMap (TreapMap mugF) Noun Noun) {env : Env Noun}
    {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool}
    (hR : Route14 Ar env jet fold frozen bakeFuel) (hP : PokeLeaves16 Ar)
    (hC : CompLeaves16 Ar D (FM15 CSet libP) (FN15 CSet libP)) (hL : ClassLeaves15 CSet libP)
    (hH : HaltLeaves16 Ar D env jet fold frozen) (hF : FormatLeaves13) :
    Assembly.Gap libP (liftPoke (enc flagsOf) (pokeS Ar))
      (liftInv (enc flagsOf) (InvSMIR Ar libP (refR D) I14)) :=
  gap16 Ar D hR hP hC (classLeaves15_of hL) hH hF

/-- **The bake leaf from Q's strict drops** (`bakeEnds_of_drops`; the tie-tolerant
`bakeEnds_of_dropsT` replaces it once merged). -/
theorem bake16_of_drops {env : Env Noun} {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool}
    {fold frozen : Bool} (h : BakeDrops (M := FinMap) libP env jet fold frozen (anaFuel env regOfP) regOfP) :
    BakeEnds libP env jet fold frozen (anaFuel env regOfP) (bakeFuel (M := FinMap)) regOfP :=
  bakeEnds_of_drops h

end Glue
end SkaModel
end Formalization
