import lemmas.Assembly
import lemmas.Glue.InvMemoP
import lemmas.Glue.LibPill
import lemmas.Glue.GuardFinalTop
import lemmas.Glue.SplitDefRun
import lemmas.Glue.GuardNaryPlain
import lemmas.Compiler.PokeLinkGlue
import lemmas.Compiler.CompMonoLinkTop5

/-!
# The assembly, thirteenth pass (track G): where `Full` stands

ONE theorem, `gap13`: the whole `Assembly.Gap` (all eight fields, hence
`Full` by `full_of`: `full13`) for the route the tracks have built,

* `lib := libP` (`Glue/LibPill.lean`),
* `pk := liftPoke (enc flagsOf) (pokeS Ar)`, `InvC := liftInv (enc flagsOf) (InvSM libP ref)`,
* `Ar` the arms of track P's route (`Route13`: `anaArmP` at the analysis fuel
  `anaFuel`, `jetRootP`, `optimizeP`, `sccOfP`, `compileUnaryP flagsOf`, the four
  `env` equations, the shape of `regOf`: CHOICES, not leaves),

from five records of NAMED LEAVES, each field one open leaf with its owner:
`PokeLeaves13` (P, K, D, Q), `CompLeaves13` (A, C, I, J, K, P, Q), `ClassLeaves13`
(the model facts of a class pair `FM`, `FN`: C, J, D, G, H), `HaltLeaves13` (F, none),
`FormatLeaves13` (none).

The class pair is a parameter: `ClassLeaves13` is closed under union (`classLeaves_or`)
and is PROVED with no leaf on `FragX` (`classLeaves_fragX`), and on the plain class
with indirect calls `PlainCalls` (= `MonoCalls ∩ PlainM`, `NaryCalls ∩ PlainNC`) from
track D's `KIMid` and track H's totality on it (`classLeaves_plain`).  So
`gap13_fragX` (no class leaf; `inFragM` / `inFragN` say every compiled nomm is in
`FragX`) and `gap13_fragXPlain` (on `FragX ∪ PlainCalls`, from `KIMid` and the two
`OptTotal` leaves on `PlainCalls`).

MISFITS bridged here:
* track P's top gives `pokeModel` on `%full` only: the other pokes are the leaf
  `PokeOther13` (P), and `pokeModel_of_fullOther` puts the two together;
* track P's top takes the gate in the OLD record `UnaryGateAt`; track K's record is
  `GateRest5` / `UnaryGateAtS` (soft members), with no map to the old one:
  `monoLinkGood6_of_rest5` and `pokeModel_fullReachP6G` (P's proof with K's record,
  asked at `PGood6` states and read at `.good5`);
* track P's top takes any fuel with `FuelOK`, `halting_of_cgMP` the fuel `anaFuel`:
  `Route13` fixes `anaFuel`, `fuelOK_anaFuel` bridges.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeF SkaModel.PokeM FinMap

/-- **Leaf (P): every poke other than `%full` is the model's** on every
`CorIn` core (`%dire`, `%fast`, `%jets ~`; P's `OtherKeeps6` says only that
they keep `PGood6`). -/
def PokeOther13 (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)) : Prop :=
  ∀ cr, CorIn cr → ∀ ov : Ovum, ¬ Ska.Hot ov.toNoun → (∀ s f, ov ≠ Ovum.full s f) →
    pokeN cr ov.toNoun = (liftPoke (enc flagsOf) (pokeS Ar) cr ov).map fun r => C r.1.toNoun r.2

/-- **`PokeModel` from its `%full` part and the other pokes.** -/
theorem pokeModel_of_fullOther {Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)}
    (hF : ∀ cr, CorIn cr → ∀ s f, pokeN cr (Ovum.full s f).toNoun =
      (liftPoke (enc flagsOf) (pokeS Ar) cr (Ovum.full s f)).map fun r => C r.1.toNoun r.2)
    (hO : PokeOther13 Ar) : Assembly.PokeModel (liftPoke (enc flagsOf) (pokeS Ar)) := by
  intro cr hc ov hh
  by_cases e : ∃ s f, ov = Ovum.full s f
  · obtain ⟨s, f, rfl⟩ := e
    exact hF cr hc s f
  · exact hO cr hc ov hh fun s f h => e ⟨s, f, h⟩

/-- **The gate on `PGood6` states from track K's record `GateRest5`** (the
misfit: P's top takes the old record `UnaryGateAt`). -/
theorem monoLinkGood6_of_rest5 (fl : Flags) (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
    (Cls : Straight (TreapMap mugF) → Prop) (hA : Ar.compileUnary = compileUnaryP fl)
    (hGR : ∀ st b sc, PGood6 Cls st → ∃ (NM CA V COLE : Noun) (envK : Comp.CallEnv) (inl : Noun → Option Nomm)
      (n : Nomm) (D : Bell → Prop), GateRest5 fl st b sc NM CA V COLE envK inl n D) :
    MonoLinkGood6 fl Ar Cls := by
  intro st b sc hg
  obtain ⟨NM, CA, V, COLE, envK, inl, n, D, H⟩ := hGR st b sc hg
  obtain ⟨ht, H'⟩ := unaryGateAtS_of_good5 hg.good5 H
  exact monoLinkAt_of fl Ar hA st b sc (unaryImageAt_of_gateDS H') (monoMissAt_of fl st b sc)

/-- **`pokeModel_fullReachP6L` with track K's gate record**: P's proof of
`pokeModel_fullReachP6` with `MonoLinkGood6` from `GateRest5` at `PGood6`
states, `SpRestGood6` from P's two leaves. -/
theorem pokeModel_fullReachP6G (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
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
    (hGR : ∀ st b sc, PGood6 OptTotal st → ∃ (NM CA V COLE : Noun) (envK : Comp.CallEnv)
      (inl : Noun → Option Nomm) (n : Nomm) (D : Bell → Prop), GateRest5 flagsOf st b sc NM CA V COLE envK inl n D)
    (hJ : JetsOfGood jetsOf) (hJC : JetsOfCole6 jetsOf)
    (hU : UnaryKeeps Ar OptTotal) (hCK : UnaryCacheKeeps Ar OptTotal) (hUS : UnarySccsIs Ar)
    (hX : OtherKeeps6 flagsOf OptTotal) :
    ∀ cr, CorIn cr → ∀ s f, pokeN cr (Ovum.full s f).toNoun =
      (liftPoke (enc flagsOf) (pokeS Ar) cr (Ovum.full s f)).map fun r => C r.1.toNoun r.2 := by
  have hR := spRestGood6_of_leaves Ar OptTotal env hA hF hreg hL
  have hM := monoLinkGood6_of_rest5 flagsOf Ar OptTotal hUA hGR
  have hI : SccImage := sccImage
  have hSc : SccOfKeeps Ar := sccOfKeeps_of hSA
  have hSI : SccOfIsK Ar := sccOfIsK_of hSA
  have hTE : TarjanExists := tarjanExists
  have hK := skaKeeps_of_armP Ar hA hJ
  have hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none := fun s a L j h => by
    rw [hA]; exact anaArmP_atom env jet fold frozen fuel bf regOf jetsOf newOf s a L j h
  intro cr hc s f
  obtain ⟨st, hg, rfl⟩ := pokeReachGood6 flagsOf Ar OptTotal env hhe hth hsoft hrf lib hA hJA hR
    (sccLink_of flagsOf hSA hI) hM (optLinkOn_optimizeP hOA) hK hU hSc hCK hSI hUS hTE hJC hAt hX cr hc.2.2
  exact pokeModel_fullGood6 flagsOf Ar OptTotal env hhe hth hsoft hrf hA hJA hR (sccLink_of flagsOf hSA hI) hM
    (optLinkOn_optimizeP hOA) hK hU hSc hSI hTE hJC hAt st hg s f

/-- **What K's record gives that the assembly does not use** (the misfit of
`CompHyp.unary` / `refMono`): at a `PGood5` state, the pill's
`+compile-unary` IS the model's `finishLUCM` (at `S := CSet`) on the code
table's nomm `n` of `b` (`DirOk n`), under the record's `env`.  P's
`MonoLinkAt` reads only that the product decodes (`UnaryImageAt`);
`CompHyp.unary` and `RefSideM.refMono` ask this equality on EVERY `InvB`
table and cache, not on reachable states, so it cannot be plugged in. -/
theorem unaryFinish_of_rest5 {Cls : Straight (TreapMap mugF) → Prop} {fl : Flags} {st : PSt} {b : Bell}
    {sc : FinMap Bell Unit} {NM CA V COLE : Noun} {env : Comp.CallEnv} {inl : Noun → Option Nomm} {n : Nomm}
    {D : Bell → Prop} (hg : PGood5 Cls st) (H : GateRest5 fl st b sc NM CA V COLE env inl n D) :
    DirOk n = true ∧ ∃ CA', nock (C cuGB (C (cuSam b.toNoun (FinMap.setNoun sc) (codeNoun fl st.long.code)
        (C st.jets (callsNoun st.long)) st.hot (cacheNoun st.cache)) compK)) cuGB
      = (Comp.finishLUCM (S := CSet) (Map := TreapMap mugF) env n).map fun s => C (C s.toNoun NM) CA' := by
  obtain ⟨ht, H'⟩ := unaryGateAtS_of_good5 hg H
  obtain ⟨CA', -, -, -, -, e⟩ := cu_gate_dir_sccDS b.toNoun (FinMap.setNoun sc) (codeNoun fl st.long.code)
    st.jets (callsNoun st.long) st.hot (cacheNoun st.cache) NM CA V COLE _ (st.cache.mono.toNoun Straight.toNoun)
    env inl n ht D H'.got H'.nomm H'.cole H'.csi H'.agree H'.rest H'.dec H'.dir H'.envFrom H'.noRing H'.ana
    H'.sccsGood H'.jug H'.heights H'.table H'.callees
  exact ⟨H'.dir, CA', e⟩

end Compiler

namespace SkaModel
namespace Glue

open Nock Ana Bake PokeM Compiler Pill Hoon

/-- The arms of track P's route. -/
abbrev ArmsP : Type := Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)

/-! ## The records -/

/-- **The route** (CHOICES of the parameters, no leaf): track P's arms, at the
analysis fuel `anaFuel` (which `halting_of_cgMP` asks), the `env` of the pill,
the registrations of the jets noun. -/
structure Route13 (Ar : ArmsP) (env : Env Noun) (jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool)
    (fold frozen : Bool) (bf : BEnv FinMap → Nat) (regOf : Noun → Noun)
    (jetsOf : Noun → Noun → Noun → LongB FinMap → LongB FinMap → Noun) (newOf : Noun → Noun) : Prop where
  he : env.he = heSock
  threshold : env.threshold = 32
  softSpot : env.softSpot = softSpotF
  registerFast : env.registerFast = registerFastP
  skaPoke : Ar.skaPoke = anaArmP env jet fold frozen (anaFuel env regOf) bf regOf jetsOf newOf
  jetRoot : Ar.jetRoot = jetRootP
  optimize : Ar.optimize = optimizeP
  sccOf : Ar.sccOf = sccOfP
  compileUnary : Ar.compileUnary = compileUnaryP flagsOf
  regs : ∀ r1 r2 r3 r4 jRest, regOf (C r1 (C r2 (C r3 (C r4 jRest)))) = C r1 (C r2 (C r3 (C r4 (A 0))))

/-- **The leaves of `pokeModel`.** -/
structure PokeLeaves13 (Ar : ArmsP) (env : Env Noun) (jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool)
    (fold frozen : Bool) (bf : BEnv FinMap → Nat)
    (jetsOf : Noun → Noun → Noun → LongB FinMap → LongB FinMap → Noun) (newOf : Noun → Noun) : Prop where
  /-- P: `BakeLinkAt` (`+bake-graph`) and `TailEndAt` (the jets) at `PGood6` states. -/
  spLeaves : SpLeavesGood OptTotal env jet fold frozen bf jetsOf newOf
  /-- K (fields owed by P): the gate of `+compile-unary`, K's record, at `PGood6` states. -/
  gate : ∀ st b sc, PGood6 OptTotal st → ∃ (NM CA V COLE : Noun) (envK : Comp.CallEnv)
      (inl : Noun → Option Nomm) (n : Nomm) (D : Bell → Prop), GateRest5 flagsOf st b sc NM CA V COLE envK inl n D
  /-- P: the jets read back (`+ska-cole-update`). -/
  jetsOfGood : JetsOfGood jetsOf
  /-- P: the cole coherence of the jets read back. -/
  jetsOfCole : JetsOfCole6 jetsOf
  /-- D: `+compile-unary` keeps the optimizer's class. -/
  unaryKeeps : UnaryKeeps Ar OptTotal
  /-- K / Q: `+compile-unary` keeps the cache facts. -/
  cacheKeeps : UnaryCacheKeeps Ar OptTotal
  /-- K / Q: the SCCs `+compile-unary` leaves (K: suspect, the `SccOfIsK` form; gone in K's `P5U`). -/
  sccsIs : UnarySccsIs Ar
  /-- P: `%dire`, `%jets`, `%fast` keep `PGood6`. -/
  otherKeeps : OtherKeeps6 flagsOf OptTotal
  /-- P: `%dire`, `%jets`, `%fast` are the model's (NEW: P's top is `%full` only). -/
  other : PokeOther13 Ar

/-- **The leaves of `CompHyp` that are not facts of a class** (the four
`RefSideM` fields `refMono`, `refNary` (A, I, K: the compile read as the
model's, at `finishLUCM` / `finishLFC`), `inFragM`, `inFragN` (C, J, K: every
compiled nomm is in the class), then the rest of `CompRestM`). -/
structure CompLeaves13 (S : Type) [Comp.HoonSet S] (Ar : ArmsP) (lib : Lib) (ref : Ref FinMap (TreapMap mugF) Noun Noun)
    (D : CompData FinMap (TreapMap mugF) Noun Noun) (FM : MonoClass) (FN : NaryClass) : Prop
    extends RefSideM S Ar lib ref D FM FN where
  /-- P: the pill's `+optimize` is `Ar.optimize` on the reference code (`hpill`; P's `OptLinkOn`). -/
  optPill : ∀ long jets hot b m s, InvB lib long → ref long jets hot b m = some s →
    nock (C optBody (C s.toNoun optC)) optBody = some (Ar.optimize s).toNoun
  /-- Q (`InlPill`) + the analysis (`InvBSR`): see the misfit in the LEDGER; over EVERY `InvB` state. -/
  inlAnnot : ∀ long jets hot b nm, InvB lib long → D.inl long jets hot b = some nm →
    Annot lib (realOf long.code) (SkaModel.Fits b.less) b.fol nm
  /-- I, J: the needs the compile reads of the callees. -/
  callee : ∀ long jets hot b m, InvB lib long → Comp.CalleeNeeds (D.env long jets hot b m) (refN Ar ref long jets hot)
  /-- A, I, K: `+compile-unary` gives the reference form. -/
  unary : ∀ b scc long jets hot c s n c', Ar.compileUnary b scc long jets hot c = some ((s, n), c') →
    ref long jets hot b true = some s ∧ (CacheOK ref long jets hot c → CacheOK ref long jets hot c')
  /-- I: `+compile-scc` gives the reference forms. -/
  scc : ∀ scc long jets hot c m c', Ar.compileScc scc long jets hot c = some (m, c') →
    (∀ b s, Treap.get m b = some s → ref long jets hot b false = some s) ∧
      (CacheOK ref long jets hot c → CacheOK ref long jets hot c')
  /-- I + no owner: the compile returns (totality; `split-max`, track S). -/
  answers : ∀ st b m s, InvS lib ref st → ref st.long st.jets st.hot b m = some s →
    (compileStep Ar st b m).isSome
  /-- no owner: what is compiled holds across `+ska-poke`. -/
  stable : ∀ s f long jets hot r b m x, Ar.skaPoke s f long jets hot = some r → InvB lib long →
    ref long jets hot b m = some x → ref r.2.1 r.2.2.1 hot b m = some x
  /-- no owner: the jetted root. -/
  jetRoot : ∀ s f long jets hot r out, Ar.skaPoke s f long jets hot = some r → InvB lib long →
    Ar.jetRoot r.2.2.1 hot r.1 = some out →
    out.nargs = 1 ∧ out.need = NeedOrd.this ∧
      ContractFwd lib (refN Ar ref r.2.1 r.2.2.1 hot) s f [s] out ∧
      ContractBwd lib (refN Ar ref r.2.1 r.2.2.1 hot) s f [s] out
  /-- no owner: `%jets ~` keeps the cache. -/
  jets : ∀ st p r, ¬ HotOvum (Ovum.jets p) → Ar.jetsPoke st p = some r →
    CacheOK ref st.long st.jets st.hot st.cache → CacheOK ref st.long r.2.1 r.2.2.1 r.2.2.2
  /-- no owner: `%fast` keeps the cache. -/
  fast : ∀ st rs p r, Ar.fastPoke st rs p = some r →
    CacheOK ref st.long st.jets st.hot st.cache → CacheOK ref st.long r.1 st.hot r.2

/-- **The model facts of a class pair**: the raw contracts (C, J), `OptIn`
(D), the entry (G, D), the totality of the pill's `+optimize` (H). -/
structure ClassLeaves13 (S : Type) [Comp.HoonSet S] (lib : Lib) (FM : MonoClass) (FN : NaryClass) : Prop where
  rawMono : RawMonoD S (TreapMap mugF) lib FM
  rawNary : RawNaryD S (TreapMap mugF) lib FN
  optInMono : OptInMono S (TreapMap mugF) FM
  optInNary : OptInNary S (TreapMap mugF) FN
  entryMono : EntryMono S (TreapMap mugF) lib FM
  entryNary : EntryNary S (TreapMap mugF) lib FN
  totalMono : OptTotalMono S FM
  totalNary : OptTotalNary S FN

/-- **The leaves of `halting`.** -/
structure HaltLeaves13 (Ar : ArmsP) (ref : Ref FinMap (TreapMap mugF) Noun Noun) (env : Env Noun)
    (jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool) (fold frozen : Bool) (bf : BEnv FinMap → Nat)
    (regOf : Noun → Noun) : Prop where
  /-- F: the call graph's pass loop ends. -/
  cg : CgHalts (M := FinMap) libP env regOf
  /-- no owner: the worklist of `+bake-graph` ends within `bf`. -/
  bake : BakeEnds libP env jet fold frozen (anaFuel env regOf) bf regOf
  /-- no owner: the root bell has a whole-subject form. -/
  root : RootAnswers libP Ar ref

/-- **The leaves of `libFormat` and `mookFormat`** (no owner; facts of the pill alone). -/
structure FormatLeaves13 : Prop where
  rendRest : RendRestTonFree
  softTank : SoftTankUnit
  skipMsg : SkipMsgTonFree
  evalMook : EvalMookSame

/-! ## `CompHyp` from the records -/

variable {S : Type} [Comp.HoonSet S]

/-- **`CompHyp` from the non-class leaves and the model facts of the class.** -/
theorem compHyp13 {Ar : ArmsP} {lib : Lib} {ref : Ref FinMap (TreapMap mugF) Noun Noun}
    {D : CompData FinMap (TreapMap mugF) Noun Noun} {FM : MonoClass} {FN : NaryClass}
    (P : CompLeaves13 S Ar lib ref D FM FN) (K : ClassLeaves13 S lib FM FN) : CompHyp Ar lib ref :=
  compHyp_of_piecesM (M' := FinMap) Ar
    { toCompRestM :=
        { toRefSideM := P.toRefSideM
          rawEntry := rawEntry_of Ar P.toRefSideM K.entryMono K.entryNary
          optRef := optRef_of_total P.toRefSideM K.totalMono K.totalNary P.optPill
          inlAnnot := P.inlAnnot
          callee := P.callee
          unary := P.unary
          scc := P.scc
          answers := P.answers
          stable := P.stable
          jetRoot := P.jetRoot
          jets := P.jets
          fast := P.fast }
      rawOptIn := rawOptIn_of Ar P.toRefSideM K.optInMono K.optInNary
      rawMono := K.rawMono
      rawNary := K.rawNary }

/-! ## THE ASSEMBLY -/

/-- **`Gap` from the named leaves** on track P's route, for any class pair
whose model facts hold. -/
theorem gap13 (Ar : ArmsP) (ref : Ref FinMap (TreapMap mugF) Noun Noun) (D : CompData FinMap (TreapMap mugF) Noun Noun)
    {FM : MonoClass} {FN : NaryClass} {env : Env Noun}
    {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool} {bf : BEnv FinMap → Nat}
    {regOf : Noun → Noun} {jetsOf : Noun → Noun → Noun → LongB FinMap → LongB FinMap → Noun} {newOf : Noun → Noun}
    (hR : Route13 Ar env jet fold frozen bf regOf jetsOf newOf)
    (hP : PokeLeaves13 Ar env jet fold frozen bf jetsOf newOf)
    (hC : CompLeaves13 S Ar libP ref D FM FN) (hK : ClassLeaves13 S libP FM FN)
    (hH : HaltLeaves13 Ar ref env jet fold frozen bf regOf) (hF : FormatLeaves13) :
    Assembly.Gap libP (liftPoke (enc flagsOf) (pokeS Ar)) (liftInv (enc flagsOf) (InvSM libP ref)) := by
  have hCH : CompHyp Ar libP ref := compHyp13 hC hK
  have hG := gap_of_armPM Ar hCH hR.skaPoke flagsOf
  exact
    { pokeModel := pokeModel_of_fullOther
        (pokeModel_fullReachP6G Ar env hR.he hR.threshold hR.softSpot hR.registerFast libP hR.skaPoke hR.jetRoot
          hR.optimize hR.sccOf hR.compileUnary (fuelOK_anaFuel env regOf) hR.regs hP.spLeaves hP.gate
          hP.jetsOfGood hP.jetsOfCole hP.unaryKeeps hP.cacheKeeps hP.sccsIs hP.otherKeeps) hP.other
      contract := hG.1
      halting := halting_of_cgMP Ar hCH hR.skaPoke hH.cg hH.bake hH.root flagsOf
      invStart := hG.2.2
      invKept := hG.2.1
      libSlam := libP_slam
      libFormat := libP_format hF.rendRest hF.softTank hF.skipMsg
      mookFormat := libP_evalMook hF.evalMook hF.skipMsg }

/-- **`Full` from the named leaves.** -/
theorem full13 (Ar : ArmsP) (ref : Ref FinMap (TreapMap mugF) Noun Noun) (D : CompData FinMap (TreapMap mugF) Noun Noun)
    {FM : MonoClass} {FN : NaryClass} {env : Env Noun}
    {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool} {bf : BEnv FinMap → Nat}
    {regOf : Noun → Noun} {jetsOf : Noun → Noun → Noun → LongB FinMap → LongB FinMap → Noun} {newOf : Noun → Noun}
    (hR : Route13 Ar env jet fold frozen bf regOf jetsOf newOf)
    (hP : PokeLeaves13 Ar env jet fold frozen bf jetsOf newOf)
    (hC : CompLeaves13 S Ar libP ref D FM FN) (hK : ClassLeaves13 S libP FM FN)
    (hH : HaltLeaves13 Ar ref env jet fold frozen bf regOf) (hF : FormatLeaves13) : Ska.Full :=
  Assembly.full_of (gap13 Ar ref D hR hP hC hK hH hF)

/-! ## The classes -/

/-- The intersection of two classes. -/
def andM (F G : MonoClass) : MonoClass := fun env N bl nm => F env N bl nm ∧ G env N bl nm

/-- The intersection of two n-ary classes. -/
def andN (F G : NaryClass) : NaryClass := fun env N bl cape bake nm => F env N bl cape bake nm ∧ G env N bl cape bake nm

/-- **The model facts are closed under union.** -/
theorem classLeaves_or {lib : Lib} {FM GM : MonoClass} {FN GN : NaryClass} (h : ClassLeaves13 S lib FM FN)
    (g : ClassLeaves13 S lib GM GN) : ClassLeaves13 S lib (orM FM GM) (orN FN GN) where
  rawMono := by
    intro code bl nm env s N hok hA hf hc hs
    rcases hf with hf | hf
    · exact h.rawMono code bl nm env s N hok hA hf hc hs
    · exact g.rawMono code bl nm env s N hok hA hf hc hs
  rawNary := by
    intro code bl nm env ord cape data bake s N hok hA hbl hn hf hc hs
    rcases hf with hf | hf
    · exact h.rawNary code bl nm env ord cape data bake s N hok hA hbl hn hf hc hs
    · exact g.rawNary code bl nm env ord cape data bake s N hok hA hbl hn hf hc hs
  optInMono := by
    intro env N bl nm s hf hs
    rcases hf with hf | hf
    · exact h.optInMono env N bl nm s hf hs
    · exact g.optInMono env N bl nm s hf hs
  optInNary := by
    intro env N bl cape bake nm ord s hf hs
    rcases hf with hf | hf
    · exact h.optInNary env N bl cape bake nm ord s hf hs
    · exact g.optInNary env N bl cape bake nm ord s hf hs
  entryMono := by
    intro env N bl nm s hf hs
    rcases hf with hf | hf
    · exact h.entryMono env N bl nm s hf hs
    · exact g.entryMono env N bl nm s hf hs
  entryNary := by
    intro env N bl cape bake nm ord s hf hs
    rcases hf with hf | hf
    · exact h.entryNary env N bl cape bake nm ord s hf hs
    · exact g.entryNary env N bl cape bake nm ord s hf hs
  totalMono := by
    intro env N bl nm c hf hs
    rcases hf with hf | hf
    · exact h.totalMono env N bl nm c hf hs
    · exact g.totalMono env N bl nm c hf hs
  totalNary := by
    intro env N bl cape bake nm ord c hf hs
    rcases hf with hf | hf
    · exact h.totalNary env N bl cape bake nm ord c hf hs
    · exact g.totalNary env N bl cape bake nm ord c hf hs

/-- **On `FragX`: every model fact is a theorem** (C, J's raw contracts on
`FragX`, D's `OptIn`, G's entry, H's totality). -/
theorem classLeaves_fragX (lib : Lib) : ClassLeaves13 S lib (liftMC (FragXM S)) (liftNC (FragXN S)) where
  rawMono := rawMonoD_of_M (rawMonoM_fragX lib)
  rawNary := rawNaryD_of (rawNary_fragX lib)
  optInMono := optInMono_fragX
  optInNary := optInNary_fragX
  entryMono := entryMono_fragX lib guardMonoX
  entryNary := entryNary_fragX lib guardNaryX
  totalMono := optTotalMono_fragX
  totalNary := optTotalNary_fragX

/-- **The plain class with calls**: the classes with a raw contract
(`MonoCalls`, `NaryCalls`) met with track D's `PlainM` / `PlainNC` (indirect
calls, no `%6`, no direct call, no hint; nothing baked). -/
def PlainCallsM (S : Type) [Comp.HoonSet S] (lib : Lib) : MonoClass := andM (MonoCalls S lib) PlainM

/-- The n-ary half. -/
def PlainCallsN (S : Type) [Comp.HoonSet S] (lib : Lib) : NaryClass := andN (NaryCalls S lib) PlainNC

/-- **On `PlainCalls`: the model facts from D's `KIMid` and H's totality.** -/
theorem classLeaves_plain (lib : Lib) (hD : ∀ env, KIMid S (TreapMap mugF) env)
    (hTM : OptTotalMono S (PlainCallsM S lib)) (hTN : OptTotalNary S (PlainCallsN S lib)) :
    ClassLeaves13 S lib (PlainCallsM S lib) (PlainCallsN S lib) where
  rawMono := fun code bl nm env s N hok hA hf hc hs =>
    rawMonoD_calls lib code bl nm env s N hok hA hf.1 hc hs
  rawNary := fun code bl nm env ord cape data bake s N hok hA hbl hn hf hc hs =>
    rawNaryD_calls lib code bl nm env ord cape data bake s N hok hA hbl hn hf.1 hc hs
  optInMono := fun env N bl nm s hf hs => optInMono_plain env N bl nm s hf.2 hs
  optInNary := fun env N bl cape bake nm ord s hf hs => optInNary_plain env N bl cape bake nm ord s hf.2 hs
  entryMono := fun env N bl nm s hf hs => entryMono_plainK lib hD env N bl nm s hf.2 hs
  entryNary := fun env N bl cape bake nm ord s hf hs => entryNary_plain lib hD env N bl cape bake nm ord s hf.2 hs
  totalMono := hTM
  totalNary := hTN

/-- **The assembly on `FragX`**: no class leaf; `CompLeaves13` on `FragX`. -/
theorem gap13_fragX (Ar : ArmsP) (ref : Ref FinMap (TreapMap mugF) Noun Noun)
    (D : CompData FinMap (TreapMap mugF) Noun Noun) {env : Env Noun}
    {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool} {bf : BEnv FinMap → Nat}
    {regOf : Noun → Noun} {jetsOf : Noun → Noun → Noun → LongB FinMap → LongB FinMap → Noun} {newOf : Noun → Noun}
    (hR : Route13 Ar env jet fold frozen bf regOf jetsOf newOf)
    (hP : PokeLeaves13 Ar env jet fold frozen bf jetsOf newOf)
    (hC : CompLeaves13 S Ar libP ref D (liftMC (FragXM S)) (liftNC (FragXN S)))
    (hH : HaltLeaves13 Ar ref env jet fold frozen bf regOf) (hF : FormatLeaves13) :
    Assembly.Gap libP (liftPoke (enc flagsOf) (pokeS Ar)) (liftInv (enc flagsOf) (InvSM libP ref)) :=
  gap13 Ar ref D hR hP hC (classLeaves_fragX libP) hH hF

/-- **The assembly on `FragX ∪ PlainCalls`**: the class leaves are D's
`KIMid` and H's totality on `PlainCalls`. -/
theorem gap13_fragXPlain (Ar : ArmsP) (ref : Ref FinMap (TreapMap mugF) Noun Noun)
    (D : CompData FinMap (TreapMap mugF) Noun Noun) {env : Env Noun}
    {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool} {bf : BEnv FinMap → Nat}
    {regOf : Noun → Noun} {jetsOf : Noun → Noun → Noun → LongB FinMap → LongB FinMap → Noun} {newOf : Noun → Noun}
    (hR : Route13 Ar env jet fold frozen bf regOf jetsOf newOf)
    (hP : PokeLeaves13 Ar env jet fold frozen bf jetsOf newOf)
    (hC : CompLeaves13 S Ar libP ref D (orM (liftMC (FragXM S)) (PlainCallsM S libP))
      (orN (liftNC (FragXN S)) (PlainCallsN S libP)))
    (hD : ∀ env, KIMid S (TreapMap mugF) env)
    (hTM : OptTotalMono S (PlainCallsM S libP)) (hTN : OptTotalNary S (PlainCallsN S libP))
    (hH : HaltLeaves13 Ar ref env jet fold frozen bf regOf) (hF : FormatLeaves13) :
    Assembly.Gap libP (liftPoke (enc flagsOf) (pokeS Ar)) (liftInv (enc flagsOf) (InvSM libP ref)) :=
  gap13 Ar ref D hR hP hC (classLeaves_or (classLeaves_fragX libP) (classLeaves_plain libP hD hTM hTN)) hH hF

end Glue
end SkaModel
end Formalization
