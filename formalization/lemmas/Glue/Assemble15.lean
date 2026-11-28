import lemmas.Glue.Assemble14
import lemmas.Glue.RefSideH
import lemmas.Glue.PlainX
import lemmas.Ska.RawInvCLCallDM
import lemmas.Compiler.CompRunHintEx

/-!
# The assembly, fifteenth pass (track G): no false leaf, hinted code in the class

ONE theorem, `gap15`: all eight fields of `Assembly.Gap` (hence `Full`, `full15`) for

* `lib := libP`, `pk := liftPoke (enc flagsOf) (pokeS Ar)` (as `gap14`),
* the reference compiler `refDH CSet D snP`: the MODEL WITH HINTS (`finishLUCH` of the
  table's nomm under the table's `+sound`, `snP long := sfSnd (codeNoun flagsOf long.code)`;
  `refD`'s n-ary half),
* `InvC := liftInv (enc flagsOf) (InvSMI libP (refDH CSet D snP) I14)` (the reached states of
  `gap14`),

from `Route14`, `PokeLeaves14` (as `gap14`), `CompLeaves15` (`CompLeaves14` at `refDH`),
`ClassLeavesH` (the class facts with the mono fields at `finishLUCH`), `HaltLeaves15`,
`FormatLeaves13`.

* `unary` on the `%full` path: K's record (`unaryOut_of_gate`, at `finishLUCM`) and
  `UnaryEnvIs14`, carried to `finishLUCH` by `dirOk_noHint` (K's record asks `DirOk` of the key:
  no hint) and `finishLUCH_eq`.
* **`gap15_plainH`**: the class `FM15` = (`FragX` ∪ `PlainCalls` ∪ `PlainCallsDM`, hint-free)
  ∪ J's `HintClsB` (hinted nomms, `hcV`); the n-ary class `FN15` = `FragXN` ∪ `PlainCallsN`.
  Its class leaves are the record `ClassLeaves15`: H's totality on `PlainCalls` and
  `PlainCallsDM`, D's `KdmMonoSpec`, the guard `GuardMonoC` on `NoSixM` (from `StraightA`, or
  from `KeyUndefC` + `SDWEndC`), and `HintLeaves` (the three model facts of J's class).  NO
  `KIMid` (misfit 8 gone: `classLeaves_plainX` uses `entryMono_plainKX`, `entryNary_plainX`,
  which have no hypothesis).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Ana Bake PokeM Compiler Pill Hoon AnnotSF

/-! ## The table's `+sound`; K's class has no hint -/

/-- **The table's `+sound`** (Q's model `sfSnd` of the code noun). -/
noncomputable def snP (long : LongB FinMap) : SndT := sfSnd (codeNoun flagsOf long.code)

/-- **K's class `DirOk` has no hint.** -/
theorem dirOk_noHint (n : Nomm) (h : DirOk n = true) : n.noHint = true := by
  induction n with
  | n2 p q info ihp ihq =>
    have : DirOk p = true ∧ DirOk q = true := by
      rcases info with _ | ⟨b, _ | k⟩ <;> simp_all [DirOk]
    simp [Nomm.noHint, ihp this.1, ihq this.2]
  | _ => simp_all [DirOk, Nomm.noHint]

/-! ## `+compile-unary` at `refDH` -/

/-- **`unary` on the `%full` path from K's record, at the model with hints.** -/
theorem unaryMid15 {Ar : ArmsP} {env : Env Noun} {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool}
    {fold frozen : Bool} {bf : BEnv FinMap → Nat} {D : CompData FinMap (TreapMap mugF) Noun Noun}
    (hR : Route14 Ar env jet fold frozen bf) (hP : PokeLeaves14 Ar env jet fold frozen bf)
    (hE : UnaryEnvIs14 D) (hCa : UnaryCacheOK14 Ar (refDH CSet D snP)) {st0 : PSt} {s f : Noun}
    {r : Bell × LongB FinMap × Noun × Noun} (hg : PGood6 OptTotal st0)
    (e1 : Ar.skaPoke s f st0.long st0.jets st0.hot = some r) {q : FinMap Bell Unit × FinMap Bell (FinMap Bell Unit)}
    (e3 : Ar.sccOf r.1 r.2.1 st0.cache.sccs = some q) {s' : Straight (TreapMap mugF)}
    {n : FinMap Bell (Straight (TreapMap mugF))} {c' : Cache FinMap (TreapMap mugF) (Noun × Noun)}
    (hu : Ar.compileUnary r.1 q.1 r.2.1 r.2.2.1 st0.hot { st0.cache with sccs := q.2 } = some ((s', n), c')) :
    refDH CSet D snP r.2.1 r.2.2.1 st0.hot r.1 true = some s' ∧
      (CacheOK (refDH CSet D snP) r.2.1 r.2.2.1 st0.hot st0.cache →
        CacheOK (refDH CSet D snP) r.2.1 r.2.2.1 st0.hot c') := by
  have hK := skaKeeps_of_armP Ar hR.skaPoke jetsOfGood_P
  obtain ⟨⟨eb, heb⟩, hq⟩ := mid_key hR.skaPoke hR.sccOf st0 s f hg.good5 r e1 q e3
  have hm := good6_mid hR.skaPoke hK (sccOfKeeps_of hR.sccOf) (sccOfIsK_of hR.sccOf) tarjanExists jetsOfCole6_P
    st0 s f hg r e1 q e3
  rw [hq] at hu
  obtain ⟨COLE, NM, CA, need, sure, sof, inl, D', hcole, H, hs⟩ := unaryOut_of_gate hR.compileUnary hP.gate hm heb hu
  have h1 := hE _ _ _ _ _ _ _ _ _ _ _ _ hm heb hcole H hs
  refine ⟨?_, hCa _ r.1 eb _ hm heb hu⟩
  have heb' : Treap.get r.2.1.code r.1 = some eb := heb
  simp only [refDH, if_true, realOf, heb', Option.map_some, Option.bind_some]
  rw [Comp.finishLUCH_eq _ _ (dirOk_noHint _ H.dir)]
  exact h1

/-! ## `+compile-unary` on the `%dire` path (misfit 4) -/

/-- **Leaf (P): `%dire` at a `PGood6` state.**  When `+scc-of` returns `q` and
`+compile-unary` returns on it, the bell is a key of the code table, `q.1` is its SCC, and the
state with the new `sccs` is `PGood6` (the `%dire` analogue of `mid_key` and `good6_mid`). -/
def DireGood6 (Ar : ArmsP) : Prop :=
  ∀ (st : PSt) b q r, PGood6 OptTotal st → InvK libP st.long → Ar.sccOf b st.long st.cache.sccs = some q →
    Ar.compileUnary b q.1 st.long st.jets st.hot { st.cache with sccs := q.2 } = some r →
    (∃ e, FinMap.get st.long.code b = some e) ∧ q.1 = sccSet st.long.code b ∧
      PGood6 OptTotal { st with cache := { st.cache with sccs := q.2 } }

/-- **The field `unaryDire` from P's `DireGood6`** and the two leaves of the `%full` path
(`UnaryEnvIs14`, `UnaryCacheOK14`): the proof of `unaryMid15`. -/
theorem unaryDire_of {Ar : ArmsP} {D : CompData FinMap (TreapMap mugF) Noun Noun}
    (hUA : Ar.compileUnary = compileUnaryP flagsOf) (hGR : GateRest6All flagsOf OptTotal) (hDG : DireGood6 Ar)
    (hE : UnaryEnvIs14 D) (hCa : UnaryCacheOK14 Ar (refDH CSet D snP)) :
    ∀ (st : PSt) b q s n c', PGood6 OptTotal st → InvK libP st.long →
      Ar.sccOf b st.long st.cache.sccs = some q →
      Ar.compileUnary b q.1 st.long st.jets st.hot { st.cache with sccs := q.2 } = some ((s, n), c') →
      refDH CSet D snP st.long st.jets st.hot b true = some s ∧
        (CacheOK (refDH CSet D snP) st.long st.jets st.hot st.cache →
          CacheOK (refDH CSet D snP) st.long st.jets st.hot c') := by
  intro st b q s n c' hg hk hq hu
  obtain ⟨⟨eb, heb⟩, hq1, hm⟩ := hDG st b q _ hg hk hq hu
  have hu' : Ar.compileUnary b (sccSet st.long.code b) st.long st.jets st.hot { st.cache with sccs := q.2 } =
      some ((s, n), c') := by rw [← hq1]; exact hu
  obtain ⟨COLE, NM, CA, need, sure, sof, inl, D', hcole, H, hs⟩ := unaryOut_of_gate hUA hGR hm heb hu'
  have h1 := hE _ _ _ _ _ _ _ _ _ _ _ _ hm heb hcole H hs
  refine ⟨?_, hCa _ b eb _ hm heb hu'⟩
  have heb' : Treap.get st.long.code b = some eb := heb
  simp only [refDH, if_true, realOf, heb', Option.map_some, Option.bind_some]
  rw [Comp.finishLUCH_eq _ _ (dirOk_noHint _ H.dir)]
  exact h1

/-! ## The leaves of `CompHypOn` at `refDH` -/

/-- **`CompLeaves14` at the model with hints** (`refDH CSet D snP` in place of `refD CSet D`;
`inFrag` at `InFragOnH`, the class family `FM` indexed by `+sound`).  Owners as in
`CompLeaves14`. -/
structure CompLeaves15 (Ar : ArmsP) (D : CompData FinMap (TreapMap mugF) Noun Noun) (FM : MonoClassH) (FN : NaryClass) :
    Prop where
  /-- K, I: the record's `env` is `D.env` for `finishLUCM`. -/
  unaryEnv : UnaryEnvIs14 D
  /-- I, K: the cache `+compile-unary` returns holds reference forms. -/
  unaryCache : UnaryCacheOK14 Ar (refDH CSet D snP)
  /-- K, P: `+compile-unary` on the `%dire` path (at a `PGood6` state, any bell). -/
  unaryDire : ∀ (st : PSt) b q s n c', PGood6 OptTotal st → InvK libP st.long →
    Ar.sccOf b st.long st.cache.sccs = some q →
    Ar.compileUnary b q.1 st.long st.jets st.hot { st.cache with sccs := q.2 } = some ((s, n), c') →
    refDH CSet D snP st.long st.jets st.hot b true = some s ∧
      (CacheOK (refDH CSet D snP) st.long st.jets st.hot st.cache →
        CacheOK (refDH CSet D snP) st.long st.jets st.hot c')
  /-- I: `+compile-scc` on the `%dire` path. -/
  scc : ∀ (st : PSt) b q m c', I14 st → Ar.sccOf b st.long st.cache.sccs = some q →
    Ar.compileScc q.1 st.long st.jets st.hot { st.cache with sccs := q.2 } = some (m, c') →
    (∀ b' s, Treap.get m b' = some s → refDH CSet D snP st.long st.jets st.hot b' false = some s) ∧
      (CacheOK (refDH CSet D snP) st.long st.jets st.hot st.cache →
        CacheOK (refDH CSet D snP) st.long st.jets st.hot c')
  /-- I + no owner: the compile returns where it runs (`split-max`, S). -/
  answers : ∀ (st : PSt) b m s, Rd14 Ar st b → InvS libP (refDH CSet D snP) st →
    refDH CSet D snP st.long st.jets st.hot b m = some s → (compileStep Ar st b m).isSome
  /-- no owner: what is compiled holds across `+ska-poke`, at reached states. -/
  stable : ∀ (st : PSt) s f r b m x, I14 st → Ar.skaPoke s f st.long st.jets st.hot = some r →
    InvB libP st.long → refDH CSet D snP st.long st.jets st.hot b m = some x →
      refDH CSet D snP r.2.1 r.2.2.1 st.hot b m = some x
  /-- no owner: the jetted root, at reached states. -/
  jetRoot : ∀ (st : PSt) s f r out, I14 st → Ar.skaPoke s f st.long st.jets st.hot = some r →
    InvB libP st.long → Ar.jetRoot r.2.2.1 st.hot r.1 = some out →
    out.nargs = 1 ∧ out.need = NeedOrd.this ∧
      ContractFwd libP (refN Ar (refDH CSet D snP) r.2.1 r.2.2.1 st.hot) s f [s] out ∧
      ContractBwd libP (refN Ar (refDH CSet D snP) r.2.1 r.2.2.1 st.hot) s f [s] out
  /-- no owner: `%jets ~` keeps the cache, at reached states. -/
  jets : ∀ st p r, I14 st → ¬ HotOvum (Ovum.jets p) → Ar.jetsPoke st p = some r →
    CacheOK (refDH CSet D snP) st.long st.jets st.hot st.cache →
      CacheOK (refDH CSet D snP) st.long r.2.1 r.2.2.1 r.2.2.2
  /-- no owner: `%fast` keeps the cache, at reached states. -/
  fast : ∀ st rs p r, I14 st → Ar.fastPoke st rs p = some r →
    CacheOK (refDH CSet D snP) st.long st.jets st.hot st.cache → CacheOK (refDH CSet D snP) st.long r.1 st.hot r.2
  /-- C, J, K, A: every compiled nomm of a reached table is in the class (at the table's `+sound`). -/
  inFrag : InFragOnH CSet Ar libP D snP FM FN Tr14
  /-- P: the pill's `+optimize` on the reference forms of reached tables. -/
  optPill : ∀ long jets hot b m s, InvB libP long → Tr14 long jets hot → refDH CSet D snP long jets hot b m = some s →
    nock (C optBody (C s.toNoun optC)) optBody = some (Ar.optimize s).toNoun
  /-- Q (no owner: the pill half): `+inlined` is `inlinedM`. -/
  inlPill : InlPill libP D
  /-- I, J: the needs the compile reads of the callees, at reached tables. -/
  callee : ∀ long jets hot b m, InvB libP long → Tr14 long jets hot →
    Comp.CalleeNeeds (D.env long jets hot b m) (refN Ar (refDH CSet D snP) long jets hot)

/-- **The state half of `CompHypOn` at `refDH`.** -/
theorem compState15 {Ar : ArmsP} {env : Env Noun} {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool}
    {fold frozen : Bool} {bf : BEnv FinMap → Nat} {D : CompData FinMap (TreapMap mugF) Noun Noun} {FM : MonoClassH}
    {FN : NaryClass} (hR : Route14 Ar env jet fold frozen bf) (hP : PokeLeaves14 Ar env jet fold frozen bf)
    (hC : CompLeaves15 Ar D FM FN) : CompStateOn Ar libP (refDH CSet D snP) I14 (Rd14 Ar) where
  unary := by
    intro st b q s n c' hrd hq hu
    rcases hrd.2 with hg | ⟨st0, s0, f0, r, hg, e1, rfl, rfl⟩
    · exact hC.unaryDire st b q s n c' hg hrd.1 hq hu
    · exact unaryMid15 hR hP hC.unaryEnv hC.unaryCache hg e1 hq hu
  scc := hC.scc
  answers := hC.answers
  stable := hC.stable
  jetRoot := hC.jetRoot
  jets := hC.jets
  fast := hC.fast

/-- **The contract-side leaves at `refDH`**: `inlAnnot` from Q's `inlAnnot_of_invK`. -/
theorem contractLeaves15 {Ar : ArmsP} {D : CompData FinMap (TreapMap mugF) Noun Noun} {FM : MonoClassH}
    {FN : NaryClass} (hC : CompLeaves15 Ar D FM FN) :
    ContractLeavesOnH CSet Ar libP (refDH CSet D snP) D snP FM FN Tr14 where
  toRefSideMOnH := refSideMOnH_refDH hC.inFrag
  optPill := hC.optPill
  inlAnnot := fun long jets hot b nm _ hT hinl => inlAnnot_of_invK hC.inlPill long jets hot b nm hT hinl
  callee := hC.callee

/-- **`CompHypOn` at the reached states, at the model with hints.** -/
theorem compHyp15 {Ar : ArmsP} {env : Env Noun} {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool}
    {fold frozen : Bool} {bf : BEnv FinMap → Nat} {D : CompData FinMap (TreapMap mugF) Noun Noun} {FM : MonoClassH}
    {FN : NaryClass} (hR : Route14 Ar env jet fold frozen bf) (hP : PokeLeaves14 Ar env jet fold frozen bf)
    (hC : CompLeaves15 Ar D FM FN) (hK : ClassLeavesH CSet libP FM FN) :
    CompHypOn Ar libP (refDH CSet D snP) I14 (Rd14 Ar) :=
  compHypOnH_of (compState15 hR hP hC) (contractLeaves15 hC) hK fun _ _ hrd => hrd.1

/-! ## THE ASSEMBLY -/

/-- **The leaves of `halting`** at `refDH`. -/
structure HaltLeaves15 (Ar : ArmsP) (D : CompData FinMap (TreapMap mugF) Noun Noun) (env : Env Noun)
    (jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool) (fold frozen : Bool) (bf : BEnv FinMap → Nat) :
    Prop where
  /-- F: the call graph's pass loop ends. -/
  cg : CgHalts (M := FinMap) libP env regOfP
  /-- Q (H2): the worklist of `+bake-graph` ends within `bf`. -/
  bake : BakeEnds libP env jet fold frozen (anaFuel env regOfP) bf regOfP
  /-- no owner: the root bell has a whole-subject form, at reached states. -/
  root : RootAnswersOn libP Ar (refDH CSet D snP) I14

/-- **`Gap` from the named leaves, over the reached states, the model with hints as the
reference.** -/
theorem gap15 (Ar : ArmsP) (D : CompData FinMap (TreapMap mugF) Noun Noun) {FM : MonoClassH} {FN : NaryClass}
    {env : Env Noun} {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool}
    {bf : BEnv FinMap → Nat}
    (hR : Route14 Ar env jet fold frozen bf) (hP : PokeLeaves14 Ar env jet fold frozen bf)
    (hC : CompLeaves15 Ar D FM FN) (hK : ClassLeavesH CSet libP FM FN)
    (hH : HaltLeaves15 Ar D env jet fold frozen bf) (hF : FormatLeaves13) :
    Assembly.Gap libP (liftPoke (enc flagsOf) (pokeS Ar))
      (liftInv (enc flagsOf) (InvSMI libP (refDH CSet D snP) I14)) := by
  have hCH := compHyp15 hR hP hC hK
  have hRO := reachOn14 hR hP
  have hG := gap_of_armPMOn Ar hCH hRO invStart14 hR.skaPoke flagsOf
  exact
    { pokeModel := pokeModel14 hR hP
      contract := hG.1
      halting := halting_of_cgMPOn Ar hCH hRO hR.skaPoke hH.cg hH.bake hH.root flagsOf
      invStart := hG.2.2
      invKept := hG.2.1
      libSlam := libP_slam
      libFormat := libP_format hF.rendRest hF.softTank hF.skipMsg
      mookFormat := libP_evalMook hF.evalMook hF.skipMsg }

/-- **`Full` from the named leaves** (`gap15`). -/
theorem full15 (Ar : ArmsP) (D : CompData FinMap (TreapMap mugF) Noun Noun) {FM : MonoClassH} {FN : NaryClass}
    {env : Env Noun} {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool}
    {bf : BEnv FinMap → Nat}
    (hR : Route14 Ar env jet fold frozen bf) (hP : PokeLeaves14 Ar env jet fold frozen bf)
    (hC : CompLeaves15 Ar D FM FN) (hK : ClassLeavesH CSet libP FM FN)
    (hH : HaltLeaves15 Ar D env jet fold frozen bf) (hF : FormatLeaves13) : Ska.Full :=
  Assembly.full_of (gap15 Ar D hR hP hC hK hH hF)

/-! ## The classes: no `KIMid`, direct calls, hints -/

variable {S : Type} [Comp.HoonSet S]

/-- **On `PlainCalls`: the model facts from H's totality alone** (`classLeaves_plain` with
`entryMono_plainKX`, `entryNary_plainX`: no `KIMid`). -/
theorem classLeaves_plainX (lib : Lib) (hTM : OptTotalMono S (PlainCallsM S lib))
    (hTN : OptTotalNary S (PlainCallsN S lib)) :
    ClassLeaves13 S lib (PlainCallsM S lib) (PlainCallsN S lib) where
  rawMono := fun code bl nm env s N hok hA hf hc hs =>
    rawMonoD_calls lib code bl nm env s N hok hA hf.1 hc hs
  rawNary := fun code bl nm env ord cape data bake s N hok hA hbl hn hf hc hs =>
    rawNaryD_calls lib code bl nm env ord cape data bake s N hok hA hbl hn hf.1 hc hs
  optInMono := fun env N bl nm s hf hs => optInMono_plain env N bl nm s hf.2 hs
  optInNary := fun env N bl cape bake nm ord s hf hs => optInNary_plain env N bl cape bake nm ord s hf.2 hs
  entryMono := fun env N bl nm s hf hs => entryMono_plainKX lib env N bl nm s hf.2 hs
  entryNary := fun env N bl cape bake nm ord s hf hs => entryNary_plainX lib env N bl cape bake nm ord s hf.2 hs
  totalMono := hTM
  totalNary := hTN

/-- **The class with direct calls**: `MonoCalls` met with track D's `PlainDM` (direct and
indirect calls, no `%6`, no hint). -/
def PlainCallsDM (S : Type) [Comp.HoonSet S] (lib : Lib) : MonoClass := andM (MonoCalls S lib) PlainDM

/-- **On `PlainCallsDM`: the model facts from D's `KdmMonoSpec`, the guard on `NoSixM` and H's
totality** (the n-ary side empty: D's n-ary leaves with direct calls are not started). -/
theorem classLeaves_plainDM (lib : Lib) (hM : Raw.KdmMonoSpec S (TreapMap mugF))
    (hG : GuardMonoC S (TreapMap mugF) NoSixM) (hTM : OptTotalMono S (PlainCallsDM S lib)) :
    ClassLeaves13 S lib (PlainCallsDM S lib) NoNary where
  rawMono := fun code bl nm env s N hok hA hf hc hs =>
    rawMonoD_calls lib code bl nm env s N hok hA hf.1 hc hs
  rawNary := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hf => hf.elim
  optInMono := fun env N bl nm s hf hs => optInMono_plainD_of hM env N bl nm s hf.2 hs
  optInNary := fun _ _ _ _ _ _ _ _ hf => hf.elim
  entryMono := fun env N bl nm s hf hs =>
    entryMono_of lib (optInMono_plainD_of hM) (readsInMono_plainD_of hM)
      (guardMonoC_sub hG fun _ _ _ nm h => noSix_of_plainD nm h) env N bl nm s hf.2 hs
  entryNary := fun _ _ _ _ _ _ _ _ hf => hf.elim
  totalMono := hTM
  totalNary := fun _ _ _ _ _ _ _ _ hf => hf.elim

/-- **The whole-subject class of `gap15_plainH`**: hint-free `FragX` ∪ `PlainCalls` ∪
`PlainCallsDM`, or J's hinted class at the table's `+sound`. -/
def FM15 (S : Type) [Comp.HoonSet S] (lib : Lib) : MonoClassH := fun snd =>
  orM (noHintM (orM (liftMC (FragXM S)) (orM (PlainCallsM S lib) (PlainCallsDM S lib)))) (HintClsB snd lib)

/-- **The n-ary class of `gap15_plainH`**: `FragXN` ∪ `PlainCallsN`. -/
def FN15 (S : Type) [Comp.HoonSet S] (lib : Lib) : NaryClass :=
  orN (orN (liftNC (FragXN S)) (orN (PlainCallsN S lib) NoNary)) NoNary

/-- **The class leaves of `gap15_plainH`**, each with its owner. -/
structure ClassLeaves15 (S : Type) [Comp.HoonSet S] (lib : Lib) : Prop where
  /-- H: the pill's `+optimize` returns on `PlainCalls` (mono, n-ary). -/
  totalPlainM : OptTotalMono S (PlainCallsM S lib)
  totalPlainN : OptTotalNary S (PlainCallsN S lib)
  /-- D: the call blocks of `+mono-try-call` (`IL` and liveness). -/
  kdm : Raw.KdmMonoSpec S (TreapMap mugF)
  /-- G: the guard of the class with calls (`guardMonoC_noSixX` from `StraightA`, or
  `guardMonoC_noSixWX` from D's `KeyUndefC` and G's `SDWEndC`). -/
  guard : GuardMonoC S (TreapMap mugF) NoSixM
  /-- H: the pill's `+optimize` returns on `PlainCallsDM`. -/
  totalPlainDM : OptTotalMono S (PlainCallsDM S lib)
  /-- D (`OptIn`), G/D (entry), H (totality): J's hinted class at `finishLUCH`. -/
  hint : HintLeaves S lib

/-- **The class facts of `FM15`, `FN15`** from `ClassLeaves15` (no `KIMid`). -/
theorem classLeaves15_of {lib : Lib} (h : ClassLeaves15 S lib) : ClassLeavesH S lib (FM15 S lib) (FN15 S lib) :=
  classLeavesH_or
    (classLeavesH_of13 (classLeaves_or (classLeaves_fragX lib)
      (classLeaves_or (classLeaves_plainX lib h.totalPlainM h.totalPlainN)
        (classLeaves_plainDM lib h.kdm h.guard h.totalPlainDM))))
    (classLeavesH_hint h.hint)

/-- **The assembly on hint-free `FragX` ∪ `PlainCalls` ∪ `PlainCallsDM` and J's hinted
class**: `gap15` with the class leaves of `ClassLeaves15` (no `KIMid`). -/
theorem gap15_plainH (Ar : ArmsP) (D : CompData FinMap (TreapMap mugF) Noun Noun) {env : Env Noun}
    {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool} {bf : BEnv FinMap → Nat}
    (hR : Route14 Ar env jet fold frozen bf) (hP : PokeLeaves14 Ar env jet fold frozen bf)
    (hC : CompLeaves15 Ar D (FM15 CSet libP) (FN15 CSet libP)) (hL : ClassLeaves15 CSet libP)
    (hH : HaltLeaves15 Ar D env jet fold frozen bf) (hF : FormatLeaves13) :
    Assembly.Gap libP (liftPoke (enc flagsOf) (pokeS Ar))
      (liftInv (enc flagsOf) (InvSMI libP (refDH CSet D snP) I14)) :=
  gap15 Ar D hR hP hC (classLeaves15_of hL) hH hF

/-- **The assembly on hint-free `FragX`**: no class leaf. -/
theorem gap15_fragX (Ar : ArmsP) (D : CompData FinMap (TreapMap mugF) Noun Noun) {env : Env Noun}
    {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool} {bf : BEnv FinMap → Nat}
    (hR : Route14 Ar env jet fold frozen bf) (hP : PokeLeaves14 Ar env jet fold frozen bf)
    (hC : CompLeaves15 Ar D (fun _ => noHintM (liftMC (FragXM CSet))) (liftNC (FragXN CSet)))
    (hH : HaltLeaves15 Ar D env jet fold frozen bf) (hF : FormatLeaves13) :
    Assembly.Gap libP (liftPoke (enc flagsOf) (pokeS Ar))
      (liftInv (enc flagsOf) (InvSMI libP (refDH CSet D snP) I14)) :=
  gap15 Ar D hR hP hC (classLeavesH_of13 (classLeaves_fragX libP)) hH hF

end Glue
end SkaModel
end Formalization
