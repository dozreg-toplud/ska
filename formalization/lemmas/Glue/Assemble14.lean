import lemmas.Glue.PiecesOn
import lemmas.Compiler.CompMonoLinkTop6
import lemmas.Ska.AnnotSInv

/-!
# The assembly, fourteenth pass (track G): `Full` over REACHED states (misfit 4 bridged)

ONE theorem, `gap14`: all eight fields of `Assembly.Gap` (hence `Full`, `full14`) for

* `lib := libP`, `pk := liftPoke (enc flagsOf) (pokeS Ar)`,
* the reference compiler `refD CSet D` (the MODEL: `finishLUCM` of the table's nomm,
  `finishLFC` of `D.inl`; `refMono` and `refNary` are no longer leaves),
* `InvC := liftInv (enc flagsOf) (InvSMI libP (refD CSet D) I14)`, with the invariant of
  reached states `I14 st := PokeReach (enc flagsOf st) ∧ InvK libP st.long` (the pill's own
  reachability, and track Q's `InvK`: a theorem, `invK_ana14`),

from the records `Route14` (choices), `PokeLeaves14` (P, K, D), `CompLeaves14` (K, I, P, Q,
none), `ClassLeaves13` (class facts), `HaltLeaves14` (F, none), `FormatLeaves13` (none).

The pill facts of `CompHyp` are now asked only where the compiler runs (`CompHypOn`,
`Glue/PokeOn.lean`): `Rd14 st b` (`InvK` and: `PGood6 st`, or `st` is the state of `%full`
after `+ska-poke` from a `PGood6` state and `b` its root).

* `unary` on the `%full` path: from track K's record `GateRest6All` (`unaryOut_of_gate`: the
  pill's `+compile-unary` IS `finishLUCM` of the code table's nomm under the record's `env`)
  and two leaves: `UnaryEnvIs14` (the record's `env` gives what `D.env` gives) and
  `UnaryCacheOK14` (the cache it returns holds reference forms).  On the `%dire` path it is the
  leaf `UnaryDire14` (P's `%dire` is a leaf too: `PokeOther13`).
* `inlAnnot`: from track Q's `inlAnnot_of_invK` and `InlPill` (no other leaf).
* the poke side: track K's top `pokeModel_fullReachP9U` (misfit 2 is gone: K's record is read
  by K's own top, no map to P's old `UnaryGateAt`).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Ana Bake PokeM Compiler Pill Hoon AnnotSF

/-! ## The records -/

/-- **The route** (choices): track P's arms at P's concrete `regOfP`, `jetsOfP`, `newOfP`, the
fuel `anaFuel`. -/
structure Route14 (Ar : ArmsP) (env : Env Noun) (jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool)
    (fold frozen : Bool) (bf : BEnv FinMap → Nat) : Prop where
  he : env.he = heSock
  threshold : env.threshold = 32
  softSpot : env.softSpot = softSpotF
  registerFast : env.registerFast = registerFastP
  skaPoke : Ar.skaPoke = anaArmP env jet fold frozen (anaFuel env regOfP) bf regOfP jetsOfP newOfP
  jetRoot : Ar.jetRoot = jetRootP
  optimize : Ar.optimize = optimizeP
  sccOf : Ar.sccOf = sccOfP
  compileUnary : Ar.compileUnary = compileUnaryP flagsOf

/-- **The leaves of `pokeModel`** (the hypotheses of K's `pokeModel_fullReachP9U`, and P's
other pokes). -/
structure PokeLeaves14 (Ar : ArmsP) (env : Env Noun) (jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool)
    (fold frozen : Bool) (bf : BEnv FinMap → Nat) : Prop where
  /-- P: `BakeLinkAt` and `TailEndAt` at `PGood6` states. -/
  spLeaves : SpLeavesGood OptTotal env jet fold frozen bf jetsOfP newOfP
  /-- K (fields owed by P, I, A): the record of `+compile-unary` at every key of a `PGood6` state. -/
  gate : GateRest6All flagsOf OptTotal
  /-- K: the keys of `sure` and `inl` in the cache `+compile-unary` returns. -/
  restKeys : UnaryRestKeys6 flagsOf OptTotal
  /-- D: `+compile-unary` keeps the optimizer's class. -/
  unaryKeeps : UnaryKeeps Ar OptTotal
  /-- P: `%dire`, `%jets ~`, `%fast` keep `PGood6`. -/
  otherKeeps : OtherKeeps6 flagsOf OptTotal
  /-- P: `%dire`, `%jets ~`, `%fast` are the model's. -/
  other : PokeOther13 Ar

/-- **The pill's poke is the model's** (K's top on `%full`, P's leaf on the others). -/
theorem pokeModel14 {Ar : ArmsP} {env : Env Noun} {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool}
    {fold frozen : Bool} {bf : BEnv FinMap → Nat} (hR : Route14 Ar env jet fold frozen bf)
    (hP : PokeLeaves14 Ar env jet fold frozen bf) : Assembly.PokeModel (liftPoke (enc flagsOf) (pokeS Ar)) :=
  pokeModel_of_fullOther
    (pokeModel_fullReachP9U Ar env hR.he hR.threshold hR.softSpot hR.registerFast libP hR.skaPoke hR.jetRoot
      hR.optimize hR.sccOf hR.compileUnary hP.spLeaves hP.gate hP.restKeys hP.unaryKeeps hP.otherKeeps) hP.other

/-- **Every reached state is `PGood6`** (K's `pokeReachGood6K` with the links of
`pokeModel_fullReachP9U`). -/
theorem good6_of_reach14 {Ar : ArmsP} {env : Env Noun} {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool}
    {fold frozen : Bool} {bf : BEnv FinMap → Nat} (hR : Route14 Ar env jet fold frozen bf)
    (hP : PokeLeaves14 Ar env jet fold frozen bf) {st : PSt} (h : PokeReach (enc flagsOf st)) : PGood6 OptTotal st := by
  have hI : SccImage := sccImage
  have hK := skaKeeps_of_armP Ar hR.skaPoke jetsOfGood_P
  have hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none := fun s a L j h => by
    rw [hR.skaPoke]; exact anaArmP_atom env jet fold frozen _ bf regOfP jetsOfP newOfP s a L j h
  obtain ⟨st', hg, he⟩ := pokeReachGood6K flagsOf Ar OptTotal env hR.he hR.threshold hR.softSpot hR.registerFast libP
    hR.skaPoke hR.sccOf hR.jetRoot
    (spRestGood6_of_leaves Ar OptTotal env hR.skaPoke (fuelOK_anaFuel env regOfP) regOfP_shape hP.spLeaves)
    (sccLink_of flagsOf hR.sccOf hI) (monoLinkGood6K_of_gate flagsOf Ar OptTotal hR.compileUnary hP.gate)
    (optLinkOn_optimizeP hR.optimize) hK hP.unaryKeeps (sccOfKeeps_of hR.sccOf)
    (unaryCacheKeeps6_of_gate hR.compileUnary hP.gate hP.restKeys) (sccOfIsK_of hR.sccOf)
    (unarySccsIs6_of_gate hR.compileUnary hP.gate) tarjanExists jetsOfCole6_P hAt hP.otherKeeps _ h
  rw [← enc_inj flagsOf _ _ he]
  exact hg

/-! ## The reached states -/

/-- **The invariant of reached states**: reached by the pill's own pokes, and track Q's `InvK`. -/
def I14 (st : PSt) : Prop := PokeReach (enc flagsOf st) ∧ InvK libP st.long

/-- **Where the compile step runs**: `InvK`, and a `PGood6` state at any bell, or the state of
`%full` after `+ska-poke` from a `PGood6` state at the root bell. -/
def Rd14 (Ar : ArmsP) (st : PSt) (b : Bell) : Prop :=
  InvK libP st.long ∧ (PGood6 OptTotal st ∨ ∃ (st0 : PSt) (s f : Noun) (r : Bell × LongB FinMap × Noun × Noun), PGood6 OptTotal st0 ∧
    Ar.skaPoke s f st0.long st0.jets st0.hot = some r ∧ st = midSt st0 r ∧ b = r.1)

/-- The reached tables. -/
def Tr14 (long : LongB FinMap) (_ _ : Noun) : Prop := InvK libP long

/-- **`InvK` is kept by track P's analysis arm** (Q's `skaPokeB_soundK` at P's root sock). -/
theorem invK_ana14 {Ar : ArmsP} {R : Type} {env : Env R} {jet : Noun → Noun → (Bell → Option Datum) → R → Bell → Bool}
    {fold frozen : Bool} {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat}
    {regOf : Noun → R} {jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun} {newOf : R → Noun}
    (hA : Ar.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf) {lib : Lib} :
    ∀ s f long jets hot r, InvK lib long → Ar.skaPoke s f long jets hot = some r → InvK lib r.2.1 := by
  intro s f long jets hot r hK h
  rw [hA] at h
  cases f with
  | atom _ => simp [anaArmP] at h
  | cell f1 f2 =>
    simp only [anaArmP, Option.map_eq_some_iff] at h
    obtain ⟨⟨rb, L', reg'⟩, hk, rfl⟩ := h
    obtain ⟨hB, hpk, hS⟩ := hK
    have hroot : (Sock.mk Cape.yes s, C f1 f2).1 ≠ Sock.void := Sock.noConfusion
    obtain ⟨h1, h2, h3, -⟩ := skaPokeB_soundK (folTopK lib) env hB hpk hS (wf_root s) (normSock_yes s) hroot hk
    exact ⟨h1, h2, h3⟩

/-- **Every poke keeps `InvK`** (only `%full` changes the table). -/
theorem pokeS_invK {Ar : ArmsP} {R : Type} {env : Env R} {jet : Noun → Noun → (Bell → Option Datum) → R → Bell → Bool}
    {fold frozen : Bool} {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat}
    {regOf : Noun → R} {jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun} {newOf : R → Noun}
    (hA : Ar.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf) {lib : Lib} :
    ∀ (st : PSt) ov p st', InvK lib st.long → pokeS Ar st ov = some (p, st') → InvK lib st'.long := by
  intro st ov p st' hm h
  cases ov with
  | full s f =>
    simp only [pokeS] at h
    obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
    have hm' : InvK lib r.2.1 := invK_ana14 hA s f _ _ _ r hm hr
    split at h
    · cases h; exact hm'
    · obtain ⟨q, hq, he⟩ := Option.map_eq_some_iff.mp h
      cases he
      rw [compileStep_long Ar hq]
      exact hm'
  | dire b m =>
    simp only [pokeS] at h
    obtain ⟨q, hq, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    rw [compileStep_long Ar hq]
    exact hm
  | jets q =>
    simp only [pokeS] at h
    obtain ⟨r, -, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    exact hm
  | fast rs q =>
    simp only [pokeS] at h
    obtain ⟨r, -, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    exact hm

theorem not_hot_noun {ov : Ovum} (h : ¬ HotOvum ov) : ¬ Ska.Hot ov.toNoun := by
  rintro ⟨hd, tl, e⟩
  cases ov with
  | jets p =>
    cases p with
    | atom n => simp [Ovum.toNoun] at e
    | cell a b => exact h trivial
  | full s f => simp [Ovum.toNoun, Tag.full, Ska.jets] at e
  | dire b m => simp [Ovum.toNoun, Tag.dire, Ska.jets] at e
  | fast r p => simp [Ovum.toNoun, Tag.fast, Ska.jets] at e

/-- **The reached states, as `ReachOn` asks.** -/
theorem reachOn14 {Ar : ArmsP} {env : Env Noun} {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool}
    {fold frozen : Bool} {bf : BEnv FinMap → Nat} (hR : Route14 Ar env jet fold frozen bf)
    (hP : PokeLeaves14 Ar env jet fold frozen bf) : ReachOn Ar I14 (Rd14 Ar) where
  now := fun st _ hi => ⟨hi.2, Or.inl (good6_of_reach14 hR hP hi.1)⟩
  ana := fun st s f r hi hr =>
    ⟨invK_ana14 hR.skaPoke s f _ _ _ r hi.2 hr, Or.inr ⟨st, s, f, r, good6_of_reach14 hR hP hi.1, hr, rfl, rfl⟩⟩
  kept := by
    intro st ov p st' hi hh h
    refine ⟨?_, pokeS_invK hR.skaPoke st ov p st' hi.2 h⟩
    have hc : CorIn (enc flagsOf st) :=
      corIn_of_tail Assembly.corIn_cor (by simp only [cor_enc flagsOf, enc_slot15]) hi.1
    have hn := not_hot_noun hh
    have hpk := pokeModel14 hR hP (enc flagsOf st) hc ov hn
    rw [liftPoke_enc (enc_inj flagsOf), h] at hpk
    exact PokeReach.poke hi.1 hpk hn

theorem invStart14 : I14 emptySt :=
  ⟨by rw [← cor_enc flagsOf]; exact PokeReach.start,
    ⟨InvB.init libP, ⟨_, PokeInvK.init libP⟩, fun bl nb hb => by simp [emptySt, realOf, Treap.get_empty] at hb⟩⟩

/-! ## `+compile-unary` from K's record -/

/-- **The pill's `+compile-unary` at a key of a `PGood6` state is `finishLUCM` of the key's
nomm, under the `env` of K's record** (`unaryFinish_of_rest5`, read through `compileUnaryP`). -/
theorem unaryOut_of_gate {Ar : ArmsP} (hUA : Ar.compileUnary = compileUnaryP flagsOf)
    (hGR : GateRest6All flagsOf OptTotal) {st : PSt} {b : Bell} {e : VarEntry FinMap} (hg : PGood6 OptTotal st)
    (he : FinMap.get st.long.code b = some e) {s : Straight (TreapMap mugF)} {n : FinMap Bell (Straight (TreapMap mugF))}
    {c' : Cache FinMap (TreapMap mugF) (Noun × Noun)}
    (hr : Ar.compileUnary b (sccSet st.long.code b) st.long st.jets st.hot st.cache = some ((s, n), c')) :
    ∃ (COLE NM CA : Noun) (need : Bell → Option NeedOrd) (sure : Bell → NeedOrd)
      (sof : Nomm → Nomm → Nomm → Bell → NeedOrd → Bool) (inl : Noun → Option Nomm) (D' : Bell → Prop),
      slot? 190 (C st.jets (callsNoun st.long)) = some COLE ∧
      GateRest6Sw flagsOf st b e NM CA COLE (envOf (codeNoun flagsOf st.long.code) COLE need sure sof) inl D' ∧
      Comp.finishLUCM (S := CSet) (envOf (codeNoun flagsOf st.long.code) COLE need sure sof) e.nomm = some s := by
  obtain ⟨-, -, -, -, -, COLE, -, -, -, hcole⟩ := gateCole_of_good hg
  obtain ⟨NM, CA, need, sure, sof, inl, D', H⟩ := hGR st b e COLE hg he hcole
  have H5 := gateRest5_of_Sw hg.good5 (gateRest5Sw_of_6 he hcole H)
  obtain ⟨-, CA', hn⟩ := unaryFinish_of_rest5 hg.good5 H5
  refine ⟨COLE, NM, CA, need, sure, sof, inl, D', hcole, H, ?_⟩
  rw [hUA] at hr
  unfold compileUnaryP at hr
  split at hr
  · rename_i hx
    have hspec : nock (C cuGB (C (cuSam b.toNoun (FinMap.setNoun (sccSet st.long.code b)) (codeNoun flagsOf st.long.code)
        (C st.jets (callsNoun st.long)) st.hot (cacheNoun st.cache)) compK)) cuGB =
        some (cuResNoun (Classical.choose hx)) := Classical.choose_spec hx
    rw [Option.some.inj hr, hn] at hspec
    obtain ⟨s', hs', e'⟩ := Option.map_eq_some_iff.1 hspec
    simp only [cuResNoun, Noun.cell.injEq] at e'
    rw [hs', straight_toNoun_inj e'.1.1]
  · cases hr

/-- **Leaf (K, I): the `env` of K's record gives what `D.env` gives** to `finishLUCM` on the
key's nomm (the compile does not depend on the cache's `need` / `sure` beyond `D.env`). -/
def UnaryEnvIs14 (D : CompData FinMap (TreapMap mugF) Noun Noun) : Prop :=
  ∀ (st : PSt) b (e : VarEntry FinMap) COLE NM CA (need : Bell → Option NeedOrd) (sure : Bell → NeedOrd)
    (sof : Nomm → Nomm → Nomm → Bell → NeedOrd → Bool) (inl : Noun → Option Nomm) (D' : Bell → Prop) (s : Straight (TreapMap mugF)),
    PGood6 OptTotal st → FinMap.get st.long.code b = some e → slot? 190 (C st.jets (callsNoun st.long)) = some COLE →
    GateRest6Sw flagsOf st b e NM CA COLE (envOf (codeNoun flagsOf st.long.code) COLE need sure sof) inl D' →
    Comp.finishLUCM (S := CSet) (envOf (codeNoun flagsOf st.long.code) COLE need sure sof) e.nomm = some s →
    Comp.finishLUCM (S := CSet) (D.env st.long st.jets st.hot b true) e.nomm = some s

/-- **Leaf (I, K): the cache `+compile-unary` returns at a key of a `PGood6` state holds
reference forms** (its `nary` entries, from `+compile-scc-in`, are the reference's). -/
def UnaryCacheOK14 (Ar : ArmsP) (ref : Ref FinMap (TreapMap mugF) Noun Noun) : Prop :=
  ∀ (st : PSt) b (e : VarEntry FinMap) r, PGood6 OptTotal st → FinMap.get st.long.code b = some e →
    Ar.compileUnary b (sccSet st.long.code b) st.long st.jets st.hot st.cache = some r →
    CacheOK ref st.long st.jets st.hot st.cache → CacheOK ref st.long st.jets st.hot r.2

/-- **`unary` on the `%full` path from K's record.** -/
theorem unaryMid14 {Ar : ArmsP} {env : Env Noun} {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool}
    {fold frozen : Bool} {bf : BEnv FinMap → Nat} {D : CompData FinMap (TreapMap mugF) Noun Noun}
    (hR : Route14 Ar env jet fold frozen bf) (hP : PokeLeaves14 Ar env jet fold frozen bf)
    (hE : UnaryEnvIs14 D) (hCa : UnaryCacheOK14 Ar (refD CSet D)) {st0 : PSt} {s f : Noun}
    {r : Bell × LongB FinMap × Noun × Noun} (hg : PGood6 OptTotal st0)
    (e1 : Ar.skaPoke s f st0.long st0.jets st0.hot = some r) {q : FinMap Bell Unit × FinMap Bell (FinMap Bell Unit)}
    (e3 : Ar.sccOf r.1 r.2.1 st0.cache.sccs = some q) {s' : Straight (TreapMap mugF)}
    {n : FinMap Bell (Straight (TreapMap mugF))} {c' : Cache FinMap (TreapMap mugF) (Noun × Noun)}
    (hu : Ar.compileUnary r.1 q.1 r.2.1 r.2.2.1 st0.hot { st0.cache with sccs := q.2 } = some ((s', n), c')) :
    refD CSet D r.2.1 r.2.2.1 st0.hot r.1 true = some s' ∧
      (CacheOK (refD CSet D) r.2.1 r.2.2.1 st0.hot st0.cache → CacheOK (refD CSet D) r.2.1 r.2.2.1 st0.hot c') := by
  have hK := skaKeeps_of_armP Ar hR.skaPoke jetsOfGood_P
  obtain ⟨⟨eb, heb⟩, hq⟩ := mid_key hR.skaPoke hR.sccOf st0 s f hg.good5 r e1 q e3
  have hm := good6_mid hR.skaPoke hK (sccOfKeeps_of hR.sccOf) (sccOfIsK_of hR.sccOf) tarjanExists jetsOfCole6_P
    st0 s f hg r e1 q e3
  rw [hq] at hu
  obtain ⟨COLE, NM, CA, need, sure, sof, inl, D', hcole, H, hs⟩ := unaryOut_of_gate hR.compileUnary hP.gate hm heb hu
  have h1 := hE _ _ _ _ _ _ _ _ _ _ _ _ hm heb hcole H hs
  refine ⟨?_, hCa _ r.1 eb _ hm heb hu⟩
  have heb' : Treap.get r.2.1.code r.1 = some eb := heb
  simp only [refD, if_true, realOf, heb', Option.map_some, Option.bind_some]
  exact h1

/-! ## The leaves of `CompHypOn` -/

/-- **The leaves of the compile at the reached states**: `+compile-unary` (K's record is in
`PokeLeaves14.gate`; here what it does not give), and the fields of `CompHyp` that are not the
contract, each asked only at reached states (`PGood6` and `InvK`, or `Rd14` / `I14`). -/
structure CompLeaves14 (Ar : ArmsP) (D : CompData FinMap (TreapMap mugF) Noun Noun) (FM : MonoClass) (FN : NaryClass) :
    Prop where
  /-- K, I: the record's `env` is `D.env` for `finishLUCM`. -/
  unaryEnv : UnaryEnvIs14 D
  /-- I, K: the cache `+compile-unary` returns holds reference forms. -/
  unaryCache : UnaryCacheOK14 Ar (refD CSet D)
  /-- K, P: `+compile-unary` on the `%dire` path (at a `PGood6` state, any bell). -/
  unaryDire : ∀ (st : PSt) b q s n c', PGood6 OptTotal st → InvK libP st.long →
    Ar.sccOf b st.long st.cache.sccs = some q →
    Ar.compileUnary b q.1 st.long st.jets st.hot { st.cache with sccs := q.2 } = some ((s, n), c') →
    refD CSet D st.long st.jets st.hot b true = some s ∧
      (CacheOK (refD CSet D) st.long st.jets st.hot st.cache → CacheOK (refD CSet D) st.long st.jets st.hot c')
  /-- I: `+compile-scc` on the `%dire` path. -/
  scc : ∀ (st : PSt) b q m c', I14 st → Ar.sccOf b st.long st.cache.sccs = some q →
    Ar.compileScc q.1 st.long st.jets st.hot { st.cache with sccs := q.2 } = some (m, c') →
    (∀ b' s, Treap.get m b' = some s → refD CSet D st.long st.jets st.hot b' false = some s) ∧
      (CacheOK (refD CSet D) st.long st.jets st.hot st.cache → CacheOK (refD CSet D) st.long st.jets st.hot c')
  /-- I + no owner: the compile returns where it runs (`split-max`, S). -/
  answers : ∀ (st : PSt) b m s, Rd14 Ar st b → InvS libP (refD CSet D) st →
    refD CSet D st.long st.jets st.hot b m = some s → (compileStep Ar st b m).isSome
  /-- no owner: what is compiled holds across `+ska-poke`, at reached states. -/
  stable : ∀ (st : PSt) s f r b m x, I14 st → Ar.skaPoke s f st.long st.jets st.hot = some r →
    InvB libP st.long → refD CSet D st.long st.jets st.hot b m = some x → refD CSet D r.2.1 r.2.2.1 st.hot b m = some x
  /-- no owner: the jetted root, at reached states. -/
  jetRoot : ∀ (st : PSt) s f r out, I14 st → Ar.skaPoke s f st.long st.jets st.hot = some r →
    InvB libP st.long → Ar.jetRoot r.2.2.1 st.hot r.1 = some out →
    out.nargs = 1 ∧ out.need = NeedOrd.this ∧
      ContractFwd libP (refN Ar (refD CSet D) r.2.1 r.2.2.1 st.hot) s f [s] out ∧
      ContractBwd libP (refN Ar (refD CSet D) r.2.1 r.2.2.1 st.hot) s f [s] out
  /-- no owner: `%jets ~` keeps the cache, at reached states. -/
  jets : ∀ st p r, I14 st → ¬ HotOvum (Ovum.jets p) → Ar.jetsPoke st p = some r →
    CacheOK (refD CSet D) st.long st.jets st.hot st.cache → CacheOK (refD CSet D) st.long r.2.1 r.2.2.1 r.2.2.2
  /-- no owner: `%fast` keeps the cache, at reached states. -/
  fast : ∀ st rs p r, I14 st → Ar.fastPoke st rs p = some r →
    CacheOK (refD CSet D) st.long st.jets st.hot st.cache → CacheOK (refD CSet D) st.long r.1 st.hot r.2
  /-- C, J, K, A: every compiled nomm of a reached table is in the class. -/
  inFrag : InFragOn CSet Ar libP D FM FN Tr14
  /-- P: the pill's `+optimize` on the reference forms of reached tables. -/
  optPill : ∀ long jets hot b m s, InvB libP long → Tr14 long jets hot → refD CSet D long jets hot b m = some s →
    nock (C optBody (C s.toNoun optC)) optBody = some (Ar.optimize s).toNoun
  /-- Q (no owner: the pill half): `+inlined` is `inlinedM`. -/
  inlPill : InlPill libP D
  /-- I, J: the needs the compile reads of the callees, at reached tables. -/
  callee : ∀ long jets hot b m, InvB libP long → Tr14 long jets hot →
    Comp.CalleeNeeds (D.env long jets hot b m) (refN Ar (refD CSet D) long jets hot)

/-- **The state half of `CompHypOn`.** -/
theorem compState14 {Ar : ArmsP} {env : Env Noun} {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool}
    {fold frozen : Bool} {bf : BEnv FinMap → Nat} {D : CompData FinMap (TreapMap mugF) Noun Noun} {FM : MonoClass}
    {FN : NaryClass} (hR : Route14 Ar env jet fold frozen bf) (hP : PokeLeaves14 Ar env jet fold frozen bf)
    (hC : CompLeaves14 Ar D FM FN) : CompStateOn Ar libP (refD CSet D) I14 (Rd14 Ar) where
  unary := by
    intro st b q s n c' hrd hq hu
    rcases hrd.2 with hg | ⟨st0, s0, f0, r, hg, e1, rfl, rfl⟩
    · exact hC.unaryDire st b q s n c' hg hrd.1 hq hu
    · exact unaryMid14 hR hP hC.unaryEnv hC.unaryCache hg e1 hq hu
  scc := hC.scc
  answers := hC.answers
  stable := hC.stable
  jetRoot := hC.jetRoot
  jets := hC.jets
  fast := hC.fast

/-- **The contract-side leaves**: `inlAnnot` from track Q's `inlAnnot_of_invK`. -/
theorem contractLeaves14 {Ar : ArmsP} {D : CompData FinMap (TreapMap mugF) Noun Noun} {FM : MonoClass}
    {FN : NaryClass} (hC : CompLeaves14 Ar D FM FN) : ContractLeavesOn CSet Ar libP (refD CSet D) D FM FN Tr14 where
  toRefSideMOn := refSideMOn_refD hC.inFrag
  optPill := hC.optPill
  inlAnnot := fun long jets hot b nm _ hT hinl => inlAnnot_of_invK hC.inlPill long jets hot b nm hT hinl
  callee := hC.callee

/-- **`CompHypOn` at the reached states.** -/
theorem compHyp14 {Ar : ArmsP} {env : Env Noun} {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool}
    {fold frozen : Bool} {bf : BEnv FinMap → Nat} {D : CompData FinMap (TreapMap mugF) Noun Noun} {FM : MonoClass}
    {FN : NaryClass} (hR : Route14 Ar env jet fold frozen bf) (hP : PokeLeaves14 Ar env jet fold frozen bf)
    (hC : CompLeaves14 Ar D FM FN) (hK : ClassLeaves13 CSet libP FM FN) :
    CompHypOn Ar libP (refD CSet D) I14 (Rd14 Ar) :=
  compHypOn_of (compState14 hR hP hC) (contractLeaves14 hC) hK fun _ _ hrd => hrd.1

/-! ## THE ASSEMBLY -/

/-- **The leaves of `halting`** (`root` at reached states only). -/
structure HaltLeaves14 (Ar : ArmsP) (D : CompData FinMap (TreapMap mugF) Noun Noun) (env : Env Noun)
    (jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool) (fold frozen : Bool) (bf : BEnv FinMap → Nat) :
    Prop where
  /-- F: the call graph's pass loop ends. -/
  cg : CgHalts (M := FinMap) libP env regOfP
  /-- Q (H2): the worklist of `+bake-graph` ends within `bf`. -/
  bake : BakeEnds libP env jet fold frozen (anaFuel env regOfP) bf regOfP
  /-- no owner: the root bell has a whole-subject form, at reached states. -/
  root : RootAnswersOn libP Ar (refD CSet D) I14

/-- **`Gap` from the named leaves, over the reached states.** -/
theorem gap14 (Ar : ArmsP) (D : CompData FinMap (TreapMap mugF) Noun Noun) {FM : MonoClass} {FN : NaryClass}
    {env : Env Noun} {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool}
    {bf : BEnv FinMap → Nat}
    (hR : Route14 Ar env jet fold frozen bf) (hP : PokeLeaves14 Ar env jet fold frozen bf)
    (hC : CompLeaves14 Ar D FM FN) (hK : ClassLeaves13 CSet libP FM FN)
    (hH : HaltLeaves14 Ar D env jet fold frozen bf) (hF : FormatLeaves13) :
    Assembly.Gap libP (liftPoke (enc flagsOf) (pokeS Ar)) (liftInv (enc flagsOf) (InvSMI libP (refD CSet D) I14)) := by
  have hCH := compHyp14 hR hP hC hK
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

/-- **`Full` from the named leaves, over the reached states.** -/
theorem full14 (Ar : ArmsP) (D : CompData FinMap (TreapMap mugF) Noun Noun) {FM : MonoClass} {FN : NaryClass}
    {env : Env Noun} {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool}
    {bf : BEnv FinMap → Nat}
    (hR : Route14 Ar env jet fold frozen bf) (hP : PokeLeaves14 Ar env jet fold frozen bf)
    (hC : CompLeaves14 Ar D FM FN) (hK : ClassLeaves13 CSet libP FM FN)
    (hH : HaltLeaves14 Ar D env jet fold frozen bf) (hF : FormatLeaves13) : Ska.Full :=
  Assembly.full_of (gap14 Ar D hR hP hC hK hH hF)

/-- **The assembly on `FragX`**: no class leaf. -/
theorem gap14_fragX (Ar : ArmsP) (D : CompData FinMap (TreapMap mugF) Noun Noun) {env : Env Noun}
    {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool} {bf : BEnv FinMap → Nat}
    (hR : Route14 Ar env jet fold frozen bf) (hP : PokeLeaves14 Ar env jet fold frozen bf)
    (hC : CompLeaves14 Ar D (liftMC (FragXM CSet)) (liftNC (FragXN CSet)))
    (hH : HaltLeaves14 Ar D env jet fold frozen bf) (hF : FormatLeaves13) :
    Assembly.Gap libP (liftPoke (enc flagsOf) (pokeS Ar)) (liftInv (enc flagsOf) (InvSMI libP (refD CSet D) I14)) :=
  gap14 Ar D hR hP hC (classLeaves_fragX libP) hH hF

end Glue
end SkaModel
end Formalization
