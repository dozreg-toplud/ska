import lemmas.Compiler.PokeLinkKeep

/-!
# `PGood3`: `PGood2` with `vars` on keys, kept by `%full`; `pokeModel` over it

`PGood3 Cls st` = `PGood2 Cls st` (`PGood`, `CodeClosed`, `CacheGood`) and
`VarsKeys` (every variant `vars` lists is a key of `code`), which the
closure of the bake needs (`addCode_closed`).  *Checked* before:
`tools/hoon/invdump2.hoon` (32 pokes mixing `%full`, `%jets` with real
drops, `%fast` with and without `reset`, `%dire`): every clause of
`PGood2`, `%vars`, `%ckey`, `%mono`, `%flag` hold after every poke.

* `good3_empty`: at the start;
* `good3_mid`: at the state the `%full` branch hands `+compiled-mono` (after
  `+scc-of`), from `SkaKeeps`, `SkaCodeKeeps` (proved for `anaArmP`,
  `skaCodeKeeps_of_armP`) and `SccOfKeeps` (`+scc-of` keeps `SccsGoodM` and
  every old entry: a pill fact on `sccOfP`, the miss with `+tarjan`);
* `good3_full_step`: `%full` keeps `PGood3`, with `UnaryKeeps` and
  `UnaryCacheKeeps` (`+compile-unary` keeps `CacheGood`: track K);
* `pokeN_fullAt4`: `pokeN_fullAt3` with `MonoLinkAt` asked only at the
  `+scc-of` the pill computes;
* `pokeModel_fullGood3`, `pokeReachGood3`, `pokeModel_fullReach3` and
  **`pokeModel_fullReachP3`** (track P's route, `anaArmP`, `optimizeP`,
  `sccOfP`, `jetRootP`, `OptTotal`): the links asked on `PGood3` states only.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeM

/-- **`PGood3`**: `PGood2` and `vars` on keys. -/
structure PGood3 (Cls : Straight (TreapMap mugF) → Prop) (st : PSt) : Prop where
  good2 : PGood2 Cls st
  vars : VarsKeys st.long.vars st.long.code

theorem good3_empty (Cls : Straight (TreapMap mugF) → Prop) : PGood3 Cls emptySt where
  good2 := good2_empty Cls
  vars := fun c v h => by
    simp [emptySt, Treap.gut, Treap.has, Treap.get_empty] at h

/-! ## The cache clauses under the writes of `%full` -/

theorem cacheGood_code {code code' : FinMap Bell (VarEntry FinMap)} {c : Cache FinMap (TreapMap mugF) (Noun × Noun)}
    (h : CacheGood code c) (hk : ∀ b e, FinMap.get code b = some e → FinMap.get code' b = some e) :
    CacheGood code' c where
  sureMap := h.sureMap
  sureKeys := h.sureKeys
  inlMap := h.inlMap
  inlKeys := fun kn v hv => by
    obtain ⟨b, e, nm, h1, h2, h3⟩ := h.inlKeys kn v hv
    exact ⟨b, e, nm, h1, hk b e h2, h3⟩
  sccs := h.sccs
  nary := h.nary

theorem cacheGood_sccs {code : FinMap Bell (VarEntry FinMap)} {c : Cache FinMap (TreapMap mugF) (Noun × Noun)}
    {sc : FinMap Bell (FinMap Bell Unit)} (h : CacheGood code c) (hs : SccsGoodM sc)
    (hx : ∀ k S, FinMap.get c.sccs k = some S → FinMap.get sc k = some S) :
    CacheGood code { c with sccs := sc } where
  sureMap := h.sureMap
  sureKeys := h.sureKeys
  inlMap := h.inlMap
  inlKeys := h.inlKeys
  sccs := hs
  nary := fun k s hk => by
    obtain ⟨S, hS, hall⟩ := h.nary k s hk
    exact ⟨S, hx k S hS, hall⟩

theorem cacheGood_mono {code : FinMap Bell (VarEntry FinMap)} {c : Cache FinMap (TreapMap mugF) (Noun × Noun)}
    (m : FinMap Bell (Straight (TreapMap mugF))) (h : CacheGood code c) : CacheGood code { c with mono := m } :=
  ⟨h.sureMap, h.sureKeys, h.inlMap, h.inlKeys, h.sccs, h.nary⟩

section Keep

variable (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)) (Cls : Straight (TreapMap mugF) → Prop)

/-- **`+scc-of` keeps `SccsGoodM` and every old entry** (a pill fact on
`sccOfP`: the hit returns `sccs`; the miss puts the SCCs of `+tarjan` on
bells not in `sccs`; `%scck`, `%sccs` of `invdump2.hoon`). -/
def SccOfKeeps : Prop :=
  ∀ b L sc q, SccsGoodM sc → Ar.sccOf b L sc = some q →
    SccsGoodM q.2 ∧ ∀ k S, FinMap.get sc k = some S → FinMap.get q.2 k = some S

/-- **`+compile-unary` keeps the cache clauses** on a `PGood3` state (track
K: `nary`, `sure`, `inl` written for whole SCCs, `sccs` by `+scc-of`). -/
def UnaryCacheKeeps : Prop :=
  ∀ (st : PSt) b sc r, PGood3 Cls st →
    Ar.compileUnary b sc st.long st.jets st.hot st.cache = some r → CacheGood st.long.code r.2

variable {Ar Cls}

/-- **`PGood3` at the state `+compiled-mono` runs on.** -/
theorem good3_mid (hK : SkaKeeps Ar) (hS : SkaCodeKeeps Ar) (hO : SccOfKeeps Ar) (st : PSt) (s f : Noun)
    (hg : PGood3 Cls st) (r : Bell × LongB FinMap × Noun × Noun)
    (e1 : Ar.skaPoke s f st.long st.jets st.hot = some r)
    (q : FinMap Bell Unit × FinMap Bell (FinMap Bell Unit)) (e3 : Ar.sccOf r.1 r.2.1 st.cache.sccs = some q) :
    PGood3 Cls { st with long := r.2.1, jets := r.2.2.1, cache := { st.cache with sccs := q.2 } } := by
  obtain ⟨hm', hj'⟩ := hK st s f r hg.good2.good.maps hg.good2.good.jets e1
  obtain ⟨hc', hv', hold⟩ := hS st s f r hg.good2.closed hg.vars e1
  obtain ⟨hsg, hx⟩ := hO _ _ _ q hg.good2.cache.sccs e3
  exact ⟨⟨⟨hm', hj', hg.good2.good.mono⟩, hc', cacheGood_sccs (cacheGood_code hg.good2.cache hold) hsg hx⟩, hv'⟩

/-- **The model's `%full` keeps `PGood3`.** -/
theorem good3_full_step (hK : SkaKeeps Ar) (hU : UnaryKeeps Ar Cls) (hS : SkaCodeKeeps Ar) (hO : SccOfKeeps Ar)
    (hC : UnaryCacheKeeps Ar Cls) (st : PSt) (s f : Noun) (pr : SkaModel.Prod (TreapMap mugF)) (st' : PSt)
    (hg : PGood3 Cls st) (h : pokeS Ar st (Ovum.full s f) = some (pr, st')) : PGood3 Cls st' := by
  have hgood := good_full_step hK hU st s f pr st' hg.good2.good h
  simp only [pokeS] at h
  obtain ⟨r, e1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨hc', hv', hold⟩ := hS st s f r hg.good2.closed hg.vars e1
  split at h
  · cases h
    exact ⟨⟨hgood, hc', cacheGood_code hg.good2.cache hold⟩, hv'⟩
  · obtain ⟨p, hp, e⟩ := Option.map_eq_some_iff.1 h
    cases e
    unfold compileStep at hp
    obtain ⟨q, e3, hp⟩ := Option.bind_eq_some_iff.1 hp
    obtain ⟨p', hp', e⟩ := Option.map_eq_some_iff.1 hp
    cases e
    simp only [if_true] at hp'
    have hmid := good3_mid hK hS hO st s f hg r e1 q e3
    refine ⟨⟨hgood, hc', ?_⟩, hv'⟩
    unfold compiledMono at hp'
    split at hp'
    · cases hp'; exact hmid.good2.cache
    · obtain ⟨r', hr', e⟩ := Option.map_eq_some_iff.1 hp'
      cases e
      have hc2 := hC { st with long := r.2.1, jets := r.2.2.1, cache := { st.cache with sccs := q.2 } } r.1 q.1 r'
        hmid hr'
      exact cacheGood_mono _ hc2

end Keep

/-! ## The links on `PGood3` states -/

section Links

variable (fl : Flags) (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
  (Cls : Straight (TreapMap mugF) → Prop)

/-- `SpRestGood` on `PGood3` states. -/
def SpRestGood3 (env : Env Noun) : Prop :=
  ∀ (st : PSt) s f₁ f₂ r1 r2 r3 r4 jRest key, PGood3 Cls st → st.jets = C r1 (C r2 (C r3 (C r4 jRest))) →
    keyRaw (enc fl st) = some key → SpRestAt fl Ar env st s (C f₁ f₂) r1 r2 r3 r4 jRest key

/-- `MonoLinkGood` on `PGood3` states. -/
def MonoLinkGood3 : Prop := ∀ (st : PSt) b sc, PGood3 Cls st → MonoLinkAt fl Ar st b sc

theorem monoLinkGood3_of (h : MonoLinkGood fl Ar Cls) : MonoLinkGood3 fl Ar Cls :=
  fun st b sc hg => h st b sc hg.good2.good

theorem spRestGood3_of (env : Env Noun) (h : SpRestGood fl Ar Cls env) : SpRestGood3 fl Ar Cls env :=
  fun st s f₁ f₂ r1 r2 r3 r4 jRest key hg => h st s f₁ f₂ r1 r2 r3 r4 jRest key hg.good2.good

/-- **`pokeN_fullAt3` with `MonoLinkAt` asked only at the `+scc-of` the
model computes.** -/
theorem pokeN_fullAt4 (hC : SccLink fl Ar sccP) (hO : OptLinkOn Cls Ar optP) (st : PSt) (s f₁ f₂ : Noun)
    (hS : SkaLinkAt fl Ar st s (C f₁ f₂))
    (hJ : ∀ r, Ar.skaPoke s (C f₁ f₂) st.long st.jets st.hot = some r →
      jrP (enc fl { st with long := r.2.1, jets := r.2.2.1 }) r.1.toNoun =
        some ((Ar.jetRoot r.2.2.1 st.hot r.1).map Straight.toNoun))
    (hM : ∀ r (q : FinMap Bell Unit × FinMap Bell (FinMap Bell Unit)), Ar.skaPoke s (C f₁ f₂) st.long st.jets st.hot = some r →
      Ar.sccOf r.1 r.2.1 st.cache.sccs = some q →
      MonoLinkAt fl Ar { st with long := r.2.1, jets := r.2.2.1, cache := { st.cache with sccs := q.2 } } r.1 q.1)
    (hIn : OptInAt Ar Cls st s (C f₁ f₂)) :
    pokeN (enc fl st) (Ovum.full s (C f₁ f₂)).toNoun =
      (liftPoke (enc fl) (pokeS Ar) (enc fl st) (Ovum.full s (C f₁ f₂))).map fun r => C r.1.toNoun r.2 := by
  rw [fullBranchIs fl st s f₁ f₂, liftPoke_enc_fl]
  unfold pillFull
  rw [hS]
  simp only [pokeS]
  cases e1 : Ar.skaPoke s (C f₁ f₂) st.long st.jets st.hot with
  | none => rfl
  | some r =>
    simp only [Option.map_some, Option.bind_some]
    rw [hJ r e1]
    simp only [Option.bind_some]
    cases e2 : Ar.jetRoot r.2.2.1 st.hot r.1 with
    | some out => simp [Prod.toNoun]
    | none =>
      simp only [Option.map_none]
      unfold compileStep
      rw [hC]
      cases e3 : Ar.sccOf r.1 r.2.1 st.cache.sccs with
      | none => rfl
      | some q =>
        simp only [Option.map_some, Option.bind_some, if_true]
        have hMq := hM r q e1 e3
        unfold MonoLinkAt at hMq
        rw [hMq]
        cases e4 : compiledMono Ar { st with long := r.2.1, jets := r.2.2.1, cache := { st.cache with sccs := q.2 } } r.1 q.1 with
        | none => rfl
        | some p =>
          simp only [Option.map_some, Option.bind_some]
          rw [hO p.1 (hIn r q p e1 e2 e3 e4)]
          simp [Prod.toNoun]

/-- **`pokeModel` on every `%full` at a `PGood3` state.** -/
theorem pokeModel_fullGood3 (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP)
    (hJA : Ar.jetRoot = jetRootP) (hR : SpRestGood3 fl Ar Cls env) (hC : SccLink fl Ar sccP)
    (hM : MonoLinkGood3 fl Ar Cls) (hO : OptLinkOn Cls Ar optP) (hK : SkaKeeps Ar) (hU : UnaryKeeps Ar Cls)
    (hS : SkaCodeKeeps Ar) (hSc : SccOfKeeps Ar)
    (hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none) (st : PSt) (hg : PGood3 Cls st) (s f : Noun) :
    pokeN (enc fl st) (Ovum.full s f).toNoun =
      (liftPoke (enc fl) (pokeS Ar) (enc fl st) (Ovum.full s f)).map fun r => C r.1.toNoun r.2 := by
  cases f with
  | atom a => rw [pokeN_full_atom, liftPoke_enc_fl]; simp [pokeS, hAt]
  | cell f₁ f₂ =>
    refine pokeN_fullAt4 fl Ar Cls hC hO st s f₁ f₂ ?_ (fun r e => ?_) (fun r q e e3 => ?_)
      (optInAt_of_good hK hU st s _ hg.good2.good)
    · obtain ⟨r1, r2, r3, r4, pd, ca, bk, hj, -⟩ := hg.good2.good.maps
      obtain ⟨key, hk, -, -⟩ := keyRaw_enc fl st hg.good2.good.jets.2
      exact skaLinkAt_of fl Ar env hhe hth hsoft hrf st s (C f₁ f₂) r1 r2 r3 r4 (C pd (C ca bk)) key hj hk
        (hR st s f₁ f₂ r1 r2 r3 r4 _ key hg hj hk)
    · obtain ⟨_, hj'⟩ := hK st s _ r hg.good2.good.maps hg.good2.good.jets e
      exact jetRootLinkG_of fl Ar hJA st s _ r e hj'
    · exact hM _ r.1 q.1 (good3_mid hK hS hSc st s _ hg r e q e3)

/-- **The pokes other than `%full` keep `PGood3`** (pill: `%dire`, `%jets`,
`%fast`; checked by `invdump2.hoon`). -/
def OtherKeeps3 : Prop :=
  ∀ (st : PSt) ovo p c', PGood3 Cls st → pokeN (enc fl st) ovo = some (C p c') → ¬ Ska.Hot ovo →
    (∀ s f, ovo ≠ (Ovum.full s f).toNoun) → ∃ st', PGood3 Cls st' ∧ enc fl st' = c'

/-- **Every core the pill reaches is an encoded `PGood3` state.** -/
def PokeReachGood3 : Prop := ∀ cr, PokeReach cr → ∃ st, PGood3 Cls st ∧ enc fl st = cr

theorem pokeReachGood3 (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP)
    (hJA : Ar.jetRoot = jetRootP) (hR : SpRestGood3 fl Ar Cls env) (hC : SccLink fl Ar sccP)
    (hM : MonoLinkGood3 fl Ar Cls) (hO : OptLinkOn Cls Ar optP) (hK : SkaKeeps Ar) (hU : UnaryKeeps Ar Cls)
    (hS : SkaCodeKeeps Ar) (hSc : SccOfKeeps Ar) (hCK : UnaryCacheKeeps Ar Cls)
    (hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none) (hX : OtherKeeps3 fl Cls) : PokeReachGood3 fl Cls := by
  intro cr h
  induction h with
  | start => exact ⟨emptySt, good3_empty Cls, (cor_enc fl).symm⟩
  | @poke c ovo p c' _ hp hh ih =>
    obtain ⟨st, hg, rfl⟩ := ih
    by_cases e : ∃ s f, ovo = (Ovum.full s f).toNoun
    · obtain ⟨s, f, rfl⟩ := e
      rw [pokeModel_fullGood3 fl Ar Cls env hhe hth hsoft hrf hJA hR hC hM hO hK hU hS hSc hAt st hg s f,
        liftPoke_enc_fl] at hp
      cases e' : pokeS Ar st (Ovum.full s f) with
      | none => rw [e'] at hp; cases hp
      | some q =>
        rw [e'] at hp
        simp only [Option.map_some, Option.some.injEq, Noun.cell.injEq] at hp
        exact ⟨q.2, good3_full_step hK hU hS hSc hCK st s f q.1 q.2 hg e', hp.2⟩
    · exact hX st ovo p c' hg hp hh fun s f h => e ⟨s, f, h⟩

/-- **`pokeModel` on `%full` at every reachable core**, over `PGood3`. -/
theorem pokeModel_fullReach3 (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP)
    (hJA : Ar.jetRoot = jetRootP) (hR : SpRestGood3 fl Ar Cls env) (hC : SccLink fl Ar sccP)
    (hM : MonoLinkGood3 fl Ar Cls) (hO : OptLinkOn Cls Ar optP) (hK : SkaKeeps Ar) (hU : UnaryKeeps Ar Cls)
    (hS : SkaCodeKeeps Ar) (hSc : SccOfKeeps Ar) (hCK : UnaryCacheKeeps Ar Cls)
    (hAt : ∀ s a L j h, Ar.skaPoke s (A a) L j h = none) (hX : OtherKeeps3 fl Cls) :
    ∀ cr, CorIn cr → ∀ s f, pokeN cr (Ovum.full s f).toNoun =
      (liftPoke (enc fl) (pokeS Ar) cr (Ovum.full s f)).map fun r => C r.1.toNoun r.2 := by
  intro cr hc s f
  obtain ⟨st, hg, rfl⟩ :=
    pokeReachGood3 fl Ar Cls env hhe hth hsoft hrf hJA hR hC hM hO hK hU hS hSc hCK hAt hX cr hc.2.2
  exact pokeModel_fullGood3 fl Ar Cls env hhe hth hsoft hrf hJA hR hC hM hO hK hU hS hSc hAt st hg s f

end Links

/-- **`pokeModel_fullReach3` on track P's route** (`anaArmP`, `optimizeP`,
`sccOfP`, `jetRootP`, `OptTotal`): `SkaCodeKeeps` is proved
(`skaCodeKeeps_of_armP`); left: `SpRestGood3` (pill, `spRest` on `PGood3`
states), `SccImage` and `SccOfKeeps` (pill, `+scc-of` with `+tarjan`),
`MonoLinkGood3` (pill, `+compiled-mono`, track K), `JetsOfGood jetsOf`
(`+ska-cole-update`), `UnaryKeeps OptTotal` (track D), `UnaryCacheKeeps`
(track K), `OtherKeeps3` (pill, `%dire`, `%jets`, `%fast`). -/
theorem pokeModel_fullReachP3 (fl : Flags) (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun))
    (env : Env Noun) (hhe : env.he = heSock) (hth : env.threshold = 32)
    (hsoft : env.softSpot = softSpotF) (hrf : env.registerFast = registerFastP)
    {jet : Noun → Noun → (Bell → Option Datum) → Noun → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → Noun}
    {jetsOf : Noun → Noun → Noun → LongB FinMap → LongB FinMap → Noun} {newOf : Noun → Noun}
    (hA : Ar.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf)
    (hJA : Ar.jetRoot = jetRootP) (hOA : Ar.optimize = optimizeP) (hSA : Ar.sccOf = sccOfP)
    (hR : SpRestGood3 fl Ar OptTotal env) (hI : SccImage) (hSc : SccOfKeeps Ar) (hM : MonoLinkGood3 fl Ar OptTotal)
    (hJ : JetsOfGood jetsOf) (hU : UnaryKeeps Ar OptTotal) (hCK : UnaryCacheKeeps Ar OptTotal)
    (hX : OtherKeeps3 fl OptTotal) :
    ∀ cr, CorIn cr → ∀ s f, pokeN cr (Ovum.full s f).toNoun =
      (liftPoke (enc fl) (pokeS Ar) cr (Ovum.full s f)).map fun r => C r.1.toNoun r.2 :=
  pokeModel_fullReach3 fl Ar OptTotal env hhe hth hsoft hrf hJA hR (sccLink_of fl hSA hI) hM
    (optLinkOn_optimizeP hOA) (skaKeeps_of_armP Ar hA hJ) hU (skaCodeKeeps_of_armP Ar hA) hSc hCK
    (fun s a L j h => by rw [hA]; exact anaArmP_atom env jet fold frozen fuel bf regOf jetsOf newOf s a L j h) hX

end Compiler
end Formalization
