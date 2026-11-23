import lemmas.Ska.PokeBake
import lemmas.Ska.Statements

/-!
# `+poke` of the compiler, and the contract from the compilation track

A model of `+poke` (`nock-compilation.hoon`) on a state `CSt`: the parts of
`long-ska` the code table depends on (`LongB`, `PokeBake.lean`), the rest of
`long-ska` (`jets`, abstract), `jets-hot` (abstract) and the cache, whose
`mono`, `nary` and `sccs` maps are modelled and whose `inl` and `sure` maps
are abstract.  `+compiled-mono` (`compiledMono`), `+compiled-nary`
(`compiledNary`) and the `%full` and `%dire` branches are modelled arm by
arm; `+scc-of`, `+compile-unary`, `+compile-scc` (the callers of `+comp`),
`+optimize`, the analysis with its baking (`+ska-poke`, modelled as
`skaPokeB` in `PokeBake.lean`), the jetted-root test of `%full` and the
`%jets` and `%fast` branches (`+hot-diff`, `+hot-stale`, `+del-bells`,
`+ska-cole-settle`, `+ska-cole-restore`, `+register-template`) are the
parameters `Arms`.  `straight` and `straight-out` are one type here.

`pokeS_sound` proves `Sound lib (pokeS A) (InvS A ref)` (the shape of
`Gap.contract`), and `pokeS_invKept` the shape of `Gap.invKept`, for the
explicit invariant `InvS`: the code-table invariant `InvB` of
`PokeBake.lean` and `CacheOK` (every compiled form in the cache is what a
reference compiler `ref` gives the bell).  They assume `CompHyp`, which names
what the compilation track must supply (`contract`: the code `ref` gives a
bell of a table that satisfies `InvB` meets `BellContract`, against the
needs `ref` gives the other bells) and what the cache must keep, and
`AnaHyp`, what the analysis gives (`skaPokeB_sound`, with HImp).
-/

namespace Formalization
namespace SkaModel

open Nock Ana Bake

namespace PokeM

variable {M : Type → Type → Type} [Treap M] {Map : Type → Type} [HoonMap Map] {J H CR : Type}

/-! ## The model -/

/-- The cache: `mono`, `nary`, `sccs`, and the rest (`inl`, `sure`). -/
structure Cache (M : Type → Type → Type) (Map : Type → Type) (CR : Type) where
  mono : M Bell (Straight Map)
  nary : M Bell (Straight Map)
  sccs : M Bell (M Bell Unit)
  rest : CR

/-- The compiler's state. -/
structure CSt (M : Type → Type → Type) (Map : Type → Type) (J H CR : Type) where
  long : LongB M
  jets : J
  hot : H
  cache : Cache M Map CR

/-- The arms `+poke` calls that the model takes as parameters. -/
structure Arms (M : Type → Type → Type) (Map : Type → Type) (J H CR : Type) where
  /-- `+ska-poke` on `[&+sub fol]`: the root bell, the new code state, the
  new jets state, and `new` (the registrations, as their noun). -/
  skaPoke : Noun → Noun → LongB M → J → H → Option (Bell × LongB M × J × Noun)
  /-- The `%full` branch for a root that is a jetted arm with a hot driver:
  the straight with one `%jsf`. -/
  jetRoot : J → H → Bell → Option (Straight Map)
  /-- `+scc-of`. -/
  sccOf : Bell → LongB M → M Bell (M Bell Unit) → Option (M Bell Unit × M Bell (M Bell Unit))
  /-- `+compile-unary`. -/
  compileUnary : Bell → M Bell Unit → LongB M → J → H → Cache M Map CR →
    Option ((Straight Map × M Bell (Straight Map)) × Cache M Map CR)
  /-- `+compile-scc`. -/
  compileScc : M Bell Unit → LongB M → J → H → Cache M Map CR → Option (M Bell (Straight Map) × Cache M Map CR)
  /-- `+optimize`. -/
  optimize : Straight Map → Straight Map
  /-- The `%jets` branch: the stale bells, the jets state, `jets-hot`, the
  cache. -/
  jetsPoke : CSt M Map J H CR → Noun → Option (List Bell × J × H × Cache M Map CR)
  /-- The `%fast` branch: the jets state and the cache. -/
  fastPoke : CSt M Map J H CR → Bool → Noun → Option (J × Cache M Map CR)

variable (A : Arms M Map J H CR)

/-- `+compiled-mono`: the cached form, or `+compile-unary`'s, cached. -/
def compiledMono (st : CSt M Map J H CR) (b : Bell) (scc : M Bell Unit) : Option (Straight Map × Cache M Map CR) :=
  match Treap.get st.cache.mono b with
  | some s => some (s, st.cache)
  | none => (A.compileUnary b scc st.long st.jets st.hot st.cache).map fun r =>
      (r.1.1, { r.2 with mono := Treap.put r.2.mono b r.1.1 })

/-- `+compiled-nary`: the cached form, or `+compile-scc`'s. -/
def compiledNary (st : CSt M Map J H CR) (b : Bell) (scc : M Bell Unit) : Option (Straight Map × Cache M Map CR) :=
  match Treap.get st.cache.nary b with
  | some s => some (s, st.cache)
  | none => (A.compileScc scc st.long st.jets st.hot st.cache).bind fun r =>
      (Treap.get r.1 b).map fun s => (s, r.2)

/-- `+scc-of`, then `+compiled-mono` or `+compiled-nary`, then `+optimize`,
as the `%full` and `%dire` branches do. -/
def compileStep (st : CSt M Map J H CR) (b : Bell) (mono : Bool) : Option (Straight Map × CSt M Map J H CR) :=
  (A.sccOf b st.long st.cache.sccs).bind fun r =>
  let st1 : CSt M Map J H CR := { st with cache := { st.cache with sccs := r.2 } }
  ((if mono then compiledMono A st1 b r.1 else compiledNary A st1 b r.1)).map fun p =>
    (A.optimize p.1, { st1 with cache := p.2 })

/-- `+poke`, on a valid ovum. -/
def pokeS (st : CSt M Map J H CR) : Ovum → Option (Prod Map × CSt M Map J H CR)
  | Ovum.full s f => (A.skaPoke s f st.long st.jets st.hot).bind fun r =>
      let st1 : CSt M Map J H CR := { st with long := r.2.1, jets := r.2.2.1 }
      match A.jetRoot r.2.2.1 st.hot r.1 with
      | some out => some (Prod.ir r.1 out r.2.2.2, st1)
      | none => (compileStep A st1 r.1 true).map fun p => (Prod.ir r.1 p.1 r.2.2.2, p.2)
  | Ovum.dire b m => (compileStep A st b m).map fun p => (Prod.ir b p.1 (Noun.atom 0), p.2)
  | Ovum.jets p => (A.jetsPoke st p).map fun r =>
      (Prod.drop r.1, { st with jets := r.2.1, hot := r.2.2.1, cache := r.2.2.2 })
  | Ovum.fast r p => (A.fastPoke st r p).map fun q => (Prod.nil, { st with jets := q.1, cache := q.2 })

/-! ## The invariant and the hypotheses -/

/-- A reference compiler: the straight (before `+optimize`) the compiler
gives a bell, as a function of the persistent state. -/
abbrev Ref (M : Type → Type → Type) (Map : Type → Type) (J H : Type) :=
  LongB M → J → H → Bell → Bool → Option (Straight Map)

/-- The needs the reference compiler answers with. -/
def refN (ref : Ref M Map J H) (long : LongB M) (jets : J) (hot : H) : Needs := fun b m =>
  (ref long jets hot b m).map fun s => (A.optimize s).need

/-- Every compiled form in the cache is the reference compiler's. -/
def CacheOK (ref : Ref M Map J H) (long : LongB M) (jets : J) (hot : H) (c : Cache M Map CR) : Prop :=
  (∀ b s, Treap.get c.mono b = some s → ref long jets hot b true = some s) ∧
    ∀ b s, Treap.get c.nary b = some s → ref long jets hot b false = some s

/-- **The invariant of the compiler's state.** -/
def InvS (lib : Lib) (ref : Ref M Map J H) (st : CSt M Map J H CR) : Prop :=
  InvB lib st.long ∧ CacheOK ref st.long st.jets st.hot st.cache

/-- **What the compilation track and the cache must supply.** -/
structure CompHyp (lib : Lib) (ref : Ref M Map J H) : Prop where
  /-- `+compile-unary` gives the reference form, and keeps the cache. -/
  unary : ∀ b scc long jets hot c s n c', A.compileUnary b scc long jets hot c = some ((s, n), c') →
    ref long jets hot b true = some s ∧ (CacheOK ref long jets hot c → CacheOK ref long jets hot c')
  /-- `+compile-scc` gives the reference forms, and keeps the cache. -/
  scc : ∀ scc long jets hot c m c', A.compileScc scc long jets hot c = some (m, c') →
    (∀ b s, Treap.get m b = some s → ref long jets hot b false = some s) ∧
      (CacheOK ref long jets hot c → CacheOK ref long jets hot c')
  /-- The compiler answers every bell the reference compiler does. -/
  answers : ∀ st b m s, InvS lib ref st → ref st.long st.jets st.hot b m = some s →
    (compileStep A st b m).isSome
  /-- **The contract**: the code the reference compiler gives a bell of a
  table that satisfies `InvB`, optimized, meets `BellContract` against the
  needs it gives the other bells; a function by subject takes its subject
  whole. -/
  contract : ∀ long jets hot b m s, InvB lib long → ref long jets hot b m = some s →
    BellContract lib (refN A ref long jets hot) b m (A.optimize s) ∧
      (m = true → (A.optimize s).nargs = 1 ∧ (A.optimize s).need = NeedOrd.this)
  /-- What is compiled holds across `+ska-poke`. -/
  stable : ∀ s f long jets hot r b m x, A.skaPoke s f long jets hot = some r → InvB lib long →
    ref long jets hot b m = some x → ref r.2.1 r.2.2.1 hot b m = some x
  /-- The straight of a jetted root meets the contract of `%full`. -/
  jetRoot : ∀ s f long jets hot r out, A.skaPoke s f long jets hot = some r → InvB lib long →
    A.jetRoot r.2.2.1 hot r.1 = some out →
    out.nargs = 1 ∧ out.need = NeedOrd.this ∧
      ContractFwd lib (refN A ref r.2.1 r.2.2.1 hot) s f [s] out ∧
      ContractBwd lib (refN A ref r.2.1 r.2.2.1 hot) s f [s] out
  /-- `%jets` with no jet named keeps the cache (`+hot-stale` drops every
  form that changed). -/
  jets : ∀ st p r, ¬ HotOvum (Ovum.jets p) → A.jetsPoke st p = some r →
    CacheOK ref st.long st.jets st.hot st.cache → CacheOK ref st.long r.2.1 r.2.2.1 r.2.2.2
  /-- `%fast` keeps the cache (it drops the cache when the rings change). -/
  fast : ∀ st rs p r, A.fastPoke st rs p = some r →
    CacheOK ref st.long st.jets st.hot st.cache → CacheOK ref st.long r.1 st.hot r.2

/-- **What the analysis gives**: `+ska-poke` keeps `InvB`, and its root bell
has the poke's formula and fits its subject.  `skaPokeB_sound` proves the
first from HImp. -/
structure AnaHyp (lib : Lib) : Prop where
  ana : ∀ s f long jets hot r, A.skaPoke s f long jets hot = some r → InvB lib long →
    InvB lib r.2.1 ∧ r.1.fol = f ∧ Fits r.1.less s

/-! ## The compile step -/

theorem compileStep_spec {lib : Lib} {ref : Ref M Map J H} (hC : CompHyp A lib ref) {st st' : CSt M Map J H CR}
    {b : Bell} {m : Bool} {c : Straight Map} (hok : CacheOK ref st.long st.jets st.hot st.cache)
    (h : compileStep A st b m = some (c, st')) :
    ∃ s, ref st.long st.jets st.hot b m = some s ∧ c = A.optimize s ∧ st'.long = st.long ∧ st'.jets = st.jets ∧
      st'.hot = st.hot ∧ CacheOK ref st'.long st'.jets st'.hot st'.cache := by
  unfold compileStep at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨⟨scc, sccs⟩, _, ⟨s, cache'⟩, hc, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  suffices ref st.long st.jets st.hot b m = some s ∧ CacheOK ref st.long st.jets st.hot cache' from
    ⟨s, this.1, rfl, rfl, rfl, rfl, this.2⟩
  cases m with
  | true =>
    simp only [if_true, compiledMono] at hc
    split at hc
    · rename_i s0 hs0
      cases hc
      exact ⟨hok.1 b _ hs0, hok⟩
    · simp only [Option.map_eq_some_iff] at hc
      obtain ⟨⟨⟨s1, n1⟩, c1⟩, hu, he⟩ := hc
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨hr, hk⟩ := hC.unary _ _ _ _ _ _ _ _ _ hu
      refine ⟨hr, fun b' s' hs' => ?_, (hk hok).2⟩
      simp only [Treap.get_put] at hs'
      split at hs'
      · rename_i e; cases hs'; subst e; exact hr
      · exact (hk hok).1 b' s' hs'
  | false =>
    simp only [Bool.false_eq_true, if_false, compiledNary] at hc
    split at hc
    · rename_i s0 hs0
      cases hc
      exact ⟨hok.2 b _ hs0, hok⟩
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
      obtain ⟨⟨m1, c1⟩, hu, s1, hs1, he⟩ := hc
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨hr, hk⟩ := hC.scc _ _ _ _ _ _ _ hu
      exact ⟨hr b _ hs1, hk hok⟩

/-- **The needs of a state** are the reference compiler's. -/
theorem needOf_eq {lib : Lib} {ref : Ref M Map J H} (hC : CompHyp A lib ref) {st : CSt M Map J H CR}
    (hI : InvS lib ref st) : needOf (pokeS A) st = refN A ref st.long st.jets st.hot := by
  funext b m
  unfold needOf refN
  simp only [pokeS]
  cases hs : compileStep A st b m with
  | none =>
    cases hr : ref st.long st.jets st.hot b m with
    | none => rfl
    | some s =>
      have := hC.answers st b m s hI hr
      rw [hs] at this; cases this
  | some p =>
    obtain ⟨c, st'⟩ := p
    obtain ⟨s, hr, rfl, -⟩ := compileStep_spec A hC hI.2 hs
    simp [hr]

/-! ## The contract -/

/-- **The model of `+poke` is sound** (`Gap.contract`'s shape): from every
state that satisfies `InvS`, `%dire` and `%full` keep it, the needs only
grow, and the code they answer meets the contract. -/
theorem pokeS_sound {lib : Lib} {ref : Ref M Map J H} (hC : CompHyp A lib ref) (hA : AnaHyp A lib) :
    Sound lib (pokeS A) (InvS lib ref) where
  dire := by
    intro st b m p st' hI h
    simp only [pokeS, Option.map_eq_some_iff] at h
    obtain ⟨⟨c, st2⟩, hs, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨s, _, rfl, hl, hj, hh, hok⟩ := compileStep_spec A hC hI.2 hs
    have hI' : InvS lib ref st2 := ⟨hl ▸ hI.1, hok⟩
    refine ⟨hI', ?_⟩
    rw [needOf_eq A hC hI, needOf_eq A hC hI', hl, hj, hh]
    exact Needs.le_refl _
  full := by
    intro st s f p st' hI h
    simp only [pokeS, Option.bind_eq_some_iff] at h
    obtain ⟨r, hr, h⟩ := h
    obtain ⟨hB, -, -⟩ := hA.ana s f st.long st.jets st.hot r hr hI.1
    have hok1 : CacheOK ref r.2.1 r.2.2.1 st.hot st.cache :=
      ⟨fun b x hx => hC.stable s f _ _ _ r b true x hr hI.1 (hI.2.1 b x hx),
       fun b x hx => hC.stable s f _ _ _ r b false x hr hI.1 (hI.2.2 b x hx)⟩
    have hI1 : InvS lib ref ({ st with long := r.2.1, jets := r.2.2.1 } : CSt M Map J H CR) := ⟨hB, hok1⟩
    have hle : needOf (pokeS A) st ≤ needOf (pokeS A) ({ st with long := r.2.1, jets := r.2.2.1 } : CSt M Map J H CR) := by
      rw [needOf_eq A hC hI, needOf_eq A hC hI1]
      intro b m x hx
      simp only [refN, Option.map_eq_some_iff] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, hC.stable s f _ _ _ r b m y hr hI.1 hy, rfl⟩
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨hI1, hle⟩
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨c, st2⟩, hs, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, rfl⟩ := he
      obtain ⟨_, _, rfl, hl, hj, hh, hok⟩ := compileStep_spec A hC hI1.2 hs
      have hI2 : InvS lib ref st2 := ⟨by rw [hl]; exact hB, hok⟩
      refine ⟨hI2, Needs.le_trans hle ?_⟩
      rw [needOf_eq A hC hI1, needOf_eq A hC hI2, hl, hj, hh]
      exact Needs.le_refl _
  dire_code := by
    intro st b m p st' hI h
    simp only [pokeS, Option.map_eq_some_iff] at h
    obtain ⟨⟨c, st2⟩, hs, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨s, hr, rfl, hl, hj, hh, hok⟩ := compileStep_spec A hC hI.2 hs
    have hI' : InvS lib ref st2 := ⟨hl ▸ hI.1, hok⟩
    refine ⟨b, A.optimize s, Noun.atom 0, rfl, ?_⟩
    rw [needOf_eq A hC hI', hl, hj, hh]
    exact (hC.contract _ _ _ b m s hI.1 hr).1
  full_code := by
    intro st s f p st' hI h
    simp only [pokeS, Option.bind_eq_some_iff] at h
    obtain ⟨r, hr, h⟩ := h
    obtain ⟨hB, hfol, hfit⟩ := hA.ana s f st.long st.jets st.hot r hr hI.1
    have hok1 : CacheOK ref r.2.1 r.2.2.1 st.hot st.cache :=
      ⟨fun b x hx => hC.stable s f _ _ _ r b true x hr hI.1 (hI.2.1 b x hx),
       fun b x hx => hC.stable s f _ _ _ r b false x hr hI.1 (hI.2.2 b x hx)⟩
    have hI1 : InvS lib ref ({ st with long := r.2.1, jets := r.2.2.1 } : CSt M Map J H CR) := ⟨hB, hok1⟩
    split at h
    · rename_i out hout
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h1, h2, h3, h4⟩ := hC.jetRoot s f _ _ _ r out hr hI.1 hout
      refine ⟨r.1, out, r.2.2.2, rfl, h1, h2, ?_, ?_⟩
      · rw [needOf_eq A hC hI1]; exact h3
      · rw [needOf_eq A hC hI1]; exact h4
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨c, st2⟩, hs, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨x, hx, rfl, hl, hj, hh, hok⟩ := compileStep_spec A hC hI1.2 hs
      have hI2 : InvS lib ref st2 := ⟨by rw [hl]; exact hB, hok⟩
      obtain ⟨hbc, hn⟩ := hC.contract _ _ _ r.1 true x hB hx
      obtain ⟨hn1, hn2⟩ := hn rfl
      refine ⟨r.1, A.optimize x, r.2.2.2, rfl, hn1, hn2, ?_⟩
      have := hbc s hfit [s] (by simp)
      rw [needOf_eq A hC hI2, hl, hj, hh, ← hfol]
      exact this

/-- **Every poke that names no jet keeps the invariant** (`Gap.invKept`'s
shape). -/
theorem pokeS_invKept {lib : Lib} {ref : Ref M Map J H} (hC : CompHyp A lib ref) (hA : AnaHyp A lib) :
    ∀ st ov p st', InvS lib ref st → ¬ HotOvum ov → pokeS A st ov = some (p, st') → InvS lib ref st' := by
  intro st ov p st' hI hhot h
  have hS := pokeS_sound A hC hA
  cases ov with
  | full s f => exact (hS.full st s f p st' hI h).1
  | dire b m => exact (hS.dire st b m p st' hI h).1
  | jets q =>
    simp only [pokeS, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    exact ⟨hI.1, hC.jets st q r hhot hr hI.2⟩
  | fast rs q =>
    simp only [pokeS, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    exact ⟨hI.1, hC.fast st rs q r hr hI.2⟩

/-- **The invariant holds of the bunt state** (`Gap.invStart`'s shape, for
the empty state the pill's core holds). -/
theorem invS_init (lib : Lib) (ref : Ref M Map J H) (jets : J) (hot : H) (rest : CR) :
    InvS lib ref (⟨⟨Treap.empty, Treap.empty, Treap.empty⟩, jets, hot,
      ⟨Treap.empty, Treap.empty, Treap.empty, rest⟩⟩ : CSt M Map J H CR) :=
  ⟨InvB.init lib, fun _ _ h => by simp [Treap.get_empty] at h, fun _ _ h => by simp [Treap.get_empty] at h⟩

end PokeM

end SkaModel
end Formalization
