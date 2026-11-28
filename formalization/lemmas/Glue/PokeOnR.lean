import lemmas.Glue.PokeOn
import lemmas.Ska.CompRingSem

/-!
# Glue: the `PokeM` chain with the cache compared up to the rings (track G, sixteenth pass;
misfit 11)

Track K's finding (`tools/hoon/ringdump.hoon`, part B): after a `%jets ~` a callee registered
after its caller gets a ring, the cached caller keeps `%jmp` / `%jsp` (`+hot-stale` drops
nothing with no driver), and a fresh compile emits `%jmf` / `%jsf`.  So `CacheOK` (every cached
form IS the reference's) is false of the real compiler; it holds only up to the rings.  Here
the chain of `PokeOn.lean` is re-proved with the cache compared up to `RingSame`:

* `RingSameN s s'`: the blocks have the same erasures (K's `RingSame`), same need, same
  argument count.  `SameO A s s'`: `RingSameN` of the OPTIMIZED forms (what the poke returns
  is `A.optimize` of the cached form).
* **`CacheOKR A ref long jets hot c`**: every cached `s` has some `s'` with
  `ref .. = some s'` and `SameO A s s'`.  `cacheOKR_of_ok`: `CacheOK` gives it.
  `cacheOKR_of_raw`: the raw form (`RingSameN s s'`, the LEDGER's statement) gives it under the
  optimizer leaf `OptRing A` (`+optimize` keeps `RingSameN`; the Hoon's passes treat `%caf`,
  `%csf`, `%jmf`, `%jsf` as `%cal`, `%csl`, `%jmp`, `%jsp`, lines 7160 to 7234).
* `InvSR := InvB ∧ CacheOKR`; `CompStateOnR`, `CompHypOnR`: `CompHypOn` with `unary`, `scc`,
  `stable` up to `SameO` and `CacheOKR` in `unary`, `scc`, `jets`, `fast`.
* **`pokeS_soundOnR`**: a cached straight's contract from its reference form's, by K's
  `execEntry_ringEq` (`bellContract_sameO`); the needs are equal (`SameO` keeps the need).
  `pokeS_invKeptOnR`, `gap_of_armPMOnR`, `fullAnswers_of_cgMPOnR`, `halting_of_cgMPOnR`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Glue

open Nock Ana Bake PokeM

section Gen

variable {M : Type → Type → Type} [Treap M] {Map : Type → Type} [HoonMap Map] {J H CR : Type}

/-! ## The same up to rings -/

/-- **Two straights the same up to rings**: blocks with the same erasures, same need, same
argument count (K's `RingRel` on two results). -/
def RingSameN (s s' : Straight Map) : Prop := Comp.RingSame s s' ∧ s.need = s'.need ∧ s.nargs = s'.nargs

theorem ringSameN_refl (s : Straight Map) : RingSameN s s := ⟨fun _ => rfl, rfl, rfl⟩

theorem ringSameN_trans {s1 s2 s3 : Straight Map} (h1 : RingSameN s1 s2) (h2 : RingSameN s2 s3) : RingSameN s1 s3 :=
  ⟨fun k => (h1.1 k).trans (h2.1 k), h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩

theorem ringSameN_symm {s1 s2 : Straight Map} (h : RingSameN s1 s2) : RingSameN s2 s1 :=
  ⟨Comp.ringSame_symm h.1, h.2.1.symm, h.2.2.symm⟩

variable (A : Arms M Map J H CR)

/-- **The optimized forms are the same up to rings.** -/
def SameO (s s' : Straight Map) : Prop := RingSameN (A.optimize s) (A.optimize s')

theorem sameO_refl (s : Straight Map) : SameO A s s := ringSameN_refl _

variable {A}

theorem sameO_trans {s1 s2 s3 : Straight Map} (h1 : SameO A s1 s2) (h2 : SameO A s2 s3) : SameO A s1 s3 :=
  ringSameN_trans h1 h2

variable (A)

/-- **Leaf (H): `+optimize` keeps `RingSameN`** (the passes treat the ring ops as the plain ones). -/
def OptRing : Prop := ∀ s s' : Straight Map, RingSameN s s' → RingSameN (A.optimize s) (A.optimize s')

/-- **Every cached form is the reference compiler's, up to rings** (of the optimized forms). -/
def CacheOKR (ref : Ref M Map J H) (long : LongB M) (jets : J) (hot : H) (c : Cache M Map CR) : Prop :=
  (∀ b s, Treap.get c.mono b = some s → ∃ s', ref long jets hot b true = some s' ∧ SameO A s s') ∧
    ∀ b s, Treap.get c.nary b = some s → ∃ s', ref long jets hot b false = some s' ∧ SameO A s s'

/-- **The raw form** (the LEDGER's statement): `RingSameN` of the cached and reference forms. -/
def CacheOKRaw (ref : Ref M Map J H) (long : LongB M) (jets : J) (hot : H) (c : Cache M Map CR) : Prop :=
  (∀ b s, Treap.get c.mono b = some s → ∃ s', ref long jets hot b true = some s' ∧ RingSameN s s') ∧
    ∀ b s, Treap.get c.nary b = some s → ∃ s', ref long jets hot b false = some s' ∧ RingSameN s s'

variable {A}

theorem cacheOKR_of_ok {ref : Ref M Map J H} {long : LongB M} {jets : J} {hot : H} {c : Cache M Map CR}
    (h : CacheOK ref long jets hot c) : CacheOKR A ref long jets hot c :=
  ⟨fun b s hs => ⟨s, h.1 b s hs, sameO_refl A s⟩, fun b s hs => ⟨s, h.2 b s hs, sameO_refl A s⟩⟩

theorem cacheOKR_of_raw (hO : OptRing A) {ref : Ref M Map J H} {long : LongB M} {jets : J} {hot : H}
    {c : Cache M Map CR} (h : CacheOKRaw ref long jets hot c) : CacheOKR A ref long jets hot c :=
  ⟨fun b s hs => (h.1 b s hs).imp fun _ ⟨e, r⟩ => ⟨e, hO _ _ r⟩,
   fun b s hs => (h.2 b s hs).imp fun _ ⟨e, r⟩ => ⟨e, hO _ _ r⟩⟩

variable (A)

/-- **The invariant of the compiler's state, up to rings.** -/
def InvSR (lib : Lib) (ref : Ref M Map J H) (st : CSt M Map J H CR) : Prop :=
  InvB lib st.long ∧ CacheOKR A ref st.long st.jets st.hot st.cache

/-! ## The contract transfers up to rings -/

section Contract
variable {lib : Lib} {N : Needs}

theorem contractFwd_ringSame {s f : Noun} {args : List Noun} {c c' : Straight Map} (h : Comp.RingSame c c')
    (hc : ContractFwd lib N s f args c') : ContractFwd lib N s f args c := by
  intro σ Inv ν O n gul ti tm r h1 h2 h3 h4 st hst hfr
  obtain ⟨ton, st', e, hr⟩ := hc σ Inv ν O n gul ti tm r h1 h2 h3 h4 st hst hfr
  exact ⟨ton, st', by rw [Comp.execEntry_ringEq h]; exact e, hr⟩

theorem contractBwd_ringSame {s f : Noun} {args : List Noun} {c c' : Straight Map} (h : Comp.RingSame c c')
    (hc : ContractBwd lib N s f args c') : ContractBwd lib N s f args c := by
  intro σ Inv ν O gul ti tm h1 h2 h3 st ton st' hst hfr e
  rw [Comp.execEntry_ringEq h] at e
  exact hc σ Inv ν O gul ti tm h1 h2 h3 st ton st' hst hfr e

theorem bellContract_ringSameN {b : Bell} {m : Bool} {c c' : Straight Map} (h : RingSameN c c')
    (hc : BellContract lib N b m c') : BellContract lib N b m c := by
  intro s hs args ha
  rw [h.2.1] at ha
  obtain ⟨h1, h2⟩ := hc s hs args ha
  exact ⟨contractFwd_ringSame h.1 h1, contractBwd_ringSame h.1 h2⟩

/-- **A cached straight's contract from its reference form's.** -/
theorem bellContract_sameO {b : Bell} {m : Bool} {s0 s : Straight Map} (h : SameO A s0 s)
    (hc : BellContract lib N b m (A.optimize s)) : BellContract lib N b m (A.optimize s0) :=
  bellContract_ringSameN h hc

end Contract

/-! ## The chain over reached states, up to rings -/

/-- **`CompStateOn` up to rings**: `unary`, `scc`, `stable` give the reference forms up to
`SameO`; the cache facts are `CacheOKR`. -/
structure CompStateOnR (lib : Lib) (ref : Ref M Map J H) (I : CSt M Map J H CR → Prop)
    (Rd : CSt M Map J H CR → Bell → Prop) : Prop where
  unary : ∀ (st : CSt M Map J H CR) b q s n c', Rd st b → A.sccOf b st.long st.cache.sccs = some q →
    A.compileUnary b q.1 st.long st.jets st.hot { st.cache with sccs := q.2 } = some ((s, n), c') →
    (∃ s', ref st.long st.jets st.hot b true = some s' ∧ SameO A s s') ∧
      (CacheOKR A ref st.long st.jets st.hot st.cache → CacheOKR A ref st.long st.jets st.hot c')
  scc : ∀ (st : CSt M Map J H CR) b q m c', I st → A.sccOf b st.long st.cache.sccs = some q →
    A.compileScc q.1 st.long st.jets st.hot { st.cache with sccs := q.2 } = some (m, c') →
    (∀ b' s, Treap.get m b' = some s → ∃ s', ref st.long st.jets st.hot b' false = some s' ∧ SameO A s s') ∧
      (CacheOKR A ref st.long st.jets st.hot st.cache → CacheOKR A ref st.long st.jets st.hot c')
  answers : ∀ (st : CSt M Map J H CR) b m s, Rd st b → InvSR A lib ref st →
    ref st.long st.jets st.hot b m = some s → (compileStep A st b m).isSome
  stable : ∀ (st : CSt M Map J H CR) s f r b m x, I st → A.skaPoke s f st.long st.jets st.hot = some r →
    InvB lib st.long → ref st.long st.jets st.hot b m = some x →
      ∃ x', ref r.2.1 r.2.2.1 st.hot b m = some x' ∧ SameO A x x'
  jetRoot : ∀ (st : CSt M Map J H CR) s f r out, I st → A.skaPoke s f st.long st.jets st.hot = some r →
    InvB lib st.long → A.jetRoot r.2.2.1 st.hot r.1 = some out →
    out.nargs = 1 ∧ out.need = NeedOrd.this ∧
      ContractFwd lib (refN A ref r.2.1 r.2.2.1 st.hot) s f [s] out ∧
      ContractBwd lib (refN A ref r.2.1 r.2.2.1 st.hot) s f [s] out
  jets : ∀ st p r, I st → ¬ HotOvum (Ovum.jets p) → A.jetsPoke st p = some r →
    CacheOKR A ref st.long st.jets st.hot st.cache → CacheOKR A ref st.long r.2.1 r.2.2.1 r.2.2.2
  fast : ∀ st rs p r, I st → A.fastPoke st rs p = some r →
    CacheOKR A ref st.long st.jets st.hot st.cache → CacheOKR A ref st.long r.1 st.hot r.2

/-- **`CompHypOn` up to rings** (the contract as before, of the reference forms). -/
structure CompHypOnR (lib : Lib) (ref : Ref M Map J H) (I : CSt M Map J H CR → Prop)
    (Rd : CSt M Map J H CR → Bell → Prop) : Prop extends CompStateOnR A lib ref I Rd where
  contract : ∀ (st : CSt M Map J H CR) b m s, Rd st b → InvB lib st.long →
    ref st.long st.jets st.hot b m = some s →
    BellContract lib (refN A ref st.long st.jets st.hot) b m (A.optimize s) ∧
      (m = true → (A.optimize s).nargs = 1 ∧ (A.optimize s).need = NeedOrd.this)

variable {A}
variable {lib : Lib} {ref : Ref M Map J H} {I : CSt M Map J H CR → Prop} {Rd : CSt M Map J H CR → Bell → Prop}

/-- **Exact `CompStateOn` gives the one up to rings** when the cache facts are proved up to rings. -/
theorem compStateOnR_of (hC : CompStateOn A lib ref I Rd)
    (hu : ∀ (st : CSt M Map J H CR) b q s n c', Rd st b → A.sccOf b st.long st.cache.sccs = some q →
      A.compileUnary b q.1 st.long st.jets st.hot { st.cache with sccs := q.2 } = some ((s, n), c') →
      CacheOKR A ref st.long st.jets st.hot st.cache → CacheOKR A ref st.long st.jets st.hot c')
    (hs : ∀ (st : CSt M Map J H CR) b q m c', I st → A.sccOf b st.long st.cache.sccs = some q →
      A.compileScc q.1 st.long st.jets st.hot { st.cache with sccs := q.2 } = some (m, c') →
      CacheOKR A ref st.long st.jets st.hot st.cache → CacheOKR A ref st.long st.jets st.hot c')
    (ha : ∀ (st : CSt M Map J H CR) b m s, Rd st b → InvSR A lib ref st →
      ref st.long st.jets st.hot b m = some s → (compileStep A st b m).isSome)
    (hj : ∀ st p r, I st → ¬ HotOvum (Ovum.jets p) → A.jetsPoke st p = some r →
      CacheOKR A ref st.long st.jets st.hot st.cache → CacheOKR A ref st.long r.2.1 r.2.2.1 r.2.2.2)
    (hf : ∀ st rs p r, I st → A.fastPoke st rs p = some r →
      CacheOKR A ref st.long st.jets st.hot st.cache → CacheOKR A ref st.long r.1 st.hot r.2) :
    CompStateOnR A lib ref I Rd where
  unary := fun st b q s n c' hrd hq hu' =>
    ⟨⟨s, (hC.unary st b q s n c' hrd hq hu').1, sameO_refl A s⟩, hu st b q s n c' hrd hq hu'⟩
  scc := fun st b q m c' hi hq hs' =>
    ⟨fun b' s h => ⟨s, (hC.scc st b q m c' hi hq hs').1 b' s h, sameO_refl A s⟩, hs st b q m c' hi hq hs'⟩
  answers := ha
  stable := fun st s f r b m x hi hr hB hx => ⟨x, hC.stable st s f r b m x hi hr hB hx, sameO_refl A x⟩
  jetRoot := hC.jetRoot
  jets := hj
  fast := hf

/-- `compileStep_specOn` up to rings: the step returns `A.optimize s0` with `s0` the same up to
rings as the reference form `s`. -/
theorem compileStep_specOnR (hC : CompStateOnR A lib ref I Rd) {st st' : CSt M Map J H CR}
    {b : Bell} {m : Bool} {c : Straight Map} (hrd : Rd st b) (hi : m = false → I st)
    (hok : CacheOKR A ref st.long st.jets st.hot st.cache)
    (h : compileStep A st b m = some (c, st')) :
    ∃ s0 s, ref st.long st.jets st.hot b m = some s ∧ SameO A s0 s ∧ c = A.optimize s0 ∧ st'.long = st.long ∧
      st'.jets = st.jets ∧ st'.hot = st.hot ∧ CacheOKR A ref st'.long st'.jets st'.hot st'.cache := by
  unfold compileStep at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨⟨scc, sccs⟩, hq, ⟨s0, cache'⟩, hc, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  suffices (∃ s, ref st.long st.jets st.hot b m = some s ∧ SameO A s0 s) ∧
      CacheOKR A ref st.long st.jets st.hot cache' by
    obtain ⟨⟨s, hs, hso⟩, hk⟩ := this
    exact ⟨s0, s, hs, hso, rfl, rfl, rfl, rfl, hk⟩
  cases m with
  | true =>
    simp only [if_true, compiledMono] at hc
    split at hc
    · rename_i s1 hs1
      cases hc
      exact ⟨hok.1 b _ hs1, hok⟩
    · simp only [Option.map_eq_some_iff] at hc
      obtain ⟨⟨⟨s1, n1⟩, c1⟩, hu, he⟩ := hc
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨hr, hk⟩ := hC.unary st b (scc, sccs) s1 n1 c1 hrd hq hu
      refine ⟨hr, fun b' s' hs' => ?_, (hk hok).2⟩
      simp only [Treap.get_put] at hs'
      split at hs'
      · rename_i e; cases hs'; subst e; exact hr
      · exact (hk hok).1 b' s' hs'
  | false =>
    simp only [Bool.false_eq_true, if_false, compiledNary] at hc
    split at hc
    · rename_i s1 hs1
      cases hc
      exact ⟨hok.2 b _ hs1, hok⟩
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
      obtain ⟨⟨m1, c1⟩, hu, s1, hs1, he⟩ := hc
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨hr, hk⟩ := hC.scc st b (scc, sccs) m1 c1 (hi rfl) hq hu
      exact ⟨hr b _ hs1, hk hok⟩

/-- `needOf_eqOn` up to rings (the need is kept by `SameO`). -/
theorem needOf_eqOnR (hC : CompStateOnR A lib ref I Rd) {st : CSt M Map J H CR} (hrd : ∀ b, Rd st b)
    (hi : I st) (hI : InvSR A lib ref st) : needOf (pokeS A) st = refN A ref st.long st.jets st.hot := by
  funext b m
  unfold needOf refN
  simp only [pokeS]
  cases hs : compileStep A st b m with
  | none =>
    cases hr : ref st.long st.jets st.hot b m with
    | none => rfl
    | some s =>
      have := hC.answers st b m s (hrd b) hI hr
      rw [hs] at this; cases this
  | some p =>
    obtain ⟨c, st'⟩ := p
    obtain ⟨s0, s, hr, hso, rfl, -⟩ := compileStep_specOnR hC (hrd b) (fun _ => hi) hI.2 hs
    simp [hr, hso.2.1]

/-- The cache facts carried across `+ska-poke` by `stable` (up to rings). -/
theorem cacheOKR_stable (hC : CompStateOnR A lib ref I Rd) {st : CSt M Map J H CR} {s f : Noun}
    {r : Bell × LongB M × J × Noun} (hi : I st) (hr : A.skaPoke s f st.long st.jets st.hot = some r)
    (hB : InvB lib st.long) (hok : CacheOKR A ref st.long st.jets st.hot st.cache) :
    CacheOKR A ref r.2.1 r.2.2.1 st.hot st.cache :=
  ⟨fun b x hx => by
    obtain ⟨y, hy, h1⟩ := hok.1 b x hx
    obtain ⟨z, hz, h2⟩ := hC.stable st s f r b true y hi hr hB hy
    exact ⟨z, hz, sameO_trans h1 h2⟩,
   fun b x hx => by
    obtain ⟨y, hy, h1⟩ := hok.2 b x hx
    obtain ⟨z, hz, h2⟩ := hC.stable st s f r b false y hi hr hB hy
    exact ⟨z, hz, sameO_trans h1 h2⟩⟩

/-- **`pokeS_sound` over the reached states, the cache up to rings.** -/
theorem pokeS_soundOnR (hC : CompHypOnR A lib ref I Rd) (hR : ReachOn A I Rd) (hA : AnaHyp A lib) :
    Sound lib (pokeS A) (fun st => InvSR A lib ref st ∧ I st) where
  dire := by
    intro st b m p st' hI h
    have hI'' : I st' := hR.kept st _ p st' hI.2 (not_hot_dire b m) h
    simp only [pokeS, Option.map_eq_some_iff] at h
    obtain ⟨⟨c, st2⟩, hs, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨-, s, _, _, rfl, hl, hj, hh, hok⟩ :=
      compileStep_specOnR hC.toCompStateOnR (hR.now st b hI.2) (fun _ => hI.2) hI.1.2 hs
    have hI' : InvSR A lib ref st2 := ⟨hl ▸ hI.1.1, hok⟩
    refine ⟨⟨hI', hI''⟩, ?_⟩
    rw [needOf_eqOnR hC.toCompStateOnR (fun b => hR.now st b hI.2) hI.2 hI.1,
      needOf_eqOnR hC.toCompStateOnR (fun b => hR.now st2 b hI'') hI'' hI', hl, hj, hh]
    exact Needs.le_refl _
  full := by
    intro st s f p st' hI h
    have hI' : I st' := hR.kept st _ p st' hI.2 (not_hot_full s f) h
    simp only [pokeS, Option.bind_eq_some_iff] at h
    obtain ⟨r, hr, h⟩ := h
    obtain ⟨hB, -, -⟩ := hA.ana s f st.long st.jets st.hot r hr hI.1.1
    have hok1 : CacheOKR A ref r.2.1 r.2.2.1 st.hot st.cache :=
      cacheOKR_stable hC.toCompStateOnR hI.2 hr hI.1.1 hI.1.2
    have hle : ∀ st2 : CSt M Map J H CR, st2.long = r.2.1 → st2.jets = r.2.2.1 → st2.hot = st.hot → I st2 →
        InvSR A lib ref st2 → needOf (pokeS A) st ≤ needOf (pokeS A) st2 := by
      intro st2 hl hj hh hI2 hS2
      rw [needOf_eqOnR hC.toCompStateOnR (fun b => hR.now st b hI.2) hI.2 hI.1,
        needOf_eqOnR hC.toCompStateOnR (fun b => hR.now st2 b hI2) hI2 hS2, hl, hj, hh]
      intro b m x hx
      simp only [refN, Option.map_eq_some_iff] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨y', hy', hso⟩ := hC.stable st s f r b m y hI.2 hr hI.1.1 hy
      exact ⟨y', hy', hso.2.1.symm⟩
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨⟨⟨hB, hok1⟩, hI'⟩, hle _ rfl rfl rfl hI' ⟨hB, hok1⟩⟩
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨c, st2⟩, hs, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, rfl⟩ := he
      obtain ⟨-, _, _, _, rfl, hl, hj, hh, hok⟩ :=
        compileStep_specOnR hC.toCompStateOnR (hR.ana st s f r hI.2 hr) (fun e => by cases e) hok1 hs
      have hI2 : InvSR A lib ref st2 := ⟨by rw [hl]; exact hB, hok⟩
      exact ⟨⟨hI2, hI'⟩, hle st2 hl hj hh hI' hI2⟩
  dire_code := by
    intro st b m p st' hI h
    have hI'' : I st' := hR.kept st _ p st' hI.2 (not_hot_dire b m) h
    simp only [pokeS, Option.map_eq_some_iff] at h
    obtain ⟨⟨c, st2⟩, hs, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨s0, s, hr, hso, rfl, hl, hj, hh, hok⟩ :=
      compileStep_specOnR hC.toCompStateOnR (hR.now st b hI.2) (fun _ => hI.2) hI.1.2 hs
    have hI' : InvSR A lib ref st2 := ⟨hl ▸ hI.1.1, hok⟩
    refine ⟨b, A.optimize s0, Noun.atom 0, rfl, ?_⟩
    rw [needOf_eqOnR hC.toCompStateOnR (fun b => hR.now st2 b hI'') hI'' hI', hl, hj, hh]
    exact bellContract_sameO _ hso (hC.contract st b m s (hR.now st b hI.2) hI.1.1 hr).1
  full_code := by
    intro st s f p st' hI h
    have hI'' : I st' := hR.kept st _ p st' hI.2 (not_hot_full s f) h
    simp only [pokeS, Option.bind_eq_some_iff] at h
    obtain ⟨r, hr, h⟩ := h
    obtain ⟨hB, hfol, hfit⟩ := hA.ana s f st.long st.jets st.hot r hr hI.1.1
    have hok1 : CacheOKR A ref r.2.1 r.2.2.1 st.hot st.cache :=
      cacheOKR_stable hC.toCompStateOnR hI.2 hr hI.1.1 hI.1.2
    have hI1 : InvSR A lib ref (midSt st r) := ⟨hB, hok1⟩
    split at h
    · rename_i out hout
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h1, h2, h3, h4⟩ := hC.jetRoot st s f r out hI.2 hr hI.1.1 hout
      refine ⟨r.1, out, r.2.2.2, rfl, h1, h2, ?_, ?_⟩
      · rw [needOf_eqOnR hC.toCompStateOnR (fun b => hR.now _ b hI'') hI'' hI1]; exact h3
      · rw [needOf_eqOnR hC.toCompStateOnR (fun b => hR.now _ b hI'') hI'' hI1]; exact h4
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨c, st2⟩, hs, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hrd := hR.ana st s f r hI.2 hr
      obtain ⟨x0, x, hx, hso, rfl, hl, hj, hh, hok⟩ :=
        compileStep_specOnR hC.toCompStateOnR hrd (fun e => by cases e) hok1 hs
      have hI2 : InvSR A lib ref st2 := ⟨by rw [hl]; exact hB, hok⟩
      obtain ⟨hbc, hn⟩ := hC.contract (midSt st r) r.1 true x hrd hB hx
      obtain ⟨hn1, hn2⟩ := hn rfl
      refine ⟨r.1, A.optimize x0, r.2.2.2, rfl, hso.2.2.trans hn1, hso.2.1.trans hn2, ?_⟩
      have := bellContract_sameO _ hso hbc s hfit [s] (by simp)
      rw [needOf_eqOnR hC.toCompStateOnR (fun b => hR.now st2 b hI'') hI'' hI2, hl, hj, hh, ← hfol]
      exact this

/-- **`pokeS_invKept` over the reached states, the cache up to rings.** -/
theorem pokeS_invKeptOnR (hC : CompHypOnR A lib ref I Rd) (hR : ReachOn A I Rd) (hA : AnaHyp A lib) :
    ∀ st ov p st', (InvSR A lib ref st ∧ I st) → ¬ HotOvum ov → pokeS A st ov = some (p, st') →
      (InvSR A lib ref st' ∧ I st') := by
  intro st ov p st' hI hhot h
  have hS := pokeS_soundOnR hC hR hA
  have hI' : I st' := hR.kept st ov p st' hI.2 hhot h
  cases ov with
  | full s f => exact (hS.full st s f p st' hI h).1
  | dire b m => exact (hS.dire st b m p st' hI h).1
  | jets q =>
    simp only [pokeS, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    exact ⟨⟨hI.1.1, hC.jets st q r hI.2 hhot hr hI.1.2⟩, hI'⟩
  | fast rs q =>
    simp only [pokeS, Option.map_eq_some_iff] at h
    obtain ⟨r, hr, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    exact ⟨⟨hI.1.1, hC.fast st rs q r hI.2 hr hI.1.2⟩, hI'⟩

variable (A)

/-- **The invariant of the sixteenth assembly**: `InvSR`, the memo's lack of callees, and `I`. -/
def InvSMIR (lib : Lib) (ref : Ref M Map J H) (I : CSt M Map J H CR → Prop) (st : CSt M Map J H CR) : Prop :=
  (InvSR A lib ref st ∧ MemoNoCallees st.long.memo) ∧ I st

/-- **`RootAnswers` at the `I` states, up to rings.** -/
def RootAnswersOnR (lib : Lib) (ref : Ref M Map J H) (I : CSt M Map J H CR → Prop) : Prop :=
  ∀ (st : CSt M Map J H CR) s f r, I st → InvSR A lib ref st → A.skaPoke s f st.long st.jets st.hot = some r →
    A.jetRoot r.2.2.1 st.hot r.1 = none → ∃ x, ref r.2.1 r.2.2.1 st.hot r.1 true = some x

/-- `RootAnswers` gives it. -/
theorem rootAnswersOnR_of {lib : Lib} {ref : Ref M Map J H} (I : CSt M Map J H CR → Prop)
    (h : ∀ (st : CSt M Map J H CR) s f r, A.skaPoke s f st.long st.jets st.hot = some r → InvB lib st.long →
      A.jetRoot r.2.2.1 st.hot r.1 = none → ∃ x, ref r.2.1 r.2.2.1 st.hot r.1 true = some x) :
    RootAnswersOnR A lib ref I :=
  fun st s f r _ hS hk hj => h st s f r hk hS.1 hj

end Gen

section P

open Compiler Pill Hoon

variable {M : Type → Type → Type} [Treap M] {Map : Type → Type} [HoonMap Map] {J H CR R : Type}

/-- **`fullAnswers_of_cgMPOn` up to rings.** -/
theorem fullAnswers_of_cgMPOnR (A : Arms M Map J H CR) {lib : Lib} {ref : Ref M Map J H}
    {I : CSt M Map J H CR → Prop} {Rd : CSt M Map J H CR → Bell → Prop} {env : Env R}
    {jet : H → J → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool} {bf : BEnv M → Nat}
    {regOf : J → R} {jetsOf : H → J → R → LongB M → LongB M → J} {newOf : R → Noun}
    (hC : CompHypOnR A lib ref I Rd) (hR : ReachOn A I Rd)
    (hA : A.skaPoke = anaArmP env jet fold frozen (anaFuel env regOf) bf regOf jetsOf newOf)
    (hcg : CgHalts (M := M) lib env regOf)
    (hb : BakeEnds lib env jet fold frozen (anaFuel env regOf) bf regOf) (hr : RootAnswersOnR A lib ref I) :
    FullAnswers (pokeS A) (InvSMIR A lib ref I) := by
  intro st s f1 f2 hI
  obtain ⟨r, hk⟩ := anaArmP_someN jetsOf newOf (anaEndsN_of_halts (anaHalts_of_cgHalts hcg)) hb
    (finalEnds_always lib env jet fold frozen _ regOf) st.hot hI.1.1.1 hI.1.2 (s := s) (f1 := f1) (f2 := f2)
    (j := st.jets)
  rw [← hA] at hk
  have hAna := anaHyp_of_armP A (lib := lib) hA
  obtain ⟨hB, -, -⟩ := hAna.ana s (C f1 f2) st.long st.jets st.hot r hk hI.1.1.1
  have hok1 : CacheOKR A ref r.2.1 r.2.2.1 st.hot st.cache :=
    cacheOKR_stable hC.toCompStateOnR hI.2 hk hI.1.1.1 hI.1.1.2
  have hI1 : InvSR A lib ref (midSt st r) := ⟨hB, hok1⟩
  simp only [pokeS, hk, Option.bind_some]
  split
  · exact ⟨_, rfl⟩
  · rename_i hj
    obtain ⟨x, hx⟩ := hr st s (C f1 f2) r hI.2 hI.1.1 hk hj
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (hC.answers _ r.1 true x (hR.ana st s _ r hI.2 hk) hI1 hx)
    exact ⟨_, by rw [hp]; rfl⟩

/-- **`gap_of_armPMOn` up to rings**: `contract`, `invKept`, `invStart` on `InvSMIR`. -/
theorem gap_of_armPMOnR (A : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)) {lib : Lib}
    {ref : Ref FinMap (TreapMap mugF) Noun Noun} {I : PSt → Prop} {Rd : PSt → Bell → Prop} {R : Type}
    {env : Env R} {jet : Noun → Noun → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
    {fuel : Noun → Noun → LongB FinMap → Noun → Nat} {bf : BEnv FinMap → Nat} {regOf : Noun → R}
    {jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun} {newOf : R → Noun}
    (hC : CompHypOnR A lib ref I Rd) (hR : ReachOn A I Rd) (h0 : I emptySt)
    (hA : A.skaPoke = anaArmP env jet fold frozen fuel bf regOf jetsOf newOf) (fl : Flags) :
    Sound lib (liftPoke (enc fl) (pokeS A)) (liftInv (enc fl) (InvSMIR A lib ref I)) ∧
    (∀ t ov p t', liftInv (enc fl) (InvSMIR A lib ref I) t → ¬ HotOvum ov →
      liftPoke (enc fl) (pokeS A) t ov = some (p, t') → liftInv (enc fl) (InvSMIR A lib ref I) t') ∧
    liftInv (enc fl) (InvSMIR A lib ref I) cor := by
  have hAna := anaHyp_of_armP A (lib := lib) hA
  have hS0 : Sound lib (pokeS A) (fun st => (InvSR A lib ref st ∧ I st) ∧ MemoNoCallees st.long.memo) :=
    sound_and (pokeS_soundOnR hC hR hAna) (pokeS_memoP A hA)
  have e : (fun st : PSt => (InvSR A lib ref st ∧ I st) ∧ MemoNoCallees st.long.memo) = InvSMIR A lib ref I :=
    funext fun st => propext ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨⟨a, c⟩, b⟩, fun ⟨⟨a, c⟩, b⟩ => ⟨⟨a, b⟩, c⟩⟩
  have hS : Sound lib (pokeS A) (InvSMIR A lib ref I) := e ▸ hS0
  have hK : ∀ st ov p st', InvSMIR A lib ref I st → ¬ HotOvum ov → pokeS A st ov = some (p, st') →
      InvSMIR A lib ref I st' := fun st ov p st' hI hh hp =>
    have k := pokeS_invKeptOnR hC hR hAna st ov p st' ⟨hI.1.1, hI.2⟩ hh hp
    ⟨⟨k.1, pokeS_memoP A hA st ov p st' hI.1.2 hp⟩, k.2⟩
  have hi := invSM_init lib ref jets0 (Noun.atom 0) (Noun.atom 0, Noun.atom 0)
  exact ⟨sound_lift (enc_inj fl) hS, invKept_lift (enc_inj fl) hK,
    ⟨emptySt, (cor_enc fl).symm, ⟨⟨hi.1.1, cacheOKR_of_ok hi.1.2⟩, hi.2⟩, h0⟩⟩

/-- **`halting` on `InvSMIR` for `enc fl`.** -/
theorem halting_of_cgMPOnR (A : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)) {lib : Lib}
    {ref : Ref FinMap (TreapMap mugF) Noun Noun} {I : PSt → Prop} {Rd : PSt → Bell → Prop} {R : Type}
    {env : Env R} {jet : Noun → Noun → (Bell → Option Datum) → R → Bell → Bool} {fold frozen : Bool}
    {bf : BEnv FinMap → Nat} {regOf : Noun → R}
    {jetsOf : Noun → Noun → R → LongB FinMap → LongB FinMap → Noun} {newOf : R → Noun}
    (hC : CompHypOnR A lib ref I Rd) (hR : ReachOn A I Rd)
    (hA : A.skaPoke = anaArmP env jet fold frozen (anaFuel env regOf) bf regOf jetsOf newOf)
    (hcg : CgHalts (M := FinMap) lib env regOf)
    (hb : BakeEnds lib env jet fold frozen (anaFuel env regOf) bf regOf) (hr : RootAnswersOnR A lib ref I)
    (fl : Flags) :
    FullAnswers (liftPoke (enc fl) (pokeS A)) (liftInv (enc fl) (InvSMIR A lib ref I)) :=
  fullAnswers_lift (enc_inj fl) (fullAnswers_of_cgMPOnR A hC hR hA hcg hb hr)

end P

end Glue
end SkaModel
end Formalization
