import lemmas.Compiler.CompSccOfAnyK

/-!
# The cache decoded through the gate: definitions (README Gaps 19 (g), decoding (b))

The cache `+compile-unary` returns is the noun of a model cache when its `mono` is the `mono` it
started with and its `nary` is the noun of a map of straights (its `sccs` is fixed by `RK`, and
its `inl` and `sure` are any nouns).  Here:

* `FinMap.uniBy` (the model's `+uni:by`: the entries of `b`, and those of `a` at the keys
  outside `b`) and **`FinMap.uniBy_toNoun`**: a map whose pairs are the `UniSpec` of two
  `FinMap.toNoun`s is the `FinMap.toNoun` of their `uniBy` (`isMap_ext`);
* `CacheDec MO0 CA`: `mono` (slot `6`) is `MO0` and `nary` (slot `2`) decodes;
  `cacheDec_cacheN` (blind to `sccs`, `inl`, `sure`), `cacheDec_put` (the `+put:by` of one
  straight), **`cacheDec_uni`** (the `+uni:by` of the loop's map);
* `RKD SC0 MO0 inl Pf`: `RKP SC0 inl Pf` with `CacheDec MO0`; `rKD_sure`, `rKD_mono`;
* `CsiDec`: decoding (a) at a loop (track I): the map `+compile-scc-in` returns is the noun of a
  map of straights.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Comp SkaModel.SccLoop

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace FinMap

variable {κ ν : Type} [DecidableEq κ] [TKey κ]

/-- **The union of `+uni:by`**: the entries of `b`, and those of `a` at the keys outside `b`. -/
def uniBy (a b : FinMap κ ν) : FinMap κ ν :=
  ⟨fun k => (b.1 k).or (a.1 k), a.supp ++ b.supp, fun k h => by
    cases e : b.1 k with
    | some v => exact List.mem_append_right _ (mem_supp b (by rw [e]; simp))
    | none =>
      have h' : (b.1 k).or (a.1 k) ≠ none := h
      rw [e] at h'
      exact List.mem_append_left _ (mem_supp a (by simpa using h'))⟩

theorem uniBy_get (a b : FinMap κ ν) (k : κ) : (uniBy a b).1 k = (b.1 k).or (a.1 k) := rfl

/-- **The `+uni:by` of two maps of the model is the noun of `uniBy`** (`isMap_ext`). -/
theorem uniBy_toNoun (f : ν → Noun) (a b : FinMap κ ν) {N : Noun} (hN : IsMap mugF N)
    (hu : UniSpec (a.toNoun f) (b.toNoun f) N) : N = (uniBy a b).toNoun f := by
  refine isMap_ext hN (isMap_toNoun f _) fun kn vn => ?_
  rw [hu, get_toNoun, get_toNoun, get_toNoun]
  constructor
  · rintro (⟨k, v, h1, rfl, rfl⟩ | ⟨⟨k, v, h1, rfl, rfl⟩, hn⟩)
    · exact ⟨k, v, by rw [uniBy_get, h1]; rfl, rfl, rfl⟩
    · refine ⟨k, v, ?_, rfl, rfl⟩
      cases e : b.1 k with
      | some w => exact absurd ⟨f w, (get_toNoun f b _ _).2 ⟨k, w, e, rfl, rfl⟩⟩ hn
      | none => rw [uniBy_get, e, h1]; rfl
  · rintro ⟨k, v, h1, rfl, rfl⟩
    rw [uniBy_get] at h1
    cases e : b.1 k with
    | some w =>
      rw [e] at h1
      exact Or.inl ⟨k, v, by rw [e]; exact h1, rfl, rfl⟩
    | none =>
      rw [e] at h1
      refine Or.inr ⟨⟨k, v, h1, rfl, rfl⟩, ?_⟩
      rintro ⟨w, hw⟩
      obtain ⟨k', w', h1', hk, -⟩ := (get_toNoun f b _ _).1 hw
      rw [← TKey.enc_inj _ _ hk, e] at h1'
      cases h1'

end FinMap

/-! ## The cache decoded -/

/-- **The cache decodes**: `mono` (slot `6`) is `MO0` and `nary` (slot `2`) is the noun of a map
of straights. -/
def CacheDec (MO0 CA : Noun) : Prop :=
  slot? 6 CA = some MO0 ∧ ∃ m : FinMap Bell (Straight (TreapMap mugF)), slot? 2 CA = some (m.toNoun Straight.toNoun)

/-- `CacheDec` does not read `sccs`, `inl`, `sure`. -/
theorem cacheDec_cacheN {MO0 NR MO SC INL SU SC' INL' SU' : Noun} (h : CacheDec MO0 (cacheN NR MO SC INL SU)) :
    CacheDec MO0 (cacheN NR MO SC' INL' SU') := by
  obtain ⟨h6, m, h2⟩ := h
  exact ⟨by simpa [cacheN, nock_exec] using h6, m, by simpa [cacheN, nock_exec] using h2⟩

/-- **The `+put:by` of one straight keeps `CacheDec`** (`FinMap.putF_toNoun`). -/
theorem cacheDec_put {MO0 NR MO SC INL SU NRU SC' INL' SU' : Noun} {b : Bell} {s : Straight (TreapMap mugF)}
    (hD : CacheDec MO0 (cacheN NR MO SC INL SU)) (hp : putF mugF b.toNoun s.toNoun NR = some NRU) :
    CacheDec MO0 (cacheN NRU MO SC' INL' SU') := by
  obtain ⟨h6, m, h2⟩ := hD
  have e : NR = m.toNoun Straight.toNoun := by simpa [cacheN, nock_exec] using h2
  subst e
  have hp' : putF mugF b.toNoun s.toNoun (m.toNoun Straight.toNoun) = some ((m.put b s).toNoun Straight.toNoun) :=
    FinMap.putF_toNoun Straight.toNoun m b s
  rw [hp'] at hp
  obtain rfl := Option.some.inj hp
  exact ⟨by simpa [cacheN, nock_exec] using h6, m.put b s, by simp [cacheN, nock_exec]⟩

/-- **The `+uni:by` of the loop's map keeps `CacheDec`** (`FinMap.uniBy_toNoun`): the loop's
final cache `[NR REST]` decodes, its map `M` decodes (decoding (a)), and `NARYU` is their union. -/
theorem cacheDec_uni {MO0 NR REST M NARYU : Noun} (hD : CacheDec MO0 (C NR REST))
    (hM : ∃ m : FinMap Bell (Straight (TreapMap mugF)), M = m.toNoun Straight.toNoun)
    (hNU : IsMap mugF NARYU) (hus : UniSpec NR M NARYU) : CacheDec MO0 (C NARYU REST) := by
  obtain ⟨h6, m, h2⟩ := hD
  obtain ⟨m', rfl⟩ := hM
  have e : NR = m.toNoun Straight.toNoun := by simpa [nock_exec] using h2
  subst e
  refine ⟨by simpa [nock_exec] using h6, FinMap.uniBy m m', ?_⟩
  rw [← FinMap.uniBy_toNoun Straight.toNoun m m' hNU hus]
  simp [nock_exec]

/-! ## The rest predicate with the cache decoded -/

/-- **`RKP` with the cache decoded** (`mono` is `MO0`, `nary` a map of straights). -/
def RKD (SC0 MO0 : Noun) (inl : Noun → Option Nomm) (Pf : Noun → Prop) (x : GenRest) : Prop :=
  RKP SC0 inl Pf x ∧ CacheDec MO0 x.cache

/-- `RKD` does not read `sure.cache`. -/
theorem rKD_sure {SC0 MO0 : Noun} {inl : Noun → Option Nomm} {Pf : Noun → Prop} :
    ∀ NR MO SC INL SU SU' s f : Noun, RKD SC0 MO0 inl Pf ⟨cacheN NR MO SC INL SU, s, f⟩ →
      RKD SC0 MO0 inl Pf ⟨cacheN NR MO SC INL SU', s, f⟩ :=
  fun NR MO SC INL SU SU' s f h => ⟨rKP_sure _ _ _ _ _ _ _ _ h.1, cacheDec_cacheN h.2⟩

theorem rKD_mono {SC0 MO0 : Noun} {inl : Noun → Option Nomm} {Pf Pf' : Noun → Prop} {x y : GenRest}
    (hP : ∀ k, Pf k → Pf' k) (hc : y.cache = x.cache) (h : RKD SC0 MO0 inl Pf' x) : RKD SC0 MO0 inl Pf y :=
  ⟨rKP_mono hP hc h.1, by rw [hc]; exact h.2⟩

/-- **Decoding (a) at a loop** (track I): the map `+compile-scc-in` returns on the SCC `S` at the
cache `[NR CR]` is the noun of a map of straights. -/
def CsiDec (S CODE JETS CALLS JH NR CR : Noun) : Prop :=
  ∀ M T, nock (C csiBody (C (csiSam S (C CODE (C JETS CALLS)) JH (C NR CR)) compK)) csiBody = some (C M T) →
    ∃ m : FinMap Bell (Straight (TreapMap mugF)), M = m.toNoun Straight.toNoun

end Compiler
end Formalization
