import lemmas.Compiler.PokeLinkGood3
import lemmas.Compiler.CompMonoLink

/-!
# From `PGood3` to the state fields of track K's `PGoodK`

`PGoodK env inl st` (`CompMonoLink.lean`) has four fields.  Two of them, and
one half of a third, are facts of the state, proved here from `PGood3`:

* `pgoodK_calls`: the field `calls` (the encoded `calls` is a map of sets),
  free from `enc`;
* `pgoodK_sccs`: the field `sccs` (`SccsGood` of the encoded `sccs.cache`)
  from `SccsGoodM` of `CacheGood`;
* `pgoodK_nary`: the `NaryClosed` half of the field `rest` from
  `NaryClosedM` of `CacheGood`.

Not state facts: the field `agree` (`AgreeE env`) says that each entry of
`nary.cache` has the need `env.need b` and each entry of `sure.cache` is
`env.sure b`, for the poke's compile `env`; and the `RInl` half of `rest`
says that each `inl.cache` entry is `inl k` for track K's `inl`.  Both
relate the cache to what the compiler computes (a "the cache is the
compile" invariant; `%ival` of `invdump2.hoon` checks the `inl` one: every
entry is `+inlined` of its bell on the state with `inl.cache` emptied).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeM FinMap

theorem getF_toNoun_some {ν : Type} (f : ν → Noun) (m : FinMap Bell ν) (k S : Noun)
    (h : getF mugF k (m.toNoun f) = some (C (A 0) S)) : ∃ b x, m.1 b = some x ∧ k = TKey.enc b ∧ S = f x := by
  by_cases hg : ∃ v, Get (m.toNoun f) k v
  · obtain ⟨v, hv⟩ := hg
    rw [getF_some (isMap_toNoun f m) hv] at h
    simp only [Option.some.injEq, Noun.cell.injEq, true_and] at h
    subst h
    exact (get_toNoun f m k v).1 hv
  · rw [getF_none (isMap_toNoun f m) (fun v hv => hg ⟨v, hv⟩)] at h
    cases h

/-- **The field `calls` of `PGoodK`**: free from `enc`. -/
theorem pgoodK_calls (L : LongB FinMap) :
    IsMap mugF (callsNoun L) ∧ ∀ k v, Get (callsNoun L) k v → IsSet mugF v := by
  refine ⟨isMap_toNoun _ _, fun k v hv => ?_⟩
  obtain ⟨_, e, _, _, rfl⟩ := (get_toNoun _ _ k v).1 hv
  exact isSet_setNoun _

/-- **The field `sccs` of `PGoodK`** from `SccsGoodM`. -/
theorem pgoodK_sccs {sc : FinMap Bell (FinMap Bell Unit)} (h : SccsGoodM sc) : SccsGood (sccsNoun sc) := by
  intro k S hk
  obtain ⟨b, S', hb, rfl, rfl⟩ := getF_toNoun_some FinMap.setNoun sc k S hk
  obtain ⟨hself, hmem⟩ := h b S' hb
  refine ⟨isSet_setNoun S', (mem_tapList_set (isSet_setNoun S') _).2 ((has_setNoun S' _).2 ⟨b, hself, rfl⟩),
    fun k' hk' => ?_⟩
  obtain ⟨b', hb', rfl⟩ := (has_setNoun S' _).1 ((mem_tapList_set (isSet_setNoun S') _).1 hk')
  refine ⟨?_, b', rfl⟩
  have e := getF_toNoun FinMap.setNoun sc b'
  rw [show sc.get b' = some S' from hmem b' hb'] at e
  exact e

/-- **The `NaryClosed` half of the field `rest` of `PGoodK`** from
`NaryClosedM`. -/
theorem pgoodK_nary {c : Cache FinMap (TreapMap mugF) (Noun × Noun)} (h : NaryClosedM c.nary c.sccs) :
    NaryClosed (sccsNoun c.sccs) (cuRest (cacheNoun c)) := by
  refine ⟨c.nary.toNoun Straight.toNoun, show slot? 2 (C (c.nary.toNoun Straight.toNoun)
    (C (c.mono.toNoun Straight.toNoun) (C (c.sccs.toNoun FinMap.setNoun) (C c.rest.1 c.rest.2)))) =
      some (c.nary.toNoun Straight.toNoun) by rw [slot?_step 2 (by omega)]; simp [child], fun k u hk => ?_⟩
  obtain ⟨b, s, hb, rfl, rfl⟩ := getF_toNoun_some Straight.toNoun c.nary k u hk
  obtain ⟨S, hS, hall⟩ := h b s hb
  refine ⟨S.setNoun, ?_, fun k' hk' => ?_⟩
  · have e := getF_toNoun FinMap.setNoun c.sccs b
    rw [show c.sccs.get b = some S from hS] at e
    exact e
  · obtain ⟨b', hb', rfl⟩ := (has_setNoun S _).1 ((mem_tapList_set (isSet_setNoun S) _).1 hk')
    obtain ⟨s', hs'⟩ := hall b' hb'
    refine ⟨s'.toNoun, ?_⟩
    have e := getF_toNoun Straight.toNoun c.nary b'
    rw [show c.nary.get b' = some s' from hs'] at e
    exact e

/-- **The state fields of `PGoodK` at a `PGood3` state.** -/
theorem pgoodK_state_of {Cls : Straight (TreapMap mugF) → Prop} {st : PSt} (hg : PGood3 Cls st) :
    SccsGood (sccsNoun st.cache.sccs) ∧
      (IsMap mugF (callsNoun st.long) ∧ ∀ k v, Get (callsNoun st.long) k v → IsSet mugF v) ∧
      NaryClosed (sccsNoun st.cache.sccs) (cuRest (cacheNoun st.cache)) :=
  ⟨pgoodK_sccs hg.good2.cache.sccs, pgoodK_calls st.long, pgoodK_nary hg.good2.cache.nary⟩

end Compiler
end Formalization
