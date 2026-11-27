import lemmas.Compiler.PokeLinkFull

/-!
# The link of `+scc-of` in the `%full` branch (`SccLink`), up to the image of its product

`sccP` (`Compiler/PokeLinkFull.lean`) slams arm `96127` of axis `63` of the
compiler's core on `[func calls.long-ska sccs.cache]` and writes the second
half of the product at axis `958`.  On an encoded state the gate is a
constant (axis `63` is inside the library: `sccG`), and its sample is the
noun of the bell, of the table's `calls` (`callsNoun`) and of `sccs`
(`sccs_raw_enc`).  `A.sccOf` is a field of `Arms` with no model of its own
(`Ska/PokeModel.lean`), so it is taken here as the pill's `+scc-of` read
back (`sccOfP`: the pair of maps whose nouns the gate returns, `none` where
the gate crashes or returns no such pair).  Then:

* `sccLink_of`: `SccLink fl A sccP` for every `A` with `A.sccOf = sccOfP`,
  from ONE hypothesis on the pill alone, `SccImage`: on the nouns of a bell,
  a `calls` table and a `sccs` map, the gate's product, when it returns, is
  the noun of a pair of maps (a set of bells and a map from bells to sets of
  bells).  The model then crashes exactly where the pill does.

What `SccImage` takes (not proved): the arm (409 cells, then `+tarjan`)
builds every set with `+put:in` and every map with `+put:by` from `~` or
from `sccs`, and reads `calls` with `+gut:by`, `+has:by`, `+get:by`; each
keeps `IsMap mugF` (`putF_spec`), so every map it returns is the
`FinMap.toNoun` of its pairs (`isMap_ext`) once its keys are bells, which
they are because they come from `b`, `calls` and `sccs`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeM

/-- The noun of `calls.long-ska` (axis `942` of the core). -/
noncomputable def callsNoun (L : LongB FinMap) : Noun := L.code.toNoun fun e => FinMap.setNoun e.calls

/-- The noun of `sccs.cache` (axis `958` of the core). -/
noncomputable def sccsNoun (sc : FinMap Bell (FinMap Bell Unit)) : Noun := sc.toNoun FinMap.setNoun

/-- The gate of `+scc-of` (arm `96127` of axis `7` of the library) slammed on
`[func calls sccs]`. -/
def sccG (func ca sc : Noun) : Option Noun :=
  (slot? 7 corLib).bind fun c => (gateAt c 96127).bind fun g => slamG g (C func (C ca sc))

theorem sccs_raw_enc (fl : Flags) (st : PSt) (func : Noun) :
    sccRaw (enc fl st) func = sccG func (callsNoun st.long) (sccsNoun st.cache.sccs) := by
  simp [sccRaw, sccG, enc, stNoun, longNoun, cacheNoun, callsNoun, sccsNoun, nock_exec]

/-- Writing `sccs.cache` into an encoded core. -/
theorem enc_edit958 (fl : Flags) (st : PSt) (sc : FinMap Bell (FinMap Bell Unit)) :
    edit? 958 (sccsNoun sc) (enc fl st) = some (enc fl { st with cache := { st.cache with sccs := sc } }) := by
  simp [enc, stNoun, cacheNoun, sccsNoun, nock_exec]

/-- The noun of a pair of maps (a set of bells, a map from bells to sets of
bells), as `+scc-of` returns it. -/
noncomputable def sccPairNoun (r : FinMap Bell Unit × FinMap Bell (FinMap Bell Unit)) : Noun :=
  C (FinMap.setNoun r.1) (sccsNoun r.2)

/-- **The model's `+scc-of`: the pill's, read back.** -/
noncomputable def sccOfP (b : Bell) (L : LongB FinMap) (sc : FinMap Bell (FinMap Bell Unit)) :
    Option (FinMap Bell Unit × FinMap Bell (FinMap Bell Unit)) :=
  open Classical in
  if h : ∃ r, sccG b.toNoun (callsNoun L) (sccsNoun sc) = some (sccPairNoun r) then
    some (Classical.choose h)
  else none

/-- **The image of `+scc-of`** (open; a statement on the pill alone): on the
nouns of a bell, a `calls` table and a `sccs` map, the gate's product, when
it returns, is the noun of a pair of maps. -/
def SccImage : Prop :=
  ∀ (b : Bell) (L : LongB FinMap) (sc : FinMap Bell (FinMap Bell Unit)) x,
    sccG b.toNoun (callsNoun L) (sccsNoun sc) = some x → ∃ r, x = sccPairNoun r

/-- **`SccLink` from the image of `+scc-of`**: for every `A` whose `sccOf`
is the pill's read back. -/
theorem sccLink_of (fl : Flags) {A : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)}
    (hA : A.sccOf = sccOfP) (hI : SccImage) : SccLink fl A sccP := by
  intro st b
  rw [hA]
  unfold sccP
  rw [sccs_raw_enc]
  cases e : sccG b.toNoun (callsNoun st.long) (sccsNoun st.cache.sccs) with
  | none =>
    have hn : ¬ ∃ r, sccG b.toNoun (callsNoun st.long) (sccsNoun st.cache.sccs) = some (sccPairNoun r) := by
      rintro ⟨r, hr⟩
      rw [e] at hr
      cases hr
    have hd : sccOfP b st.long st.cache.sccs = none := by
      unfold sccOfP; rw [dif_neg hn]
    rw [hd]
    rfl
  | some x =>
    obtain ⟨r0, hr0⟩ := hI b st.long st.cache.sccs x e
    have hex : ∃ r, sccG b.toNoun (callsNoun st.long) (sccsNoun st.cache.sccs) = some (sccPairNoun r) :=
      ⟨r0, by rw [e, hr0]⟩
    have hd : sccOfP b st.long st.cache.sccs = some (Classical.choose hex) := by
      unfold sccOfP; rw [dif_pos hex]
    have h2 := Classical.choose_spec hex
    generalize Classical.choose hex = r at h2 hd
    rw [e] at h2
    rw [hd]
    cases h2
    simp [sccPairNoun, enc_edit958]

end Compiler
end Formalization
