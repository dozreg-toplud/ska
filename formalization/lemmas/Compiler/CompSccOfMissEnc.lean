import lemmas.Compiler.CompTarjanBunt
import lemmas.Compiler.TreapSet

/-!
# The miss of `+scc-of` on the encoded state (track Q)

On track P's nouns (`callsNoun`, `sccsNoun`, `PokeLinkScc.lean`): `calls`
is a map of set nouns (`callsOK_callsNoun`), and a bell without an entry in
`sccs` looks up to `~`, so **`sccG_miss_enc`**: on a cache miss, at every
fuel, whenever `scoMiss` returns, `sccG` returns the same noun.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeM Tarjan

/-- `calls.long-ska` is a map of set nouns. -/
theorem callsOK_callsNoun (L : LongB FinMap) : CallsOK (callsNoun L) := by
  refine ⟨FinMap.isMap_toNoun _ _, fun k v h => ?_⟩
  obtain ⟨b, e, -, -, rfl⟩ := (FinMap.get_toNoun _ L.code k v).1 h
  exact Tree.of_isSet (FinMap.isSet_setNoun _)

/-- **The miss of `+scc-of` on the encoded state is `scoMiss`.** -/
theorem sccG_miss_enc (b : Bell) (L : LongB FinMap) (sc : FinMap Bell (FinMap Bell Unit)) (hb : sc.get b = none)
    (n : Nat) :
    ∀ r, scoMiss b.toNoun (callsNoun L) (sccsNoun sc) n = some r →
      sccG b.toNoun (callsNoun L) (sccsNoun sc) = some r := by
  have hg : getF mugF b.toNoun (sccsNoun sc) = some (A 0) := by
    have h := FinMap.getF_toNoun FinMap.setNoun sc b
    rw [hb] at h
    exact h
  exact sccG_missJ _ _ _ hg (callsOK_callsNoun L) n

end Compiler
end Formalization
