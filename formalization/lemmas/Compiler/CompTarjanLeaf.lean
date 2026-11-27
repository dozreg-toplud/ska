import lemmas.Compiler.CompTarjanPoke
import lemmas.Compiler.CompTarjanBridge
import lemmas.Compiler.PokeLinkLoop

/-!
# Track P's leaf on `+tarjan`, `SccsLeafAt`, as a theorem (track Q)

`SccsLeafAt` (`PokeLinkLoop.lean`): push 8 of `spRest` returns a list of SCC
sets that is `TarjanSpecN` of the new code.  **`sccsLeafAt_of_tarjan`**, with
no hypothesis, on every table `nc` and every subject of the leaf:

* `nc` empty: the guard `?:  =(~ new-code)  ~` returns `~` (`srSccs_empty`),
  which is `TarjanSpecN nc ~` (`tarjanSpecN_empty`);
* otherwise `tarjanM` of the jug graph returns a `TjSpec` list `L`
  (`tarjanM_spec`, its keys distinct: `jugGr_keys_nodup`, not empty:
  `jugGr_ne`), the pill returns the flop of the list of `L`'s sets
  (`srSccs_tarjan`), and that flop is `TarjanSpecN nc` (`tarjanSpecN_of`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeM Tarjan

/-- **`SccsLeafAt` holds**: push 8 returns a `TarjanSpecN` list of the new
code, on every table and subject. -/
theorem sccsLeafAt_of_tarjan (root : Ident) (r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN : Noun)
    (gr : Callgraph FinMap × Noun)
    (r : Callgraph FinMap × FinMap Bell (FDatum FinMap) × Memo FinMap × FDatum FinMap × Noun)
    (nc baked : FinMap Bell (VarEntry FinMap)) (vr : Noun) :
    SccsLeafAt root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r nc baked vr := by
  by_cases h : ∃ b e, FinMap.get nc b = some e
  · obtain ⟨b0, e0, h0⟩ := h
    obtain ⟨L, hL, hspec⟩ := tarjanM_spec (tjGraph (jugNoun nc)) (jugGr_ne nc h0) (jugGr_keys_nodup nc)
    obtain ⟨Ss, hS, hrun⟩ := srSccs_tarjan root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r nc baked vr h0 hL
    exact ⟨_, hrun, tarjanSpecN_of hspec hS⟩
  · have hn : ∀ b, FinMap.get nc b = none := fun b => by
      cases e : FinMap.get nc b with
      | none => rfl
      | some v => exact absurd ⟨b, v, e⟩ h
    exact ⟨_, srSccs_empty root r1 r2 r3 r4 jRest codeN callsN varsN seekN hotN gr r nc baked vr hn,
      tarjanSpecN_empty hn⟩

end Compiler
end Formalization
