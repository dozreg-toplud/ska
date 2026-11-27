import lemmas.Compiler.CompSccOfMissImg
import lemmas.Compiler.CompSccOfMissIs
import lemmas.Compiler.CompInlinedL5

/-!
# `+scc-of` writes whole SCCs: track P's `SccOfIs`, restated truthfully (track Q)

Track P's `SccOfIs` (`PokeLinkGood5.lean`) is FALSE as stated: it needs two
more hypotheses (`CompSccOfMissIs.lean`, `sccOfIs_needs_key`,
`sccOfIs_needs_good`):

* `b` a key of `L.code`: on a non-key `b` the miss stores `b ↦ {b}`, while
  `sccSet L.code b` is empty;
* `SccsGoodM sc`: with `sc = {m ↦ {b, m}}` on a two-cycle `b ↔ m` (`SccsIs`
  holds), the walk of the miss stops at `m` and stores `b ↦ {b}`.

`SccOfIsK` is `SccOfIs` with both; **`sccOfIsK_of`**: it holds for every `Ar`
with `Ar.sccOf = sccOfP`.  At `good5_mid`'s call `SccsGoodM` is
`hg.good4.good3.good2.cache.sccs`; that the root bell is a key of the new
code is track P's.

* `sccOfP_is`: the answer of `+scc-of` on a key is its SCC, and every entry
  of the new `sccs` is its bell's SCC (hit: `sccOfP_hit`; miss:
  `sccOfP_miss`, old entries by `SccsIs`, new ones by `scoScc_set`);
* `singleScc_of_sccOf`: track Q's `SingleScc` (`CompInlinedL5.lean`) for a
  `single` that answers `true` only where `+scc-of`'s set is a singleton.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeF SkaModel.PokeM Tarjan

/-- **`SccOfIs` with the two hypotheses it needs**: `SccsGoodM sc` and `b` a
key of the table. -/
def SccOfIsK (Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)) : Prop :=
  ∀ b L sc q, CodeClosed L.code → SccsIs L.code sc → SccsGoodM sc → (∃ e, FinMap.get L.code b = some e) →
    Ar.sccOf b L sc = some q → SccsIs L.code q.2

/-- **The answer of `+scc-of` on a key is its SCC**, and every entry of the
new `sccs` is its bell's SCC. -/
theorem sccOfP_is {b : Bell} {L : LongB FinMap} {sc : FinMap Bell (FinMap Bell Unit)}
    {q : FinMap Bell Unit × FinMap Bell (FinMap Bell Unit)} (hC : CodeClosed L.code) (hs : SccsIs L.code sc)
    (hg : SccsGoodM sc) (hb0 : ∃ e, FinMap.get L.code b = some e) (h : sccOfP b L sc = some q) :
    SccsIs L.code q.2 ∧ q.1 = sccSet L.code b := by
  cases e : sc.get b with
  | some v =>
    rw [sccOfP_hit e] at h
    cases h
    exact ⟨hs, hs b v e⟩
  | none =>
    obtain ⟨h1, h2⟩ := sccOfP_miss e h
    have key : SccsIs L.code q.2 := by
      intro k S hk
      rcases (h2 k S).1 hk with ⟨ho, -⟩ | ⟨hr, hS⟩
      · exact hs k S ho
      · exact scoScc_set hC hs hg hb0 e hr S hS
    exact ⟨key, key b q.1 h1⟩

/-- **`SccOfIsK` holds** for the pill's `+scc-of` read back. -/
theorem sccOfIsK_of {Ar : Arms FinMap (TreapMap mugF) Noun Noun (Noun × Noun)} (hA : Ar.sccOf = sccOfP) :
    SccOfIsK Ar := by
  intro b L sc q hC hs hg hb0 h
  rw [hA] at h
  exact (sccOfP_is hC hs hg hb0 h).1

/-- **`SingleScc` from `+scc-of`**: a `single` that answers `true` on a key
only where `+scc-of`'s set is a singleton. -/
theorem singleScc_of_sccOf {L : LongB FinMap} {sc : FinMap Bell (FinMap Bell Unit)} {single : Bell → Bool}
    (hC : CodeClosed L.code) (hs : SccsIs L.code sc) (hg : SccsGoodM sc)
    (hsg : ∀ c, single c = true → (∃ e, FinMap.get L.code c = some e) →
      ∃ q, sccOfP c L sc = some q ∧ ∀ d, FinMap.get q.1 d = some () → d = c) :
    SingleScc L.code single := by
  intro c hc hk d hd
  obtain ⟨q, hq, h1⟩ := hsg c hc hk
  apply h1 d
  rw [(sccOfP_is hC hs hg hk hq).2]
  exact sccSet_get.2 hd

end Compiler
end Formalization
