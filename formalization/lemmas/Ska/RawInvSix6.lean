import lemmas.Ska.RawInvCAT

/-!
# `ATS6`: the state invariant through `%6`

README Gaps 14 (b), track D.  At `%6` the down clause of `ATS` fails
(`+fork-need`'s `o0`/`o1` hop up to the join; `+fork`'s `insertHop` turns an
old entry block into a hop to a new block: `RawInvCLCheckSixR.lean`).  What
holds at every sub-run there (checked, 0 failures) is "no dangling jump and
no cycle".  Here it is a Prop:

* `JEdge bl y x`: `y` is a jump target of the block at `x`;
* `Acyc bl`: every label is accessible for `JEdge` (no infinite jump path;
  on a finite map, no cycle);
* **`ATS6 g`**: `ATS` with its down clause replaced by `Acyc` (no dangling
  jump is in `BATC`: every jump targets a block with as many parameters as
  it passes);
* `ats6_of_ats`: `ATS` gives `ATS6` (a jump goes down).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {Map : Type → Type} [HoonMap Map]

/-- **`y` is a jump target of the block at `x`.** -/
def JEdge (bl : Map Blob) (y x : Nat) : Prop :=
  ∃ b, HoonMap.get bl x = some b ∧ ∃ j ∈ finJumps b.fin, j.there = y

/-- **No infinite jump path**: every label is accessible for `JEdge`. -/
def Acyc (bl : Map Blob) : Prop := ∀ k, Acc (JEdge bl) k

/-- **The state invariant through `%6`**: no `drop`, labels from `1` below
`bo`, every block meets `BATC` (so no dangling jump), and no cycle. -/
def ATS6 (g : Comp.Gen Map) : Prop :=
  g.drop = false ∧ 1 ≤ g.bo ∧
    (∀ k b, HoonMap.get g.blocks k = some b → k < g.bo ∧ BATC g.blocks b ∧ 1 ≤ k) ∧ Acyc g.blocks

/-- A map whose jumps go down has no cycle. -/
theorem acyc_of_down {bl : Map Blob} (h : ∀ k b, HoonMap.get bl k = some b → ∀ j ∈ finJumps b.fin, j.there < k) :
    Acyc bl := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    refine Acc.intro k fun y hy => ?_
    obtain ⟨b, hb, j, hj, rfl⟩ := hy
    exact ih _ (h k b hb j hj)

/-- **`ATS` gives `ATS6`.** -/
theorem ats6_of_ats {g : Comp.Gen Map} (h : ATS g) : ATS6 g := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun k b hb => ?_, acyc_of_down fun k b hb => (h3 k b hb).2.2.2⟩
  obtain ⟨a, c, d, -⟩ := h3 k b hb
  exact ⟨a, c, d⟩

end Raw
end SkaModel
end Formalization
