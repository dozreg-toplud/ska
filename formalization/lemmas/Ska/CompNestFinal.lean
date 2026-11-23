import lemmas.Ska.CompNestRun

/-!
# A helper for the final pass with nested `%6`

`down_of_fins`: blocks whose terminators are those of blocks that go down
go down.  `CompNestFinalP.lean` uses it.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- Blocks with the terminators of blocks that go down go down. -/
theorem down_of_fins {bs bs' : Map Blob} (hd : Down bs)
    (h : ∀ k b', HoonMap.get bs' k = some b' → ∃ b, HoonMap.get bs k = some b ∧ b'.fin = b.fin) : Down bs' := by
  intro k b' hk
  obtain ⟨b, hb, hf⟩ := h k b' hk
  rw [hf]; exact hd k b hb

end Comp
end SkaModel
end Formalization
