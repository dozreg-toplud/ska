module

public import lemmas.CueTac
public import lemmas.KernelRfl
/-!
The pill as the glue of its list of chunks, and the windows of
`lemmas/Pill/Cue/Win.lean` from it (`winOK_pill`).
-/

@[expose] public section

set_option exponentiation.threshold 20000

namespace Formalization
namespace Pill
namespace Cue

open Nock CueRel

/-- The chunks of `pill`, the same term as in its definition. -/
def pillList : List Nat := pill_list%

theorem pill_eq : pill = glue pillList := rfl

theorem pillList_lt : ∀ c ∈ pillList, c < 2 ^ 8192 := by
  have h : (pillList.all fun c => decide (c < 2 ^ 8192)) = true := by kernel_rfl
  simpa using h

theorem winOK_pill (k W : Nat) (h : glue ((pillList.drop k).take 2) = W) :
    WinOK pill W (8192 * k) := by
  rw [pill_eq]; exact winOK_glue pillList_lt k W h

end Cue
end Pill
end Formalization
