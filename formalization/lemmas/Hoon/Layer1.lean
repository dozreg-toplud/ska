module

public import lemmas.Hoon.Arith
public import lemmas.Pill.Facts
/-!
The pill's first layer satisfies the predicates of the arithmetic arms.  This
file and `Layer2.lean` are the only theorem files that import the pill's bulk
and `Facts.lean`: a change elsewhere in the pill rebuilds them and leaves the
gate theorems alone.
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

theorem decIn_layer1 : DecIn layer1 := dec.arm_at

/-! ## The pill's first layer -/

/-- `layer1` holds every arithmetic arm with what it reads. -/
theorem arith_layer1 :
    AddIn layer1 ∧ SubIn layer1 ∧ MulIn layer1 ∧ LthIn layer1 ∧ LteIn layer1 ∧
    GteIn layer1 ∧ GthIn layer1 ∧ MaxIn layer1 ∧ MinIn layer1 ∧ DvrIn layer1 ∧
    DivIn layer1 ∧ ModIn layer1 := by
  have d := dec.arm_at
  have a := add.arm_at
  have s := sub.arm_at
  have l := lth.arm_at
  have le := lte.arm_at
  have gt := gth.arm_at
  have dv := dvr.arm_at
  exact ⟨⟨a, d⟩, ⟨s, d⟩, ⟨mul.arm_at, a, d⟩, ⟨l, d⟩, ⟨le, l, d⟩, ⟨gte.arm_at, l, d⟩,
    ⟨gt, le, l, d⟩, ⟨max.arm_at, gt, le, l, d⟩, ⟨min.arm_at, l, d⟩, ⟨dv, ⟨l, d⟩, s, d⟩,
    ⟨div.arm_at, dv, ⟨l, d⟩, s, d⟩, ⟨mod.arm_at, dv, ⟨l, d⟩, s, d⟩⟩

end Hoon
end Formalization

end
