module

public import lemmas.Pill.Facts
public import lemmas.Pill.Arm.Inlineable
import all lemmas.Pill.Arm.Inlineable

/-!
Two placements in the analysis core `ana` that the generated `Facts.lean`
does not list, for the case `%2` of `fol-loop`: `+inlineable` at axis `763`,
and the noun at axis `1023`, which the `%fast` hint of the trap
`nock-2-direct-non-inlined` reads as its parent.
-/

@[expose] public section

namespace Formalization
namespace Pill

open Nock

theorem inlineable.arm_at_ana : slot? 763 ana = some inlineable.arm := by kernel_rfl

theorem ana_1023_some : (slot? 1023 ana).isSome = true := by kernel_rfl

end Pill
end Formalization

end
