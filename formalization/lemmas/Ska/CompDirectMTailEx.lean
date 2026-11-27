import lemmas.Ska.CompDirectMTail
import lemmas.Ska.CompDirectMCheck

/-!
# The direct tail call at the top: the instance of `R`

README Gaps 18.9 (track J, 2026-11-27).  `callR` is `[2 [0 1] [1 R] R-bell]`,
the call of `[8 [1 R] [9 2 [0 1]]]` (`%dt` of `tools/hoon/directdump.hoon`)
once its subject `[R s]` is made: `bellT` is the bell of a caller whose
subject fits `R-bell` (the sock `[R ?]`) and whose formula is
`[2 [0 1] [1 R]]`.  Its whole-subject code (checked below) is the tail of
`%dt`'s eight blocks with the subject in register `2` (`mov 0 2`; `clq 2`;
`hed 2 4`, `tal 2 3`; `mov 3 1`; `jmp R-bell [1]`; `jsp R-bell 2`), and it
meets the bell contract for every needs table that holds `R-bell`'s n-ary
need `[~ this]` and some need for its call by subject
(`callR_bellContract`).  `%dt` itself is not covered: its subject part
`[[1 R] [0 1]]` has a `%1` under `%next`, which no class with `RunOKLB`
contains yet (README Gaps 18.9).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

/-- The caller's bell: the subject fits `R-bell`, the formula is the tail
call of `R`. -/
def bellT : Bell := ⟨bellR.less, tailFol nounR⟩

/- The whole-subject code of `callR`, registers and labels as the Hoon's
(the `#guard` also shows that `finishLUCM envD callR` is `some`, so
`callR_bellContract` is not vacuous). -/
#guard monoOutM callR 7 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 2] (hp 5)), (1, bk [] (Termin.jmp bellR [1])),
    (2, bk [] (Termin.jsp bellR 2)), (3, bk [Pole.mov 3 1] (hp 1)),
    (4, bk [Pole.hed 2 4, Pole.tal 2 3] (hp 3)), (5, bk [] (Termin.clq 2 (jmp0 4) (jmp0 2))), (6, Option.none)])

/-- **The bell contract of `R`'s tail call at the top**, on the real
whole-subject code, for every needs table with `R-bell`'s n-ary need
`[~ this]` and a need for its call by subject. -/
theorem callR_bellContract {lib : Lib} {N : Needs} {ndT : NeedOrd}
    (hNf : N bellR false = some (NeedOrd.pair NeedOrd.none NeedOrd.this)) (hNt : N bellR true = some ndT)
    {cd : Straight FM} (hc : finishLUCM (S := LS) envD callR = some cd) :
    cd.need = NeedOrd.this ∧ BellContract lib N bellT true cd :=
  finishLUCM_bellContractTail (S := LS) (bl := bellT) rfl rfl (by simp [envD]) hNf hNt
    (fun x gul y hx hm => by
      have := Mink.det hm ⟨1, minkStep_axis1 _ _ _ _ _⟩
      cases this; exact hx)
    (fun x gul g hx hm => by
      have := Mink.det hm ⟨1, minkStep_quote _ _ _ _ _ _⟩
      cases this; rfl) hc

end Comp
end SkaModel
end Formalization
