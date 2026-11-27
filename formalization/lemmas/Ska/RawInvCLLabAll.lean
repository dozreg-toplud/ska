import lemmas.Ska.RawInvCLLabSplit
import lemmas.Ska.RawInvCLLabCopy
import lemmas.Ska.RawInvCLLabRun

/-!
# `LabUniq` at run level on `PlainN`

README Gaps 14 (b), track D.  **`labRun_plain`**: every run of `runLC env
sup nm` on `PlainN`, from a state with `ATS` and a `Fresh` goal whose tree
is `LabUniq` with its entries below `bo` (`LG`), ends with a `Fresh` jump
and a result tree that is `LabUniq` with its entries below the new `bo`.
`labRun_plainOf` (`RawInvCLLabRun.lean`) with the steps of
`RawInvCLLabSplit.lean` and `RawInvCLLabCopy.lean`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

theorem labSteps : LabSteps S Map :=
  ⟨fun h hl hq => lab_splitL h hl hq, fun h hl hq => lab_intoL h hl hq, fun h hl hq => lab_fromL h hl hq,
    fun h h1 h2 q1 q2 => lab_copyL h h1 h2 q1 q2, fun h hl hq => lab_pastL h hl hq⟩

/-- **`LabUniq` at run level on `PlainN`.** -/
theorem labRun_plain (env : CallEnv) :
    ∀ (nm : Nomm), PlainN nm → ∀ (sup : Option Nomm), HRL (Map := Map) (runLC (S := S) env sup nm) :=
  labRun_plainOf env labSteps

end Raw
end SkaModel
end Formalization
