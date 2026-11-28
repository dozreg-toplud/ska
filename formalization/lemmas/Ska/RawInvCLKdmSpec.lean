import lemmas.Ska.RawInvCLKdmLoop
import lemmas.Ska.RawInvCLKdmBlocks

/-!
# The call blocks of `+mono-try-call` and the whole-subject leaves with direct calls

README Gaps 14 (b), track D.  `KdmMonoSpec` (`RawInvCLCallDM.lean`: `IL`
plus liveness across `+need-ord-alloc-regs` and the call blocks of
`+mono-try-call`) is a theorem: `kmb_monoSpec_of` (`RawInvCLKdmBlocks.lean`)
from the loop `kml_loop` (`RawInvCLKdmLoop.lean`).  So:

* **`kdmMonoSpec`**;
* **`liveRunM_plainD`**: the liveness of every run of `runLCM env true` on
  `PlainD` (direct calls included), no hypothesis;
* **`Glue.optInMono_plainD`**, **`Glue.readsInMono_plainD`**: track G's two
  whole-subject leaves on `PlainDM`, no hypothesis.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The call blocks of a direct call** (`KdmMonoSpec`), no hypothesis. -/
theorem kdmMonoSpec : KdmMonoSpec S Map := kmb_monoSpec_of kml_loop

/-- **The liveness of every run on `PlainD`**, direct calls included. -/
theorem liveRunM_plainD (env : CallEnv) :
    ∀ (nm : Nomm), PlainD nm → ∀ (sup : Option Nomm), kdlLRLM S Map env sup nm :=
  liveRunM_plainD_ofM kdmMonoSpec env

end Raw

namespace Glue

open Nock Opt Comp Raw

variable {Map : Type → Type} [HoonMap Map] [Comp.HoonMapKeys Map] [Opt.MapKeys Map]
variable {S : Type} [Comp.HoonSet S]

/-- **Leaf `OptInMono` on `PlainDM`** (direct calls included), no hypothesis. -/
theorem optInMono_plainD : OptInMono S Map PlainDM := optInMono_plainD_of kdmMonoSpec

/-- **Leaf `ReadsInMono` on `PlainDM`** (direct calls included), no hypothesis. -/
theorem readsInMono_plainD : ReadsInMono S Map PlainDM := readsInMono_plainD_of kdmMonoSpec

end Glue
end SkaModel
end Formalization
