import lemmas.Ska.RawInvCLSARunN
import lemmas.Ska.RawInvCLRunLN
import lemmas.Ska.RawInvCLLiveN
import lemmas.Ska.RawInvCLLeaves

/-!
# The n-ary leaves with direct calls

README Gaps 14 (b), track D.  The n-ary top run is `runLC`, that is
`runLCM env false` (`runLCM_false`): a direct call goes through `callL`'s
`some (b, key)` branch (the drop, or the `%cal` block after `+kerf`, the
`jmp` block under `%done`).  On `PlainD`:

* single assignment `sarRunF_plainD`, `topSAR_plainDF`
  (`RawInvCLSARunN.lean`, fork `kxs`);
* the frame and the labels `frameRunF_plainD`, `labRunF_plainD`
  (`RawInvCLRunLN.lean`, fork `kxf`);
* the liveness `liveRunF_plainD_of` and the n-ary pass
  `optIn_finishLFC_ofD`, `readsIn_finishLFC_ofD` from the frame and the
  labels (`RawInvCLLiveN.lean`, fork `kxl`).

So **`liveRunF_plainD`** and track G's two n-ary leaves on
`PlainDC := liftNC fun _ bake nm => PlainD nm ∧ ∀ ned, bake ned = (ned, [])`:
**`Glue.optInNary_plainD`**, **`Glue.readsInNary_plainD`**, no hypothesis;
`Glue.plainNC_plainDC`, `Glue.plainM_plainDM`: the plain classes are in them.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The liveness of every run of `runLCM env false` on `PlainD`**, no
hypothesis. -/
theorem liveRunF_plainD (env : CallEnv) :
    ∀ (nm : Nomm), PlainD nm → ∀ (sup : Option Nomm), kxlLRLF S Map env sup nm :=
  liveRunF_plainD_of env (frameRunF_plainD env) (labRunF_plainD env)

end Raw

namespace Glue

open Nock Opt Comp Raw

variable {Map : Type → Type} [HoonMap Map] [Comp.HoonMapKeys Map] [Opt.MapKeys Map]
variable {S : Type} [Comp.HoonSet S]

/-- **The n-ary class with direct and indirect calls and no `%6`**:
`PlainD`, nothing baked. -/
def PlainDC : NaryClass := liftNC fun _ bake nm => Raw.PlainD nm ∧ ∀ ned, bake ned = (ned, [])

/-- `PlainNC` is in `PlainDC`. -/
theorem plainNC_plainDC : ∀ env N bl cape bake nm, PlainNC env N bl cape bake nm → PlainDC env N bl cape bake nm :=
  fun _ _ _ _ _ nm h => ⟨Raw.plainN_plainD nm h.1, h.2⟩

/-- `PlainM` is in `PlainDM`. -/
theorem plainM_plainDM : ∀ env N bl nm, PlainM env N bl nm → PlainDM env N bl nm :=
  fun _ _ _ nm h => Raw.plainN_plainD nm h

/-- **Leaf `OptInNary` on `PlainDC`** (direct calls included), no hypothesis. -/
theorem optInNary_plainD : OptInNary S Map PlainDC := by
  intro env N bl cape bake nm ord s hf hs
  exact optIn_finishLFC_ofD env (frameRunF_plainD env) (labRunF_plainD env) hf.1 (topSAR_plainDF hf.1) hf.2 hs

/-- **Leaf `ReadsInNary` on `PlainDC`** (direct calls included), no hypothesis. -/
theorem readsInNary_plainD : ReadsInNary S Map PlainDC := by
  intro env N bl cape bake nm ord s hf hs
  exact readsIn_finishLFC_ofD env (frameRunF_plainD env) (labRunF_plainD env) hf.1 (topSAR_plainDF hf.1) hf.2 hs

end Glue
end SkaModel
end Formalization
