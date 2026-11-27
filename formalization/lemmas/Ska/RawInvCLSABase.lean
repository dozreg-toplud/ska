import lemmas.Ska.RawInvCLTopU
import lemmas.Ska.RawInvCLSplitSpec
import lemmas.Ska.RawInvCLIntoSpec

/-!
# Single assignment of the raw blocks with calls: the shared statements

README Gaps 14 (b), track D.  The open facts `TopSAU`, `TopSAR` of
`RawInvCLTopU.lean` / `RawInvCLTopN.lean` ask `SAB` (every register defined
at most once in the whole map, no trace op, every jump argument defined by
its own block) of the raw blocks after the top run (and its `+kerf`).

* `liveRun_plain`: `LRL` on all of `PlainN`, unconditional (`SplitSpecL`
  and `IntoSpecL` are theorems).
* `KerfSAB`: `+kerf` keeps `SAB` under `IL` of the goal (the statement the
  run-level induction of single assignment uses at the indirect call and the
  whole-subject pass uses after the top run).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **`LRL` on all of `PlainN`**, with no hypothesis. -/
theorem liveRun_plain (env : CallEnv) : ∀ (nm : Nomm), PlainN nm → ∀ (sup : Option Nomm), LRL S Map env sup nm :=
  liveRun_plain_of_specs env splitSpecL intoSpecL

/-- **`+kerf` keeps single assignment** under `IL` of the goal. -/
def KerfSAB (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] : Prop :=
  ∀ (K : Nat → Nat → Prop) (nex : NextL S) (g0 g1 : Comp.Gen Map) (out pro : Nat),
    IL K nex.goal g0 → SAB g0.blocks → (kerf nex : CM Map (Nat × Nat)) g0 = some ((out, pro), g1) →
      SAB g1.blocks

end Raw
end SkaModel
end Formalization
