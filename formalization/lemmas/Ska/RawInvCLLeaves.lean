import lemmas.Ska.RawInvCLSARun
import lemmas.Ska.RawInvCLSACountSplit
import lemmas.Ska.RawInvCLSACountInto
import lemmas.Ska.RawInvCLSACountK
import lemmas.Ska.RawInvCLSACountCopy
import lemmas.Glue.GuardCalls

/-!
# Track G's four leaves on the class with indirect calls and no `%6`

README Gaps 14 (b), track D.  The raw code of `PlainN` (`%0`, `%1`, `%3`,
`%4`, `%5`, cons, `%7`, `%10`, indirect calls `[2 p q]`, nested; no `%6`, no
direct call, no hint) meets `OptIn` and `ReadsIn`, with no hypothesis:

* `sarStepsW`: the five definition counts (`scsp_split`, `scit_into`,
  `sccp_copy`, `sccl_collapse`, `sckf_kerf`), so **`topSAR_plain`** and
  **`topSAU_plain`** (single assignment of the raw blocks after the top run
  and after its `+kerf`) are theorems;
* **`optInMono_plain`**, **`readsInMono_plain`** (whole subject,
  `finishLUCM`) on `PlainM`, **`optInNary_plain`**, **`readsInNary_plain`**
  (n-ary, `finishLFC`) on `PlainNC` (`PlainN` with nothing baked), in the
  exact forms `OptInMono`, `ReadsInMono` (`Glue/MonoCalls.lean`,
  `Glue/GuardCalls.lean`), `OptInNary`, `ReadsInNary`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map] [MapKeys Map]

/-- **The five definition counts**: every field of `SarStepsW` proved. -/
theorem sarStepsW : SarStepsW S Map := ⟨scsp_split, scit_into, sccp_copy, sccl_collapse, sckf_kerf⟩

/-- **Single assignment of the raw blocks after the top run** on `PlainN`. -/
theorem topSAR_plain {env : CallEnv} {nm : Nomm} (hp : PlainN nm) : TopSAR S Map env nm :=
  topSAR_plainW sarStepsW hp

/-- **Single assignment after the top run and its `+kerf`** on `PlainN`. -/
theorem topSAU_plain {env : CallEnv} {nm : Nomm} (hp : PlainN nm) : TopSAU S Map env nm :=
  topSAU_plainW sarStepsW hp

end Raw

namespace Glue

open Nock Opt Comp Raw

variable {Map : Type → Type} [HoonMap Map] [Comp.HoonMapKeys Map] [Opt.MapKeys Map]
variable {S : Type} [Comp.HoonSet S]

/-- **The whole-subject class with indirect calls and no `%6`**: `PlainN`. -/
def PlainM : MonoClass := liftMC Comp.PlainN

/-- **The n-ary class with indirect calls and no `%6`**: `PlainN`, nothing
baked. -/
def PlainNC : NaryClass := liftNC fun _ bake nm => Comp.PlainN nm ∧ ∀ ned, bake ned = (ned, [])

/-- **Leaf `OptInMono` on `PlainM`.** -/
theorem optInMono_plain : OptInMono S Map PlainM := by
  intro env N bl nm s hf hs
  exact optIn_finishLUCM_of splitSpecL intoSpecL hf (topSAU_plain hf) hs

/-- **Leaf `ReadsInMono` on `PlainM`.** -/
theorem readsInMono_plain : ReadsInMono S Map PlainM := by
  intro env N bl nm s hf hs
  exact readsIn_finishLUCM_of splitSpecL intoSpecL hf (topSAU_plain hf) hs

/-- **Leaf `OptInNary` on `PlainNC`.** -/
theorem optInNary_plain : OptInNary S Map PlainNC := by
  intro env N bl cape bake nm ord s hf hs
  exact optIn_finishLFC_of splitSpecL intoSpecL hf.1 (topSAR_plain hf.1) hf.2 hs

/-- **Leaf `ReadsInNary` on `PlainNC`.** -/
theorem readsInNary_plain : ReadsInNary S Map PlainNC := by
  intro env N bl cape bake nm ord s hf hs
  exact readsIn_finishLFC_of splitSpecL intoSpecL hf.1 (topSAR_plain hf.1) hf.2 hs

end Glue
end SkaModel
end Formalization
