import lemmas.Ska.CompFrontS

/-!
# The fronts of a pair whose parts read their goals' registers: `frontS_pairX`

README Gaps 12.32.  `frontS_pair` (`CompFrontS.lean`) composes the parts'
state-level fronts at one goal label when neither reads its goal's sure
registers (`E = Need.none`).  `frontS_pairX` takes parts of any flag: the
head's goal registers `Ep` and the tail's `Eq` are either the parent's own
(`+split` of `pair a b` or `both r a b`: `Ep = a`, `Eq = b`, held because `E`
holds the product) or the fresh halves `h`, `t` of `+split` of `this r`,
which the parent's witness holds (`pairWitX`, `H = pair (this h) (this t)`).

Tested before the proof (scratch `DisTest.lean` on the executable model of
`CompCall.lean`: 75 nomms built from `[0 1]`, `[0 2]`, `[0 3]`, `[4 [0 2]]`,
`[3 [0 3]]`, `[4 [0 1]]`, `[1 5]`, `[2 [0 3] [0 2]]` and cons, under 30 flat
lazy goals of 6 sure needs and 5 bond lists, 2 jumps, 2 states; 4,136 runs).
At every GOAL label a run's result entry is apart from its goal's sure
registers when the goal's entries are (no failure: the source of `hEp` and
`hEq`), and every result's entries are apart from its own sure registers
(no failure: the goal's property is kept).  At NEW labels the first fails
108 times, every one a cons with a hinted tail: the park entry
`(g''.bo, ofSure hed.sure)` holds the goal's own registers
(`[[0 1] [2 [0 3] [0 2]]]` under the sure need `[this 0 this 1]` has the
result entry `(5, this 0)`), so it is a fact about goal labels only.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The witness relation of a pair with halves `H`**: `pairWit` with the
registers `H` of the halves that `+split` allocated (`this r` split into
fresh `h`, `t`: `H = pair (this h) (this t)`), or `Need.none` when the
halves are the goal's own registers, holding the parts' products. -/
def pairWitX (comb : Noun → Noun → Noun) (H : Need) (Qp Qq : Wit) : Wit :=
  fun s v d w => ∃ vp vq dp dq wp wq, v = comb vp vq ∧ d = Need.pair H (Need.pair dp dq) ∧
    w = C (C vp vq) (C wp wq) ∧ Qp s vp dp wp ∧ Qq s vq dq wq

/-- **`frontS_pair` for parts of any flag** (README Gaps 12.32).  The head's
and the tail's fronts may read their goals' sure registers `Ep`, `Eq`; they
are held where the parent's goal registers `E` hold the product and the
halves `H` in the witness hold the parts' products (`hEH`), and the copy's
moves (and, for `Eq`, the head's ops) leave them alone (`hEp`, `hEq`).  The
halves lie in the parent's range below the tail's start, apart from the
parts' entries at the label and from the halves of the goal entry (`hH`). -/
