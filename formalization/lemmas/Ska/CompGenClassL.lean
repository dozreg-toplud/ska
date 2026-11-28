import lemmas.Ska.CompGenClassI
import lemmas.Ska.CompGenClassJ
import lemmas.Ska.CompGenClassK

/-!
# The one induction with no premise on `[0 a]`, `[1 k]`, the cons, `[7 p q]`

README Gaps 12.39, item 12.  The cons is in `NextGCS` with no premise
(`closedS_cons`: `closedS_cons_of` fed by `consSemPre_of`, `frontsSG_consG`
and `genFrag_minkEq`).  `ConsFrag f nm`: the nomms built of `[0 a]`
(`a ≥ 2`), `[1 k]`, the cons and `[7 p q]`, with their formulas, and
`nextGCS_consFrag`: every one of them is in `NextGCS` at every `P`.

`[3 p]`, `[4 p]`, `[5 p q]` are NOT in `NextGCS` as stated (`x = false`,
`FrontsSG` with `E = none`): under a goal with an entry, `+collapse-lazy-atom`
takes the goal's sure register as the product register, and the front at the
entry's label reads it (`[4 [0 2]]` under the sure need `[0]` with the entry
`(1, [2])`: front `[mov 0 2]`; 336 of 5,040 flat-goal runs, a scratch check
of `chk`).  Their class carries `x = true` (`E = L.sure.ned`), as the old
tower's `lokS_four_run` does.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The cons is in `NextGCS`, no premise.** -/
theorem closedS_cons (lib : Lib) (N : Needs) (env : CallEnv) : ClosedSCons S Map lib N env :=
  closedS_cons_gen lib N env (consSemPre_of lib) frontsSG_consG

/-- **The fragment with no premise**: `[0 a]` (`a ≥ 2`), `[1 k]`, the cons,
`[7 p q]`, with their formulas. -/
inductive ConsFrag : Noun → Nomm → Prop
  | n0 {a : Nat} : 2 ≤ a → ConsFrag (slot a) (Nomm.n0 a)
  | n1 (k : Noun) : ConsFrag (quote k) (Nomm.n1 k)
  | cons {fp fq : Noun} {p q : Nomm} : ConsFrag fp p → ConsFrag fq q → ConsFrag (C fp fq) (Nomm.cons p q)
  | n7 {fb fc : Noun} {p q : Nomm} : ConsFrag fb p → ConsFrag fc q → ConsFrag (n3 (A 7) fb fc) (Nomm.n7 p q)

theorem ConsFrag.toGen {f : Noun} {nm : Nomm} (h : ConsFrag f nm) : GenFrag f nm := by
  induction h with
  | n0 ha => exact GenFrag.n0 ha
  | n1 k => exact GenFrag.n1 k
  | cons _ _ ihp ihq => exact GenFrag.cons ihp ihq
  | n7 _ _ ihp ihq => exact GenFrag.n7 ihp ihq

/-- **The one induction with no premise**: every nomm of `ConsFrag` is in
`NextGCS` at every `P`. -/
theorem nextGCS_consFrag (lib : Lib) (N : Needs) (env : CallEnv) {f : Noun} {nm : Nomm} (hf : ConsFrag f nm) :
    ∀ P, NextGCS (S := S) (Map := Map) lib N env P f nm := by
  induction hf with
  | n0 ha => exact closedS_n0 lib N env ha
  | n1 k => exact closedS_n1 lib N env k
  | cons hp hq ihp ihq => exact closedS_cons lib N env hp.toGen hq.toGen ihp ihq
  | n7 _ _ ihp ihq => exact closedS_n7 lib N env ihp ihq

/-- **The one induction on `GenFrag`, with the premises only on `[3 p]`,
`[4 p]`, `[5 p q]`.** -/
theorem nextGCS_all (lib : Lib) (N : Needs) (env : CallEnv) (h3 : ClosedSN3 S Map lib N env)
    (h4 : ClosedSN4 S Map lib N env) (h5 : ClosedSN5 S Map lib N env) {f : Noun} {nm : Nomm} (hf : GenFrag f nm) :
    ∀ P, NextGCS (S := S) (Map := Map) lib N env P f nm :=
  nextGCS_all_of h3 h4 h5 (closedS_cons lib N env) hf

end Comp
end SkaModel
end Formalization
