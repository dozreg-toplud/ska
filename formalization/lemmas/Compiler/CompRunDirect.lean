import lemmas.Compiler.CompRunDirectN
import lemmas.Compiler.CompRunFiveL
import lemmas.Compiler.CompRunResAll
import lemmas.Compiler.Safe

/-!
# The direct call of the case `%2` of `+run`: the dropped call

README Gaps 19.  The parts of `cr2Dir` (cut in `CompRunDirectN.lean`) that
the dropped call runs, each against the model `callL` of `Ska/CompCall.lean`
with `info = some (b, key)`:

* `crd_pure`: the push of `callee-pure`, `pure:(~(got by code.long-ska)
  b-callee)`, given the entry of `b` in `code` (`hgot`, `hv`).
* `crd_test`: the test `&(callee-pure ?=(%next -.goal) (none-equivalent
  laz.goal))` on a `%next` goal (`ne_all`).
* `crd_drop`: the dropped call (`+safe-fol-fol`, the run of `q`, `+past`,
  the run of `p`, `+copy`), as `cr2_tailL` for the indirect call.
* `comp_run_n2_drop`: the case `%2` with a callee whose code entry is
  `pure` on a `%next` goal whose need asks nothing, on every goal with
  `GInv`, against `runLC env msup`; `res_n2_drop`: what it returns
  (`GRes`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

variable {ctx : Noun}

/-- The noun of a direct call. -/
theorem crd_noun (p q : Nomm) (b : Bell) (key : Option Noun) :
    (Nomm.n2 p q (some (b, key))).toNoun
      = C (A 2) (C p.toNoun (C q.toNoun (C (A 0) (C b.toNoun (unitNoun id key))))) := rfl

/-- **The push of `callee-pure`**: the field `pure` (axis `6`) of the entry
of `b` in `code.long-ska` (axis `52` of the context). -/
theorem crd_pure (hc : CompIn ctx) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (P Q B K V PV mono goal region sup : Noun) (g : Gen (TreapMap mugF)) (x : GenRest)
    (hgot : getF mugF B cod = some (C (A 0) V)) (hv : slot? 6 V = some PV) :
    nock (crSubj mono (C (A 2) (C P (C Q (C (A 0) (C B K))))) goal region sup (compCore g x ctx)) crDPure
      = some PV := by
  have hgt := got_gate (mug := mugF) layer2 ⟨need.arm_at, someIn_layer2, gorIn_morIn_layer2.1⟩ B cod V hgot
  unfold crDPure
  simp [nock_exec, crSubj, compCore, hc, hcode, by.arm_at, by_arm, by.got.arm_at, got_arm, hgt, hv]

/-- **The test of the drop** on a `%next` goal, the callee pure: `+none-equivalent`
of the goal's need (`ne_all`). -/
theorem crd_test (h7 : slot? 7 ctx = some compK) (N mono region sup : Noun) (laz : Lazy CSet) (th : Jmp)
    (g : Gen (TreapMap mugF)) (x : GenRest) :
    nock (C (A 0) (crSubj mono N (CGoalL.next laz th).toNoun region sup (compCore g x ctx))) crDTest
      = some (loob (Lazy.noneEquivalentL laz)) := by
  have hD0 := compK_ne
  have hn := ne_all laz
  rw [cgl_next_noun]
  unfold crDTest
  generalize compK = KC at h7 hD0 hn
  cases e : Lazy.noneEquivalentL laz <;>
    simp [nock_exec, crSubj, compCore, h7, hD0, ne_arm, hn, e, loob]

/-- `ana` is at axis `63` of the context. -/
theorem crd_ctx63 (h7 : slot? 7 ctx = some compK) : slot? 63 ctx = some ana := by
  have h1 : slot? 7 ctx = slot? 1 compK := h7
  have := slot_spine (by omega) (by omega) h1 3
  simp only [show 2 ^ 3 * (7 + 1) - 1 = 63 from rfl, show 2 ^ 3 * (1 + 1) - 1 = 15 from rfl] at this
  rw [this]; rfl

/-- The model of the dropped call. -/
noncomputable def crdDropM (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (th : Jmp) (region : List Nat) :
    CM (TreapMap mugF) (NextL CSet) := do
  let nexFol ← (if safeFolFol q then pure ⟨Lazy.ofSure Sure.bunt, th⟩
    else runLC env msup q (CGoalL.next (Lazy.ofSure Sure.bunt) th) region : CM (TreapMap mugF) (NextL CSet))
  let nexFol ← pastL noCode nexFol p region
  let nexSub ← runLC env msup p (CGoalL.next (Lazy.ofSure Sure.bunt) nexFol.th) region
  copyL nexSub nexFol.laz

/-- **The model of the case on a dropped call**: a callee whose code entry is
`pure`, a `%next` goal whose need asks nothing. -/
theorem crd_model (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (b : Bell) (key : Option Noun)
    (laz : Lazy CSet) (th : Jmp) (region : List Nat) (hpu : env.pure b = true)
    (hne : Lazy.noneEquivalentL laz = true) (hpc : hinted env.cod p = hinted noCode p) :
    (runLC env msup (Nomm.n2 p q (some (b, key))) (CGoalL.next laz th) region : CM (TreapMap mugF) (NextL CSet))
      = crdDropM env msup p q th region := by
  simp only [runLC, callL, hpu, hne, Bool.and_self, if_true, crdDropM, pastL_cod hpc]

end Compiler
end Formalization
