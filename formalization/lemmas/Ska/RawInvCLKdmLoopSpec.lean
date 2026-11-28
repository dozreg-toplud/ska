import lemmas.Ska.RawInvCLCallDM

/-!
# The statement of the loop of `+mono-try-call` (liveness)

README Gaps 14 (b), track D.  The interface between the proof of the loop
(`RawInvCLKdmLoop.lean`, `kml_loop`) and the proof of `KdmMonoSpec` from it
(`RawInvCLKdmBlocks.lean`, `kmb_monoSpec_of`).

**`KmlLoopSpec`**: a run of `monoTryLoop fail ned r o` from a state where
the goal "`o` or `fail`" (`%pick`) holds `IL`, `ned`'s registers are
distinct, below `re`, undefined and no key, and so is `r` (not in `ned`),
ends at a block `o'` where "`o'` or `fail`" holds `IL`, and a register live
at `o'` is `r`, or live at `o` and not in `ned`, or live at `fail` (in the
blocks before the run, read modulo `unproxy`).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

/-- **What the loop of `+mono-try-call` leaves** (see the header). -/
def KmlLoopSpec (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] : Prop :=
  ∀ (K : Nat → Nat → Prop) (fail : Nat) (ned : Need) (r o : Nat) (g g' : Comp.Gen Map) (o' : Nat),
    IL K (CGoalL.pick (jmp0 o) (jmp0 fail) : CGoalL S) g →
    Distinct ned →
    (∀ y, NMem ned y → y < g.re ∧ ¬ Defd g.blocks y ∧ HoonMap.get g.cond y = Option.none) →
    r < g.re → ¬ Defd g.blocks r → HoonMap.get g.cond r = Option.none → ¬ NMem ned r →
    (monoTryLoop fail ned r o : CM Map Nat) g = some (o', g') →
    IL K (CGoalL.pick (jmp0 o') (jmp0 fail) : CGoalL S) g' ∧
    ∀ y, LiveK (unpM g') K o' y →
      y = r ∨ (LiveK (unpM g) K o y ∧ ¬ NMem ned y) ∨ LiveK (unpM g) K fail y

end Raw
end SkaModel
end Formalization
