import lemmas.Compiler.SkaPrune
import lemmas.Compiler.GitMi

/-!
# `+memo-final-entry` and the analysis part of `+ska-poke`

`+memo-final-entry` is the gate at arm `340` of `ana` (`mfe_at`), with the
battery `mfeBat` written out here:
`[[[8 [7 [9 20 [0 31]] [9 341 [0 1]]] [9 2 [10 [6 [[0 478] [0 56]]] [0 2]]]] [0 25]] [10 [2 [1 0]] [0 13]]]`,
that is `[[(app:ca indi.d more.id) fol.id] d(callees ~)]` with `+app:ca`
pulled from `lib` at axis `7` of its context (`mfe_gate`, against
`Ana.memoFinalEntry`).
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon SkaModel.Ana

set_option linter.unusedSimpArgs false

/-! ## `+memo-final-entry` -/

/-- The battery of the gate `+memo-final-entry`. -/
def mfeBat : Noun :=
  let pull := C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 31)))) (C (A 9) (C (A 341) (C (A 0) (A 1)))))
  let slam := C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 478)) (C (A 0) (A 56)))) (C (A 0) (A 2)))))
  C (C (C (A 8) (C pull slam)) (C (A 0) (A 25)))
    (C (A 10) (C (C (A 2) (C (A 1) (A 0))) (C (A 0) (A 13))))

/-- The bunt of the sample of `+memo-final-entry`, kept whole. -/
noncomputable def mfeBunt : Noun := (slot? 2725 ana).getD (A 0)

theorem mfe_at : slot? 340 ana = some (C (A 8) (C (C (A 1) mfeBunt) (C (C (A 1) mfeBat) (C (A 0) (A 1))))) := by
  kernel_rfl

theorem mfe_arm_run (ctx : Noun) (h : slot? 340 ctx = slot? 340 ana) :
    nock ctx (C (A 9) (C (A 340) (C (A 0) (A 1)))) = some (C mfeBat (C mfeBunt ctx)) := by
  rw [nock_op9, nock_op0]
  simp only [slot?_one, Option.bind_some, h, mfe_at]
  simp only [nock_exec]

theorem ana_lib7 : slot? 7 ana = some lib := knit_anno.lib.arm_at

/-- **`+memo-final-entry`** on `[id d]`, in a context with `lib` at axis `7`,
returns the noun of `Ana.memoFinalEntry id d`. -/
theorem mfe_gate (ctx : Noun) (hlib : slot? 7 ctx = some lib) (id : Ident) (d : FDatum FinMap) :
    nock (C mfeBat (C (C (identNoun id) d.toNoun) ctx)) mfeBat
      = some (C (identNoun (memoFinalEntry id d).1) (memoFinalEntry id d).2.toNoun) := by
  have hs : Treap.setNoun (Treap.empty : FinMap CalleeEntry Unit) = A 0 := FinMap.setNoun_empty
  unfold mfeBat
  simp only [nock_exec, hlib, Option.bind_some, ca.lib.arm_at, ca_lib_arm, ca.app.arm_at, ca_app_arm,
    identNoun, FDatum.toNoun, ca_app_pill, memoFinalEntry, hs]

end Compiler
end Formalization
