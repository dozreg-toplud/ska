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

/-! ## The gate of `~(rep by pruned)` in the trap `%poke-just-code` -/

/-- Its head: `(~(put by dats) [less-code.d fol.id] d)`. -/
def pjHead : Noun :=
  let door := C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 8388607))))
    (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 58))) (C (A 0) (A 2)))))))
  let key := C (A 7) (C (C (A 0) (A 3)) (C (C (A 0) (A 206)) (C (A 0) (A 49))))
  C (A 8) (C door (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C key (C (A 0) (A 57)))) (C (A 0) (A 2)))))))

/-- Its tail: `(put:mi memo -.entry +.entry)` of `entry=(memo-final-entry id d)`. -/
def pjTail : Noun :=
  let mfe := C (A 8) (C (C (A 9) (C (A 340) (C (A 0) (A 2047))))
    (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 56)) (C (A 0) (A 57)))) (C (A 0) (A 2)))))))
  let pm := C (A 7) (C (C (A 9) (C (A 84) (C (A 0) (A 4095)))) (C (A 9) (C (A 4) (C (A 0) (A 1)))))
  let sl := C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 123)) (C (C (A 0) (A 12)) (C (A 0) (A 13)))))
    (C (A 0) (A 2)))))
  C (A 8) (C mfe (C (A 8) (C pm sl)))

/-- The battery of the gate of the `+rep`. -/
def pjGate : Noun := C pjHead pjTail

/-- The accumulator `[dats memo]` of the `+rep`. -/
noncomputable def pjAcc (s : FinMap Bell (FDatum FinMap) × Memo FinMap) : Noun :=
  C (Treap.toNoun FDatum.toNoun s.1) (memoNoun s.2)

/-- One step of `pokeMemo`. -/
noncomputable def pjStep (s : FinMap Bell (FDatum FinMap) × Memo FinMap) (e : Ident × FDatum FinMap) :
    FinMap Bell (FDatum FinMap) × Memo FinMap :=
  (Treap.put s.1 ⟨e.2.less, e.1.2⟩ e.2,
   let me := memoFinalEntry e.1 e.2
   putMi s.2 me.1 me.2)

/-- The layout that the gate reads from the context `bc` of its core: `ana`
(as `ctx`) at `511`, layer 2 at `2097151`. -/
structure PjCtx (bc ctx : Noun) : Prop where
  hctx : slot? 511 bc = some ctx
  l2 : slot? 2097151 bc = some layer2
  mfe : slot? 340 ctx = some (C (A 8) (C (C (A 1) mfeBunt) (C (C (A 1) mfeBat) (C (A 0) (A 1)))))
  lib : slot? 7 ctx = some lib
  mi : slot? 84 ctx = some mi.arm
  miIn : MiIn ctx

set_option maxHeartbeats 1000000 in
/-- **The gate of the `+rep`** on one entry `[id d]` and the accumulator. -/
theorem pj_gate {bc ctx : Noun} (h : PjCtx bc ctx) (k : Ident) (v : FDatum FinMap)
    (s : FinMap Bell (FDatum FinMap) × Memo FinMap) :
    nock (C pjGate (C (C (C (identNoun k) v.toNoun) (pjAcc s)) bc)) pjGate = some (pjAcc (pjStep s (k, v))) := by
  have hp : nock (C by.put.battery (C (C (Bell.toNoun ⟨v.less, k.2⟩) v.toNoun)
      (C by.battery (C (Treap.toNoun FDatum.toNoun s.1) layer2)))) by.put.battery
      = some (Treap.toNoun FDatum.toNoun (Treap.put s.1 (⟨v.less, k.2⟩ : Bell) v)) :=
    put_gate layer2 gorIn_morIn_layer2 _ _ _ _
      (FinMap.putF_toNoun FDatum.toNoun s.1 (⟨v.less, k.2⟩ : Bell) v)
  have hm := mfe_gate ctx h.lib k v
  have hpm := mi_put_gate ctx h.miIn s.2 (memoFinalEntry k v).1 (memoFinalEntry k v).2
  simp only [Bell.toNoun, FDatum.toNoun] at hp
  simp only [identNoun, FDatum.toNoun] at hm hpm
  unfold pjGate pjHead pjTail pjAcc pjStep
  simp only [nock_exec, Option.bind_some, h.hctx, h.l2, h.mfe, h.mi, by.arm_at, by_arm, by.put.arm_at, put_arm,
    identNoun, FDatum.toNoun, hp, mi_arm, mi.put.arm_at, mi_put_arm, hm, hpm]

end Compiler
end Formalization
