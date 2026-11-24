import lemmas.Compiler.SkaPassLoop

/-!
# The gate `+analyze`

`+analyze` (arm `92` of the core `K` of `+ska-callgraph`) against
`Ana.analyzeStep`, over an evaluator `nockW c` with `c` equal to `nock` off
`FFar`, with `+run` (`RunIsW`), the gate `+cull` (`hcu`) and the pass loop
(`hpl`) as parameters.  `analyzeStepH` is the model's step with `+cull`
given, and `analyzeStep n` is its instance at `Ana.cull n`
(`analyzeStepH_eq`, by `rfl`).

The subject of the battery is the gate `[bat [[id st] K]]` (`anaSubj`); the
persistent memo `memo-final` is the sample's `memo-final` of `+ska-callgraph`,
at axis `122` of `K` (`hmemo`).  The battery is split by a kernel-checked
equation (`analyze_battery_eq`): the lookup in the memo (`aHitF`), the hit
(`aHitB`), the push of the new function and the call of `+run` (`aMissF`),
the test of the lowlink (`aRestF`) and the root's branches (`aYes`).
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon SkaModel.Ana

variable {R : Type}

set_option linter.unusedSimpArgs false

/-- `+analyze` with `+cull` given. -/
noncomputable def analyzeStepH (cu : Ident → SkaState FinMap R → Option (SkaState FinMap R)) (memoF : Memo FinMap)
    (run : RunGo FinMap R) (passLoop : PassGo FinMap R) (id : Ident) (st : SkaState FinMap R) :
    Option (Nat × SkaState FinMap R) :=
  match gitMi memoF id.2 id.1 with
  | none => none
  | some (some hit) => some (st.next, { st with g := Treap.put st.g id hit.2, done := putMi st.done id hit.2 })
  | some none =>
  let index := st.next
  let st := { st with next := index + 1, order := Treap.put st.order id index, stk := id :: st.stk,
                      g := Treap.put st.g id FDatum.bunt }
  (run id index st).bind fun r =>
  let st := r.2
  if r.1.1 ≠ index then some (r.1.1, st) else
  if r.1.2.1 = true then (cu id st).bind fun st => passLoop id index 1 st else
  (Ana.above id st.stk).bind fun ab =>
  if ab.length ≠ 1 then (cu id st).bind fun st => passLoop id index 1 st else
  (Ana.pop id st).map fun st' => (st.next, st')

theorem analyzeStepH_eq (n : Nat) (memoF : Memo FinMap) (run : RunGo FinMap R) (pl : PassGo FinMap R)
    (id : Ident) (st : SkaState FinMap R) :
    analyzeStepH (Ana.cull n) memoF run pl id st = Ana.analyzeStep n memoF run pl id st := by
  unfold analyzeStepH Ana.analyzeStep Ana.cullPass
  rcases gitMi memoF id.2 id.1 with _ | _ | _ <;> rfl

/-! ## The battery, split -/

/-- `=/  hit  (git:mi memo-final fol.id more.id)`. -/
def aHitF : Noun :=
  C (A 8) (C (C (A 7) (C (C (A 9) (C (A 84) (C (A 0) (A 127)))) (C (A 9) (C (A 11) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1018)) (C (C (A 0) (A 57)) (C (A 0) (A 56))))) (C (A 0) (A 2)))))))

def aTestF : Noun := C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))

/-- The hit: the memoized datum put in `g` and `done`. -/
def aHitB : Noun :=
  C (A 8) (C (C (A 0) (A 11)) (C (C (A 0) (A 1982)) (C (A 10) (C (C (A 6) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 84) (C (A 0) (A 511)))) (C (A 9) (C (A 4) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 502)) (C (C (A 0) (A 124)) (C (A 0) (A 6))))) (C (A 0) (A 2))))))))) (C (A 10) (C (C (A 2) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 250))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 124)) (C (A 0) (A 6)))) (C (A 0) (A 2))))))))) (C (A 0) (A 61))))))))

/-- The push of the new function onto the state. -/
def aEditF : Noun :=
  C (A 10) (C (C (A 61) (C (A 10) (C (C (A 62) (C (A 4) (C (A 0) (A 2)))) (C (A 10) (C (C (A 30) (C (C (A 0) (A 60)) (C (A 0) (A 990)))) (C (A 10) (C (C (A 14) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 1006))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 124)) (C (A 0) (A 6)))) (C (A 0) (A 2))))))))) (C (A 10) (C (C (A 2) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 250))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 124)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (C (A 0) (C (C (A 0) (A 0)) (C (C (A 1) (A 0)) (C (A 1) (C (A 1) (C (C (A 0x64696f76) (A 0)) (A 0)))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 61))))))))))) (C (A 0) (A 1)))

/-- The call of `+run`. -/
def aRunF : Noun :=
  C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 95) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 124)) (C (C (A 0) (A 6)) (C (A 0) (A 125))))) (C (A 0) (A 2)))))))))

/-- The root of a component: the pass loop after `+cull`, or `+pop`. -/
def aYes : Noun :=
  C (A 6) (C (C (A 6) (C (C (A 0) (A 10)) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 22) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 252)) (C (A 0) (A 4062)))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 5)))) (C (A 1) (A 1))))))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C (C (A 7) (C (C (A 10) (C (C (A 125) (C (A 8) (C (C (A 9) (C (A 10) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 252)) (C (A 0) (A 253)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 1) (A 1)) (C (A 8) (C (C (A 1) ska_analyze.loop1) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))))) (C (C (A 0) (A 4030)) (C (A 8) (C (C (A 9) (C (A 4) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 252)) (C (A 0) (A 253)))) (C (A 0) (A 2)))))))))))

/-- The miss: `index`, the push, `+run`, then `F`. -/
def aMissF (F : Noun) : Noun :=
  C (A 8) (C (C (A 0) (A 958)) (C (A 7) (C aEditF (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C aRunF F)))))))

/-- The state of `+run` put back and the test of the lowlink. -/
def aRestF (Y : Noun) : Noun :=
  C (A 7) (C (C (A 10) (C (C (A 125) (C (A 0) (A 5))) (C (A 0) (A 1))))
    (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3)))
      (C (A 6) (C (C (A 5) (C (C (A 0) (A 4)) (C (A 0) (A 6)))) (C Y (C (C (A 0) (A 4)) (C (A 0) (A 125)))))))))

theorem analyze_battery_eq : ska_analyze.battery =
    C (A 8) (C aHitF (C (A 6) (C aTestF (C (aMissF (aRestF aYes)) aHitB)))) := by kernel_rfl

end Compiler
end Formalization
