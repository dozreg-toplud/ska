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

/-- The root's branch that runs `+cull` and starts the pass loop. -/
def aCullP : Noun :=
  C (A 7) (C (C (A 10) (C (C (A 125) (C (A 8) (C (C (A 9) (C (A 10) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 252)) (C (A 0) (A 253)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 1) (A 1)) (C (A 8) (C (C (A 1) ska_analyze.loop1) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))))

/-- `|(back !?=([* ~] (above id stk.st)))`. -/
def aTestY : Noun :=
  C (A 6) (C (C (A 0) (A 10)) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 22) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 252)) (C (A 0) (A 4062)))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 5)))) (C (A 1) (A 1))))))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))

/-- `[next.st (pop id st)]`. -/
def aPopB : Noun :=
  C (C (A 0) (A 4030)) (C (A 8) (C (C (A 9) (C (A 4) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 252)) (C (A 0) (A 253)))) (C (A 0) (A 2))))))))

/-- The root of a component: the pass loop after `+cull`, or `+pop`. -/
def aYes : Noun := C (A 6) (C aTestY (C aCullP aPopB))

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

theorem slot_st_stk (regsNoun : R → Noun) (st : SkaState FinMap R) :
    slot? 30 (st.toNoun regsNoun) = some (listNoun identNoun st.stk) := by
  simp [SkaState.toNoun, nock_exec]

theorem slot_st_next (regsNoun : R → Noun) (st : SkaState FinMap R) :
    slot? 62 (st.toNoun regsNoun) = some (A st.next) := by
  simp [SkaState.toNoun, nock_exec]

theorem ana_test_miss (c : Noun → Noun → Option Noun) (s X Y : Noun) :
    nockW c (C (A 0) s) (C (A 6) (C aTestF (C X Y))) = nockW c (C (A 0) s) X := by
  simp [aTestF, nock_exec]

theorem ana_test_hit (c : Noun → Noun → Option Noun) (e s X Y : Noun) :
    nockW c (C (C (A 0) e) s) (C (A 6) (C aTestF (C X Y))) = nockW c (C (C (A 0) e) s) Y := by
  simp [aTestF, nock_exec]

theorem bunt_toNoun : (FDatum.bunt : FDatum FinMap).toNoun
    = C (A 0) (C (C (A 0) (A 0)) (C (C (A 1) (A 0)) (C (A 1) (C (A 1) (C (C (A 0x64696f76) (A 0)) (A 0)))))) := by
  simp only [FDatum.toNoun, FDatum.bunt, show Treap.setNoun (Treap.empty : FinMap CalleeEntry Unit) = A 0 from
    FinMap.setNoun_empty]
  rfl

/-- The state after the push of a new function. -/
noncomputable def missSt (id : Ident) (st : SkaState FinMap R) : SkaState FinMap R :=
  { st with next := st.next + 1, order := Treap.put st.order id st.next, stk := id :: st.stk,
            g := Treap.put st.g id FDatum.bunt }

section chunks
variable (c : Noun → Noun → Option Noun) (hcf : ∀ s f, FFar f → c s f = nock s f)
  (regsNoun : R → Noun) (K : Noun) (hK : slot? 31 K = some ana) (hKb : slot? 2 K = some ska_cg.k_bat)
  (id : Ident)

include hcf hK in
set_option maxHeartbeats 1000000 in
/-- The lookup in the persistent memo. -/
theorem ana_hit (memoF : Memo FinMap) (hmemo : slot? 122 K = some (memoNoun memoF)) (st : SkaState FinMap R)
    (F : Noun) :
    nockW c (anaSubj regsNoun K id st) (C (A 8) (C aHitF F))
      = (gitMi memoF id.2 id.1).bind fun h => nockW c (C (unitNoun entryNoun h) (anaSubj regsNoun K id st)) F := by
  have hg := mi_git_pill memoF id.2 id.1
  unfold anaSubj aHitF
  cases e : gitMi memoF id.2 id.1 with
  | none =>
    rw [e] at hg
    simp (disch := ffar_disch) [nock_exec, hcf, hK, hmemo, identNoun, mi.arm_at, mi_arm, mi.git.arm_at,
      mi_git_arm, hg]
  | some h =>
    rw [e] at hg
    simp (disch := ffar_disch) [nock_exec, hcf, hK, hmemo, identNoun, mi.arm_at, mi_arm, mi.git.arm_at,
      mi_git_arm, hg]

include hcf hK in
set_option maxHeartbeats 1000000 in
/-- A hit: the memoized datum put in `g` and `done`. -/
theorem ana_hitb (e : Ident × FDatum FinMap) (st : SkaState FinMap R) :
    nockW c (C (C (A 0) (entryNoun e)) (anaSubj regsNoun K id st)) aHitB
      = some (anaNoun regsNoun (st.next, { st with g := Treap.put st.g id e.2, done := putMi st.done id e.2 })) := by
  have hl2 := K_layer2 hK
  obtain ⟨g, done, order, stk, next, moved, tick, ticks, regs, stats⟩ := st
  have hpg : nock (C by.put.battery (C (C (identNoun id) e.2.toNoun)
      (C by.battery (C (Treap.toNoun FDatum.toNoun g) layer2)))) by.put.battery
      = some (Treap.toNoun FDatum.toNoun (Treap.put g id e.2)) :=
    put_gate layer2 gorIn_morIn_layer2 _ _ _ _ (FinMap.putF_toNoun FDatum.toNoun g id e.2)
  have hpm := mi_put_pill done id e.2
  unfold anaSubj aHitB entryNoun anaNoun
  simp (disch := ffar_disch) [nock_exec, hcf, hK, hl2, SkaState.toNoun, by_arm, by.arm_at, by.put.arm_at, hpg,
    mi.arm_at, mi_arm, mi.put.arm_at, mi_put_arm, hpm]

include hcf hK hKb in
set_option maxHeartbeats 1000000 in
/-- A miss: the new function numbered and pushed, then `+run` made by `c`. -/
theorem ana_miss (run : RunGo FinMap R) (hrun : RunIsW c regsNoun K run) (st : SkaState FinMap R) (F : Noun) :
    nockW c (C (A 0) (anaSubj regsNoun K id st)) (aMissF F)
      = (run id st.next (missSt id st)).bind fun r =>
          nockW c (C (runNoun regsNoun r) (C (A st.next) (C (A 0) (anaSubj regsNoun K id (missSt id st))))) F := by
  have hl2 := K_layer2 hK
  have h95 := slot_K95 hKb
  have hr := hrun id st.next (missSt id st)
  obtain ⟨g, done, order, stk, next, moved, tick, ticks, regs, stats⟩ := st
  have hpg : nock (C by.put.battery (C (C (identNoun id) (C (A 0) (C (C (A 0) (A 0)) (C (C (A 1) (A 0)) (C (A 1)
      (C (A 1) (C (C (A 0x64696f76) (A 0)) (A 0))))))))
      (C by.battery (C (Treap.toNoun FDatum.toNoun g) layer2)))) by.put.battery
      = some (Treap.toNoun FDatum.toNoun (Treap.put g id FDatum.bunt)) := by
    rw [← bunt_toNoun]
    exact put_gate layer2 gorIn_morIn_layer2 _ _ _ _ (FinMap.putF_toNoun FDatum.toNoun g id FDatum.bunt)
  have hpo : nock (C by.put.battery (C (C (identNoun id) (A next))
      (C by.battery (C (Treap.toNoun A order) layer2)))) by.put.battery
      = some (Treap.toNoun A (Treap.put order id next)) :=
    put_gate layer2 gorIn_morIn_layer2 _ _ _ _ (FinMap.putF_toNoun A order id next)
  unfold runSubj missSt at hr
  simp only [SkaState.toNoun, listNoun] at hr
  unfold anaSubj aMissF aEditF aRunF missSt
  simp only [SkaState.toNoun]
  cases e : run id next ⟨Treap.put g id FDatum.bunt, done, Treap.put order id next, id :: stk, next + 1, moved,
      tick, ticks, regs, stats⟩ with
  | none =>
    rw [e] at hr
    simp (disch := ffar_disch) [nock_exec, hcf, hK, hl2, h95, by_arm, by.arm_at, by.put.arm_at, hpg, hpo, hr,
      listNoun]
  | some r =>
    rw [e] at hr
    simp (disch := ffar_disch) [nock_exec, hcf, hK, hl2, h95, by_arm, by.arm_at, by.put.arm_at, hpg, hpo, hr,
      listNoun]

/-- The state of `+run` put back, and the test of the lowlink. -/
theorem ana_rest (Y : Noun) (r : (Nat × Bool × Bool) × SkaState FinMap R) (index : Nat) (st : SkaState FinMap R) :
    nockW c (C (runNoun regsNoun r) (C (A index) (C (A 0) (anaSubj regsNoun K id st)))) (aRestF Y)
      = if r.1.1 = index then
          nockW c (C (C (A r.1.1) (C (flag r.1.2.1) (flag r.1.2.2)))
            (C (A index) (C (A 0) (anaSubj regsNoun K id r.2)))) Y
        else some (anaNoun regsNoun (r.1.1, r.2)) := by
  obtain ⟨⟨low, back, ch⟩, st2⟩ := r
  unfold anaSubj runNoun anaNoun aRestF
  by_cases h : low = index
  · subst h; simp [nock_exec, eqCode]
  · have h' : ¬ index = low := fun e => h e.symm
    simp [nock_exec, eqCode, h, h']

include hcf hK hKb in
set_option maxHeartbeats 2000000 in
/-- The root of a component: the pass loop made by `c` after `+cull` made by
`c`, or `+pop` of a trivial component. -/
theorem ana_yes (cu : Ident → SkaState FinMap R → Option (SkaState FinMap R))
    (hcu : ∀ st, c (cullS0 regsNoun K id st) ska_cg.cull.battery = (cu id st).map (SkaState.toNoun regsNoun))
    (pl : PassGo FinMap R) (index : Nat)
    (hpl : ∀ lbc st, c (passSubj regsNoun K lbc (A 0) ska_analyze.battery id index 1 st) ska_analyze.loop1
      = (pl id index 1 st).map (anaNoun regsNoun))
    (low : Nat) (back ch : Bool) (st : SkaState FinMap R) :
    nockW c (C (C (A low) (C (flag back) (flag ch))) (C (A index) (C (A 0) (anaSubj regsNoun K id st)))) aYes
      = (if back = true then (cu id st).bind fun st => pl id index 1 st else
         (Ana.above id st.stk).bind fun ab =>
         if ab.length ≠ 1 then (cu id st).bind fun st => pl id index 1 st else
         (Ana.pop id st).map fun st' => (st.next, st')).map (anaNoun regsNoun) := by
  have h10 := slot_K10 hKb
  have h4 := slot_K4 hKb
  have h22 := slot_K22 hKb
  have habv := above_gate K id st.stk
  have hc := hcu st
  have hp := pop_gate' regsNoun K hK id st
  unfold cullS0 at hc
  have hq : ∀ lbc st3, c (C ska_analyze.loop1 (C (A 1) (C lbc (C (A index) (C (A 0) (C ska_analyze.battery
      (C (C (identNoun id) (SkaState.toNoun regsNoun st3)) K))))))) ska_analyze.loop1
      = (pl id index 1 st3).map (anaNoun regsNoun) := fun lbc st3 => hpl lbc st3
  have hcull : ∀ lbc : Noun, nockW c (C lbc (C (A index) (C (A 0) (anaSubj regsNoun K id st)))) aCullP
      = ((cu id st).bind fun st => pl id index 1 st).map (anaNoun regsNoun) := by
    intro lbc
    unfold anaSubj aCullP
    cases hr : cu id st with
    | none =>
      rw [hr] at hc
      simp (disch := ffar_disch) [nock_exec, hcf, h10, hc]
    | some st3 =>
      rw [hr] at hc
      simp (disch := ffar_disch) [nock_exec, hcf, h10, hc, hq]
  unfold aYes aTestY aPopB
  cases back with
  | true =>
    have e := hcull (C (A low) (C (flag true) (flag ch)))
    simp only [flag, if_true] at e ⊢
    simp (disch := ffar_disch) [nock_exec, e]
  | false =>
    have e := hcull (C (A low) (C (flag false) (flag ch)))
    simp only [flag, Bool.false_eq_true, if_false] at e ⊢
    cases hab : Ana.above id st.stk with
    | none =>
      rw [hab] at habv
      unfold anaSubj
      simp (disch := ffar_disch) [nock_exec, hcf, h22, habv, slot_st_stk]
    | some ab =>
      rw [hab] at habv
      rcases ab with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · unfold anaSubj at e ⊢
        simp (disch := ffar_disch) [nock_exec, hcf, h22, habv, slot_st_stk, listNoun] at e ⊢
        exact e
      · unfold anaSubj
        simp (disch := ffar_disch) [nock_exec, hcf, h22, h4, habv, slot_st_stk, slot_st_next, listNoun, hp]
        cases Ana.pop id st <;> rfl
      · unfold anaSubj at e ⊢
        simp (disch := ffar_disch) [nock_exec, hcf, h22, habv, slot_st_stk, listNoun] at e ⊢
        exact e

include hcf hK hKb in
/-- **`+analyze`** over an evaluator `c` that is `nock` off `FFar`:
`analyzeStepH` with `+run` (`run`), `+cull` (`cu`) and the pass loop (`pl`)
made by `c`, with `memo-final` at axis `122` of `K`. -/
theorem analyze_stepW (memoF : Memo FinMap) (hmemo : slot? 122 K = some (memoNoun memoF))
    (run : RunGo FinMap R) (hrun : RunIsW c regsNoun K run)
    (cu : Ident → SkaState FinMap R → Option (SkaState FinMap R))
    (hcu : ∀ st, c (cullS0 regsNoun K id st) ska_cg.cull.battery = (cu id st).map (SkaState.toNoun regsNoun))
    (pl : PassGo FinMap R)
    (hpl : ∀ lbc index st, c (passSubj regsNoun K lbc (A 0) ska_analyze.battery id index 1 st) ska_analyze.loop1
      = (pl id index 1 st).map (anaNoun regsNoun))
    (st : SkaState FinMap R) :
    nockW c (anaSubj regsNoun K id st) ska_analyze.battery
      = (analyzeStepH cu memoF run pl id st).map (anaNoun regsNoun) := by
  conv => lhs; arg 3; rw [analyze_battery_eq]
  rw [ana_hit c hcf regsNoun K hK id memoF hmemo st]
  unfold analyzeStepH
  rcases gitMi memoF id.2 id.1 with _ | _ | hit
  · rfl
  · simp only [Option.bind_some, unitNoun]
    rw [ana_test_miss, ana_miss c hcf regsNoun K hK hKb id run hrun st]
    simp only [ana_rest c regsNoun K id, ana_yes c hcf regsNoun K hK hKb id cu hcu pl _ (hpl · st.next ·)]
    unfold missSt
    cases run id st.next _ with
    | none => rfl
    | some r =>
      simp only [Option.bind_some]
      by_cases hl : r.1.1 = st.next
      · simp only [hl, if_true, ne_eq, not_true_eq_false, if_false]
      · simp only [hl, if_false, ne_eq, not_false_eq_true, if_true]
        rfl
  · simp only [Option.bind_some, unitNoun]
    rw [ana_test_hit, ana_hitb c hcf regsNoun K hK id hit st]
    rfl

end chunks

/-! ## The gates `+sweep` and `+cull` over an evaluator -/

/-- The battery of `+sweep` over an evaluator: the loop's first call, made by
`c`. -/
theorem sweep_batteryW (c : Noun → Noun → Option Noun) (hcf : ∀ s f, FFar f → c s f = nock s f)
    (regsNoun : R → Noun) (K : Noun) (hK : slot? 31 K = some ana) (id : Ident)
    (was : FinMap Ident Unit) (st : SkaState FinMap R) :
    nockW c (sweepS0 regsNoun K id was st) ska_cg.sweep.battery
      = c (sweepSubj regsNoun K id was st (Treap.ins Treap.empty id) [(id, kids st id)] []) ska_cg.sweep.loop := by
  have hkids := kids_gate regsNoun K hK ska_cg.sweep.battery (identNoun id) (Treap.setNoun was) st
  simp only [sweepSubj, stackNoun, listNoun, setNoun_single]
  unfold sweepS0
  nockW_open ska_cg.sweep.battery
  simp (disch := ffar_disch) [nock_exec, hcf, hkids]

set_option maxHeartbeats 4000000 in
theorem nockW_buntF_cons (c : Noun → Noun → Option Noun) (s d : Noun) :
    nockW c s (C buntF d) = (nockW c s buntF).bind fun x => (nockW c s d).bind fun y => some (C x y) := by
  unfold buntF; rw [nockW_cell]

/-- `cull_run` over an evaluator `c` that is `nock` off `FFar`, with the loop
`live` made by `c`, and the bunt of `identity` under `c` as a hypothesis
(`hbunt`; `mold_bunt'` gives it for `nock`). -/
theorem cull_runW (c : Noun → Noun → Option Noun) (hcf : ∀ s f, FFar f → c s f = nock s f)
    (regsNoun : R → Noun) (K : Noun) (hK : slot? 31 K = some ana)
    (hKb : slot? 2 K = some ska_cg.k_bat) (id : Ident) (st : SkaState FinMap R) (ab : List Ident)
    (hab : Ana.above id st.stk = some ab) (o : Option (FinMap Ident Unit))
    (hbunt : ∀ X, slot? 2047 X = some anaTail → nockW c X buntF = some identBunt)
    (hl : c (liveSubj regsNoun K id st (Treap.silt ab) [id] Treap.empty) ska_cg.cull.loop
      = o.map Treap.setNoun) :
    nockW c (cullS0 regsNoun K id st) ska_cg.cull.battery
      = (o.map (cullEnd st (Treap.silt ab))).map (SkaState.toNoun regsNoun) := by
  have hl1 := K_layer1 hK
  have hl2 := K_layer2 hK
  have hK22 := slot_K22 hKb
  have hK63 : slot? 63 K = some anaTail := by rw [K_tail63 hK, ana_tail]
  obtain ⟨g, done, order, stk, next, moved, tick, ticks, regs, stats⟩ := st
  obtain ⟨runs, passes, lateRuns, misses, culled⟩ := stats
  simp only at hab
  have habv := above_gate K id stk
  rw [hab] at habv
  have hsilt : nock (C siltBattery (C (listNoun identNoun ab) layer2)) siltBattery
      = some (Treap.setNoun (Treap.silt ab : FinMap Ident Unit)) := by
    rw [listNoun_map_listN]; exact silt_gate _ _ (silt_setNoun ab)
  simp only [liveSubj, listNoun] at hl
  rw [show Treap.setNoun (Treap.empty : FinMap Ident Unit) = A 0 from FinMap.setNoun_empty] at hl
  simp only [SkaState.toNoun, Stats.toNoun, Option.map_some] at hl habv
  generalize hM : (Treap.silt ab : FinMap Ident Unit) = members at hsilt hl
  cases o with
  | none =>
    simp only [Option.map_none] at hl ⊢
    unfold cullS0
    nockW_open ska_cg.cull.battery
    simp (disch := ffar_disch) [nock_exec, hcf, SkaState.toNoun, Stats.toNoun, hK22, habv, hl2, silt_arm_at, hsilt, hl]
  | some live =>
    have hdead := dif_in_gate layer2 gorIn_morIn_layer2 _ _ _ (dif_setNoun members live)
    simp only [Option.map_some, cullEnd]
    generalize hD : Treap.dif members live = dead at hdead
    by_cases hd : Treap.tap dead = []
    · have h0 := (setNoun_nil_iff dead).2 hd
      rw [h0] at hdead
      simp only [hd, if_true]
      unfold cullS0
      nockW_open ska_cg.cull.battery
      simp (disch := ffar_disch) [nock_exec, hcf, SkaState.toNoun, Stats.toNoun, hK22, habv, hl2, silt_arm_at, hsilt, hl, in_arm,
        in.arm_at, in.dif.arm_at, dif_in_arm, hdead]
    · have h0 : ¬ Treap.setNoun dead = A 0 := fun e => hd ((setNoun_nil_iff dead).1 e)
      have h0' : ¬ A 0 = Treap.setNoun dead := fun e => h0 e.symm
      simp only [hd, if_false]
      have hwyt := wyt_loop layer2 (arith_layer1.1 : Below AddIn layer2) in.battery (Treap.setNoun dead)
        (Tree.of_isSet (FinMap.isSet_setNoun dead))
      rw [wyt_setNoun] at hwyt
      have hadd := add_gate layer1 arith_layer1.1.2 culled (Treap.wyt dead)
      have hskip := cull_skip dead stk
      have hmov := dif_in_gate layer2 gorIn_morIn_layer2 _ _ _ (dif_setNoun moved dead)
      have hrep := cull_rep regsNoun dead
        { g := g, done := done, order := order, stk := stk.filter (fun i => !Treap.has dead i), next := next,
          moved := Treap.dif moved dead, tick := tick, ticks := ticks, regs := regs,
          stats := { runs := runs, passes := passes, lateRuns := lateRuns, misses := misses,
                     culled := culled + Treap.wyt dead } }
        (C (Treap.setNoun dead) (C (Treap.setNoun live) (C (Treap.setNoun members) (C ska_cg.cull.battery
          (C (C (identNoun id) (SkaState.toNoun regsNoun
            { g := g, done := done, order := order, stk := stk.filter (fun i => !Treap.has dead i), next := next,
              moved := Treap.dif moved dead, tick := tick, ticks := ticks, regs := regs,
              stats := { runs := runs, passes := passes, lateRuns := lateRuns, misses := misses,
                         culled := culled + Treap.wyt dead } })) K)))))
        (by simp [nock_exec, hl2])
      simp only [SkaState.toNoun, Stats.toNoun] at hrep
      unfold cullS0
      nockW_open ska_cg.cull.battery
      rw [show (C (A 7) (C (C (A 9) (C (A 186) (C (A 0) (A 2047)))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))
        = buntF from rfl]
      simp (disch := first | ffar_disch | simp [nock_exec, hK63, ana_tail]) [nock_exec, hcf, SkaState.toNoun, Stats.toNoun, hK22, habv, hl2, hl1, silt_arm_at, hsilt, hl, in_arm,
        in.arm_at, in.dif.arm_at, dif_in_arm, hdead, h0', in.wyt.arm_at, wyt_arm, hwyt, add.arm_at,
        add_arm, hadd, skip.arm_at, skip_arm, hskip, has_in_arm, in.has.arm_at, hmov, in.rep.arm_at, rep_arm,
        nockW_buntF_cons c, hbunt, ana_tail, hK63, hrep]


end Compiler
end Formalization
