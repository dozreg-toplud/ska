import lemmas.Ska.RawInvCLConsArm
import lemmas.Ska.RawInvCLCall

/-!
# The run-level liveness with calls, restated with the label clause

README Gaps 14 (b), track D.  `ArmsL` (`RawInvCLRun.lean`) has no member:
its fields `cons` and `n10` are false (`RawInvCLConsArm.lean`,
`RawInvCLTen.lean`: under `goalDup`, a goal with two bonds at one label that
meets `IL`, the cons and `%10` split the goal's tree and `+copy` drops a
bond), so `liveRun_plainOf` is vacuous.  The true statement is `LRL`
(`RawInvCLTen.lean`): `LR` from goals that also meet `LG` (`LabUniq`,
entries below `bo`).

* `liveRun_thenL`, `liveRun_n4*L`, `liveRun_clqL`, `liveRun_n3L`,
  `five_tailL`, `liveRun_n5L`, `liveRun_n2L`: the proofs of
  `RawInvCLArms.lean`, `RawInvCLFive.lean`, `RawInvCLCall.lean` with the
  sub-runs' hypothesis `LRL` (every sub-run there is under a goal
  `ofSure _`, `lg_ofSure`); the text is theirs.
* `liveRun_n7L`: `p` for `q`'s result, whose `LG` comes from `labRun_plain`.
* **`ArmsLL`** (the fields still open, `cons` and `n10`, in the `LRL` form),
  **`liveRun_plainOfL`** (`LRL` on all of `PlainN` from `ArmsLL`),
  `liveRun_plain_topOfL` (the top run: `LG` of `%done` is `True`),
  **`armsLL_of`** (`ArmsLL` from the two checked specs `SplitSpecL` and
  `IntoSpecL`), `liveRun_plain_of_specs`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **A local step, then a sub-run for its result.** -/
theorem liveRun_thenL {rp : CGoalL S → List Nat → CM Map (NextL S)}
    (ih : LiveRunL (Map := Map) rp) {K : Nat → Nat → Prop} {goal : CGoalL S} {g0 g1 g2 : Comp.Gen Map}
    {nex1 nex : NextL S} {region : List Nat} (hG : LG nex1.goal g1) (hJ : IL K nex1.goal g1) (hL : LiveC K goal g0 g1 nex1)
    (h : rp nex1.goal region g1 = some (nex, g2)) : JL K nex g2 ∧ LiveC K goal g0 g2 nex := by
  obtain ⟨J, L⟩ := ih K nex1.goal region g1 g2 nex hJ hG h
  exact ⟨J, hL.trans L⟩

/-- **`%4` under `%done`, both halves.** -/
theorem liveRun_n4_doneL (env : CallEnv) (sup : Option Nomm) {p : Nomm}
    (ih : LRL S Map env sup p) {K : Nat → Nat → Prop} {region : List Nat}
    {g0 g1 : Comp.Gen Map} {nex : NextL S} (hI : IL K (CGoalL.done : CGoalL S) g0)
    (h : runLC env sup (Nomm.n4 p) (CGoalL.done : CGoalL S) region g0 = some (nex, g1)) :
    JL K nex g1 ∧ LiveC K CGoalL.done g0 g1 nex := by
  have hd : g0.drop = false := hI.ats.1
  simp only [runLC] at h
  obtain ⟨pro, ga, ha, h⟩ := bind_some h
  rw [re_apply] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  obtain ⟨arg, gb, hb, h⟩ := bind_some h
  rw [re_apply] at hb
  simp only [Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  obtain ⟨o, gc, hc, h⟩ := bind_some h
  rw [emit_apply] at hc
  simp only [Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  have u0 : unproxy g0.cond g0.re = g0.re := unproxy_none (hI.cond_ge (Nat.le_refl _))
  have u1 : unproxy g0.cond (g0.re + 1) = g0.re + 1 := unproxy_none (hI.cond_ge (Nat.le_succ _))
  refine liveRun_thenL (nex1 := ⟨ofSure (lazyReg (g0.re + 1)), jmp0 g0.bo⟩) ih (lg_ofSure _ _ _) ?_ ?_ h
  · exact il_emitGoal (R := g0.re + 1 + 1) hI (by omega) rfl
      (batc_fresh fun j hj => by simp [finJumps] at hj)
      ⟨fun x hx => by simp at hx, by
        intro q hq x hx
        simp only [List.mem_singleton] at hq
        subst hq
        simp only [Comp.poleRegs, List.mem_cons, List.not_mem_nil, or_false] at hx
        omega, show g0.re < g0.re + 1 + 1 by omega⟩
      (fun r hr => by simp [blockDefs, aliasDst] at hr; omega)
      (fun r hr => by
        have e : r = g0.re + 1 := hr
        subst e; exact ⟨Nat.le_succ _, by omega, by simp [blockDefs, aliasDst]⟩) trivial
  · refine liveC_emitG hI _ _ _ (fun r hr hn => hn ?_) (fun j hj => by simp [renBlob, renFin, getJmps] at hj)
    obtain ⟨-, hr | ⟨hnd, hr⟩⟩ := hr
    · have e : r = g0.re + 1 := by
        simpa [renBlob, renPole, OpsRF, aliasReads, aliasDst, Opt.poleRegs, u0, u1] using hr
      exact e
    · exact (hnd (by simpa [renBlob, renPole, renFin, finRegs, defsOf, aliasDst, u0, u1] using hr)).elim

/-- **`%4` under `%pick`, both halves.** -/
theorem liveRun_n4_pickL (env : CallEnv) (sup : Option Nomm) {p : Nomm}
    (ih : LRL S Map env sup p) {K : Nat → Nat → Prop} {z o : Jmp}
    {region : List Nat} {g0 g1 : Comp.Gen Map} {nex : NextL S} (hI : IL K (CGoalL.pick z o : CGoalL S) g0)
    (h : runLC env sup (Nomm.n4 p) (CGoalL.pick z o : CGoalL S) region g0 = some (nex, g1)) :
    JL K nex g1 ∧ LiveC K (CGoalL.pick z o) g0 g1 nex := by
  have hd : g0.drop = false := hI.ats.1
  obtain ⟨hz, ho⟩ := (hI.goal : GoalL g0 (CGoalL.pick z o))
  obtain ⟨bz, hbz, -, az⟩ := hz
  obtain ⟨bo', hbo, -, ao⟩ := ho
  simp only [runLC] at h
  obtain ⟨pro, ga, ha, h⟩ := bind_some h
  rw [re_apply] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  obtain ⟨arg, gb, hb, h⟩ := bind_some h
  rw [re_apply] at hb
  simp only [Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  obtain ⟨o', gc, hc, h⟩ := bind_some h
  rw [emit_apply] at hc
  simp only [Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  have u0 : unproxy g0.cond g0.re = g0.re := unproxy_none (hI.cond_ge (Nat.le_refl _))
  have u1 : unproxy g0.cond (g0.re + 1) = g0.re + 1 := unproxy_none (hI.cond_ge (Nat.le_succ _))
  refine liveRun_thenL (nex1 := ⟨ofSure (lazyReg (g0.re + 1)), jmp0 g0.bo⟩) ih (lg_ofSure _ _ _) ?_ ?_ h
  · exact il_emitGoal (R := g0.re + 1 + 1) hI (by omega) rfl
      (batc_fresh fun j hj => by
        simp only [finJumps, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        · exact hI.goal.1
        · exact hI.goal.2)
      ⟨fun x hx => by simp at hx, by
        intro q hq x hx
        simp only [List.mem_singleton] at hq
        subst hq
        simp only [Comp.poleRegs, List.mem_cons, List.not_mem_nil, or_false] at hx
        omega, ⟨show g0.re < g0.re + 1 + 1 by omega, jmpIn_nil az, jmpIn_nil ao⟩⟩
      (fun r hr => by simp [blockDefs, aliasDst] at hr; omega)
      (fun r hr => by
        have e : r = g0.re + 1 := hr
        subst e; exact ⟨Nat.le_succ _, by omega, by simp [blockDefs, aliasDst]⟩) trivial
  · refine liveC_emitG hI _ _ _ (fun r hr hn => (hn ?_).elim) (fun j hj => ?_)
    · obtain ⟨-, hr | ⟨hnd, hr⟩⟩ := hr
      · have e : r = g0.re + 1 := by
          simpa [renBlob, renPole, OpsRF, aliasReads, aliasDst, Opt.poleRegs, u0, u1] using hr
        exact e
      · exact (hnd (by simpa [renBlob, renPole, renFin, finRegs, jmpRegs, renJmp_nil _ az, renJmp_nil _ ao,
          defsOf, aliasDst, u0, u1, az, ao] using hr)).elim
    · simp only [renBlob, renFin, getJmps, renJmp_nil _ az, renJmp_nil _ ao, List.mem_cons, List.not_mem_nil,
        or_false] at hj
      rcases hj with rfl | rfl
      · exact ⟨hI.lab hbz, fun r hl _ _ => Or.inl hl⟩
      · exact ⟨hI.lab hbo, fun r hl _ _ => Or.inr hl⟩

/-- **The tail of `%4` under `%next`**: the `%inc` block into `pro`, hopping
to `there`, then the operand for its argument. -/
theorem liveRun_n4_tailL (env : CallEnv) (sup : Option Nomm) {p : Nomm}
    (ih : LRL S Map env sup p) {K : Nat → Nat → Prop} {region : List Nat}
    {pro there : Nat} {g1 g2 : Comp.Gen Map} {nex : NextL S}
    (hI : IL K (CGoalL.next (ofSure (lazyReg (S := S) pro)) (jmp0 there)) g1)
    (h : (do
      let arg ← re
      let o ← emit ⟨[], [Pole.inc arg pro], Termin.hop (jmp0 there)⟩
      runLC env sup p (CGoalL.next (ofSure (lazyReg (S := S) arg)) (jmp0 o)) region : CM Map (NextL S)) g1 =
        some (nex, g2)) :
    JL K nex g2 ∧ LiveC K (CGoalL.next (ofSure (lazyReg (S := S) pro)) (jmp0 there)) g1 g2 nex := by
  have hd : g1.drop = false := hI.ats.1
  obtain ⟨arg, ga, ha, h⟩ := bind_some h
  rw [re_apply] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  obtain ⟨o, gc, hc, h⟩ := bind_some h
  rw [emit_apply] at hc
  simp only [Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  obtain ⟨hF, -, hE⟩ := (hI.goal : GoalL g1 (CGoalL.next (ofSure (lazyReg (S := S) pro)) (jmp0 there)))
  obtain ⟨bt, hbt, -, -⟩ := hF
  have hpro : pro < g1.re ∧ ¬ Defd g1.blocks pro :=
    (hE _ (List.mem_cons_self ..)).2.2 pro (show pro = pro from rfl)
  have hkey : HoonMap.get g1.cond pro = Option.none := by
    cases e : HoonMap.get g1.cond pro with
    | none => rfl
    | some v => exact ((hI.cond _ v e).2.2.1 (gregL_ofSure.mpr rfl)).elim
  have upro : unproxy g1.cond pro = pro := unproxy_none hkey
  have u1 : unproxy g1.cond g1.re = g1.re := unproxy_none (hI.cond_ge (Nat.le_refl _))
  refine liveRun_thenL (nex1 := ⟨ofSure (lazyReg (S := S) g1.re), jmp0 g1.bo⟩) ih (lg_ofSure _ _ _) ?_ ?_ h
  · exact il_emitGoal' (R := g1.re + 1) hI (by omega) rfl (batc_fresh fun j hj => by
        simp only [finJumps, List.mem_singleton] at hj
        subst hj; exact hI.goal.1)
      ⟨fun x hx => by simp at hx, by
        intro q hq x hx
        simp only [List.mem_singleton] at hq
        subst hq
        simp only [Comp.poleRegs, List.mem_cons, List.not_mem_nil, or_false] at hx
        omega, fun x hx => by simp [jmp0] at hx⟩
      (fun r hr => by
        simp [blockDefs, aliasDst] at hr
        subst hr; exact hkey)
      (fun r hr => by
        have e : r = g1.re := hr
        subst e; refine ⟨Nat.le_refl _, by omega, ?_⟩
        simp only [blockDefs, aliasDst, List.nil_append, List.filterMap_cons, List.filterMap_nil,
          List.mem_singleton]
        omega) trivial
  · refine liveC_emitG hI _ _ _ (fun r hr hn => (hn ?_).elim) (fun j hj => ?_)
    · obtain ⟨-, hr | ⟨hnd, hr⟩⟩ := hr
      · have hne : g1.re ≠ pro := by omega
        have e : r = g1.re := by
          simpa [renBlob, renPole, OpsRF, aliasReads, aliasDst, Opt.poleRegs, u1, upro, List.erase_cons, hne]
            using hr
        exact e
      · simp [renBlob, renFin, finRegs, jmpRegs, jmp0, renJmp] at hr
    · simp only [renBlob, renFin, getJmps, List.mem_singleton] at hj
      subst hj
      refine ⟨hI.lab hbt, fun r hl hnd _ => ?_⟩
      have hr : r ≠ pro := fun e => hnd (by
        subst e; simp [renBlob, renPole, blockDefs, aliasDst, upro])
      exact hl.mono_r fun x hk => hk.elim id fun hz => (hr ((lazK_ofSure.mp hz).2)).elim

/-- **`%4` under `%next`, both halves**, from the spec of `+collapse-lazy-atom`. -/
theorem liveRun_n4_nextL (env : CallEnv) (sup : Option Nomm) {p : Nomm} (hC : CollapseSpecL S Map)
    (ih : LRL S Map env sup p) {K : Nat → Nat → Prop} {laz : Lazy S} {th : Jmp}
    {region : List Nat} {g0 g1 : Comp.Gen Map} {nex : NextL S} (hI : IL K (CGoalL.next laz th) g0)
    (h : runLC env sup (Nomm.n4 p) (CGoalL.next laz th) region g0 = some (nex, g1)) :
    JL K nex g1 ∧ LiveC K (CGoalL.next laz th) g0 g1 nex := by
  simp only [runLC] at h
  obtain ⟨a, ga, ha, h⟩ := bind_some h
  obtain ⟨⟨pro, there⟩, gb, hb, h⟩ := bind_some h
  have T : IL K (CGoalL.next (ofSure (lazyReg (S := S) pro)) (jmp0 there)) gb ∧
      LiveC K (CGoalL.next laz th) g0 gb ⟨ofSure (lazyReg (S := S) pro), jmp0 there⟩ := by
    cases a with
    | some x =>
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      exact hC K laz th g0 ga pro there hI ha
    | none =>
      obtain ⟨hn, hargs, rfl⟩ := collapseL_none ha
      obtain ⟨r, gc, hc, hb⟩ := bind_some hb
      rw [re_apply] at hc
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      simp only [hargs, if_true, pure_apply, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hb
      exact il_live_none hI hn hargs
  obtain ⟨J, L⟩ := liveRun_n4_tailL env sup ih T.1 h
  exact ⟨J, T.2.trans L⟩

/-- **`%4` under every goal, both halves**, from the spec of
`+collapse-lazy-atom`. -/
theorem liveRun_n4L (env : CallEnv) (sup : Option Nomm) {p : Nomm} (hC : CollapseSpecL S Map)
    (ih : LRL S Map env sup p) :
    LRL S Map env sup (Nomm.n4 p) := by
  intro K goal region g0 g1 nex hI hG h
  cases goal with
  | done => exact liveRun_n4_doneL env sup ih hI h
  | pick z o => exact liveRun_n4_pickL env sup ih hI h
  | next laz th => exact liveRun_n4_nextL env sup hC ih hI h

/-- **The `%clq` block for a `%pick` goal**, then the operand for its
register: `%3` under `%pick`, and the tail of `%3` under `%done` and
`%next`. -/
theorem liveRun_clqL (env : CallEnv) (sup : Option Nomm) {p : Nomm}
    (ih : LRL S Map env sup p) {K : Nat → Nat → Prop} {z o : Jmp}
    {region : List Nat} {g0 g1 : Comp.Gen Map} {nex : NextL S} (hI : IL K (CGoalL.pick z o : CGoalL S) g0)
    (h : (do
      let r ← re
      let oc ← emit ⟨[], [], Termin.clq r z o⟩
      runLC env sup p (CGoalL.next (ofSure (lazyReg (S := S) r)) (jmp0 oc)) region : CM Map (NextL S)) g0 =
        some (nex, g1)) :
    JL K nex g1 ∧ LiveC K (CGoalL.pick z o) g0 g1 nex := by
  have hd : g0.drop = false := hI.ats.1
  obtain ⟨hz, ho⟩ := (hI.goal : GoalL g0 (CGoalL.pick z o))
  obtain ⟨bz, hbz, -, az⟩ := hz
  obtain ⟨bo', hbo, -, ao⟩ := ho
  obtain ⟨r, ga, ha, h⟩ := bind_some h
  rw [re_apply] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  obtain ⟨o', gc, hc, h⟩ := bind_some h
  rw [emit_apply] at hc
  simp only [Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  have u0 : unproxy g0.cond g0.re = g0.re := unproxy_none (hI.cond_ge (Nat.le_refl _))
  refine liveRun_thenL (nex1 := ⟨ofSure (lazyReg (S := S) g0.re), jmp0 g0.bo⟩) ih (lg_ofSure _ _ _) ?_ ?_ h
  · exact il_emitGoal (R := g0.re + 1) hI (by omega) rfl
      (batc_fresh fun j hj => by
        simp only [finJumps, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        · exact hI.goal.1
        · exact hI.goal.2)
      ⟨fun x hx => by simp at hx, RegsIn.nil _, ⟨show g0.re < g0.re + 1 by omega, jmpIn_nil az, jmpIn_nil ao⟩⟩
      (fun r hr => by simp [blockDefs] at hr)
      (fun r hr => by
        have e : r = g0.re := hr
        subst e; exact ⟨Nat.le_refl _, by omega, by simp [blockDefs]⟩) trivial
  · refine liveC_emitG hI _ _ _ (fun r hr hn => (hn ?_).elim) (fun j hj => ?_)
    · obtain ⟨-, hr | ⟨-, hr⟩⟩ := hr
      · simp [renBlob, OpsRF] at hr
      · exact (show r = g0.re by
          simpa [renBlob, renFin, finRegs, jmpRegs, renJmp_nil _ az, renJmp_nil _ ao, u0, az, ao] using hr)
    · simp only [renBlob, renFin, getJmps, renJmp_nil _ az, renJmp_nil _ ao, List.mem_cons, List.not_mem_nil,
        or_false] at hj
      rcases hj with rfl | rfl
      · exact ⟨hI.lab hbz, fun r hl _ _ => Or.inl hl⟩
      · exact ⟨hI.lab hbo, fun r hl _ _ => Or.inr hl⟩

/-- **`%3` under every goal, both halves**, from the specs of
`+collapse-lazy-atom` and `+forl`. -/
theorem liveRun_n3L (env : CallEnv) (sup : Option Nomm) {p : Nomm} (hC : CollapseSpecL S Map)
    (hF : ForlSpecL S Map) (ih : LRL S Map env sup p) :
    LRL S Map env sup (Nomm.n3 p) := by
  intro K goal region g0 g1 nex hI hG h
  cases goal with
  | pick z o =>
    simp only [runLC] at h
    exact liveRun_clqL env sup ih hI h
  | done =>
    simp only [runLC] at h
    obtain ⟨⟨o0, o1⟩, ga, ha, h⟩ := bind_some h
    obtain ⟨I, D⟩ := doneBlocks_spec hI ha
    obtain ⟨J, L⟩ := liveRun_clqL env sup ih I h
    exact ⟨J, fun r hl => (D r (L r hl)).elim⟩
  | next laz th =>
    simp only [runLC] at h
    by_cases hn : noneEquivalentL laz = true
    · rw [if_pos hn] at h; exact ih K _ region g0 g1 nex hI hG h
    · rw [if_neg hn] at h
      obtain ⟨a, ga, ha, h⟩ := bind_some h
      cases a with
      | none => cases h
      | some x =>
        obtain ⟨r, there⟩ := x
        obtain ⟨I1, L1⟩ := hC K laz th g0 ga r there hI ha
        obtain ⟨⟨z, o'⟩, gb, hb, h⟩ := bind_some h
        obtain ⟨I2, L2⟩ := hF K r there ga gb z o' I1 hb
        obtain ⟨J, L⟩ := liveRun_clqL env sup ih I2 h
        exact ⟨J, fun y hl => L1 y (L2 y (L y hl))⟩

/-- **The tail of `%5`** from the goal "`rq` at `o`": `JL` of the result,
and a register live at its entry is not `rp` and is live for that goal. -/
theorem five_tailL (env : CallEnv) (sup : Option Nomm) {p q : Nomm} (hp : PlainN p) (hq : PlainN q)
    (ihp : LRL S Map env sup p) (ihq : LRL S Map env sup q) {K : Nat → Nat → Prop} {region : List Nat}
    {rp rq o : Nat} {g3 g4 g5 g6 g7 : Comp.Gen Map} {nq nq' np nex : NextL S}
    (hI : IL K (CGoalL.next (ofSure (lazyReg (S := S) rq)) (jmp0 o)) g3)
    (hrp : rp < g3.re) (hdp : ¬ Defd g3.blocks rp) (hkp : HoonMap.get g3.cond rp = Option.none) (hne : rp ≠ rq)
    (h1 : runLC env sup q (CGoalL.next (ofSure (lazyReg (S := S) rq)) (jmp0 o)) region g3 = some (nq, g4))
    (h2 : pastL env.cod nq p region g4 = some (nq', g5))
    (h3 : runLC env sup p (CGoalL.next (ofSure (lazyReg (S := S) rp)) nq'.th) region g5 = some (np, g6))
    (h4 : copyL np nq'.laz g6 = some (nex, g7)) :
    JL K nex g7 ∧ ∀ r, LiveK (unpM g7) (fun x y => K x y ∨ lazK nex.th.there nex.laz x y) nex.th.there r →
      r ≠ rp ∧ GLiveKL (unpM g3) K (CGoalL.next (ofSure (lazyReg (S := S) rq)) (jmp0 o)) r := by
  obtain ⟨Jq, Lq⟩ := ihq K _ region g3 g4 nq hI (lg_ofSure _ _ _) h1
  obtain ⟨Ip, Lpast⟩ := pastL_spec Jq h2
  have Fq := frameRun_plain env q hq sup _ region g3 g4 nq h1
  have Dpast := frame_pastL h2
  obtain ⟨-, -, -, lq1, lq2⟩ := (labRun_plain (S := S) (Map := Map) env q hq sup
    (CGoalL.next (ofSure (lazyReg (S := S) rq)) (jmp0 o)) region).run g3 nq g4 hI.ats
    ⟨hI.goal.1, lg_ofSure _ _ _⟩ h1
  obtain ⟨LU2, -⟩ := lab_pastL h2 lq1 lq2
  rcases nq' with ⟨second, ⟨a2, s2⟩⟩
  obtain ⟨_, _, _, ha2⟩ := (Ip.goal : GoalL g5 (CGoalL.next second ⟨a2, s2⟩)).1
  simp only at ha2
  subst ha2
  have hrs : ∀ y, LReg second y → y ≠ rp := by
    intro y hy e
    rcases Fq.2 y (gregL_goal.mpr (Dpast.2 y hy)) with h | h
    · exact hne (e.symm.trans (gregL_ofSure.mp h))
    · omega
  have FL : FrL (CGoalL.next (ofSure (lazyReg (S := S) rq)) (jmp0 o)) g3 g5 :=
    frL_iff.mpr ((frL_iff.mp Fq.1).trans (Dpast.1.mono fun y h => h.elim))
  have Ip' : IL (fun x y => K x y ∨ lazK s2 second x y)
      (CGoalL.next (ofSure (lazyReg (S := S) rp)) (⟨[], s2⟩ : Jmp)) g5 :=
    il_lazyReg_after (il_addKills Ip) FL hrp hdp hkp (fun hg => hne (gregL_ofSure.mp hg)) Ip.goal.1
  obtain ⟨Jp, Lp⟩ := ihp _ _ region g5 g6 np Ip' (lg_ofSure _ _ _) h3
  have Fp := frameRun_plain env p hp sup _ region g5 g6 np h3
  obtain ⟨-, KP56, -, LU1, -⟩ := (labRun_plain (S := S) (Map := Map) env p hp sup
    (CGoalL.next (ofSure (lazyReg (S := S) rp)) (⟨[], s2⟩ : Jmp)) region).run g5 np g6 Ip.ats
    ⟨Ip.goal.1, lg_ofSure _ _ _⟩ h3
  have Ig : IL K (CGoalL.next second (jmp0 s2)) g6 :=
    il_glue Ip Jp (fun x y h => Or.inl h) Fp KP56 hrs
  have TA : TreesApart np.th.there np.laz s2 second := by
    intro e he e' he' y hy hy'
    have hg : GRegL (CGoalL.next np.laz np.th) y := ⟨e, he, hy⟩
    have hlt := ((Ip.goal : GoalL g5 (CGoalL.next second (⟨[], s2⟩ : Jmp))).2.2 e' he').2.2 y hy'
    rcases Fp.2 y hg with h | h
    · exact hrs y ((gregL_next (th := jmp0 s2)).mp ⟨e', he', hy'⟩) (gregL_ofSure.mp h)
    · have := hlt.1; omega
  obtain ⟨Inex, Lc⟩ := (copyL_spec (S := S) (Map := Map)) K np second s2 g6 g7 nex
    (Jp.monoK fun x y h => Or.inl h) Ig TA LU1 LU2 h4
  refine ⟨Inex, fun r hl => ?_⟩
  have h5 : LiveK (unpM g5) (fun x y => (K x y ∨ lazK s2 second x y) ∨
      lazK s2 (ofSure (lazyReg (S := S) rp)) x y) s2 r := Lp r (Lc r hl)
  have hne' : r ≠ rp := fun e => h5.nk (Or.inr (lazK_ofSure.mpr ⟨rfl, e⟩))
  have h5' : LiveK (unpM g5) (fun x y => K x y ∨ lazK s2 second x y) s2 r := h5.mono fun x y h => Or.inl h
  exact ⟨hne', Lq r (Lpast r h5')⟩

/-- **The arm `%5`, both halves**, from `LR` of its parts. -/
theorem liveRun_n5L (env : CallEnv) (sup : Option Nomm) {p q : Nomm} (hp : PlainN p) (hq : PlainN q)
    (ihp : LRL S Map env sup p) (ihq : LRL S Map env sup q) : LRL S Map env sup (Nomm.n5 p q) := by
  intro K goal region g0 g1 nex hI hG h
  simp only [runLC] at h
  obtain ⟨rp, ga, ha, h⟩ := bind_some h
  obtain ⟨erp, ar, abl, acd, abo, adr⟩ := re_state ha
  obtain ⟨rq, gb, hb, h⟩ := bind_some h
  obtain ⟨erq, br, bbl, bcd, bbo, bdr⟩ := re_state hb
  obtain ⟨o, gc, hc, h⟩ := bind_some h
  obtain ⟨nq, gd, h1, h⟩ := bind_some h
  obtain ⟨nq', ge, h2, h⟩ := bind_some h
  obtain ⟨np, gf, h3, h4⟩ := bind_some h
  subst erp erq
  have Ib : IL K goal gb := il_re_up hI (by omega) (bbl.trans abl) (bcd.trans acd) (bbo.trans abo) (bdr.trans adr)
  have hU : unpM gb = unpM g0 := by simp only [unpM, bbl, abl, bcd, acd]
  have hpl : g0.re < gb.re := by omega
  have hql : ga.re < gb.re := by omega
  have hne : g0.re ≠ ga.re := by omega
  have hdp : ¬ Defd gb.blocks g0.re := by
    rw [bbl, abl]; intro hd; have := defd_lt hI.regs hd; omega
  have hdq : ¬ Defd gb.blocks ga.re := by
    rw [bbl, abl]; intro hd; have := defd_lt hI.regs hd; omega
  have hkp : HoonMap.get gb.cond g0.re = Option.none := by rw [bcd, acd]; exact hI.cond_ge (Nat.le_refl _)
  have hkq : HoonMap.get gb.cond ga.re = Option.none := by rw [bcd, acd]; exact hI.cond_ge (by omega)
  have hgp : ¬ GRegL goal g0.re := fun hg => by have := (hI.greg_lt hg).1; omega
  have hgq : ¬ GRegL goal ga.re := fun hg => by have := (hI.greg_lt hg).1; omega
  have O : OPh K goal gb gc g0.re ga.re o := by
    cases goal with
    | pick z o0 => exact oph_eqq Ib hpl hql hne hdp hdq hkp hkq hc
    | done =>
      obtain ⟨⟨o0, o1⟩, gx, hx, hc'⟩ := bind_some hc
      obtain ⟨Ix, Dead⟩ := doneBlocks_spec Ib hx
      have dx := frame_doneBlocks hx
      obtain ⟨p1, p2, p3⟩ := df_keep dx hpl (by omega) hdp hkp
      obtain ⟨q1, q2, q3⟩ := df_keep dx hql (by omega) hdq hkq
      obtain ⟨O1, O2, O3⟩ := oph_eqq Ix p1 q1 hne p2 q2 p3 q3 hc'
      exact ⟨O1, fun r hr hl => (Dead r (O2 r hr hl)).elim, O3⟩
    | next laz th =>
      obtain ⟨a, gx, hx, hc'⟩ := bind_some hc
      obtain ⟨dA, rA⟩ := frame_collapseL hx
      have nlp : ¬ (gb.re ≤ g0.re ∨ LReg laz g0.re) := fun h => h.elim (fun h => by omega)
        fun h => hgp (gregL_next.mpr h)
      have nlq : ¬ (gb.re ≤ ga.re ∨ LReg laz ga.re) := fun h => h.elim (fun h => by omega)
        fun h => hgq (gregL_next.mpr h)
      obtain ⟨p1, p2, p3⟩ := df_keep dA hpl nlp hdp hkp
      obtain ⟨q1, q2, q3⟩ := df_keep dA hql nlq hdq hkq
      cases a with
      | none =>
        obtain ⟨hn, hargs, rfl⟩ := collapseL_none hx
        dsimp only at hc'
        rw [if_pos hargs] at hc'
        exact oph_equ Ib hn hargs hpl hql hdp hdq hkp hkq hc'
      | some x =>
        obtain ⟨r0, o0⟩ := x
        dsimp only at hc'
        obtain ⟨⟨z, o1⟩, gy, hy, hc''⟩ := bind_some hc'
        obtain ⟨I1, L1⟩ := collapseSpecL K laz th gb gx r0 o0 Ib hx
        obtain ⟨I2, L2⟩ := forlSpecL K r0 o0 gx gy z o1 I1 hy
        have dB := frame_forl hy
        have r0f := rA r0 o0 rfl
        have xr : gb.re ≤ gx.re := dA.1
        obtain ⟨p1', p2', p3'⟩ := df_keep dB p1 (fun h => h.elim (fun e => nlp (e ▸ r0f)) fun h => by omega)
          p2 p3
        obtain ⟨q1', q2', q3'⟩ := df_keep dB q1 (fun h => h.elim (fun e => nlq (e ▸ r0f)) fun h => by omega)
          q2 q3
        obtain ⟨O1, O2, O3⟩ := oph_eqq I2 p1' q1' hne p2' q2' p3' q3' hc''
        exact ⟨O1, fun r hr hl => L1 r (L2 r (O2 r hr hl)), O3⟩
  obtain ⟨O1, O2, O3, O4, O5⟩ := O
  obtain ⟨J, L⟩ := five_tailL env sup hp hq ihp ihq O1 O3 O4 O5 hne h1 h2 h3 h4
  refine ⟨J, fun r hl => ?_⟩
  obtain ⟨hr, hg⟩ := L r hl
  have := O2 r hr hg
  rw [hU] at this
  exact this

/-- **The arm `%2` (the indirect call), both halves**, from `LR` of its
parts. -/
theorem liveRun_n2L (env : CallEnv) (sup : Option Nomm) {p q : Nomm} (hp : PlainN p) (hq : PlainN q)
    (ihp : LRL S Map env sup p) (ihq : LRL S Map env sup q) : LRL S Map env sup (Nomm.n2 p q Option.none) := by
  intro K goal region g0 g1 nex hI hG h
  simp only [runLC, callL] at h
  obtain ⟨ns, ga, ha, h⟩ := bind_some h
  obtain ⟨⟨out, pro⟩, gb, hb, h⟩ := bind_some h
  obtain ⟨rSub, gc, hc, h⟩ := bind_some h
  obtain ⟨erS, cr, cbl, ccd, cbo, cdr⟩ := re_state hc
  obtain ⟨rFol, gd, hd, h⟩ := bind_some h
  obtain ⟨erF, dr, dbl, dcd, dbo, ddr⟩ := re_state hd
  obtain ⟨o, ge, he, h⟩ := bind_some h
  obtain ⟨nq, gf, h1, h⟩ := bind_some h
  obtain ⟨nq', gg, h2, h⟩ := bind_some h
  obtain ⟨np, gh, h3, h4⟩ := bind_some h
  subst erS erF
  have Ia : IL K ns.goal ga := il_simpleNextL hI ha
  have La : LiveC K goal g0 ga ns := liveC_simpleNextL hI ha
  obtain ⟨Ib, Lb⟩ := kerfSpecL K ns ga gb out pro Ia hb
  have Id : IL K (CGoalL.next (ofSure (lazyReg (S := S) pro)) (jmp0 out)) gd :=
    il_re_up Ib (by omega) (dbl.trans cbl) (dcd.trans ccd) (dbo.trans cbo) (ddr.trans cdr)
  have hU : unpM gd = unpM gb := by simp only [unpM, dbl, cbl, dcd, ccd]
  have hpro : pro < gb.re := (Ib.entry_regs (o := out) _ List.mem_cons_self pro rfl).1
  have hpl : gb.re < gd.re := by omega
  have hql : gc.re < gd.re := by omega
  have hne : gb.re ≠ gc.re := by omega
  have hdp : ¬ Defd gd.blocks gb.re := by
    rw [dbl, cbl]; intro hd'; have := defd_lt Ib.regs hd'; omega
  have hdq : ¬ Defd gd.blocks gc.re := by
    rw [dbl, cbl]; intro hd'; have := defd_lt Ib.regs hd'; omega
  have hkp : HoonMap.get gd.cond gb.re = Option.none := by rw [dcd, ccd]; exact Ib.cond_ge (Nat.le_refl _)
  have hkq : HoonMap.get gd.cond gc.re = Option.none := by rw [dcd, ccd]; exact Ib.cond_ge (by omega)
  obtain ⟨O1, O2, O3, O4, O5⟩ := oph_nok Id hpl hql hne (by omega) (by omega) hdp hdq hkp hkq he
  obtain ⟨J, L⟩ := five_tailL env sup hp hq ihp ihq O1 O3 O4 O5 hne h1 h2 h3 h4
  refine ⟨J, fun r hl => ?_⟩
  obtain ⟨hr, hg⟩ := L r hl
  have h5 := O2 r hr hg
  rw [hU] at h5
  exact La r (Lb r h5)

/-- **`%7` with the label clause**: `q` for the goal, then `p` for `q`'s
result, whose `LG` comes from `labRun_plain`. -/
theorem liveRun_n7L (env : CallEnv) (sup : Option Nomm) {p q : Nomm} (hq : PlainN q)
    (ihq : LRL S Map env (some p) q) (ihp : LRL S Map env sup p) : LRL S Map env sup (Nomm.n7 p q) := by
  intro K goal region g0 g2 nex hI hG h
  simp only [runLC] at h
  obtain ⟨nex1, g1, h1, h2⟩ := bind_some h
  obtain ⟨J1, L1⟩ := ihq K goal region g0 g1 nex1 hI hG h1
  have G1 : LG nex1.goal g1 :=
    ((labRun_plain (S := S) (Map := Map) env q hq (some p) goal region).run g0 nex1 g1 hI.ats
      ⟨gfl_of_il hI, hG⟩ h1).2.2.2
  obtain ⟨J2, L2⟩ := ihp K nex1.goal region g1 g2 nex (jl_il J1) G1 h2
  exact ⟨J2, L1.trans L2⟩

/-- **The arms not closed yet, in the `LRL` form.** -/
structure ArmsLL (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (env : CallEnv) :
    Prop where
  cons : ∀ sup p q, PlainN p → PlainN q → LRL S Map env sup p → LRL S Map env sup q →
    LRL S Map env sup (Nomm.cons p q)
  n10 : ∀ sup a v q, PlainN v → PlainN q → LRL S Map env sup v → LRL S Map env sup q →
    LRL S Map env sup (Nomm.n10 a v q)

/-- **The run-level liveness with calls on all of `PlainN`**, with the label
clause, from the arms not closed yet. -/
theorem liveRun_plainOfL (env : CallEnv) (A : ArmsLL S Map env) :
    ∀ (nm : Nomm), PlainN nm → ∀ (sup : Option Nomm), LRL S Map env sup nm
  | Nomm.n0 ax, _, sup => lrl_of_lr (liveRun_n0 env sup ax)
  | Nomm.n1 k, _, sup => lrl_of_lr (liveRun_n1 env sup k)
  | Nomm.n3 p, h, sup => liveRun_n3L env sup collapseSpecL forlSpecL (liveRun_plainOfL env A p h sup)
  | Nomm.n4 p, h, sup => liveRun_n4L env sup collapseSpecL (liveRun_plainOfL env A p h sup)
  | Nomm.n5 p q, h, sup =>
    liveRun_n5L env sup h.1 h.2 (liveRun_plainOfL env A p h.1 sup) (liveRun_plainOfL env A q h.2 sup)
  | Nomm.cons p q, h, sup =>
    A.cons sup p q h.1 h.2 (liveRun_plainOfL env A p h.1 sup) (liveRun_plainOfL env A q h.2 sup)
  | Nomm.n7 p q, h, sup =>
    liveRun_n7L env sup h.2 (liveRun_plainOfL env A q h.2 (some p)) (liveRun_plainOfL env A p h.1 sup)
  | Nomm.n10 a v q, h, sup =>
    A.n10 sup a v q h.1 h.2 (liveRun_plainOfL env A v h.1 sup) (liveRun_plainOfL env A q h.2 sup)
  | Nomm.n2 p q Option.none, h, sup =>
    liveRun_n2L env sup h.1 h.2 (liveRun_plainOfL env A p h.1 sup) (liveRun_plainOfL env A q h.2 sup)
  | Nomm.n2 _ _ (some _), h, _ => h.elim
  | Nomm.n6 _ _ _, h, _ => h.elim
  | Nomm.n11s _ _ _, h, _ => h.elim
  | Nomm.n11d _ _ _ _, h, _ => h.elim
  | Nomm.n12 _ _, h, _ => h.elim
  | Nomm.mean _ _ _ _ _, h, _ => h.elim

/-- **The top run** of a `PlainN` nomm from `gen0` under `%done`, from the
arms not closed yet in the `LRL` form. -/
theorem liveRun_plain_topOfL (env : CallEnv) (A : ArmsLL S Map env) {nm : Nomm} (hp : PlainN nm)
    {nex : NextL S} {g1 : Comp.Gen Map}
    (h : runLC env Option.none nm (CGoalL.done : CGoalL S) [] (gen0 : Comp.Gen Map) = some (nex, g1)) :
    JL (fun _ _ => False) nex g1 ∧ LiveC (fun _ _ => False) CGoalL.done gen0 g1 nex :=
  liveRun_plainOfL env A nm hp Option.none _ _ _ _ _ _ il_gen0 trivial h

/-- **`ArmsLL` from the specs of `+split` and `+into`** (both checked at
every split and into of `PlainN`, not proved). -/
theorem armsLL_of (env : CallEnv) (hS : SplitSpecL S Map) (hI : IntoSpecL S Map) : ArmsLL S Map env :=
  ⟨fun sup _ _ hp hq ihp ihq => liveRun_consL env sup hp hq ihp ihq hS, armsL_n10L hI env⟩

theorem liveRun_plain_of_specs (env : CallEnv) (hS : SplitSpecL S Map) (hI : IntoSpecL S Map) :
    ∀ (nm : Nomm), PlainN nm → ∀ (sup : Option Nomm), LRL S Map env sup nm :=
  liveRun_plainOfL env (armsLL_of env hS hI)

end Raw
end SkaModel
end Formalization
