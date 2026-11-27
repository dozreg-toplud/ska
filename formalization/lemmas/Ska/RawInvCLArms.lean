import lemmas.Ska.RawInvCLCollapse

/-!
# The run-level liveness with calls: the arms that emit a local block

README Gaps 14 (b), track D.  The cases `%3`, `%4`, `%5` under `%done` and
`%pick` emit one block after fresh registers, with the goal of the sub-run at
it, and run the operand for that goal: no walk.

* **`liveC_emitG`**: the liveness spec of such a block, from what it reads
  and where it jumps.
* `liveRun_then`: the local block's `IL` and `LiveC`, then the sub-run's
  `LiveRun`, compose.
* **`liveRun_n4_done`**, **`liveRun_n4_pick`**: `%4` under `%done` and
  `%pick`, both halves, from `LiveRun` of the operand.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The liveness spec of a fresh block with the goal `ofSure s` at it**: a
register it reads first that the need does not define, and a register live
past one of its jumps (each below `bo`) that it does not define, are ones the
outer goal may leave live. -/
theorem liveC_emitG {K : Nat → Nat → Prop} {goal : CGoalL S} {g0 : Comp.Gen Map} (hI : IL K goal g0) (R : Nat)
    (b : Blob) (s : Sure S)
    (hb : ∀ r, BlockRF (renBlob (unproxy g0.cond) b) r → ¬ NMem s.ned r → GLiveKL (unpM g0) K goal r)
    (hj : ∀ j ∈ getJmps (renBlob (unproxy g0.cond) b).fin, j.there < g0.bo ∧
      ∀ r, LiveK (unpM g0) K j.there r → r ∉ blockDefs (renBlob (unproxy g0.cond) b) → ¬ NMem s.ned r →
        GLiveKL (unpM g0) K goal r) :
    LiveC K goal g0 (({ g0 with re := R } : Comp.Gen Map).emitted b) ⟨ofSure s, jmp0 g0.bo⟩ := by
  have hd : g0.drop = false := hI.ats.1
  have hget := unpM_emitted_self (g := { g0 with re := R }) hd b
  intro y hl
  cases hl with
  | here hb' hr hk' =>
    have hb2 := hget.symm.trans hb'
    cases hb2
    exact hb y hr (fun hm => hk' (Or.inr (lazK_ofSure.mpr ⟨rfl, hm⟩)))
  | next hb' hjj hl hdf hk' =>
    have hb2 := hget.symm.trans hb'
    cases hb2
    obtain ⟨hlt, hJ⟩ := hj _ hjj
    refine hJ y ?_ hdf (fun hm => hk' (Or.inr (lazK_ofSure.mpr ⟨rfl, hm⟩)))
    exact (liveK_frameP hI.downU (fun x hx => (unpM_emitted_ne (g := { g0 with re := R }) hd _
      (Nat.ne_of_lt hx)).trans rfl) hlt).mp (hl.mono fun _ _ hk => Or.inl hk)

/-- **A local step, then a sub-run for its result.** -/
theorem liveRun_then {rp : CGoalL S → List Nat → CM Map (NextL S)}
    (ih : LiveRun (Map := Map) IL JL rp) {K : Nat → Nat → Prop} {goal : CGoalL S} {g0 g1 g2 : Comp.Gen Map}
    {nex1 nex : NextL S} {region : List Nat} (hJ : IL K nex1.goal g1) (hL : LiveC K goal g0 g1 nex1)
    (h : rp nex1.goal region g1 = some (nex, g2)) : JL K nex g2 ∧ LiveC K goal g0 g2 nex := by
  obtain ⟨J, L⟩ := ih K nex1.goal region g1 g2 nex hJ h
  exact ⟨J, hL.trans L⟩

/-- No key of `cond` at or above `re` under `IL`. -/
theorem IL.cond_ge {K : Nat → Nat → Prop} {goal : CGoalL S} {g : Comp.Gen Map} (h : IL K goal g) {x : Nat}
    (hx : g.re ≤ x) : HoonMap.get g.cond x = Option.none := by
  cases e : HoonMap.get g.cond x with
  | none => rfl
  | some v => have := (h.cond _ v e).1; omega

/-! ## `%4` under `%done` and `%pick` -/

/-- **`%4` under `%done`, both halves.** -/
theorem liveRun_n4_done (env : CallEnv) (sup : Option Nomm) {p : Nomm}
    (ih : LiveRun (Map := Map) IL JL (runLC (S := S) env sup p)) {K : Nat → Nat → Prop} {region : List Nat}
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
  refine liveRun_then (nex1 := ⟨ofSure (lazyReg (g0.re + 1)), jmp0 g0.bo⟩) ih ?_ ?_ h
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
theorem liveRun_n4_pick (env : CallEnv) (sup : Option Nomm) {p : Nomm}
    (ih : LiveRun (Map := Map) IL JL (runLC (S := S) env sup p)) {K : Nat → Nat → Prop} {z o : Jmp}
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
  refine liveRun_then (nex1 := ⟨ofSure (lazyReg (g0.re + 1)), jmp0 g0.bo⟩) ih ?_ ?_ h
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

end Raw
end SkaModel
end Formalization
