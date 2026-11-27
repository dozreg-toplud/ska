import lemmas.Ska.RawInvCLCollapse
import lemmas.Ska.CompCollapsePre

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

/-! ## `%4` under `%next` -/

/-- **`il_emitGoal` with old definitions**: the block may define registers
below `re` that are no key of `cond`. -/
theorem il_emitGoal' {K : Nat → Nat → Prop} {goal : CGoalL S} {g : Comp.Gen Map} (hI : IL K goal g) {R : Nat}
    (hR : g.re ≤ R) {b : Blob} {s : Sure S} (hp : b.par = []) (hbat : BATC g.blocks b) (hin : BlobIn (· < R) b)
    (hdef : ∀ r ∈ blockDefs b, HoonMap.get g.cond r = Option.none)
    (hs : ∀ r, NMem s.ned r → g.re ≤ r ∧ r < R ∧ r ∉ blockDefs b)
    (hds : Distinct s.ned) :
    IL K (CGoalL.next (ofSure s) (jmp0 g.bo)) (({ g with re := R } : Comp.Gen Map).emitted b) := by
  have hd : g.drop = false := hI.ats.1
  have A : ATS ({ g with re := R } : Comp.Gen Map) := hI.ats
  obtain ⟨A1, -, hget⟩ := ats_emit A hbat
  have hfree : HoonMap.get g.blocks g.bo = Option.none := hI.ats.free
  have hD : ∀ r, Defd (({ g with re := R } : Comp.Gen Map).emitted b).blocks r ↔ Defd g.blocks r ∨ r ∈ blockDefs b :=
    fun r => by
      show Defd (if g.drop then g.blocks else HoonMap.put g.blocks g.bo b) r ↔ _
      simp only [hd, Bool.false_eq_true, if_false]
      exact defd_put hfree
  refine ⟨A1, fun k b' hb' => ?_, fun k v hk => ?_, hI.kvan.mono (Nat.le_succ _), ?_⟩
  · rw [em_get (g := ({ g with re := R } : Comp.Gen Map)) hd] at hb'
    split at hb'
    · cases hb'; exact hin
    · exact (hI.regs k b' hb').mono fun x hx => Nat.lt_of_lt_of_le hx hR
  · obtain ⟨k1, k2, k3, k4, k5⟩ := hI.cond k v hk
    refine ⟨Nat.lt_of_lt_of_le k1 hR, fun hdk => ?_, fun hg => ?_, Nat.lt_of_lt_of_le k4 hR, k5⟩
    · rcases (hD k).mp hdk with h | h
      · exact k2 h
      · have e := hdef k h
        have hk' : HoonMap.get g.cond k = some v := hk
        rw [e] at hk'; cases hk'
    · have := (hs k (gregL_ofSure.mp hg)).1; omega
  · refine ⟨⟨b, hget, hp, rfl⟩, ?_, fun e he => ?_⟩
    · rw [entries_ofSure]; exact List.pairwise_singleton _ _
    · rw [entries_ofSure, List.mem_singleton] at he
      subst he
      refine ⟨⟨b, hget, hp⟩, hds, fun r hr => ⟨(hs r hr).2.1, fun hdr => ?_⟩⟩
      rcases (hD r).mp hdr with h | h
      · have := defd_lt hI.regs h; have := (hs r hr).1; omega
      · exact (hs r hr).2.2 h

/-- **A none-equivalent lazy need kills nothing.** -/
theorem lazK_none {o : Nat} {laz : Lazy S} (h : noneEquivalentL laz = true) {x r : Nat} : ¬ lazK o laz x r := by
  rintro ⟨e, he, -, hm⟩
  rcases List.mem_cons.mp he with rfl | he
  · rw [(noneEq_sure h).1] at hm; exact hm
  · rw [(noneEq_sure (noneEq_entries laz h e he)).1] at hm; exact hm

/-- **What `+collapse-lazy-atom` must give** (the spec that the arms `%3`,
`%4`, `%5` use under `%next`): when it returns `(r, there)`, the goal "`r`
at `there`" holds `IL`, and a register live at `there` with `r` killed there
is one the goal `%next laz th` may leave live. -/
def CollapseSpecL (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] : Prop :=
  ∀ (K : Nat → Nat → Prop) (laz : Lazy S) (th : Jmp) (g0 g1 : Comp.Gen Map) (r there : Nat),
    IL K (CGoalL.next laz th) g0 →
    (collapseLazyAtomL ⟨laz, th⟩ : CM Map (Option (Nat × Nat))) g0 = some (some (r, there), g1) →
    IL K (CGoalL.next (ofSure (lazyReg (S := S) r)) (jmp0 there)) g1 ∧
      LiveC K (CGoalL.next laz th) g0 g1 ⟨ofSure (lazyReg (S := S) r), jmp0 there⟩

/-- `+collapse-lazy-atom` that returns `~`: the need is none-equivalent, the
continuation takes no argument, the state is unchanged. -/
theorem collapseL_none {laz : Lazy S} {th : Jmp} {g0 g1 : Comp.Gen Map}
    (h : (collapseLazyAtomL ⟨laz, th⟩ : CM Map (Option (Nat × Nat))) g0 = some (Option.none, g1)) :
    noneEquivalentL laz = true ∧ th.args = [] ∧ g1 = g0 := by
  simp only [collapseLazyAtomL] at h
  by_cases ha : th.args ≠ []
  · rw [if_pos ha] at h; cases h
  · rw [if_neg ha] at h
    simp only [ne_eq, Decidable.not_not] at ha
    by_cases hn : noneEquivalentL laz = true
    · rw [if_pos hn] at h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨hn, ha, h.2.symm⟩
    · exfalso
      rw [if_neg hn] at h
      obtain ⟨ned, ga, -, h⟩ := bind_some h
      obtain ⟨⟨r, o⟩, gb, -, h⟩ := bind_some h
      obtain ⟨g, gc, hc, h⟩ := bind_some h
      simp only [get_apply, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      split at h
      · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq, reduceCtorEq, false_and] at h
      · obtain ⟨u, gd, -, h⟩ := bind_some h
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq, reduceCtorEq, false_and] at h

/-- **The `~` branch of `%4` under `%next`**: a fresh `pro` at the
continuation, which the none-equivalent need does not kill. -/
theorem il_live_none {K : Nat → Nat → Prop} {laz : Lazy S} {th : Jmp} {g0 : Comp.Gen Map}
    (hI : IL K (CGoalL.next laz th) g0) (hn : noneEquivalentL laz = true) (_ha : th.args = []) :
    IL K (CGoalL.next (ofSure (lazyReg (S := S) g0.re)) (jmp0 th.there)) ({ g0 with re := g0.re + 1 } : Comp.Gen Map) ∧
      LiveC K (CGoalL.next laz th) g0 ({ g0 with re := g0.re + 1 } : Comp.Gen Map)
        ⟨ofSure (lazyReg (S := S) g0.re), jmp0 th.there⟩ := by
  obtain ⟨hF, -, -⟩ := (hI.goal : GoalL g0 (CGoalL.next laz th))
  obtain ⟨b, hb, hp, -⟩ := hF
  refine ⟨⟨hI.ats, fun k b' hb' => (hI.regs k b' hb').mono fun x hx => Nat.lt_succ_of_lt hx,
    fun k v hk => ?_, hI.kvan, ⟨b, hb, hp, rfl⟩, ?_, fun e he => ?_⟩, fun y hl => ?_⟩
  · obtain ⟨k1, k2, -, k4, k5⟩ := hI.cond k v hk
    refine ⟨Nat.lt_succ_of_lt k1, k2, fun hg => ?_, Nat.lt_succ_of_lt k4, k5⟩
    have e : k = g0.re := gregL_ofSure.mp hg
    omega
  · rw [entries_ofSure]; exact List.pairwise_singleton _ _
  · rw [entries_ofSure, List.mem_singleton] at he
    subst he
    refine ⟨⟨b, hb, hp⟩, trivial, fun r hr => ?_⟩
    have e : r = g0.re := hr
    subst e
    exact ⟨Nat.lt_succ_self _, fun hdr => by have := defd_lt hI.regs hdr; omega⟩
  · exact hl.mono fun x z hk => hk.imp id fun hz => (lazK_none hn hz).elim

/-- **The tail of `%4` under `%next`**: the `%inc` block into `pro`, hopping
to `there`, then the operand for its argument. -/
theorem liveRun_n4_tail (env : CallEnv) (sup : Option Nomm) {p : Nomm}
    (ih : LiveRun (Map := Map) IL JL (runLC (S := S) env sup p)) {K : Nat → Nat → Prop} {region : List Nat}
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
  refine liveRun_then (nex1 := ⟨ofSure (lazyReg (S := S) g1.re), jmp0 g1.bo⟩) ih ?_ ?_ h
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
theorem liveRun_n4_next (env : CallEnv) (sup : Option Nomm) {p : Nomm} (hC : CollapseSpecL S Map)
    (ih : LiveRun (Map := Map) IL JL (runLC (S := S) env sup p)) {K : Nat → Nat → Prop} {laz : Lazy S} {th : Jmp}
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
  obtain ⟨J, L⟩ := liveRun_n4_tail env sup ih T.1 h
  exact ⟨J, T.2.trans L⟩

/-- **`%4` under every goal, both halves**, from the spec of
`+collapse-lazy-atom`. -/
theorem liveRun_n4 (env : CallEnv) (sup : Option Nomm) {p : Nomm} (hC : CollapseSpecL S Map)
    (ih : LiveRun (Map := Map) IL JL (runLC (S := S) env sup p)) :
    LiveRun (Map := Map) IL JL (runLC (S := S) env sup (Nomm.n4 p)) := by
  intro K goal region g0 g1 nex hI h
  cases goal with
  | done => exact liveRun_n4_done env sup ih hI h
  | pick z o => exact liveRun_n4_pick env sup ih hI h
  | next laz th => exact liveRun_n4_next env sup hC ih hI h

end Raw
end SkaModel
end Formalization
