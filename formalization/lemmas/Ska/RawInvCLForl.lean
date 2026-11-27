import lemmas.Ska.RawInvCLArms

/-!
# The run-level liveness with calls: `+forl`

README Gaps 14 (b), track D.

* `il_emitDone`: a block emitted after fresh registers, defining only
  registers that are no key of `cond`, keeps `IL` under `%done`.
* `unpM_emitted_lt`: the unproxied blocks below `bo` do not change on an
  emit.
* **`forlSpecL`**: the spec `ForlSpecL` of `+forl` (the block `barg` with
  the parameter `[r]` hopping to `there`, and the blocks `if0` / `if1`
  hopping to it with `[some r0]` / `[some r1]`).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **A block emitted after fresh registers keeps `IL` under `%done`**, when
it defines only registers that are no key of `cond`. -/
theorem il_emitDone {K : Nat → Nat → Prop} {goal : CGoalL S} {g : Comp.Gen Map} (hI : IL K goal g) {R : Nat}
    (hR : g.re ≤ R) {b : Blob} (hbat : BATC g.blocks b) (hin : BlobIn (· < R) b)
    (hdef : ∀ r ∈ blockDefs b, HoonMap.get g.cond r = Option.none) :
    IL K (CGoalL.done : CGoalL S) (({ g with re := R } : Comp.Gen Map).emitted b) := by
  have hd : g.drop = false := hI.ats.1
  have A : ATS ({ g with re := R } : Comp.Gen Map) := hI.ats
  obtain ⟨A1, -, -⟩ := ats_emit A hbat
  have hfree : HoonMap.get g.blocks g.bo = Option.none := hI.ats.free
  have hD : ∀ r, Defd (({ g with re := R } : Comp.Gen Map).emitted b).blocks r ↔ Defd g.blocks r ∨ r ∈ blockDefs b :=
    fun r => by
      show Defd (if g.drop then g.blocks else HoonMap.put g.blocks g.bo b) r ↔ _
      simp only [hd, Bool.false_eq_true, if_false]
      exact defd_put hfree
  refine ⟨A1, fun k b' hb' => ?_, fun k v hk => ?_, hI.kvan.mono (Nat.le_succ _), trivial⟩
  · rw [em_get (g := ({ g with re := R } : Comp.Gen Map)) hd] at hb'
    split at hb'
    · cases hb'; exact hin
    · exact (hI.regs k b' hb').mono fun x hx => Nat.lt_of_lt_of_le hx hR
  · obtain ⟨k1, k2, -, k4, k5⟩ := hI.cond k v hk
    refine ⟨Nat.lt_of_lt_of_le k1 hR, fun hdk => ?_, fun hg => hg, Nat.lt_of_lt_of_le k4 hR, k5⟩
    rcases (hD k).mp hdk with h | h
    · exact k2 h
    · have e := hdef k h
      have hk' : HoonMap.get g.cond k = some v := hk
      rw [e] at hk'; cases hk'

/-- The unproxied blocks below `bo` do not change on an emit. -/
theorem unpM_emitted_lt {g : Comp.Gen Map} (hd : g.drop = false) (b : Blob) {x : Nat} (hx : x < g.bo) :
    HoonMap.get (unpM (g.emitted b)) x = HoonMap.get (unpM g) x :=
  unpM_emitted_ne hd b (Nat.ne_of_lt hx)

/-- **The spec of `+forl`.** -/
theorem forlSpecL : ForlSpecL S Map := by
  intro K r there g1 g2 z o hI h
  have hd : g1.drop = false := hI.ats.1
  obtain ⟨hF, -, hE⟩ := (hI.goal : GoalL g1 (CGoalL.next (ofSure (lazyReg (S := S) r)) (jmp0 there)))
  obtain ⟨bt, hbt, hpt, -⟩ := hF
  have hr : r < g1.re ∧ ¬ Defd g1.blocks r := (hE _ (List.mem_cons_self ..)).2.2 r (show r = r from rfl)
  have hkey : HoonMap.get g1.cond r = Option.none := by
    cases e : HoonMap.get g1.cond r with
    | none => rfl
    | some v => exact ((hI.cond _ v e).2.2.1 (gregL_ofSure.mpr rfl)).elim
  have hthere : there < g1.bo := hI.lab hbt
  simp only [forl] at h
  obtain ⟨r0, ga, ha, h⟩ := bind_some h
  rw [re_apply] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  obtain ⟨r1, gb, hb, h⟩ := bind_some h
  rw [re_apply] at hb
  simp only [Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  obtain ⟨barg, gc, hc, h⟩ := bind_some h
  rw [emit_apply] at hc
  simp only [Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  obtain ⟨if0, gd, hd', h⟩ := bind_some h
  rw [emit_apply] at hd'
  simp only [Option.some.injEq, Prod.mk.injEq] at hd'
  obtain ⟨rfl, rfl⟩ := hd'
  obtain ⟨if1, ge, he, h⟩ := bind_some h
  rw [emit_apply] at he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  -- the three states
  have u0 : unproxy g1.cond g1.re = g1.re := unproxy_none (hI.cond_ge (Nat.le_refl _))
  have u1 : unproxy g1.cond (g1.re + 1) = g1.re + 1 := unproxy_none (hI.cond_ge (Nat.le_succ _))
  have ur : unproxy g1.cond r = r := unproxy_none hkey
  have hbB : ∀ (k : Nat) (x : Nat), x < g1.re + 1 + 1 → BlobIn (· < g1.re + 1 + 1)
      (⟨[], [Pole.imm (A k) x], Termin.hop ⟨[some x], g1.bo⟩⟩ : Blob) := fun k x hx =>
    ⟨fun y hy => by simp at hy, by
      intro q hq y hy
      simp only [List.mem_singleton] at hq
      subst hq
      simp only [Comp.poleRegs, List.mem_cons, List.not_mem_nil, or_false] at hy
      subst hy; exact hx, fun y hy => by
      simp only [List.mem_singleton, Option.some.injEq] at hy
      subst hy; exact hx⟩
  have I1 := il_emitDone (R := g1.re + 1 + 1) hI (by omega) (b := ⟨[r], [], Termin.hop (jmp0 there)⟩)
    (batc_fresh fun j hj => by
      simp only [finJumps, List.mem_singleton] at hj
      subst hj; exact ⟨bt, hbt, hpt, rfl⟩)
    ⟨fun x hx => by
      simp only [List.mem_singleton] at hx
      show x < g1.re + 1 + 1; omega, RegsIn.nil _, jmpIn_nil rfl⟩
    (fun x hx => by
      simp only [blockDefs, List.filterMap_nil, List.append_nil, List.mem_singleton] at hx
      subst hx; exact hkey)
  have hd1 : (({ g1 with re := g1.re + 1 + 1 } : Comp.Gen Map).emitted
      ⟨[r], [], Termin.hop (jmp0 there)⟩).drop = false := hd
  have hbatI : ∀ (x : Nat), BATC (({ g1 with re := g1.re + 1 + 1 } : Comp.Gen Map).emitted
      ⟨[r], [], Termin.hop (jmp0 there)⟩).blocks (⟨[], [Pole.imm (A 0) x], Termin.hop ⟨[some x], g1.bo⟩⟩ : Blob) := by
    intro x
    refine ⟨fun j hj => ?_, fun ht => by cases ht⟩
    simp only [finJumps, List.mem_singleton] at hj
    subst hj
    exact ⟨⟨[r], [], Termin.hop (jmp0 there)⟩, by
      rw [em_get (g := ({ g1 with re := g1.re + 1 + 1 } : Comp.Gen Map)) hd, if_pos rfl], rfl⟩
  have I2 := il_emitDone (R := g1.re + 1 + 1) I1 (Nat.le_refl _)
    (hbatI g1.re) (hbB 0 g1.re (by omega))
    (fun x hx => by
      simp only [blockDefs, aliasDst, List.nil_append, List.filterMap_cons, List.filterMap_nil,
        List.mem_singleton] at hx
      subst hx; exact hI.cond_ge (Nat.le_refl _))
  have hbatI2 : BATC ((({ g1 with re := g1.re + 1 + 1 } : Comp.Gen Map).emitted
      ⟨[r], [], Termin.hop (jmp0 there)⟩).emitted ⟨[], [Pole.imm (A 0) g1.re], Termin.hop ⟨[some g1.re], g1.bo⟩⟩).blocks
      (⟨[], [Pole.imm (A 1) (g1.re + 1)], Termin.hop ⟨[some (g1.re + 1)], g1.bo⟩⟩ : Blob) := by
    refine ⟨fun j hj => ?_, fun ht => by cases ht⟩
    simp only [finJumps, List.mem_singleton] at hj
    subst hj
    refine ⟨⟨[r], [], Termin.hop (jmp0 there)⟩, ?_, rfl⟩
    rw [em_get hd1, if_neg (by simp [emitted_bo]),
      em_get (g := ({ g1 with re := g1.re + 1 + 1 } : Comp.Gen Map)) hd, if_pos rfl]
  have I3 := il_emitDone (R := g1.re + 1 + 1) I2 (Nat.le_refl _) hbatI2 (hbB 1 (g1.re + 1) (by omega))
    (fun x hx => by
      simp only [blockDefs, aliasDst, List.nil_append, List.filterMap_cons, List.filterMap_nil,
        List.mem_singleton] at hx
      subst hx; exact hI.cond_ge (Nat.le_succ _))
  have hd2 : ((({ g1 with re := g1.re + 1 + 1 } : Comp.Gen Map).emitted
      ⟨[r], [], Termin.hop (jmp0 there)⟩).emitted
      ⟨[], [Pole.imm (A 0) g1.re], Termin.hop ⟨[some g1.re], g1.bo⟩⟩).drop = false := hd
  refine ⟨il_regoal I3 ⟨⟨⟨[], [Pole.imm (A 0) g1.re], Termin.hop ⟨[some g1.re], g1.bo⟩⟩, ?_, rfl, rfl⟩,
    ⟨⟨[], [Pole.imm (A 1) (g1.re + 1)], Termin.hop ⟨[some (g1.re + 1)], g1.bo⟩⟩, ?_, rfl, rfl⟩⟩ fun _ h => h, ?_⟩
  · rw [em_get hd2, if_neg (by simp [emitted_bo, jmp0]), em_get hd1, if_pos (by simp [emitted_bo, jmp0])]
  · rw [em_get hd2, if_pos (by simp [emitted_bo, jmp0])]
  -- the liveness: `if0` / `if1` → `barg` → `there`
  have hbarg : HoonMap.get (unpM ((((({ g1 with re := g1.re + 1 + 1 } : Comp.Gen Map).emitted
      ⟨[r], [], Termin.hop (jmp0 there)⟩).emitted
      ⟨[], [Pole.imm (A 0) g1.re], Termin.hop ⟨[some g1.re], g1.bo⟩⟩).emitted
      ⟨[], [Pole.imm (A 1) (g1.re + 1)], Termin.hop ⟨[some (g1.re + 1)], g1.bo⟩⟩))) g1.bo =
      some (renBlob (unproxy g1.cond) ⟨[r], [], Termin.hop (jmp0 there)⟩) := by
    rw [unpM_emitted_lt hd2 _ (by simp [emitted_bo]; omega), unpM_emitted_lt hd1 _ (by simp [emitted_bo])]
    exact unpM_emitted_self (g := { g1 with re := g1.re + 1 + 1 }) hd _
  have hframe : ∀ x, x < g1.bo → HoonMap.get (unpM ((((({ g1 with re := g1.re + 1 + 1 } : Comp.Gen Map).emitted
      ⟨[r], [], Termin.hop (jmp0 there)⟩).emitted
      ⟨[], [Pole.imm (A 0) g1.re], Termin.hop ⟨[some g1.re], g1.bo⟩⟩).emitted
      ⟨[], [Pole.imm (A 1) (g1.re + 1)], Termin.hop ⟨[some (g1.re + 1)], g1.bo⟩⟩))) x = HoonMap.get (unpM g1) x := by
    intro x hx
    rw [unpM_emitted_lt hd2 _ (by simp [emitted_bo]; omega), unpM_emitted_lt hd1 _ (by simp [emitted_bo]; omega),
      unpM_emitted_lt (g := { g1 with re := g1.re + 1 + 1 }) hd _ hx]
    rfl
  -- from `barg`
  have hB : ∀ y, LiveK (unpM ((((({ g1 with re := g1.re + 1 + 1 } : Comp.Gen Map).emitted
      ⟨[r], [], Termin.hop (jmp0 there)⟩).emitted
      ⟨[], [Pole.imm (A 0) g1.re], Termin.hop ⟨[some g1.re], g1.bo⟩⟩).emitted
      ⟨[], [Pole.imm (A 1) (g1.re + 1)], Termin.hop ⟨[some (g1.re + 1)], g1.bo⟩⟩))) K g1.bo y →
      LiveK (unpM g1) (fun x y => K x y ∨ lazK there (ofSure (lazyReg (S := S) r)) x y) there y := by
    intro y hl
    cases hl with
    | here hb' hr' _ =>
      rw [hbarg] at hb'; cases hb'
      obtain ⟨-, hr' | ⟨-, hr'⟩⟩ := hr'
      · simp [renBlob, OpsRF] at hr'
      · simp [renBlob, renFin, finRegs, jmpRegs, jmp0, renJmp] at hr'
    | next hb' hj hl' hdf _ =>
      rw [hbarg] at hb'; cases hb'
      simp only [renBlob, renFin, getJmps, List.mem_singleton] at hj
      subst hj
      have hyr : y ≠ r := fun e => hdf (by subst e; simp [blockDefs, renBlob, ur])
      have hl2 := (liveK_frameP hI.downU hframe hthere).mp hl'
      exact hl2.mono_r fun x hk => hk.elim id fun hz => (hyr ((lazK_ofSure.mp hz).2)).elim
  -- from `if0` / `if1`
  have hI01 : ∀ (k x : Nat), x = g1.re ∨ x = g1.re + 1 → ∀ (lab : Nat) y,
      HoonMap.get (unpM ((((({ g1 with re := g1.re + 1 + 1 } : Comp.Gen Map).emitted
      ⟨[r], [], Termin.hop (jmp0 there)⟩).emitted
      ⟨[], [Pole.imm (A 0) g1.re], Termin.hop ⟨[some g1.re], g1.bo⟩⟩).emitted
      ⟨[], [Pole.imm (A 1) (g1.re + 1)], Termin.hop ⟨[some (g1.re + 1)], g1.bo⟩⟩))) lab =
        some (renBlob (unproxy g1.cond) ⟨[], [Pole.imm (A k) x], Termin.hop ⟨[some x], g1.bo⟩⟩) →
      LiveK (unpM ((((({ g1 with re := g1.re + 1 + 1 } : Comp.Gen Map).emitted
      ⟨[r], [], Termin.hop (jmp0 there)⟩).emitted
      ⟨[], [Pole.imm (A 0) g1.re], Termin.hop ⟨[some g1.re], g1.bo⟩⟩).emitted
      ⟨[], [Pole.imm (A 1) (g1.re + 1)], Termin.hop ⟨[some (g1.re + 1)], g1.bo⟩⟩))) K lab y →
      LiveK (unpM g1) (fun x y => K x y ∨ lazK there (ofSure (lazyReg (S := S) r)) x y) there y := by
    intro k x hx lab y hget hl
    have ux : unproxy g1.cond x = x := by rcases hx with rfl | rfl <;> assumption
    cases hl with
    | here hb' hr' _ =>
      rw [hget] at hb'; cases hb'
      obtain ⟨-, hr' | ⟨hnd, hr'⟩⟩ := hr'
      · simp [renBlob, renPole, OpsRF, aliasReads, aliasDst, Opt.poleRegs, ux] at hr'
      · have e : y = x := by simpa [renBlob, renFin, finRegs, jmpRegs, renJmp, ux] using hr'
        exact (hnd (by simp [renBlob, renPole, defsOf, aliasDst, ux, e])).elim
    | next hb' hj hl' _ _ =>
      rw [hget] at hb'; cases hb'
      simp only [renBlob, renFin, getJmps, List.mem_singleton] at hj
      subst hj
      exact hB y hl'
  intro y hl
  rcases hl with hl | hl
  · refine hI01 0 g1.re (Or.inl rfl) _ y ?_ hl
    show HoonMap.get _ (g1.bo + 1) = _
    rw [unpM_emitted_lt hd2 _ (by simp [emitted_bo])]
    exact unpM_emitted_self hd1 _
  · refine hI01 1 (g1.re + 1) (Or.inr rfl) _ y ?_ hl
    exact unpM_emitted_self hd2 _

end Raw
end SkaModel
end Formalization
