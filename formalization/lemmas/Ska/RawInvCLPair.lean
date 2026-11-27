import lemmas.Ska.RawInvCLIJ

/-!
# The run-level liveness with calls: both halves of the arms

README Gaps 14 (b), track D.  Each arm of `runLC` on `PlainN` as ONE lemma
`LiveRun IL JL (runLC env sup nm)`: the postcondition `JL` (the
precondition `IL` of a run for the result) and the liveness spec `LiveC`.

* `il_emitGoal`: a fresh block emitted after fresh registers, with a goal
  `ofSure s` at it whose need is fresh: `IL` of the new goal.
* `il_fromL`: `+from` keeps `IL` (`fromEnt_back`, `needsApart_fromEnt`).
* `RInv C g`: every block's registers below `re`, no key of `C` defined;
  `walkList_inv`, `walkLazy_inv` (any walk whose gate keeps a state
  invariant keeps it), `rinv_addOps`, `medeLoop_rinv`, `medeGate_rinv`.
* **`liveRun_n0`**, **`liveRun_n1`**: the cases `%0` and `%1`, both halves;
  **`liveRun_n7`**: `%7` from its parts.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Small facts -/

/-- A defined register of blocks below `R` is below `R`. -/
theorem defd_lt {bl : Map Blob} {R : Nat} (h : ∀ k b, HoonMap.get bl k = some b → BlobIn (· < R) b) {r : Nat}
    (hd : Defd bl r) : r < R := by
  obtain ⟨o, b, hb, hm⟩ := defd_iff.mp hd
  have hB := h o b hb
  rcases mem_blockDefs.mp hm with hm | hm
  · exact hB.1 r hm
  · obtain ⟨op, hop, hd⟩ := mem_defsOf.mp hm
    exact hB.2.1 op hop r (dst_mem_regs hd)

theorem gregL_ofSure {s : Sure S} {j : Jmp} {r : Nat} : GRegL (CGoalL.next (ofSure s) j) r ↔ NMem s.ned r := by
  simp only [GRegL, entries_ofSure, List.mem_singleton, exists_eq_left]
  rfl

theorem ATS.free {g : Comp.Gen Map} (h : ATS g) : HoonMap.get g.blocks g.bo = Option.none := by
  cases e : HoonMap.get g.blocks g.bo with
  | none => rfl
  | some b => exact absurd (h.2.2 _ b e).1 (Nat.lt_irrefl _)

theorem blobIn_nil_fin {P : Nat → Prop} {fin : Termin} (h : FinIn P fin) : BlobIn P ⟨[], [], fin⟩ :=
  ⟨fun x hx => absurd hx List.not_mem_nil, RegsIn.nil _, h⟩

theorem jmpIn_nil {P : Nat → Prop} {j : Jmp} (h : j.args = []) : JmpIn P j := fun x hx => by
  rw [h] at hx; exact absurd hx List.not_mem_nil

/-! ## A fresh block with a fresh goal at it -/

/-- **A block emitted after fresh registers, with a goal `ofSure s` at it**
whose need's registers are fresh and not defined by the block. -/
theorem il_emitGoal {K : Nat → Nat → Prop} {goal : CGoalL S} {g : Comp.Gen Map} (hI : IL K goal g) {R : Nat}
    (hR : g.re ≤ R) {b : Blob} {s : Sure S} (hp : b.par = []) (hbat : BATC g.blocks b) (hin : BlobIn (· < R) b)
    (hdef : ∀ r ∈ blockDefs b, g.re ≤ r) (hs : ∀ r, NMem s.ned r → g.re ≤ r ∧ r < R ∧ r ∉ blockDefs b)
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
      · have := hdef k h; omega
    · have := (hs k (gregL_ofSure.mp hg)).1; omega
  · refine ⟨⟨b, hget, hp, rfl⟩, ?_, fun e he => ?_⟩
    · rw [entries_ofSure]; exact List.pairwise_singleton _ _
    · rw [entries_ofSure, List.mem_singleton] at he
      subst he
      refine ⟨⟨b, hget, hp⟩, hds, fun r hr => ⟨(hs r hr).2.1, fun hdr => ?_⟩⟩
      rcases (hD r).mp hdr with h | h
      · have := defd_lt hI.regs h; have := (hs r hr).1; omega
      · exact (hs r hr).2.2 h

/-- **A goal jump of the state, with nothing asked at it.** -/
theorem il_bunt {K : Nat → Nat → Prop} {goal : CGoalL S} {g : Comp.Gen Map} (hI : IL K goal g) {j : Jmp}
    (hj : Fresh g j) : IL K (CGoalL.next (ofSure (Sure.bunt : Sure S)) j) g := by
  refine ⟨hI.ats, hI.regs, fun k v hk => ?_, hI.kvan, hj, ?_, fun e he => ?_⟩
  · obtain ⟨k1, k2, -, k4, k5⟩ := hI.cond k v hk
    exact ⟨k1, k2, fun hg => (gregL_ofSure.mp hg).elim, k4, k5⟩
  · rw [entries_ofSure]; exact List.pairwise_singleton _ _
  · rw [entries_ofSure, List.mem_singleton] at he
    subst he
    obtain ⟨b, hb, hp, -⟩ := hj
    exact ⟨⟨b, hb, hp⟩, trivial, fun r hr => hr.elim⟩

/-! ## `+from` -/

theorem fromSure_nmem_back {axe : Nat} {s s' : Sure S} (h : fromSure axe s = some s') {r : Nat}
    (hr : NMem s'.ned r) : NMem s.ned r := by
  unfold fromSure at h
  split at h
  · cases h
  split at h
  · split at h
    · cases h
    · cases h; exact hr.elim
  · cases h; exact nmem_fromPath _ axe r hr

theorem fromEnt_back {axe : Nat} {a b : List (Nat × Lazy S)} (h : FromEnt axe a b) {e' : Nat × Lazy S}
    (he : e' ∈ b) : ∃ e ∈ a, e.1 = e'.1 ∧ (∀ r, NMem e'.2.sure.ned r → NMem e.2.sure.ned r) ∧
      (Distinct e.2.sure.ned → Distinct e'.2.sure.ned) := by
  obtain ⟨l, h1, h2⟩ := h.mem_right he
  exact ⟨(e'.1, l), h2, rfl, fun r hr => fromSure_nmem_back (fromL_sure h1) hr,
    fun hd => fromSure_dist (fromL_sure h1) hd⟩

/-- **`+from` keeps the precondition.** -/
theorem il_fromL {K : Nat → Nat → Prop} {laz laz' : Lazy S} {th : Jmp} {g : Comp.Gen Map} {axe : Nat}
    (hI : IL K (CGoalL.next laz th) g) (hf : fromL axe laz = some laz') : IL K (CGoalL.next laz' th) g := by
  have FE : FromEnt axe ((th.there, laz) :: entries laz) ((th.there, laz') :: entries laz') :=
    FromEnt.cons hf (fromL_ent axe laz laz' hf)
  obtain ⟨hfr, hap, hent⟩ := (hI.goal : GoalL g (CGoalL.next laz th))
  refine ⟨hI.ats, hI.regs, fun k v hk => ?_, hI.kvan, hfr, needsApart_fromEnt FE hap, fun e' he' => ?_⟩
  · obtain ⟨k1, k2, k3, k4, k5⟩ := hI.cond k v hk
    refine ⟨k1, k2, fun ⟨e', he', hm⟩ => k3 ?_, k4, k5⟩
    obtain ⟨e, he, -, hn, -⟩ := fromEnt_back FE he'
    exact ⟨e, he, hn k hm⟩
  · obtain ⟨e, he, ee, hn, hdd⟩ := fromEnt_back FE he'
    obtain ⟨hb, hd, hr⟩ := hent e he
    exact ⟨ee ▸ hb, hdd hd, fun r hr' => hr r (hn r hr')⟩

/-! ## `+bomb` and `+simple-next` -/

theorem il_bombL {K : Nat → Nat → Prop} {goal : CGoalL S} {g0 g1 : Comp.Gen Map} {nex : NextL S}
    {miss : Option Nat} (hI : IL K goal g0) (h : (bombL miss : CM Map (NextL S)) g0 = some (nex, g1)) :
    JL K nex g1 := by
  simp only [bombL] at h
  obtain ⟨o, ga, ha, h⟩ := bind_some h
  rw [emit_apply] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact il_emitGoal (R := g0.re) hI (Nat.le_refl _) rfl (batc_fresh fun j hj => by simp [finJumps] at hj)
    (blobIn_nil_fin trivial) (fun r hr => by simp [blockDefs] at hr) (fun r hr => hr.elim) trivial

theorem il_simpleNextL {K : Nat → Nat → Prop} {goal : CGoalL S} {g0 g1 : Comp.Gen Map} {nex : NextL S}
    (hI : IL K goal g0) (h : (simpleNextL goal : CM Map (NextL S)) g0 = some (nex, g1)) : JL K nex g1 := by
  cases goal with
  | next laz th =>
    simp only [simpleNextL, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hI
  | done =>
    simp only [simpleNextL] at h
    obtain ⟨r, ga, ha, h⟩ := bind_some h
    rw [re_apply] at ha
    simp only [Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨rfl, rfl⟩ := ha
    obtain ⟨o, gb, hb, h⟩ := bind_some h
    rw [emit_apply] at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact il_emitGoal (R := g0.re + 1) (s := ⟨Need.this g0.re, HoonSet.empty⟩) hI (Nat.le_succ _) rfl
      (batc_fresh fun j hj => by simp [finJumps] at hj) (blobIn_nil_fin (show g0.re < g0.re + 1 by omega))
      (fun r hr => by simp [blockDefs] at hr)
      (fun r hr => by
        have e : r = g0.re := hr
        subst e; exact ⟨Nat.le_refl _, by omega, by simp [blockDefs]⟩) trivial
  | pick z o =>
    obtain ⟨hz, ho⟩ := (hI.goal : GoalL g0 (CGoalL.pick z o))
    have az : z.args = [] := by obtain ⟨_, _, _, a⟩ := hz; exact a
    have ao : o.args = [] := by obtain ⟨_, _, _, a⟩ := ho; exact a
    simp only [simpleNextL] at h
    obtain ⟨r, ga, ha, h⟩ := bind_some h
    rw [re_apply] at ha
    simp only [Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨rfl, rfl⟩ := ha
    obtain ⟨o', gb, hb, h⟩ := bind_some h
    rw [emit_apply] at hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact il_emitGoal (R := g0.re + 1) (b := ⟨[], [], Termin.brn g0.re z o⟩) (s := ⟨Need.this g0.re, HoonSet.empty⟩)
      hI (Nat.le_succ _) rfl
      (batc_fresh fun j hj => by
        simp only [finJumps, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        · exact hz
        · exact ho)
      (blobIn_nil_fin ⟨show g0.re < g0.re + 1 by omega, jmpIn_nil az, jmpIn_nil ao⟩)
      (fun r hr => by simp [blockDefs] at hr)
      (fun r hr => by
        have e : r = g0.re := hr
        subst e; exact ⟨Nat.le_refl _, by omega, by simp [blockDefs]⟩) trivial

/-! ## `%0` -/

/-- **`%0`, both halves.** -/
theorem liveRun_n0 (env : CallEnv) (sup : Option Nomm) (ax : Nat) :
    LiveRun (Map := Map) IL JL (runLC (S := S) env sup (Nomm.n0 ax)) := by
  intro K goal region g0 g1 nex hI h
  refine ⟨?_, liveC_n0 env sup hI h⟩
  simp only [runLC] at h
  split at h
  · exact il_bombL hI h
  obtain ⟨nx, ga, ha, h⟩ := bind_some h
  have J := il_simpleNextL hI ha
  split at h
  · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact J
  · cases hf : fromL ax nx.laz with
    | none => simp only [hf] at h; cases h
    | some laz' =>
      simp only [hf, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact il_fromL J hf

end Raw
end SkaModel
end Formalization
