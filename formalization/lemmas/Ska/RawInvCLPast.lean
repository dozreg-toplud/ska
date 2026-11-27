import lemmas.Ska.RawInvCLColSpec

/-!
# The run-level liveness with calls: `+past`

README Gaps 14 (b), track D.  The shared step of `%5`, cons and the call
`%2`: `+past` parks the result's need in a bond behind a fresh hop block.

* **`pastL_spec`**: `+past` keeps `IL` of the result's goal, and its result
  meets `LiveC` against the goal of its input (the kills of the parked
  root move from the continuation to the hop block, those of the other
  entries stay).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **`+past`, both halves.** -/
theorem pastL_spec {K : Nat → Nat → Prop} {cod : Bell → Option Bool} {nex nex' : NextL S} {nom : Nomm}
    {region : List Nat} {g g' : Comp.Gen Map} (hI : IL K nex.goal g)
    (h : pastL cod nex nom region g = some (nex', g')) : IL K nex'.goal g' ∧ LiveC K nex.goal g g' nex' := by
  rcases nex with ⟨⟨s, f, b⟩, th⟩
  have hpure : nex' = ⟨mk s f b, th⟩ → g' = g → IL K nex'.goal g' ∧ LiveC K (CGoalL.next (mk s f b) th) g g' nex' := by
    rintro rfl rfl; exact ⟨hI, liveC_refl⟩
  unfold pastL at h
  split at h
  · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    exact hpure h.1.symm h.2.symm
  rcases hh : hinted cod nom with _ | ⟨_ | _⟩
  · rw [hh] at h; cases h
  · rw [hh] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    exact hpure h.1.symm h.2.symm
  rw [hh] at h
  dsimp only at h
  have hd : g.drop = false := hI.ats.1
  obtain ⟨hth, hap, hent⟩ := (hI.goal : GoalL g (CGoalL.next (mk s f b) th))
  obtain ⟨bt, hbt, hpt, targs⟩ := hth
  replace targs : th.args = [] := targs
  obtain ⟨o, ga, ha, h⟩ := bind_some h
  rw [emit_apply] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  obtain ⟨u, gb, hb, h⟩ := bind_some h
  simp only [setTag, Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨-, rfl⟩ := hb
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hd1 : (g.emitted ⟨[], [], Termin.hop th⟩).drop = false := hd
  rw [if_neg (by rw [hd1]; exact Bool.false_ne_true)]
  have hbat : BATC g.blocks ⟨[], [], Termin.hop th⟩ := batc_fresh fun j hj => by
    simp only [finJumps, List.mem_singleton] at hj
    subst hj; exact ⟨bt, hbt, hpt, targs⟩
  obtain ⟨A1, -, hget⟩ := ats_emit hI.ats hbat
  have hfree : HoonMap.get g.blocks g.bo = Option.none := hI.ats.free
  have hD : ∀ r, Defd (g.emitted ⟨[], [], Termin.hop th⟩).blocks r → Defd g.blocks r := fun r hr => by
    have e := (defd_put (b := (⟨[], [], Termin.hop th⟩ : Blob)) hfree (r := r)).mp
      (by simpa [Gen.emitted, hd] using hr)
    rcases e with e | e
    · exact e
    · simp [blockDefs] at e
  -- the entries of the result
  have hP := entries_past (Sure.bunt : Sure S) (mk s f b) g.bo
  have hmem : ∀ e, e ∈ entries (mk (Sure.bunt : Sure S) [] ((g.bo, mk s f []) :: b)) →
      e = (g.bo, mk s f []) ∨ e ∈ entries (mk s f b) := fun e he =>
    List.mem_cons.mp (hP.mem_iff.mp he)
  have hold : ∀ e ∈ (g.bo, mk (Sure.bunt : Sure S) [] ((g.bo, mk s f []) :: b)) ::
      entries (mk (Sure.bunt : Sure S) [] ((g.bo, mk s f []) :: b)), ∀ y, NMem e.2.sure.ned y →
      ∃ e' ∈ (th.there, mk s f b) :: entries (mk s f b), NMem e'.2.sure.ned y ∧ (e.1 = g.bo ∨ e = e') := by
    intro e he y hy
    rcases List.mem_cons.mp he with rfl | he
    · exact hy.elim
    · rcases hmem e he with rfl | he
      · exact ⟨_, List.mem_cons_self .., hy, Or.inl rfl⟩
      · exact ⟨e, List.mem_cons_of_mem _ he, hy, Or.inr rfl⟩
  refine ⟨⟨A1, fun k b' hb' => ?_, fun k v hk => ?_, hI.kvan.mono (Nat.le_succ _), ?_⟩, ?_⟩
  · rw [em_get hd] at hb'
    split at hb'
    · cases hb'; exact blobIn_nil_fin (jmpIn_nil targs)
    · exact hI.regs k b' hb'
  · obtain ⟨k1, k2, k3, k4, k5⟩ := hI.cond k v hk
    refine ⟨k1, fun hdk => k2 (hD k hdk), fun ⟨e, he, hm⟩ => k3 ?_, k4, k5⟩
    obtain ⟨e', he', hm', -⟩ := hold e he k hm
    exact ⟨e', he', hm'⟩
  · refine ⟨⟨_, hget, rfl, rfl⟩, ?_, fun e he => ?_⟩
    · refine needsApart_perm (List.Perm.cons _ hP.symm) ?_
      refine List.Pairwise.cons (fun e _ r hr => hr.elim) ?_
      exact List.Pairwise.cons (fun e he => (List.pairwise_cons.mp hap).1 e he) (List.pairwise_cons.mp hap).2
    · have hroot := hent _ (List.mem_cons_self ..)
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨⟨_, hget, rfl⟩, trivial, fun y hy => hy.elim⟩
      · rcases hmem e he with rfl | he
        · exact ⟨⟨_, hget, rfl⟩, hroot.2.1, fun y hy => ⟨(hroot.2.2 y hy).1,
            fun hdy => (hroot.2.2 y hy).2 (hD y hdy)⟩⟩
        · obtain ⟨⟨b1, hb1, hp1⟩, hd1', hr1⟩ := hent e (List.mem_cons_of_mem _ he)
          refine ⟨⟨b1, ?_, hp1⟩, hd1', fun y hy => ⟨(hr1 y hy).1, fun hdy => (hr1 y hy).2 (hD y hdy)⟩⟩
          rw [em_get hd, if_neg (Nat.ne_of_lt (hI.lab hb1))]
          exact hb1
  -- the liveness
  intro y hl
  have hself := unpM_emitted_self hd ⟨[], [], Termin.hop th⟩
  cases hl with
  | here hb' hr _ =>
    have e := hself.symm.trans hb'
    cases e
    obtain ⟨-, hr | ⟨-, hr⟩⟩ := hr
    · simp [renBlob, OpsRF] at hr
    · simp [renBlob, renFin, finRegs, jmpRegs, renJmp_nil _ targs, targs] at hr
  | next hb' hj hl' _ hk =>
    have e := hself.symm.trans hb'
    cases e
    simp only [renBlob, renFin, getJmps, renJmp_nil _ targs, List.mem_singleton] at hj
    subst hj
    have hys : ¬ NMem s.ned y := fun hm => hk (Or.inr ⟨(g.bo, mk s f []),
      List.mem_cons_of_mem _ (hP.mem_iff.mpr (List.mem_cons_self ..)), rfl, hm⟩)
    have hl2 := (liveK_frameP hI.downU (fun x hx => unpM_emitted_lt hd _ hx) (hI.lab hbt)).mp hl'
    refine hl2.mono_r fun x hx => ?_
    rcases hx with hx | ⟨e, he, ex, hm⟩
    · exact Or.inl hx
    · rcases List.mem_cons.mp he with rfl | he
      · exact (hys hm).elim
      · exact Or.inr ⟨e, List.mem_cons_of_mem _ (hP.mem_iff.mpr (List.mem_cons_of_mem _ he)), ex, hm⟩

end Raw
end SkaModel
end Formalization
