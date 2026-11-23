import lemmas.Ska.CompForkNeed

/-!
# Runs for a fork-free goal `%next`, with `%6` in them

`RunOKN nm sur th g0 g1 nex`: the relation for one run of `runL` for the
fork-free goal `%next sur th`, whose result may have lazy blocks (from a
`%6` in the nomm).  It is `RunOKP` with the goal's part of `RunOK`: the
registers of the subject's need are the goal's or fresh, a subject without
the shape or looks of that need is one on which the nomm crashes or makes a
product without those of the goal, and the code keeps the registers
allocated before the run and the input registers, except the goal's.  It
has no `Grow`: the code of `%6` under `%next` jumps up, from the fork blocks
to the join of `+fork-need`, which is allocated after them.

`runOKN_frag`: every nomm of `Frag` meets it.  `sect_spec`: `+sect` when the
branches made no proxy.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The relation for one run of `runL` for a fork-free goal `%next`.** -/
structure RunOKN (lib : Lib) (nm : Nomm) (sur : Sure S) (th : Jmp) (g0 g1 : Gen Map) (nex : NextL S) : Prop where
  ext : Ext g0 g1
  grow : GrowU g0 g1
  cnd : g1.cond = g0.cond
  lo : 1 ≤ nex.th.there
  hi : nex.th.there < g1.bo
  ent : Entry g1 (CGoal.next sur th) nex.th
  regs : ∀ r, NMem nex.laz.sure.ned r → NMem sur.ned r ∨ (g0.re ≤ r ∧ r < g1.re)
  dist : Distinct nex.laz.sure.ned
  eregs : ∀ e ∈ entries nex.laz, Distinct e.2.sure.ned ∧ ∀ r, NMem e.2.sure.ned r → g0.re ≤ r ∧ r < g1.re
  labs : ∀ e ∈ entries nex.laz, g0.bo ≤ e.1 ∧ e.1 < nex.th.there ∧
    ∃ th, HoonMap.get g1.blocks e.1 = some ⟨[], [], Termin.hop th⟩
  nodup : ((entries nex.laz).map Prod.fst).Nodup
  size : (entries nex.laz).length ≤ 2 * sixCount nm
  nec : ∀ s, ¬ FitsS nex.laz.sure s → pureEval nm s = none ∨ ∃ p, pureEval nm s = some p ∧ ¬ FitsS sur p
  sem : ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s0 s : Noun),
    AgreeP lib O c gul st t ned g0 g1 nex.laz s0 s → (∀ r, NMem ned r → g1.re ≤ r) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    GoalSem lib O c gul st (fun r => (r < g0.re ∨ NMem ned r) ∧ ¬ NMem sur.ned r) regs t nex.th
      (CGoal.next sur th) (pureEval nm s)

/-- **Every nomm of `Frag` meets `RunOKN`.** -/
theorem runOKN_frag (lib : Lib) {sur : Sure S} {th : Jmp} {nm : Nomm} (hf : Frag nm (CGoal.next sur th))
    {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S} (hj : GJ g0.bo (CGoal.next sur th)) (b0 : 1 ≤ g0.bo)
    (d0 : g0.drop = false) (hu : UpBelow g0) (hok : GoalOK g0 (CGoal.next sur th)) (hcl : Clean sur.ned)
    (h : runL nm (CGoalL.next (ofSure sur) th) region g0 = some (nex, g1)) :
    RunOKN (Map := Map) lib nm sur th g0 g1 nex := by
  rw [show (CGoalL.next (ofSure sur) th : CGoalL S) = CGoal.toL (CGoal.next sur th) from rfl, runL_frag hf] at h
  obtain ⟨⟨n, g⟩, hr, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have R := run_ok lib nm _ g0 g n hf hok hcl hr
  have D := run_down (S := S) (Map := Map) nm _ g0 g n hj b0 d0 hr
  refine ⟨R.ext, D.grow.toU hu, (kc_run nm _).keep g0 n g hr, D.lo, D.hi, D.entry, R.regs, R.dist,
    by simp [Next.toL, entries_ofSure], by simp [Next.toL, entries_ofSure], by simp [Next.toL, entries_ofSure],
    by simp [Next.toL, entries_ofSure], fun s hs => R.nec s hs, ?_⟩
  intro c ned σ O st t gul s0 s ag hned regs hh _
  have := R.sem d0 c (fun o h0 h1 => ag.1 o h0 h1 (by simp [Next.toL, entries_ofSure])) σ O st s regs t gul hh
  refine goalSem_mono (fun r hr => ⟨?_, hr.2⟩) _ _ this
  rcases hr.1 with e | e
  · exact Or.inl e
  · exact Or.inr (hned r e)

/-- `+fork-sure` changes no block above the join. -/
theorem forkSure_other {sur : Sure S} {o : Nat} {g g' : Gen Map} {s0 s1 : Sure S}
    (h : forkSure sur o g.bo (g.bo + 1) { g with bo := g.bo + 2 } = some ((s0, s1), g')) (hd : g.drop = false) :
    ∀ k, g.bo + 3 ≤ k → HoonMap.get g'.blocks k = HoonMap.get g.blocks k := by
  unfold forkSure at h
  obtain ⟨⟨n0, n1⟩, gK, hK, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  unfold forkNeed at hK
  obtain ⟨⟨m0, m1⟩, gN, hN, h⟩ := bind_some hK
  obtain ⟨⟨kk, eN⟩, -⟩ := forkNeedGo_spec _ _ _ _ _ hN
  subst eN
  simp only [bind_apply, emit_apply, Option.bind_some, pure_apply] at h
  simp only [emir, Gen.emitted, hd, Bool.false_eq_true, if_false, Option.bind_some, pure_apply,
    Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  intro k' hk'
  simp [HoonMap.get_put, show k' ≠ g.bo + 1 by omega, show k' ≠ g.bo by omega, show k' ≠ g.bo + 2 by omega]

/-- **`+fork-sure` grows the state with hops up**: the fork blocks hop up to
the join, which hops down to the goal's block. -/
theorem growU_forkSure {sur : Sure S} {th : Jmp} {g gF : Gen Map} {s0 s1 : Sure S}
    (h : forkSure sur th.there g.bo (g.bo + 1) { g with bo := g.bo + 2 } = some ((s0, s1), gF))
    (hd : g.drop = false) (h1 : 1 ≤ th.there) (h2 : th.there < g.bo) (hu : UpBelow g) : GrowU g gF := by
  obtain ⟨-, -, -, -, -, -, -, -, -, boF, drF, -, -, bk0, bk1, bk2, keepF⟩ := forkSure_spec h hd
  have oth := forkSure_other h hd
  have notUp : ∀ t, ¬ UpAt gF.blocks (g.bo + 2) t := by
    rintro t ⟨b, j, hb, hf, ht, hlt⟩
    rw [bk2] at hb; cases hb; simp only [Termin.hop.injEq] at hf; subst hf; simp only [jmp0] at ht; omega
  refine growU_of (by omega) drF (fun k hk => ?_) (fun k b' hk1 hk2 hb => ?_)
  · rcases hk with hk | hk
    · exact keepF k hk
    · exact oth k (by omega)
  · have : k = g.bo ∨ k = g.bo + 1 ∨ k = g.bo + 2 := by omega
    rcases this with rfl | rfl | rfl
    · rw [bk0] at hb; cases hb
      intro j hj; simp only [finJumps, List.mem_singleton] at hj; subst hj
      exact ⟨by dsimp only; omega, Or.inr ⟨rfl, by dsimp only; omega, by dsimp only; omega, notUp⟩⟩
    · rw [bk1] at hb; cases hb
      intro j hj; simp only [finJumps, List.mem_singleton] at hj; subst hj
      exact ⟨by dsimp only; omega, Or.inr ⟨rfl, by dsimp only; omega, by dsimp only; omega, notUp⟩⟩
    · rw [bk2] at hb; cases hb
      intro j hj; simp only [finJumps, List.mem_singleton] at hj; subst hj
      refine ⟨by simp only [jmp0]; omega, Or.inl ⟨by simp only [jmp0]; omega, fun t ht => ?_⟩⟩
      simp only [jmp0] at ht
      have ht' : UpAt g.blocks th.there t := by
        obtain ⟨b, j, hb, hf, e, hlt⟩ := ht
        exact ⟨b, j, (keepF _ h2).symm.trans hb, hf, e, hlt⟩
      have := hu _ t ht'; omega

/-- **`+sect` when the branches made no proxy**: the two lazy blocks at the
next labels, tagged, and the blocks otherwise as they were. -/
theorem sect_spec {nex0 nex1 : NextL S} {o0 o1 : Nat} {rb : List Nat} {cnd : Map (Nat × List Nat)}
    {g g' : Gen Map} {lz : Lazy S} {yes nuh : Nat} (hd : g.drop = false) (hc : g.cond = cnd)
    (h : sect nex0 nex1 o0 o1 rb cnd cnd g = some ((lz, yes, nuh), g')) :
    yes = g.bo ∧ nuh = g.bo + 1 ∧ nex0.th.args = [] ∧ nex1.th.args = [] ∧
    lz = mk Sure.bunt [((g.bo, nex0.laz), (g.bo + 1, nex1.laz))] [] ∧
    SameBlocks (sixGenL g nex0.th nex1.th rb) g' := by
  unfold sect at h
  split at h
  · cases h
  · rename_i rid rest
    obtain ⟨o0b, g1, h1, h⟩ := bind_some h
    obtain ⟨o1b, g2, h2, h⟩ := bind_some h
    obtain ⟨_, g3, h3, h⟩ := bind_some h
    obtain ⟨_, g4, h4, h⟩ := bind_some h
    obtain ⟨g5, g5', h5, h⟩ := bind_some h
    simp only [get, Option.some.injEq, Prod.mk.injEq] at h5
    obtain ⟨rfl, rfl⟩ := h5
    rw [emit_apply] at h1 h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h1 h2
    obtain ⟨rfl, rfl⟩ := h1
    obtain ⟨rfl, rfl⟩ := h2
    rw [setTag_apply] at h3 h4
    simp only [Option.some.injEq, Prod.mk.injEq] at h3 h4
    obtain ⟨_, rfl⟩ := h3
    obtain ⟨_, rfl⟩ := h4
    have e4 : (((g.emitted ⟨[], [], Termin.hop nex0.th⟩).emitted ⟨[], [], Termin.hop nex1.th⟩).tagged
        g.bo (rid :: rest)).tagged (g.emitted ⟨[], [], Termin.hop nex0.th⟩).bo (rid :: rest) =
        sixGenL g nex0.th nex1.th (rid :: rest) := rfl
    rw [e4] at h
    dsimp only at h
    have d4 : (sixGenL g nex0.th nex1.th (rid :: rest)).drop = false := by simp [hd]
    rw [if_neg (by rw [d4]; simp)] at h
    obtain ⟨u, g6, h6, h⟩ := bind_some h
    have S6 := sectThread_same (by rw [sixGenL_cond, hc]) h6
    revert h; split
    · intro h; cases h
    · rename_i a0
      split
      · intro h; cases h
      · rename_i a1
        intro h
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
        simp only [ne_eq, Decidable.not_not] at a0 a1
        exact ⟨rfl, rfl, a0, a1, rfl, S6⟩

end Comp
end SkaModel
end Formalization
