import lemmas.Ska.CompLeafKeep
import lemmas.Ska.CompSixNextRun
import lemmas.Ska.CompFootTen

/-!
# The relaxed `sem` at the leaves of `RunOKP` and `RunOKN`

README Gaps 12.2: the `sem` of `RunOKP` and `RunOKN` asks the input
registers `ned` to lie at or above the end of the run (`∀ r, NMem ned r →
g1.re ≤ r`).  The collapse case needs them to lie there or in the run's own
sure need.  `SemPR` and `SemNR` are the two `sem` fields with that relaxed
hypothesis, and `runOKP_frag_semR`, `runOKN_frag_semR` prove them at the
leaves (`Frag`), where the relations take `sem` from `RunOK`, through the
leaf conversion `leaf_keep` with the footprint `run_foot`.  They assume, beside
what `runOKP_frag` and `runOKN_frag` assume, that the state has no block at or
above `g0.bo` (`Clear`, which `clear_gen0` gives at the top and `GrowU` keeps)
and that the goal's jumps pass no arguments (`LeafJ`), as they do wherever
the relations are used (`runX_ok` takes `%pick` with jumps without arguments
and `NextOK` a `%next` whose jump has none).  The relations themselves are not
changed yet: `RunOKG.toP` and every proof of a `sem` of `RunOKG` pass the strict
hypothesis on, so `RunOKP`, `RunOKG`, `RunOKN` and `RunOKE` have to change
together.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The `sem` of `RunOKP` with the relaxed hypothesis on the input
registers**: they lie at or above the end of the run, or in its result's sure
need. -/
def SemPR (lib : Lib) (nm : Nomm) (goal : CGoal S) (g0 g1 : Gen Map) (nex : NextL S) : Prop :=
  ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s0 s : Noun),
    AgreeP lib O c gul st t ned g0 g1 nex.laz s0 s →
    (∀ r, NMem ned r → g1.re ≤ r ∨ NMem nex.laz.sure.ned r) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    GoalSem lib O c gul st (fun r => r < g0.re ∨ NMem ned r) regs t nex.th goal (pureEval nm s)

/-- **The `sem` of `RunOKN` with the relaxed hypothesis.** -/
def SemNR (lib : Lib) (nm : Nomm) (sur : Sure S) (th : Jmp) (g0 g1 : Gen Map) (nex : NextL S) : Prop :=
  ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s0 s : Noun),
    AgreeP lib O c gul st t ned g0 g1 nex.laz s0 s →
    (∀ r, NMem ned r → g1.re ≤ r ∨ NMem nex.laz.sure.ned r) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    GoalSem lib O c gul st (fun r => (r < g0.re ∨ NMem ned r) ∧ ¬ NMem sur.ned r) regs t nex.th
      (CGoal.next sur th) (pureEval nm s)

theorem jmpIn_nil {P : Nat → Prop} {j : Jmp} (h : j.args = []) : JmpIn P j := fun x hx => by
  rw [h] at hx; cases hx

/-- **The relaxed `sem` at a leaf for `%done` or `%pick`.** -/
theorem runOKP_frag_semR (lib : Lib) {goal : CGoal S} {nm : Nomm} (hf : Frag nm goal) (hg : NotNext goal)
    {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S} (hj : GJ g0.bo goal) (hl : LeafJ g0.bo goal)
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hc : Clear g0)
    (h : runL nm (CGoal.toL goal) region g0 = some (nex, g1)) :
    SemPR (Map := Map) lib nm goal g0 g1 nex := by
  rw [runL_frag hf] at h
  obtain ⟨⟨n, g⟩, hr, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have hok : GoalOK g0 goal := by cases goal with | next => exact hg.elim | _ => trivial
  have hcl : GClean goal := by cases goal with | next => exact hg.elim | _ => trivial
  have hin : GoalIn g0.re goal := by
    cases goal with
    | next => exact hg.elim
    | pick z o => exact ⟨jmpIn_nil hl.1.1, jmpIn_nil hl.2.1⟩
    | done => trivial
  have hD : GDist goal := by cases goal with | next => exact hg.elim | _ => trivial
  have R := run_ok lib nm goal g0 g n hf hok hcl hr
  have D := run_down (S := S) (Map := Map) nm goal g0 g n hj b0 d0 hr
  have F := run_foot (S := S) (Map := Map) nm goal g0 g n d0 hin hD hr
  intro c ned σ O st t gul s0 s ag hned regs hh _
  have := leaf_keep (O := O) (gul := gul) R D.grow F hc d0 hl c (fun o h0 h1 => ag.1 o h0 h1 (by simp [Next.toL, entries_ofSure]))
    st s regs t hh
  refine goalSem_mono (fun r hr => ⟨?_, notNext_gmem hg r⟩) goal _ this
  rcases hr with e | e
  · exact Or.inl e
  · rcases hned r e with e' | e'
    · exact Or.inr (Or.inl e')
    · exact Or.inr (Or.inr e')

/-- **The relaxed `sem` at a leaf for a fork-free `%next`.** -/
theorem runOKN_frag_semR (lib : Lib) {sur : Sure S} {th : Jmp} {nm : Nomm} (hf : Frag nm (CGoal.next sur th))
    {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S} (hj : GJ g0.bo (CGoal.next sur th))
    (hth : th.args = []) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hc : Clear g0)
    (hok : GoalOK g0 (CGoal.next sur th)) (hcl : Clean sur.ned)
    (h : runL nm (CGoalL.next (ofSure sur) th) region g0 = some (nex, g1)) :
    SemNR (Map := Map) lib nm sur th g0 g1 nex := by
  rw [show (CGoalL.next (ofSure sur) th : CGoalL S) = CGoal.toL (CGoal.next sur th) from rfl, runL_frag hf] at h
  obtain ⟨⟨n, g⟩, hr, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have R := run_ok lib nm _ g0 g n hf hok hcl hr
  have D := run_down (S := S) (Map := Map) nm _ g0 g n hj b0 d0 hr
  have F := run_foot (S := S) (Map := Map) nm (CGoal.next sur th) g0 g n d0 ⟨hok.2, jmpIn_nil hth⟩ hok.1 hr
  intro c ned σ O st t gul s0 s ag hned regs hh _
  have := leaf_keep (O := O) (gul := gul) R D.grow F hc d0 ⟨hth, hj.2⟩ c
    (fun o h0 h1 => ag.1 o h0 h1 (by simp [Next.toL, entries_ofSure])) st s regs t hh
  refine goalSem_mono (fun r hr => ⟨?_, hr.2⟩) _ _ this
  rcases hr.1 with e | e
  · exact Or.inl e
  · rcases hned r e with e' | e'
    · exact Or.inr (Or.inl e')
    · exact Or.inr (Or.inr e')

end Comp
end SkaModel
end Formalization
