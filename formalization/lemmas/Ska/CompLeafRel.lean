import lemmas.Ska.CompLeafKeep
import lemmas.Ska.CompSixNextRun
import lemmas.Ska.CompFootTen

/-!
# The relaxed `sem` at the leaves of `RunOKP`, `RunOKG` and `RunOKN`

README Gaps 12.2: the `sem` of the run relations asks the input registers
`ned` to lie at or above the end of the run (`∀ r, NMem ned r → g1.re ≤ r`).
The collapse case needs some of them in the run's own sure need.

The form first planned, `g1.re ≤ r ∨ NMem nex.laz.sure.ned r`, does not
compose through two operands (`binaryN_ok`).  In `[5 [0 2] [0 3]]` the sure
need of the whole is `pair rp rq` (the merge of the two operands' needs,
`rp` and `rq` the operand registers allocated first), so `ned` may contain
`rq`; the `sem` of `[0 2]`, which runs first, is then asked for `rq` with
`rq` below that run's start and outside its sure need `pair rp none`.  In
`[5 [0 1] [1 6]]` (the test of the README's target) `ned` contains `rp`,
which is below the start of `[1 6]` and outside its empty sure need.  What
holds in both is that the register was allocated before the sub-run and is
not named by its goal.  So the hypothesis is `InR`: from the end on, below
the start and not named by the goal, or in the result's sure need.  The code
of a run writes none of these (`FootR.wr`, `Foot.wr`), so the leaf
conversion keeps them.

The keep set must grow too (`KeepI`): the old one, `(r < g0.re ∨ NMem ned r)
∧ ¬ GMem goal r`, drops an input register named by the goal, and the
operand `[0 1]` of `[5 [0 1] [1 6]]` runs for the goal `%next rp`, whose sure
need is `rp`, with `rp` in `ned`.  `KeepI` keeps every input register.

`SemPR` (for `%done` and `%pick`, where the goal names no register) and
`SemGR`, `SemNR` (any goal, `%next`) are the `sem` fields with these forms,
`SemPR.strict` and `SemGR.strict` recover the strict ones, and
`runOKP_frag_semR`, `runOKN_frag_semR` prove them at the leaves (`Frag`)
through `leaf_keepK`, the leaf conversion `leaf_sem` with the footprint
`run_foot` and any keep set outside it.  They assume, beside what
`runOKP_frag` and `runOKN_frag` assume, that the state has no block at or
above `g0.bo` (`Clear`, which `clear_gen0` gives at the top and `GrowU`
keeps) and that the goal's jumps pass no arguments (`LeafJ`).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The input registers a run may be given** (`ned` of `sem`): from its
end on, allocated before it and not named by its goal, or in its result's sure
need `sur`.  The code of the run writes none of them (`FootR.wr`). -/
def InR (goal : CGoal S) (g0 g1 : Gen Map) (sur : Need) (r : Nat) : Prop :=
  g1.re ≤ r ∨ (r < g0.re ∧ ¬ GMem goal r) ∨ NMem sur r

/-- **The registers the code keeps**, for the input need `ned`: those
allocated before the run and not named by the goal, and the input registers. -/
def KeepI (goal : CGoal S) (g0 : Gen Map) (ned : Need) (r : Nat) : Prop :=
  (r < g0.re ∧ ¬ GMem goal r) ∨ NMem ned r

/-- **The `sem` of `RunOKP` with the relaxed hypothesis on the input
registers** (`InR`). -/
def SemPR (lib : Lib) (nm : Nomm) (goal : CGoal S) (g0 g1 : Gen Map) (nex : NextL S) : Prop :=
  ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s0 s : Noun),
    AgreeP lib O c gul st t ned g0 g1 nex.laz s0 s →
    (∀ r, NMem ned r → InR goal g0 g1 nex.laz.sure.ned r) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    GoalSem lib O c gul st (fun r => r < g0.re ∨ NMem ned r) regs t nex.th goal (pureEval nm s)

/-- **The `sem` of `RunOKG` with the relaxed hypothesis**: the code keeps
`KeepI`, every input register included. -/
def SemGR (lib : Lib) (nm : Nomm) (goal : CGoal S) (g0 g1 : Gen Map) (nex : NextL S) : Prop :=
  ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s0 s : Noun),
    AgreeP lib O c gul st t ned g0 g1 nex.laz s0 s →
    (∀ r, NMem ned r → InR goal g0 g1 nex.laz.sure.ned r) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    GoalSem lib O c gul st (KeepI goal g0 ned) regs t nex.th goal (pureEval nm s)

/-- **The `sem` of `RunOKN` with the relaxed hypothesis.** -/
abbrev SemNR (lib : Lib) (nm : Nomm) (sur : Sure S) (th : Jmp) (g0 g1 : Gen Map) (nex : NextL S) : Prop :=
  SemGR (Map := Map) lib nm (CGoal.next sur th) g0 g1 nex

/-- The strict `sem` (input registers from the end of the run on) follows. -/
theorem SemPR.strict {lib : Lib} {nm : Nomm} {goal : CGoal S} {g0 g1 : Gen Map} {nex : NextL S}
    (h : SemPR (Map := Map) lib nm goal g0 g1 nex) :
    ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s0 s : Noun),
    AgreeP lib O c gul st t ned g0 g1 nex.laz s0 s → (∀ r, NMem ned r → g1.re ≤ r) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    GoalSem lib O c gul st (fun r => r < g0.re ∨ NMem ned r) regs t nex.th goal (pureEval nm s) :=
  fun c ned σ O st t gul s0 s ag hn => h c ned σ O st t gul s0 s ag fun r hr => Or.inl (hn r hr)

/-- The strict `sem` of `RunOKG` follows. -/
theorem SemGR.strict {lib : Lib} {nm : Nomm} {goal : CGoal S} {g0 g1 : Gen Map} {nex : NextL S}
    (h : SemGR (Map := Map) lib nm goal g0 g1 nex) :
    ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s0 s : Noun),
    AgreeP lib O c gul st t ned g0 g1 nex.laz s0 s → (∀ r, NMem ned r → g1.re ≤ r) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    GoalSem lib O c gul st (fun r => (r < g0.re ∨ NMem ned r) ∧ ¬ GMem goal r) regs t nex.th goal (pureEval nm s) :=
  fun c ned σ O st t gul s0 s ag hn regs hh hN =>
    goalSem_mono (fun _ hr => hr.1.elim (fun e => Or.inl ⟨e, hr.2⟩) Or.inr) goal _
      (h c ned σ O st t gul s0 s ag (fun r hr => Or.inl (hn r hr)) regs hh hN)

theorem jmpIn_nil {P : Nat → Prop} {j : Jmp} (h : j.args = []) : JmpIn P j := fun x hx => by
  rw [h] at hx; cases hx

/-- **The leaf conversion for any keep set inside the footprint's
complement.** -/
theorem leaf_keepK {lib : Lib} {σ : Type} {O : Oracle σ} {gul : Noun} {nm : Nomm} {goal : CGoal S}
    {g0 g1 : Gen Map} {nex : Next S}
    (R : RunOK lib nm goal g0 g1 nex) (G : Grow g0 g1) (F : Foot g0 g1 goal nex) (hc : Clear g0)
    (d0 : g0.drop = false) (hj : LeafJ g0.bo goal) {K : Nat → Prop}
    (hK : ∀ r, K r → (r < g0.re ∧ ¬ GMem goal r) ∨ g1.re ≤ r ∨ NMem nex.laz.ned r)
    (c : Straight Map) (ag : Agree c g0 g1) (st : σ) (s : Noun) (regs : Map (Option Noun)) (t : Trace)
    (hh : HoldsS nex.laz regs s) :
    GoalSem lib O c gul st K regs t nex.th goal (pureEval nm s) :=
  leaf_sem R d0 (fun k b hk _ hb => (clear_new hc G F.wr k b hk hb).1) hj
    (fun r hr hq => by
      obtain ⟨h1, h2, h3⟩ := hq
      rcases hK r hr with ⟨e, e'⟩ | e | e
      · rcases h2 with h2 | h2
        · omega
        · exact e' h2
      · omega
      · exact h3 e) c ag st s regs t hh

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
  refine leaf_keepK (O := O) (gul := gul) R D.grow F hc d0 hl (fun r hr => ?_) c
    (fun o h0 h1 => ag.1 o h0 h1 (by simp [Next.toL, entries_ofSure])) st s regs t hh
  rcases hr with e | e
  · exact Or.inl ⟨e, notNext_gmem hg r⟩
  · rcases hned r e with e' | e' | e'
    · exact Or.inr (Or.inl e')
    · exact Or.inl e'
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
  refine leaf_keepK (O := O) (gul := gul) R D.grow F hc d0 ⟨hth, hj.2⟩ (fun r hr => ?_) c
    (fun o h0 h1 => ag.1 o h0 h1 (by simp [Next.toL, entries_ofSure])) st s regs t hh
  rcases hr with e | e
  · exact Or.inl e
  · rcases hned r e with e' | e' | e'
    · exact Or.inr (Or.inl e')
    · exact Or.inl e'
    · exact Or.inr (Or.inr e')

end Comp
end SkaModel
end Formalization
