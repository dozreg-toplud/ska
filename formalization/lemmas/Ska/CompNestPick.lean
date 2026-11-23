import lemmas.Ska.CompNestFinal
import lemmas.Ska.CompCopyFresh

/-!
# Nested `[6 c a b]` under `%done` and `%pick`, and as a test

`FragP goal nm`: the nomm of `Frag` for `goal`, and `[6 c a b]` whose test
is again `FragP` for `%pick` and whose branches are `FragP` for `goal`.  So
`%6` nests in the branches and in the tests to any depth.  The goals are
`%done` and `%pick` (`NotNext`).

The test of a `%6` may now have forks of its own: `+copy` puts them side by
side with the fork of the two branches, since their lazy blocks were
allocated after those of the branches (`copyL_six_apart`, from
`copyLazyL_apart`).

`RunOKP` is `RunOKD` of `CompNestRun.lean` for a goal: under `%pick` the
code keeps the registers allocated before the run and the input registers
(`GoalSem` with that set), and the ops in front of the lazy blocks keep the
registers allocated before the end of the run outside their own need's.
`runP_ok`: `runL` meets it on `FragP` when the nomm has at most 255 `%6`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-! ## The fragment -/

/-- A goal `%done` or `%pick`. -/
def NotNext : CGoal S → Prop
  | CGoal.next _ _ => False
  | _ => True

/-- **The fragment with `%6` nested in the branches and in the tests.** -/
inductive FragP : CGoal S → Nomm → Prop
  | frag {goal : CGoal S} {nm : Nomm} : Frag nm goal → FragP goal nm
  | six {goal : CGoal S} {c a b : Nomm} : (∀ z o, FragP (CGoal.pick z o) c) → FragP goal a → FragP goal b →
      FragP goal (Nomm.n6 c a b)

theorem fragP_pure {goal : CGoal S} {nm : Nomm} (h : FragP goal nm) : nm.pure = true := by
  induction h with
  | frag hf => exact (frag_pure_noSix _ _ hf).1
  | six _ _ _ ihc iha ihb =>
    simp only [Nomm.pure, Bool.and_eq_true]
    exact ⟨⟨ihc (jmp0 0) (jmp0 0), iha⟩, ihb⟩

/-! ## The case `%6` for `%done` and `%pick` -/

/-- The branch of `run` for `%6` that `%done` and `%pick` take. -/
def sixBody (p q r : Nomm) (goal : CGoalL S) (region : List Nat) : CM Map (NextL S) := do
  let nex1 ← runL r goal region
  let nex0 ← runL q goal region
  let yes ← emit ⟨[], [], Termin.hop nex0.th⟩
  let nuh ← emit ⟨[], [], Termin.hop nex1.th⟩
  setTag yes region
  setTag nuh region
  if nex0.th.args ≠ [] then fun _ => Option.none else
  if nex1.th.args ≠ [] then fun _ => Option.none else
  let lazy ← liftO (pastFork noCode (mk Sure.bunt [((yes, nex0.laz), (nuh, nex1.laz))] []) p)
  let nexCond ← runL p (CGoalL.pick (jmp0 yes) (jmp0 nuh)) region
  if !(lazyBig (softLess noSoft lazy)) then copyL nexCond lazy else do
    let o ← emit ⟨[], [], Termin.hop nexCond.th⟩
    let lazy ← lazyShut o lazy
    copyL ⟨nexCond.laz, jmp0 o⟩ lazy

theorem runL_n6_body (p q r : Nomm) {goal : CGoal S} (hg : NotNext goal) (region : List Nat) :
    (runL (Nomm.n6 p q r) (CGoal.toL goal) region : CM Map (NextL S)) =
      sixBody p q r (CGoal.toL goal) region := by
  cases goal with
  | next => exact hg.elim
  | pick z o => unfold runL; rfl
  | done => unfold runL; rfl

/-- **`sixBody` taken apart** when the fork is not big. -/
theorem sixBody_apart {c a b : Nomm} (hcp : c.pure = true) {goal : CGoalL S} {region : List Nat}
    {g0 g4 : Gen Map} {nex : NextL S} (h : sixBody c a b goal region g0 = some (nex, g4)) :
    ∃ (x1 x0 xc : NextL S) (g1 g2 g3 : Gen Map),
      runL b goal region g0 = some (x1, g1) ∧ runL a goal region g1 = some (x0, g2) ∧
      x0.th.args = [] ∧ x1.th.args = [] ∧
      runL c (CGoalL.pick (jmp0 g2.bo) (jmp0 (g2.bo + 1))) region (sixGenL g2 x0.th x1.th region) =
        some (xc, g3) ∧
      (lazyBig (mk (Sure.bunt : Sure S) [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))] []) = false →
        copyL xc (mk (Sure.bunt : Sure S) [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))] []) g3 = some (nex, g4)) := by
  simp only [sixBody] at h
  obtain ⟨x1, g1, h1, h⟩ := bind_some h
  obtain ⟨x0, g2, h2, h⟩ := bind_some h
  simp only [bind_apply, emit_apply, setTag_apply, Option.bind_some] at h
  by_cases a0' : x0.th.args ≠ []
  · simp [a0'] at h
  have a0 : x0.th.args = [] := by simpa using a0'
  by_cases a1' : x1.th.args ≠ []
  · simp [a0, a1'] at h
  have a1 : x1.th.args = [] := by simpa using a1'
  simp only [a0, a1, ne_eq, not_true_eq_false, if_false] at h
  rw [show liftO (pastFork noCode (mk (Sure.bunt : Sure S)
      [((g2.bo, x0.laz), ((g2.emitted ⟨[], [], Termin.hop x0.th⟩).bo, x1.laz))] []) c) =
      (pure (mk (Sure.bunt : Sure S)
      [((g2.bo, x0.laz), ((g2.emitted ⟨[], [], Termin.hop x0.th⟩).bo, x1.laz))] []) : CM Map (Lazy S)) by
    rw [pastFork_pure _ _ hcp]; rfl] at h
  obtain ⟨lz, gl, hl, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hl
  obtain ⟨rfl, rfl⟩ := hl
  obtain ⟨xc, g3, h3, h⟩ := bind_some h
  refine ⟨x1, x0, xc, g1, g2, g3, h1, h2, a0, a1, h3, fun hbig => ?_⟩
  have hcond : (!(lazyBig (softLess noSoft (mk (Sure.bunt : Sure S)
      [((g2.bo, x0.laz), ((g2.emitted ⟨[], [], Termin.hop x0.th⟩).bo, x1.laz))] [])))) = true := by
    rw [softLess_noSoft]; simp only [emitted_bo]; rw [hbig]; rfl
  rw [if_pos hcond] at h
  exact h

theorem forkEntries_append : ∀ (f1 f2 : List (ForkE S)), forkEntries (f1 ++ f2) = forkEntries f1 ++ forkEntries f2
  | [], _ => rfl
  | ((oy, y), (on, n)) :: rest, f2 => by
    simp only [List.cons_append, forkEntries, forkEntries_append rest f2, List.append_assoc]

theorem fork_mem_entries {e : ForkE S} : ∀ {f : List (ForkE S)}, e ∈ f → e.1 ∈ forkEntries f
  | ((oy, y), (on, n)) :: rest, h => by
    simp only [forkEntries, List.mem_append, List.mem_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl (Or.inl (Or.inl rfl))
    · exact Or.inr (fork_mem_entries h)

/-- **`+copy` of a test's `next` with the fork of the branches**, when the
test's forks name other yes blocks. -/
theorem copyL_six_apart (xc : NextL S) (l0 l1 : Lazy S) (y n : Nat) (g : Gen Map)
    (hap : ∀ e ∈ xc.laz.fork, e.1.1 ≠ y) :
    (copyL xc (mk Sure.bunt [((y, l0), (n, l1))] []) g : Option (NextL S × Gen Map)) =
      (addOps g.bo [] (g.emitted ⟨[], [], Termin.hop xc.th⟩)).map fun p =>
        (⟨mk ⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩
          (xc.laz.fork ++ [((y, l0), (n, l1))]) xc.laz.bond, jmp0 g.bo⟩, p.2) := by
  unfold copyL
  rw [bind_apply, emit_apply, Option.bind_some]
  rcases hx : xc.laz with ⟨s1, f1, b1⟩
  rw [hx] at hap
  simp only [fork_mk] at hap
  rw [copyLazyL_apart _ s1 f1 b1 _ (fun e he e' he' => by
      simp only [fork_mk, List.mem_singleton] at he'; subst he'; exact hap e he)
    (fun e _ e' he' => by simp at he')]
  simp only [sure_mk, fork_mk, bond_mk, Sure.bunt, List.append_nil]
  rw [bind_apply, bind_apply, copyNeed_none, Option.bind_some, bind_apply]
  cases addOps g.bo [] (g.emitted ⟨[], [], Termin.hop xc.th⟩) with
  | none => rfl
  | some p => rfl

/-! ## The relation -/

/-- `AgreeF` with the ops of the lazy blocks keeping the registers below the
end of the run. -/
def AgreeP (lib : Lib) {σ : Type} (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (t : Trace)
    (ned : Need) (g0 g1 : Gen Map) (laz : Lazy S) (s : Noun) : Prop :=
  (∀ o, g0.bo ≤ o → o < g1.bo → o ∉ (entries laz).map Prod.fst →
    HoonMap.get c.blocks o = HoonMap.get g1.blocks o) ∧
  ∀ e ∈ entries laz, ∃ A th, HoonMap.get g1.blocks e.1 = some ⟨[], [], Termin.hop th⟩ ∧
    HoonMap.get c.blocks e.1 = some ⟨[], A, Termin.hop th⟩ ∧ FillSem lib O c gul st t ned g1.re e.2.sure A s

/-- **The relation for one run of `runL` for `%done` or `%pick`.** -/
structure RunOKP (lib : Lib) (nm : Nomm) (goal : CGoal S) (g0 g1 : Gen Map) (nex : NextL S) : Prop where
  ext : Ext g0 g1
  grow : Grow g0 g1
  cnd : g1.cond = g0.cond
  lo : 1 ≤ nex.th.there
  hi : nex.th.there < g1.bo
  ent : Entry g1 goal nex.th
  regs : ∀ r, NMem nex.laz.sure.ned r → g0.re ≤ r ∧ r < g1.re
  dist : Distinct nex.laz.sure.ned
  eregs : ∀ e ∈ entries nex.laz, Distinct e.2.sure.ned ∧ ∀ r, NMem e.2.sure.ned r → g0.re ≤ r ∧ r < g1.re
  labs : ∀ e ∈ entries nex.laz, g0.bo ≤ e.1 ∧ e.1 < nex.th.there ∧
    ∃ th, HoonMap.get g1.blocks e.1 = some ⟨[], [], Termin.hop th⟩
  nodup : ((entries nex.laz).map Prod.fst).Nodup
  size : (entries nex.laz).length ≤ 2 * sixCount nm
  nec : ∀ s, ¬ FitsS nex.laz.sure s → pureEval nm s = none
  sem : ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s : Noun),
    AgreeP lib O c gul st t ned g0 g1 nex.laz s → (∀ r, NMem ned r → g1.re ≤ r) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s →
    GoalSem lib O c gul st (fun r => r < g0.re ∨ NMem ned r) regs t nex.th goal (pureEval nm s)

/-! ## `GoalSem` -/

section GS
variable {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}

theorem goalSem_mono {K K' : Nat → Prop} (hk : ∀ r, K' r → K r) {regs : Map Noun} {je : Jmp} :
    ∀ (goal : CGoal S) (v : Option Noun), GoalSem lib O c gul st K regs t je goal v →
      GoalSem lib O c gul st K' regs t je goal v
  | CGoal.done, _, h => h
  | CGoal.next _ _, some _, h => ⟨fun f => by
      obtain ⟨R, hh, k, e⟩ := h.1 f; exact ⟨R, hh, fun r hr => k r (hk r hr), e⟩, h.2⟩
  | CGoal.next _ _, none, h => h
  | CGoal.pick _ _, some (Noun.atom 0), h => by
      obtain ⟨R, k, e⟩ := h; exact ⟨R, fun r hr => k r (hk r hr), e⟩
  | CGoal.pick _ _, some (Noun.atom 1), h => by
      obtain ⟨R, k, e⟩ := h; exact ⟨R, fun r hr => k r (hk r hr), e⟩
  | CGoal.pick _ _, some (Noun.atom (_ + 2)), h => h
  | CGoal.pick _ _, some (Noun.cell _ _), h => h
  | CGoal.pick _ _, none, h => h

/-- `GoalSem` through code in front that keeps the registers of `K`. -/
theorem goalSem_pre {K : Nat → Prop} {regs regs' : Map Noun} {je je' : Jmp}
    (hk : ∀ r, K r → SkaModel.read r regs' = SkaModel.read r regs)
    (he : goJ lib O c gul st regs t je = goJ lib O c gul st regs' t je') :
    ∀ (goal : CGoal S) (v : Option Noun), GoalSem lib O c gul st K regs' t je' goal v →
      GoalSem lib O c gul st K regs t je goal v
  | CGoal.done, _, h => he.trans h
  | CGoal.next _ _, some _, h => ⟨fun f => by
      obtain ⟨R, hh, k, e⟩ := h.1 f
      exact ⟨R, hh, fun r hr => (k r hr).trans (hk r hr), he.trans e⟩, fun f => he.trans (h.2 f)⟩
  | CGoal.next _ _, none, h => he.trans h
  | CGoal.pick _ _, some (Noun.atom 0), h => by
      obtain ⟨R, k, e⟩ := h; exact ⟨R, fun r hr => (k r hr).trans (hk r hr), he.trans e⟩
  | CGoal.pick _ _, some (Noun.atom 1), h => by
      obtain ⟨R, k, e⟩ := h; exact ⟨R, fun r hr => (k r hr).trans (hk r hr), he.trans e⟩
  | CGoal.pick _ _, some (Noun.atom (_ + 2)), h => he.trans h
  | CGoal.pick _ _, some (Noun.cell _ _), h => he.trans h
  | CGoal.pick _ _, none, h => he.trans h

theorem goalSem_none {K : Nat → Prop} {regs : Map Noun} {je : Jmp} :
    ∀ (goal : CGoal S), goJ lib O c gul st regs t je = some (Tone.two t, st) →
      GoalSem lib O c gul st K regs t je goal none
  | CGoal.done, h => h
  | CGoal.next _ _, h => h
  | CGoal.pick _ _, h => h

end GS

end Comp
end SkaModel
end Formalization
