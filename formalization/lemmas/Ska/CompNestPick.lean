import lemmas.Ska.CompNestFinal
import lemmas.Ska.CompCopyFresh
import lemmas.Ska.CompGrowU

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

`RunOKP nm goal g0 g1 nex`: the relation for one run of `runL`.  The state
grew, every lazy block of the need (`entries`) was allocated in the run, is
the block `⟨[], [], hop th⟩` and lies below the block `nex` enters, their
labels are distinct, and the registers of every need in the tree were
allocated in the run.  `sem`: in a program that holds the blocks of `g1`
outside the lazy blocks and, at each lazy block, ops in front that fill the
need taken there from the input registers `ned` (`AgreeP`), entering `nex`
with the sure part held for the subject `s` of the run and the input
registers holding the subject `s0` of the function does what `+mink` does,
for the goal (`GoalSem`).  The lazy blocks are filled for `s` from
registers that hold `s0` (`FillSem` with two subjects); here, inside one
`%6`, the two are the same, and the final pass takes `s0 = s`.  Under `%pick` the code keeps
the registers allocated before the run and the input registers, and the ops
in front of the lazy blocks keep the registers allocated before the end of
the run outside their own need's.  `nec`: only the sure part is checked at
the entry; the needs in the forks are checked in their lazy blocks, that is
only on the branch taken.
`runP_ok`: `runL` meets it on `FragP` when the nomm has at most 255 `%6`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

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
    (ned : Need) (g0 g1 : Gen Map) (laz : Lazy S) (s0 s : Noun) : Prop :=
  (∀ o, g0.bo ≤ o → o < g1.bo → o ∉ (entries laz).map Prod.fst →
    HoonMap.get c.blocks o = HoonMap.get g1.blocks o) ∧
  ∀ e ∈ entries laz, ∃ A th, HoonMap.get g1.blocks e.1 = some ⟨[], [], Termin.hop th⟩ ∧
    HoonMap.get c.blocks e.1 = some ⟨[], A, Termin.hop th⟩ ∧ FillSem lib O c gul st t ned g1.re e.2.sure A s0 s

/-- **The relation for one run of `runL` for `%done` or `%pick`.** -/
structure RunOKP (lib : Lib) (nm : Nomm) (goal : CGoal S) (g0 g1 : Gen Map) (nex : NextL S) : Prop where
  ext : Ext g0 g1
  grow : GrowU g0 g1
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
  sem : ∀ (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (st : σ) (t : Trace) (gul : Noun) (s0 s : Noun),
    AgreeP lib O c gul st t ned g0 g1 nex.laz s0 s → (∀ r, NMem ned r → g1.re ≤ r) →
    ∀ regs, HoldsS nex.laz.sure regs s → HoldsN ned regs s0 →
    GoalSem lib O c gul st (fun r => r < g0.re ∨ NMem ned r) regs t nex.th goal (pureEval nm s)

/-! ## `GoalSem` -/

section GS
variable {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}

theorem goalSem_mono {K K' : Nat → Prop} (hk : ∀ r, K' r → K r) {regs : Map (Option Noun)} {je : Jmp} :
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
theorem goalSem_pre {K : Nat → Prop} {regs regs' : Map (Option Noun)} {je je' : Jmp}
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

theorem goalSem_none {K : Nat → Prop} {regs : Map (Option Noun)} {je : Jmp} :
    ∀ (goal : CGoal S), goJ lib O c gul st regs t je = some (Tone.two t, st) →
      GoalSem lib O c gul st K regs t je goal none
  | CGoal.done, h => h
  | CGoal.next _ _, h => h
  | CGoal.pick _ _, h => h

end GS

theorem fillSem_runK {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}
    {ned : Need} {lo : Nat} {L : Sure S} {A : List Pole} {s0 s : Noun} (F : FillSem lib O c gul st t ned lo L A s0 s)
    {R : Map (Option Noun)} (hR : HoldsN ned R s0) (th : Jmp) :
    (FitsS L s → ∃ R', HoldsS L R' s ∧
      (∀ x, (NMem ned x ∨ x < lo) → ¬ NMem L.ned x → SkaModel.read x R' = SkaModel.read x R) ∧
      execBlob lib O c gul st R t ⟨[], A, Termin.hop th⟩ [] = goJ lib O c gul st R' t th) ∧
    (¬ FitsS L s → execBlob lib O c gul st R t ⟨[], A, Termin.hop th⟩ [] = some (Tone.two t, st)) := by
  refine ⟨fun f => ?_, fun f => ?_⟩
  · obtain ⟨R', hr, hh, k⟩ := (F R hR).1 f
    refine ⟨R', hh, k, ?_⟩
    have := hr [] (Termin.hop th)
    rw [List.append_nil] at this
    rw [this, execBlob_hop]
  · have := (F R hR).2 f [] (Termin.hop th)
    rwa [List.append_nil] at this

theorem FillSem.mono' {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ}
    {t : Trace} {ned : Need} {lo lo' : Nat} {L : Sure S} {A : List Pole} {s : Noun}
    (h : FillSem lib O c gul st t ned lo L A s0 s) (hl : lo' ≤ lo) : FillSem lib O c gul st t ned lo' L A s0 s :=
  FillSem.mono h hl

theorem entries_eq (l : Lazy S) : entries l = bondEntries l.bond ++ forkEntries l.fork := by
  cases l; rfl

theorem entries_copy_six (xl : Lazy S) (s : Sure S) (y n : Nat) (l0 l1 : Lazy S) :
    entries (mk s (xl.fork ++ [((y, l0), (n, l1))]) xl.bond) =
      entries xl ++ ((y, l0) :: entries l0 ++ ((n, l1) :: entries l1)) := by
  rw [entries_eq xl]
  simp [entries, forkEntries_append, forkEntries, List.append_assoc]

theorem notNext_gmem {goal : CGoal S} (hg : NotNext goal) (r : Nat) : ¬ GMem goal r := by
  cases goal with
  | next => exact hg.elim
  | pick => exact id
  | done => exact id

theorem notNext_gnot {goal : CGoal S} (hg : NotNext goal) (p : Noun) : ¬ GNot goal p := by
  cases goal with
  | next => exact hg.elim
  | pick => exact id
  | done => exact id

theorem runOKP_frag (lib : Lib) {goal : CGoal S} {nm : Nomm} (hf : Frag nm goal) (hg : NotNext goal)
    {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S} (hj : GJ g0.bo goal) (b0 : 1 ≤ g0.bo)
    (d0 : g0.drop = false) (hu : UpBelow g0) (h : runL nm (CGoal.toL goal) region g0 = some (nex, g1)) :
    RunOKP (Map := Map) lib nm goal g0 g1 nex := by
  rw [runL_frag hf] at h
  obtain ⟨⟨n, g⟩, hr, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have hok : GoalOK g0 goal := by cases goal with | next => exact hg.elim | _ => trivial
  have hcl : GClean goal := by cases goal with | next => exact hg.elim | _ => trivial
  have R := run_ok lib nm goal g0 g n hf hok hcl hr
  have D := run_down (S := S) (Map := Map) nm goal g0 g n hj b0 d0 hr
  refine ⟨R.ext, D.grow.toU hu, (kc_run nm goal).keep g0 n g hr, D.lo, D.hi, D.entry, fun r hr => ?_, R.dist,
    by simp [Next.toL, entries_ofSure], by simp [Next.toL, entries_ofSure], by simp [Next.toL, entries_ofSure],
    by simp [Next.toL, entries_ofSure], fun s hs => ?_, ?_⟩
  · rcases R.regs r hr with e | e
    · exact (notNext_gmem hg r e).elim
    · exact e
  · rcases R.nec s hs with e | ⟨p, _, e⟩
    · exact e
    · exact (notNext_gnot hg p e).elim
  · intro c ned σ O st t gul s0 s ag hned regs hh _
    have := R.sem d0 c (fun o h0 h1 => ag.1 o h0 h1 (by simp [Next.toL, entries_ofSure])) σ O st s regs t gul hh
    refine goalSem_mono (fun r hr => ⟨?_, notNext_gmem hg r⟩) goal _ this
    rcases hr with e | e
    · exact Or.inl e
    · exact Or.inr (hned r e)

/-- **What the induction gives for `%done` or `%pick`**: every run of `nm`
for the goal meets `RunOKP`. -/
abbrev OKP (lib : Lib) (goal : CGoal S) (nm : Nomm) : Prop :=
  ∀ {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}, NotNext goal → GJ g0.bo goal →
    sixCount nm ≤ 255 → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 →
    runL nm (CGoal.toL goal) region g0 = some (nex, g1) → RunOKP (Map := Map) lib nm goal g0 g1 nex

/-- **`[6 c a b]` for `%done` or `%pick`**, from `RunOKP` of the test for
`%pick` and of the branches for the goal. -/
theorem sixP_ok (lib : Lib) {goal : CGoal S} {c a b : Nomm} (hcp : c.pure = true)
    (ihc : ∀ z o : Jmp, z.args = [] → o.args = [] → OKP (Map := Map) lib (CGoal.pick z o : CGoal S) c) (iha : OKP (Map := Map) lib goal a)
    (ihb : OKP (Map := Map) lib goal b) : OKP (Map := Map) lib goal (Nomm.n6 c a b) := by
  intro region g0 g4 nex hg hj hcount b0 d0 hu h
  rw [runL_n6_body c a b hg] at h
  obtain ⟨x1, x0, xc, g1, g2, g3, h1, h2, _, _, h3, hrest⟩ := sixBody_apart hcp h
  simp only [sixCount] at hcount
  have Rb := ihb hg hj (by omega) b0 d0 hu h1
  have u1 : UpBelow g1 := Rb.grow.up hu
  have d1 : g1.drop = false := Rb.ext.2.2.1.trans d0
  have b01 : g0.bo ≤ g1.bo := Rb.ext.2.1
  have b1 : 1 ≤ g1.bo := Nat.le_trans b0 b01
  have Ra := iha hg (hj.mono b01) (by omega) b1 d1 u1 h2
  have u2 : UpBelow g2 := Ra.grow.up u1
  have d2 : g2.drop = false := Ra.ext.2.2.1.trans d1
  have b12 : g1.bo ≤ g2.bo := Ra.ext.2.1
  have GU : GrowU g2 (sixGenL g2 x0.th x1.th region) := (grow_sixGenL region (jumpsBelow_hop Ra.lo Ra.hi)
    (jumpsBelow_hop Rb.lo (by have := Rb.hi; omega))).toU u2
  have uG : UpBelow (sixGenL g2 x0.th x1.th region) := GU.up u2
  have hbig : lazyBig (mk (Sure.bunt : Sure S) [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))] []) = false := by
    apply lazyBig_entries
    rw [entries_six]; simp only [List.length_append, List.length_cons]
    have := Ra.size; have := Rb.size; simp only [lazyMax]; omega
  -- the test
  have dG : (sixGenL g2 x0.th x1.th region).drop = false := by simp [d2]
  have Rc := ihc (jmp0 g2.bo) (jmp0 (g2.bo + 1)) rfl rfl trivial
    ⟨⟨by simp only [jmp0]; omega, by simp only [jmp0, sixGenL_bo]; omega⟩,
      by simp only [jmp0]; omega, by simp only [jmp0, sixGenL_bo]; omega⟩ (by omega)
    (by simp only [sixGenL_bo]; omega) dG uG h3
  have u3 : UpBelow g3 := Rc.grow.up uG
  have d3 : g3.drop = false := Rc.ext.2.2.1.trans dG
  have bG3 : g2.bo + 2 ≤ g3.bo := by have := Rc.ext.2.1; simpa using this
  have hap : ∀ e ∈ xc.laz.fork, e.1.1 ≠ g2.bo := fun e he => by
    have hm : e.1 ∈ entries xc.laz := by rw [entries_eq]; exact List.mem_append_right _ (fork_mem_entries he)
    have := (Rc.labs _ hm).1; simp only [sixGenL_bo] at this; omega
  have hcp := hrest hbig
  rw [copyL_six_apart xc x0.laz x1.laz g2.bo (g2.bo + 1) g3 hap] at hcp
  obtain ⟨⟨u, g4'⟩, hadd, e4⟩ := Option.map_eq_some_iff.mp hcp
  simp only [Prod.mk.injEq] at e4
  obtain ⟨rfl, rfl⟩ := e4
  obtain ⟨A4, r4, bo4, _⟩ := addOps_nil hadd
  simp only [emitted_re, emitted_bo] at r4 bo4
  -- the states
  have E2 : Ext g2 (sixGenL g2 x0.th x1.th region) := ext_sixGenL _ _ _ _
  have E4 : Ext g3 g4' := (ext_emit g3 _).trans (ext_addOps_nil hadd)
  have E24 : Ext g2 g4' := E2.trans (Rc.ext.trans E4)
  have E14 : Ext g1 g4' := Ra.ext.trans E24
  have E04 : Ext g0 g4' := Rb.ext.trans E14
  have re01 := Rb.ext.1
  have re12 := Ra.ext.1
  have re2G : g2.re ≤ g3.re := by have := Rc.ext.1; simpa using this
  have h4k : ∀ k, k ≠ g3.bo → HoonMap.get g4'.blocks k = HoonMap.get g3.blocks k := fun k hk =>
    (A4 k).trans (get_emitted_ne hk)
  have h4o : HoonMap.get g4'.blocks g3.bo = some ⟨[], [], Termin.hop xc.th⟩ :=
    (A4 g3.bo).trans (emitted_get g3 _ d3)
  have hG3 : ∀ k, k < g2.bo + 2 → HoonMap.get g3.blocks k =
      HoonMap.get (sixGenL g2 x0.th x1.th region).blocks k := fun k hk => Rc.ext.2.2.2 k (by simpa using hk)
  have h4y : HoonMap.get g4'.blocks g2.bo = some ⟨[], [], Termin.hop x0.th⟩ := by
    rw [h4k _ (by omega), hG3 _ (by omega)]; exact sixGenL_get_y _ _ _ d2
  have h4n : HoonMap.get g4'.blocks (g2.bo + 1) = some ⟨[], [], Termin.hop x1.th⟩ := by
    rw [h4k _ (by omega), hG3 _ (by omega)]; exact sixGenL_get_n _ _ _ d2
  have h42 : ∀ k, k < g2.bo → HoonMap.get g4'.blocks k = HoonMap.get g2.blocks k := E24.2.2.2
  have h41 : ∀ k, k < g1.bo → HoonMap.get g4'.blocks k = HoonMap.get g1.blocks k := E14.2.2.2
  -- the labels
  have lc : ∀ e ∈ entries xc.laz, g2.bo + 2 ≤ e.1 ∧ e.1 < g3.bo := fun e he => by
    have := Rc.labs e he; have := Rc.hi; simp only [sixGenL_bo] at *; omega
  have la : ∀ e ∈ entries x0.laz, g1.bo ≤ e.1 ∧ e.1 < g2.bo := fun e he =>
    ⟨(Ra.labs e he).1, Nat.lt_trans (Ra.labs e he).2.1 Ra.hi⟩
  have lb : ∀ e ∈ entries x1.laz, g0.bo ≤ e.1 ∧ e.1 < g1.bo := fun e he =>
    ⟨(Rb.labs e he).1, Nat.lt_trans (Rb.labs e he).2.1 Rb.hi⟩
  have lc' := labels_bound (P := fun o => g2.bo + 2 ≤ o ∧ o < g3.bo) lc
  have la' := labels_bound (P := fun o => g1.bo ≤ o ∧ o < g2.bo) la
  have lb' := labels_bound (P := fun o => g0.bo ≤ o ∧ o < g1.bo) lb
  have en := entries_copy_six xc.laz (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
    g2.bo (g2.bo + 1) x0.laz x1.laz
  have memE : ∀ e, e ∈ entries (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
      (xc.laz.fork ++ [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))]) xc.laz.bond) ↔
      e ∈ entries xc.laz ∨ e = (g2.bo, x0.laz) ∨ e ∈ entries x0.laz ∨ e = (g2.bo + 1, x1.laz) ∨
        e ∈ entries x1.laz := by
    intro e; rw [en]; simp only [List.mem_append, List.mem_cons]
    constructor
    · rintro (h | (h | h) | (h | h))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    · rintro (h | h | h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl (Or.inl h))
      · exact Or.inr (Or.inl (Or.inr h))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  have labAll : ∀ e ∈ entries (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
      (xc.laz.fork ++ [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))]) xc.laz.bond),
      (g2.bo + 2 ≤ e.1 ∧ e.1 < g3.bo ∧ e ∈ entries xc.laz) ∨ e.1 = g2.bo ∨
      (g1.bo ≤ e.1 ∧ e.1 < g2.bo ∧ e ∈ entries x0.laz) ∨ e.1 = g2.bo + 1 ∨
      (g0.bo ≤ e.1 ∧ e.1 < g1.bo ∧ e ∈ entries x1.laz) := by
    intro e he
    rcases (memE e).mp he with h | h | h | h | h
    · exact Or.inl ⟨(lc e h).1, (lc e h).2, h⟩
    · exact Or.inr (Or.inl (by rw [h]))
    · exact Or.inr (Or.inr (Or.inl ⟨(la e h).1, (la e h).2, h⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [h]))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨(lb e h).1, (lb e h).2, h⟩)))
  have reC : ∀ r, g2.re ≤ r → r < g3.re → g0.re ≤ r ∧ r < g4'.re := fun r h1 h2 => ⟨by omega, by omega⟩
  have reB : ∀ r, g1.re ≤ r → r < g2.re → g0.re ≤ r ∧ r < g4'.re := fun r h1 h2 => ⟨by omega, by omega⟩
  have reA : ∀ r, g0.re ≤ r → r < g1.re → g0.re ≤ r ∧ r < g4'.re := fun r h1 h2 => ⟨h1, by omega⟩
  refine ⟨E04, ?_, ?_, by simp only [jmp0]; omega, by simp only [jmp0]; omega,
    Or.inl ⟨⟨[], [], Termin.hop xc.th⟩, h4o, rfl, rfl⟩, fun r hr => ?_, Rc.dist, ?_, ?_, ?_, ?_, fun s hs => ?_, ?_⟩
  · -- grow
    have GE := growU_emit (b := ⟨[], [], Termin.hop xc.th⟩) (jumpsBelow_hop Rc.lo Rc.hi) u3
    exact Rb.grow.trans (Ra.grow.trans (GU.trans
      (Rc.grow.trans (GE.trans (growU_addOps hadd (GE.up u3))))))
  · -- cond
    rw [(KC.addOps' _ _).keep _ _ _ hadd, emitted_cond, Rc.cnd, sixGenL_cond, Ra.cnd, Rb.cnd]
  · -- regs
    have := Rc.regs r hr; simp only [sixGenL_re] at this; exact reC r this.1 this.2
  · -- eregs
    intro e he
    rcases (memE e).mp he with h | rfl | h | rfl | h
    · exact ⟨(Rc.eregs e h).1, fun r hr => by
        have := (Rc.eregs e h).2 r hr; simp only [sixGenL_re] at this; exact reC r this.1 this.2⟩
    · exact ⟨Ra.dist, fun r hr => reB r (Ra.regs r hr).1 (Ra.regs r hr).2⟩
    · exact ⟨(Ra.eregs e h).1, fun r hr => reB r ((Ra.eregs e h).2 r hr).1 ((Ra.eregs e h).2 r hr).2⟩
    · exact ⟨Rb.dist, fun r hr => reA r (Rb.regs r hr).1 (Rb.regs r hr).2⟩
    · exact ⟨(Rb.eregs e h).1, fun r hr => reA r ((Rb.eregs e h).2 r hr).1 ((Rb.eregs e h).2 r hr).2⟩
  · -- labs
    intro e he
    simp only [jmp0]
    rcases (memE e).mp he with h | rfl | h | rfl | h
    · obtain ⟨_, _, th, hth⟩ := Rc.labs e h
      have := lc e h
      exact ⟨by omega, by omega, th, (h4k _ (by omega)).trans hth⟩
    · exact ⟨by omega, by omega, x0.th, h4y⟩
    · obtain ⟨_, _, th, hth⟩ := Ra.labs e h
      have := la e h
      exact ⟨by omega, by omega, th, (h42 _ this.2).trans hth⟩
    · exact ⟨by omega, by omega, x1.th, h4n⟩
    · obtain ⟨l1, _, th, hth⟩ := Rb.labs e h
      have := lb e h
      exact ⟨l1, by omega, th, (h41 _ this.2).trans hth⟩
  · -- nodup
    rw [en, List.map_append, List.nodup_append, List.map_append, List.nodup_append]
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, List.mem_append]
    refine ⟨Rc.nodup, ⟨⟨fun hm => by have := la' _ hm; omega, Ra.nodup⟩,
      ⟨fun hm => by have := lb' _ hm; omega, Rb.nodup⟩, fun x hx y hy => ?_⟩, fun x hx y hy => ?_⟩
    · have hx' : g1.bo ≤ x ∧ x ≤ g2.bo := by
        rcases hx with e | e
        · omega
        · have := la' x e; omega
      rcases hy with e | e
      · omega
      · have := lb' y e; omega
    · have := lc' x hx
      rcases hy with (e | e) | (e | e)
      · omega
      · have := la' y e; omega
      · omega
      · have := lb' y e; omega
  · -- size
    rw [en]; simp only [List.length_append, List.length_cons, sixCount]
    have := Ra.size; have := Rb.size; have := Rc.size; omega
  · -- nec
    have fo' : ¬ FitsS xc.laz.sure s := fun f => hs ⟨f.1, (looks_uni_empty _ _).mpr f.2⟩
    rw [pureEval_n6, Rc.nec s fo']; rfl
  · -- sem
    intro cc ned σ O st t gul s0 s ag hned regs hh hn
    have notLab : ∀ o, g0.bo ≤ o → o < g4'.bo → (g3.bo ≤ o ∨
        (g2.bo + 2 ≤ o ∧ o < g3.bo ∧ o ∉ (entries xc.laz).map Prod.fst) ∨
        (g1.bo ≤ o ∧ o < g2.bo ∧ o ∉ (entries x0.laz).map Prod.fst) ∨
        (o < g1.bo ∧ o ∉ (entries x1.laz).map Prod.fst)) →
        HoonMap.get cc.blocks o = HoonMap.get g4'.blocks o := by
      intro o h0 h1 hc'
      refine ag.1 o h0 h1 fun hm => ?_
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
      rcases labAll e he with ⟨x1', x2', x3'⟩ | x | ⟨x1', x2', x3'⟩ | x | ⟨x1', x2', x3'⟩
      · rcases hc' with y | ⟨_, _, y⟩ | y | y
        · omega
        · exact y (List.mem_map_of_mem x3')
        · omega
        · omega
      · rcases hc' with y | y | y | y <;> omega
      · rcases hc' with y | y | ⟨_, _, y⟩ | y
        · omega
        · omega
        · exact y (List.mem_map_of_mem x3')
        · omega
      · rcases hc' with y | y | y | y <;> omega
      · rcases hc' with y | y | y | ⟨_, y⟩
        · omega
        · omega
        · omega
        · exact y (List.mem_map_of_mem x3')
    have hc3 : HoonMap.get cc.blocks g3.bo = some ⟨[], [], Termin.hop xc.th⟩ :=
      (notLab g3.bo (by omega) (by omega) (Or.inl (Nat.le_refl _))).trans h4o
    have hre4 : ∀ r, NMem ned r → g4'.re ≤ r := hned
    have agC : AgreeP lib O cc gul st t ned (sixGenL g2 x0.th x1.th region) g3 xc.laz s0 s := by
      refine ⟨fun o h0 h1 hnl => ?_, fun e he => ?_⟩
      · simp only [sixGenL_bo] at h0
        rw [notLab o (by omega) (by omega) (Or.inr (Or.inl ⟨h0, h1, hnl⟩)), h4k o (by omega)]
      · obtain ⟨A, th, hg, hcb, hF⟩ := ag.2 e ((memE e).mpr (Or.inl he))
        exact ⟨A, th, (h4k _ (by have := lc e he; omega)).symm.trans hg, hcb, hF.mono (by omega)⟩
    have agA : AgreeP lib O cc gul st t ned g1 g2 x0.laz s0 s := by
      refine ⟨fun o h0 h1 hnl => ?_, fun e he => ?_⟩
      · rw [notLab o (by omega) (by omega) (Or.inr (Or.inr (Or.inl ⟨h0, h1, hnl⟩))), h42 o h1]
      · obtain ⟨A, th, hg, hcb, hF⟩ := ag.2 e ((memE e).mpr (Or.inr (Or.inr (Or.inl he))))
        exact ⟨A, th, (h42 _ (la e he).2).symm.trans hg, hcb, hF.mono (by omega)⟩
    have agB : AgreeP lib O cc gul st t ned g0 g1 x1.laz s0 s := by
      refine ⟨fun o h0 h1 hnl => ?_, fun e he => ?_⟩
      · rw [notLab o (by omega) (by omega) (Or.inr (Or.inr (Or.inr ⟨h1, hnl⟩))), h41 o h1]
      · obtain ⟨A, th, hg, hcb, hF⟩ := ag.2 e ((memE e).mpr (Or.inr (Or.inr (Or.inr (Or.inr he)))))
        exact ⟨A, th, (h41 _ (lb e he).2).symm.trans hg, hcb, hF.mono (by omega)⟩
    -- a lazy block
    have lazyBlk : ∀ (o : Nat) (x : NextL S) (nm' : Nomm) (gA gB : Gen Map),
        (o, x.laz) ∈ entries (mk (⟨xc.laz.sure.ned, HoonSet.uni xc.laz.sure.lok HoonSet.empty⟩ : Sure S)
          (xc.laz.fork ++ [((g2.bo, x0.laz), (g2.bo + 1, x1.laz))]) xc.laz.bond) →
        HoonMap.get g4'.blocks o = some ⟨[], [], Termin.hop x.th⟩ → RunOKP (Map := Map) lib nm' goal gA gB x →
        AgreeP lib O cc gul st t ned gA gB x.laz s0 s → gB.re ≤ g4'.re → g0.re ≤ gA.re →
        ∀ R2, HoldsN ned R2 s0 →
          GoalSem lib O cc gul st (fun r => r < g0.re ∨ NMem ned r) R2 t (jmp0 o) goal (pureEval nm' s) := by
      intro o x nm' gA gB hm hb R agX hre hlo R2 hR2
      obtain ⟨A, th, hg, hcb, hF⟩ := ag.2 _ hm
      rw [hb] at hg
      simp only [Option.some.injEq, Blob.mk.injEq, Termin.hop.injEq, true_and] at hg
      subst hg
      have dj : ∀ y, NMem ned y → ¬ NMem x.laz.sure.ned y := fun y hy hy' => by
        have := hned y hy; have := (R.regs y hy').2; omega
      have e0 : goJ lib O cc gul st R2 t (jmp0 o) =
          execBlob lib O cc gul st R2 t ⟨[], A, Termin.hop x.th⟩ [] := goJ_jmp0 _ _ _ _ hcb
      by_cases f : FitsS x.laz.sure s
      · obtain ⟨R3, hh3, k3, e3⟩ := (fillSem_runK hF hR2 x.th).1 f
        have hn3 : HoldsN ned R3 s0 := HoldsN.agree ned (fun y hy => k3 y (Or.inl hy) (dj y hy)) hR2
        have S3 := R.sem cc ned σ O st t gul s0 s agX (fun r hr => Nat.le_trans hre (hned r hr)) R3 hh3 hn3
        refine goalSem_pre (fun r hr => ?_) (e0.trans e3) goal _
          (goalSem_mono (fun r hr => hr.elim (fun h => Or.inl (by omega)) Or.inr) goal _ S3)
        rcases hr with hr | hr
        · exact k3 r (Or.inr (by omega)) (fun h => by have := (R.regs r h).1; omega)
        · exact k3 r (Or.inl hr) (dj r hr)
      · rw [R.nec s f]
        exact goalSem_none goal (e0.trans ((fillSem_runK hF hR2 x.th).2 f))
    have Hc := Rc.sem cc ned σ O st t gul s0 s agC (fun r hr => by have := hned r hr; omega) regs
      ⟨hh.1, (looks_uni_empty _ _).mp hh.2⟩ hn
    have e0 : goJ lib O cc gul st regs t (jmp0 g3.bo) = goJ lib O cc gul st regs t xc.th := by
      rw [goJ_jmp0 _ _ _ _ hc3, execBlob_hop]
    have kk : ∀ R2 : Map (Option Noun), (∀ r, (r < (sixGenL g2 x0.th x1.th region).re ∨ NMem ned r) →
        SkaModel.read r R2 = SkaModel.read r regs) →
        ∀ r, (r < g0.re ∨ NMem ned r) → SkaModel.read r R2 = SkaModel.read r regs :=
      fun R2 k2 r hr => k2 r (hr.elim (fun h => Or.inl (by simp only [sixGenL_re]; omega)) Or.inr)
    show GoalSem lib O cc gul st (fun r => r < g0.re ∨ NMem ned r) regs t (jmp0 g3.bo) goal
      (pureEval (Nomm.n6 c a b) s)
    rw [pureEval_n6]
    cases ec : pureEval c s with
    | none => rw [ec] at Hc; exact goalSem_none goal (e0.trans Hc)
    | some v =>
      rw [ec] at Hc
      rcases v with ⟨_ | _ | k⟩ | ⟨x, y⟩
      · obtain ⟨R2, k2, e2⟩ := Hc
        exact goalSem_pre (kk R2 k2) (e0.trans e2) goal _
          (lazyBlk g2.bo x0 a g1 g2 ((memE _).mpr (Or.inr (Or.inl rfl))) h4y Ra agA (by omega) (by omega) R2
            (HoldsN.agree ned (fun x hx => k2 x (Or.inr hx)) hn))
      · obtain ⟨R2, k2, e2⟩ := Hc
        exact goalSem_pre (kk R2 k2) (e0.trans e2) goal _
          (lazyBlk (g2.bo + 1) x1 b g0 g1 ((memE _).mpr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) h4n Rb agB
            (by omega) (Nat.le_refl _) R2 (HoldsN.agree ned (fun x hx => k2 x (Or.inr hx)) hn))
      · exact goalSem_none goal (e0.trans Hc)
      · exact goalSem_none goal (e0.trans Hc)

/-- **`runL` meets `RunOKP` on `FragP`** for `%done` and `%pick`, when the
nomm has at most 255 `%6`. -/
theorem runP_ok (lib : Lib) {goal : CGoal S} {nm : Nomm} (hf : FragP goal nm) :
    ∀ {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}, NotNext goal → GJ g0.bo goal →
    sixCount nm ≤ 255 → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 →
    runL nm (CGoal.toL goal) region g0 = some (nex, g1) → RunOKP (Map := Map) lib nm goal g0 g1 nex := by
  induction hf with
  | frag hf => intro region g0 g1 nex hg hj _ b0 d0 hu h; exact runOKP_frag lib hf hg hj b0 d0 hu h
  | @six goal c a b hc _ _ ihc iha ihb =>
    exact sixP_ok lib (fragP_pure (hc (jmp0 0) (jmp0 0))) (fun z o _ _ => ihc z o) iha ihb

end Comp
end SkaModel
end Formalization
