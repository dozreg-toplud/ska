import lemmas.Ska.CompMede

/-!
# `%3` and `%4` for `%done` and `%pick`

`unary_ok`: a block that takes the product of `p` from one register and does
for a goal what `f` of it asks, emitted before `p` is compiled for the goal
`%next` into that register, gives the relation for the nomm whose value is
the value of `p` through `f`.  The cases `%3` and `%4` of `run` for `%done`
and `%pick` are such blocks.
-/

set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

theorem unary_ok {lib : Lib} {nm p : Nomm} {goal : CGoal S} {g0 g' g1 : Gen Map} {a o : Nat}
    {nexp : Next S} {f : Noun → Option Noun}
    (hev : ∀ s, pureEval nm s = (pureEval p s).bind f) (hpre : Ext g0 g')
    (ha : g0.re ≤ a ∧ a < g'.re) (ho : o < g'.bo)
    (hp : RunOK lib p (CGoal.next (lazyReg a) (jmp0 o)) g' g1 nexp)
    (hblk : ∀ (c : Straight Map), Agree c g0 g' → g0.drop = false →
      ∀ (σ : Type) (O : Oracle σ) st regs t gul x, SkaModel.read a regs = some x →
      GoalSem lib O c gul st (Keep g0 goal) regs t (jmp0 o) goal (f x))
    (hgo : g0.bo ≤ o) :
    RunOK lib nm goal g0 g1 nexp where
  ext := hpre.trans hp.ext
  regs := fun r hr => by
    rcases hp.regs r hr with h | ⟨h1, h2⟩
    · simp only [GMem, lazyReg, NMem] at h; subst h
      exact Or.inr ⟨ha.1, Nat.lt_of_lt_of_le ha.2 hp.ext.1⟩
    · exact Or.inr ⟨Nat.le_trans hpre.1 h1, h2⟩
  nec := fun s hs => by
    rw [hev]
    rcases hp.nec s hs with h | ⟨x, h1, h2⟩
    · rw [h]; exact Or.inl rfl
    · exact absurd ⟨trivial, looks_empty x⟩ h2
  dist := hp.dist
  sem := fun hd c hag σ O st s regs t gul hh => by
    have hd' : g'.drop = false := hpre.2.2.1.trans hd
    have Hp := hp.sem hd' c (hag.right hpre) σ O st s regs t gul hh
    rw [hev]
    cases e : pureEval p s with
    | none => rw [e] at Hp; exact goalSem_crash goal Hp
    | some x =>
      rw [e] at Hp
      obtain ⟨regs', hh', hk, he⟩ := Hp.1 ⟨trivial, looks_empty x⟩
      exact GoalSem.transfer he (fun r ⟨h1, h2⟩ => hk r ⟨Nat.lt_of_lt_of_le h1 hpre.1, fun e => by
          simp only [GMem, lazyReg, NMem] at e; omega⟩)
        (hblk c (hag.left hpre hp.ext) hd σ O st regs' t gul x hh')

/-- `[4 p]`: the value through `+(x)`. -/
def incF : Noun → Option Noun
  | Noun.atom a => some (A (a + 1))
  | Noun.cell _ _ => none

theorem pureEval_n4 (p : Nomm) (s : Noun) : pureEval (Nomm.n4 p) s = (pureEval p s).bind incF := by
  simp only [pureEval]; cases pureEval p s with
  | none => rfl
  | some x => cases x <;> rfl

theorem pureEval_n3 (p : Nomm) (s : Noun) :
    pureEval (Nomm.n3 p) s = (pureEval p s).bind fun x => some (wut x) := by
  simp only [pureEval]

theorem emitted_get' {g : Gen Map} {b : Blob} (hd : g.drop = false) {c : Straight Map}
    (hc : HoonMap.get c.blocks g.bo = HoonMap.get (g.emitted b).blocks g.bo) :
    HoonMap.get c.blocks g.bo = some b := hc.trans (emitted_get g b hd)

theorem run_n4_done_ok {lib : Lib} {p : Nomm} {g0 g1 : Gen Map} {nex : Next S}
    (h : run (Nomm.n4 p) (CGoal.done : CGoal S) g0 = some (nex, g1))
    (ih : ∀ (laz : Sure S) (th : Jmp) (g g' : Gen Map) (nex' : Next S), GoalOK g (CGoal.next laz th) →
      run p (CGoal.next laz th) g = some (nex', g') → RunOK lib p (CGoal.next laz th) g g' nex') :
    RunOK lib (Nomm.n4 p) CGoal.done g0 g1 nex := by
  simp only [run, bind_apply, re_apply, emit_apply, Option.bind_some] at h
  refine unary_ok (pureEval_n4 p) ((ext_re _).trans ((ext_re _).trans (ext_emit _ _)))
    ⟨Nat.le_succ _, by simp [emitted_re]⟩ (by simp [emitted_bo])
    (ih _ _ _ _ _ ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; simp [emitted_re]⟩ h) ?_
    (by simp)
  intro c hc hd σ O st regs t gul x hx
  have hb := emitted_get' (by simpa using hd) (hc _ (by simp) (by simp [emitted_bo]))
  simp only [GoalSem]
  rw [goJ_jmp0 _ _ _ _ hb]
  cases x with
  | atom n =>
    rw [show [Pole.inc _ _] = [Pole.inc _ _] ++ [] from rfl, runs_inc hx]
    simp [incF, toneOf, execBlob_don', read_store_eq]
  | cell u v =>
    rw [show [Pole.inc _ _] = [Pole.inc _ _] ++ [] from rfl, crashes_inc hx]
    rfl

theorem run_n4_pick_ok {lib : Lib} {p : Nomm} {z o : Jmp} {g0 g1 : Gen Map} {nex : Next S}
    (h : run (Nomm.n4 p) (CGoal.pick z o : CGoal S) g0 = some (nex, g1))
    (ih : ∀ (laz : Sure S) (th : Jmp) (g g' : Gen Map) (nex' : Next S), GoalOK g (CGoal.next laz th) →
      run p (CGoal.next laz th) g = some (nex', g') → RunOK lib p (CGoal.next laz th) g g' nex') :
    RunOK lib (Nomm.n4 p) (CGoal.pick z o) g0 g1 nex := by
  simp only [run, bind_apply, re_apply, emit_apply, Option.bind_some] at h
  refine unary_ok (pureEval_n4 p) ((ext_re _).trans ((ext_re _).trans (ext_emit _ _)))
    ⟨Nat.le_succ _, by simp [emitted_re]⟩ (by simp [emitted_bo])
    (ih _ _ _ _ _ ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; simp [emitted_re]⟩ h) ?_
    (by simp)
  intro c hc hd σ O st regs t gul x hx
  have hb := emitted_get' (by simpa using hd) (hc _ (by simp) (by simp [emitted_bo]))
  have hj := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
  cases x with
  | atom n =>
    rw [show [Pole.inc _ _] = [Pole.inc _ _] ++ [] from rfl, runs_inc hx, execBlob_brn, read_store_eq,
      Option.bind_some] at hj
    rcases n with _ | n
    · simp only [incF]
      refine ⟨store g0.re (A (0 + 1)) regs, fun r ⟨h1, _⟩ => read_store_ne (show r ≠ g0.re by omega) _ _, ?_⟩
      rw [hj]; simp
    · simp only [incF]
      exact goalSem_pick_other (by simp) (by simp) (by rw [hj]; simp)
  | cell u v =>
    simp only [incF]
    apply goalSem_crash
    rw [hj, show [Pole.inc _ _] = [Pole.inc _ _] ++ [] from rfl, crashes_inc hx]

theorem execBlob_clq {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ}
    (regs : Map Noun) (t : Trace) (r : Nat) (z o : Jmp) :
    execBlob lib O c gul st regs t ⟨[], [], Termin.clq r z o⟩ [] =
      (SkaModel.read r regs).bind fun v => match v with
        | Noun.cell _ _ => goJ lib O c gul st regs t z
        | Noun.atom _ => goJ lib O c gul st regs t o := by
  rw [execBlob]; simp only [goJ]; cases SkaModel.read r regs with
  | none => rfl
  | some v => cases v <;> rfl

theorem run_n3_pick_ok {lib : Lib} {p : Nomm} {z o : Jmp} {g0 g1 : Gen Map} {nex : Next S}
    (h : run (Nomm.n3 p) (CGoal.pick z o : CGoal S) g0 = some (nex, g1))
    (ih : ∀ (laz : Sure S) (th : Jmp) (g g' : Gen Map) (nex' : Next S), GoalOK g (CGoal.next laz th) →
      run p (CGoal.next laz th) g = some (nex', g') → RunOK lib p (CGoal.next laz th) g g' nex') :
    RunOK lib (Nomm.n3 p) (CGoal.pick z o) g0 g1 nex := by
  simp only [run, bind_apply, re_apply, emit_apply, Option.bind_some] at h
  refine unary_ok (pureEval_n3 p) ((ext_re _).trans (ext_emit _ _))
    ⟨Nat.le_refl _, by simp [emitted_re]⟩ (by simp [emitted_bo])
    (ih _ _ _ _ _ ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; simp [emitted_re]⟩ h) ?_
    (by simp)
  intro c hc hd σ O st regs t gul x hx
  have hb := emitted_get' (by simpa using hd) (hc _ (by simp) (by simp [emitted_bo]))
  have hj := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
  rw [execBlob_clq, hx, Option.bind_some] at hj
  cases x with
  | atom n => exact ⟨regs, fun _ _ => rfl, by rw [hj]⟩
  | cell u v => exact ⟨regs, fun _ _ => rfl, by rw [hj]⟩

end Comp
end SkaModel
end Formalization
