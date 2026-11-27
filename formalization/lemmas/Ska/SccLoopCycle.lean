import lemmas.Ska.SccLoop
import lemmas.Ska.SccLoopMsg

/-! # A member compile under which the loop of `+compile-scc-in` never ends (README Gaps 21.8)

One bell `0` that calls itself, under the cape `[[| |] [| |]]`, whose `need-new` is a function
of the view of its own need: `this ↦ bTT ↦ bBig ↦ this` (`Comp.msgOrd_cycle`), `sur` always
`none`.  It meets `Hyp` (`cyc_hyp`: the compile reads only its kid, ignores the mode,
`msgOrd_self`, `msgOrd_abs`), and yet every sweep changes the entry: after the `%may` sweep
the entries go `bTT`, `bBig`, `this`, `bTT`, ... and the loop runs out of any fuel tried
(`cyc_loop`, 12 sweeps: four turns of the cycle).  So the loop's termination is not a consequence of `Hyp`: it needs a
property of the member compile. -/

namespace Formalization.SkaModel.SccLoop
open Formalization.SkaModel Formalization.SkaModel.Comp

/-- The need of the member as a function of the view of its own need. -/
def cycF (v : NeedOrd) : NeedOrd :=
  if v = NeedOrd.this then bTT else if v = bTT then bBig else NeedOrd.this

def cyc : Cfg Nat NeedOrd where
  scc := [0]
  order := [0]
  kids := fun _ => [0]
  none := NeedOrd.none
  msg := fun _ n p => msgOrd n p cape22
  comp := fun _ _ vn _ => ⟨cycF (vn 0), NeedOrd.none⟩

theorem cyc_hyp : Hyp cyc where
  kidsOnly := by
    intro b m vn vs vn' vs' h
    have := (h 0 (by simp [cyc])).1
    simp [cyc, this]
  shape := by intro b vn vs; rfl
  msgSelf := by intro b n; exact msgOrd_self n cape22
  msgAbs := by intro b n p; exact msgOrd_abs n p cape22

/-- Each sweep on a state whose entry is on the cycle and whose bell changed at its last run. -/
def CycInv (st : St Nat NeedOrd) : Prop :=
  ∃ v, (v = NeedOrd.this ∨ v = bTT ∨ v = bBig) ∧ st.ml 0 = some v ∧
    ∃ r, st.ran 0 = some r ∧ st.chg 0 = some r

theorem cyc_sweep (top : Nat → NeedOrd) (st : St Nat NeedOrd) (h : CycInv st) :
    (sweep cyc top st).any = true ∧ CycInv (sweep cyc top st) := by
  obtain ⟨v, hv, hml, r, hr, hc⟩ := h
  have hd : dirty cyc st 0 = true := by simp [dirty, cyc, hr, hc]
  have e : sweep cyc top st = sweepStep cyc top st 0 := rfl
  rw [e]
  unfold sweepStep
  rw [if_pos hd]
  refine ⟨rfl, ?_⟩
  have k : msgOrd (cycF v) v cape22 = cycF v ∧ cycF v ≠ v := by
    rcases hv with rfl | rfl | rfl <;> decide
  refine ⟨cycF v, ?_, ?_, st.tick + 1, by simp, ?_⟩
  · rcases hv with rfl | rfl | rfl <;> decide
  · simp only [member, viewN, cyc, hml, upd_same, Option.getD_some, k.1]
  · simp only [member, viewN, cyc, hml, Option.getD_some, k.1]
    simp [k.2]

theorem cyc_loop_none (top : Nat → NeedOrd) :
    ∀ n (st : St Nat NeedOrd), CycInv st → loop cyc top n st = none := by
  intro n
  induction n with
  | zero => intro st _; rfl
  | succ n ih =>
    intro st h
    obtain ⟨ha, hi⟩ := cyc_sweep top st h
    simp only [loop, ha, if_true]
    apply ih
    obtain ⟨v, hv, hml, r, hr, hc⟩ := hi
    exact ⟨v, hv, hml, r, hr, hc⟩

/-- **The loop never returns**, whatever the fuel: after the `%may` sweep the entry goes
`bTT`, `bBig`, `this`, `bTT`, ..., each sweep a change. -/
theorem cyc_never (n : Nat) : compileSccIn cyc false n St.empty = none := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [compileSccIn, Bool.false_eq_true, if_false]
    simp only [loop]
    have h1 : (sweep cyc (topOf cyc (maySweep cyc St.empty)) { maySweep cyc St.empty with
        ml := fun _ => none, tick := 0, ran := fun _ => none, chg := fun _ => none,
        any := false, rd := fun _ => none }).any = true := by decide
    rw [if_pos h1]
    rw [cyc_loop_none _ n _ ?_]
    · rfl
    · refine ⟨bTT, Or.inr (Or.inl rfl), by decide, 1, by decide, by decide⟩

end Formalization.SkaModel.SccLoop
