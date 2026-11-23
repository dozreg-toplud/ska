import lemmas.Ska.CompSixNextRun

/-!
# `[6 c a b]` under a fork-free `%next`: what the code does

`sixNext_okN`: from `RunOKP` of the test for `%pick` and `RunOKN` of the
branches for the forked goals, the case `%6` for a fork-free goal `%next sur
th` meets `RunOKN`.  The code: the test's code goes to the yes block or the
no block, which are lazy blocks of the result (filled from the input
registers); each hops to its branch's code, whose goal is a copy `u` of the
need `sur` in fresh registers at the fork block `o0` or `o1`; that block
hops to the join of `+fork-need`, whose `+eval-pass` moves the copy into the
registers of `sur` (`goJ_fork`), and the join hops to the goal's block.
The threading of `+sect` changes no block, since the branches made no proxy
(`sect_spec`).

`lazyBlkN`: entering one of the two lazy blocks does for the goal `%next sur
th` what the branch does.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **A lazy block of `%6` under `%next`**: entering it does for the goal
`%next sur th` what its branch does, through the fork block `ob` and the
join `barg`. -/
theorem lazyBlkN {lib : Lib} {σ : Type} {O : Oracle σ} {cc : Straight Map} {gul : Noun} {st : σ} {t : Trace}
    {ned : Need} {sur : Sure S} {th : Jmp} (hth : th.args = []) (dsur : Distinct sur.ned)
    {g0 g9 : Gen Map} (hsur : ∀ r, NMem sur.ned r → r < g0.re) (hned : ∀ r, NMem ned r → g9.re ≤ r)
    {barg : Nat} (hbarg : HoonMap.get cc.blocks barg = some ⟨flattenNeed sur.ned, [], Termin.hop (jmp0 th.there)⟩)
    {o ob : Nat} {x : NextL S} {nm' : Nomm} {u : Sure S} {gA gB : Gen Map} {A : List Pole} {s0 s : Noun}
    (hcb : HoonMap.get cc.blocks o = some ⟨[], A, Termin.hop x.th⟩)
    (hF : FillSem lib O cc gul st t ned g9.re x.laz.sure A s0 s)
    (R : RunOKN (Map := Map) lib nm' u (jmp0 ob) gA gB x) (agX : AgreeP lib O cc gul st t ned gA gB x.laz s0 s)
    (hre : gB.re ≤ g9.re) (hlo : g0.re ≤ gA.re)
    (hl : u.lok = sur.lok) (hcp : NCopy sur.ned u.ned) (hu : ∀ r, NMem u.ned r → g0.re ≤ r ∧ r < gA.re)
    (hob : HoonMap.get cc.blocks ob = some ⟨[], [], Termin.hop ⟨(flattenNeed u.ned).map some, barg⟩⟩)
    (R2 : Map Noun) (hR2 : HoldsN ned R2 s0) :
    GoalSem lib O cc gul st (fun r => (r < g0.re ∨ NMem ned r) ∧ ¬ NMem sur.ned r) R2 t (jmp0 o)
      (CGoal.next sur th) (pureEval nm' s) := by
  have e0 : goJ lib O cc gul st R2 t (jmp0 o) = execBlob lib O cc gul st R2 t ⟨[], A, Termin.hop x.th⟩ [] :=
    goJ_jmp0 _ _ _ _ hcb
  have fitsIff : ∀ p, FitsS u p ↔ FitsS sur p := fun p => by
    simp only [FitsS, hl, hcp.fits p]
  have ujs : ∀ y, NMem u.ned y → ¬ NMem sur.ned y := fun y h1 h2 => by
    have := (hu y h1).1; have := hsur y h2; omega
  have eAB := R.ext.1
  have dj : ∀ y, NMem ned y → ¬ NMem x.laz.sure.ned y := fun y hy hy' => by
    have := hned y hy
    rcases R.regs y hy' with e | e
    · have := (hu y e).2; omega
    · omega
  by_cases f : FitsS x.laz.sure s
  · obtain ⟨R3, hh3, k3, e3⟩ := (fillSem_runK hF hR2 x.th).1 f
    have hn3 : HoldsN ned R3 s0 := HoldsN.agree ned (fun y hy => k3 y (Or.inl hy) (dj y hy)) hR2
    have S3 := R.sem cc ned σ O st t gul s0 s agX (fun r hr => Nat.le_trans hre (hned r hr)) R3 hh3 hn3
    have keep3 : ∀ r, ((r < g0.re ∨ NMem ned r) ∧ ¬ NMem sur.ned r) →
        SkaModel.read r R3 = SkaModel.read r R2 := by
      intro r hr
      refine k3 r (hr.1.elim (fun h => Or.inr (by omega)) Or.inl) (fun hx => ?_)
      rcases R.regs r hx with e | e
      · rcases hr.1 with h | h
        · have := (hu r e).1; omega
        · have := hned r h; have := (hu r e).2; omega
      · rcases hr.1 with h | h
        · omega
        · have := hned r h; omega
    cases ev : pureEval nm' s with
    | none =>
      rw [ev] at S3
      exact goalSem_none (CGoal.next sur th) ((e0.trans e3).trans S3)
    | some p =>
      rw [ev] at S3
      refine ⟨fun fp => ?_, fun fp => (e0.trans e3).trans (S3.2 fun fu => fp ((fitsIff p).mp fu))⟩
      obtain ⟨R4, hh4, k4, e4⟩ := S3.1 ((fitsIff p).mpr fp)
      obtain ⟨R5, hh5, k5, e5⟩ := goJ_fork (lib := lib) (O := O) (gul := gul) (st := st) hth hob hbarg hcp dsur
        ujs hh4 t
      refine ⟨R5, hh5, fun r hr => ?_, (e0.trans e3).trans (e4.trans e5)⟩
      rw [k5 r hr.2, k4 r ⟨hr.1.elim (fun h => Or.inl (by omega)) Or.inr, fun hu' => ?_⟩, keep3 r hr]
      rcases hr.1 with h | h
      · have := (hu r hu').1; omega
      · have := hned r h; have := (hu r hu').2; omega
  · have crash := e0.trans ((fillSem_runK hF hR2 x.th).2 f)
    rcases R.nec s f with ev | ⟨p, ev, nf⟩
    · rw [ev]; exact goalSem_none _ crash
    · rw [ev]
      exact ⟨fun fp => absurd ((fitsIff p).mpr fp) nf, fun _ => crash⟩

end Comp
end SkaModel
end Formalization
