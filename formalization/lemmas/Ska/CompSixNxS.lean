import lemmas.Ska.CompSixNxRel
import lemmas.Ska.CompSixNext
import lemmas.Ska.CompSixFuel
import lemmas.Ska.CompTagU

/-!
# `[6 c a b]` under `%next`, phase S: the pieces (generated in part)

README Gaps 12.36.  Written by `tools/gen/sixnxs.py`; do not edit by hand.
Phase S is the goal whose entries ask nothing; under a goal with no entry it
is the only phase (`sixNextLC_fork_free`).

* `sixNextSimpleC_apart`: the run taken apart (the text of
  `sixNextSimple_apart` with `+past-fork` of `cod`).
* `runLC_six_nextE`: at a goal with no entry `%6` is `sixNextSimpleC`.
* `TagLS`: every key a run under a goal with no entry adds to `cond` has a
  tag with its region as a suffix (what `+sect` needs of the branches to
  thread nothing, `sect_specV` through `sect_h0`, `sect_h1`), checked on the
  branches in `CompSixNxCheck.lean`; `sect_specS`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **`sixNextSimpleC` taken apart** (generated from `sixNextSimple_apart`). -/
theorem sixNextSimpleC_apart {cod : Bell → Option Bool} {rp rq rr : CGoalL S → List Nat → CM Map (NextL S)} {p : Nomm}
    {laz : Lazy S} {th : Jmp} {region : List Nat} {g0 g9 : Gen Map} {nex : NextL S}
    (h : sixNextSimpleC cod rp rq rr p laz th region g0 = some (nex, g9)) :
    ∃ (s0 s1 : Sure S) (x1 x0 xc : NextL S) (lz lw : Lazy S) (yes nuh : Nat) (gF gR gQ gS gC : Gen Map),
      forkSure laz.sure th.there g0.bo (g0.bo + 1) { g0 with bo := g0.bo + 1 + 1 } = some ((s0, s1), gF) ∧
      rr (CGoalL.next (ofSure s1) (jmp0 (g0.bo + 1))) (gF.id :: region) { gF with id := gF.id + 1 } =
        some (x1, gR) ∧
      rq (CGoalL.next (ofSure s0) (jmp0 g0.bo)) (gF.id :: region) gR = some (x0, gQ) ∧
      sect x0 x1 g0.bo (g0.bo + 1) (gF.id :: region) gF.cond gR.cond gQ = some ((lz, yes, nuh), gS) ∧
      pastFork cod lz p = some lw ∧
      rp (CGoalL.pick (jmp0 yes) (jmp0 nuh)) region gS = some (xc, gC) ∧
      (lazyBig lw = false → copyL xc lw gC = some (nex, g9)) := by
  simp only [sixNextSimpleC] at h
  obtain ⟨o0, ga, ha, h⟩ := bind_some h
  obtain ⟨o1, gb, hb, h⟩ := bind_some h
  simp only [oo, Option.some.injEq, Prod.mk.injEq] at ha hb
  obtain ⟨rfl, rfl⟩ := ha
  obtain ⟨rfl, rfl⟩ := hb
  obtain ⟨⟨s0, s1⟩, gF, hF, h⟩ := bind_some h
  obtain ⟨rid, gI, hI, h⟩ := bind_some h
  simp only [idM, Option.some.injEq, Prod.mk.injEq] at hI
  obtain ⟨rfl, rfl⟩ := hI
  obtain ⟨cb, gc1, hc1, h⟩ := bind_some h
  simp only [getCond, Option.some.injEq, Prod.mk.injEq] at hc1
  obtain ⟨rfl, rfl⟩ := hc1
  obtain ⟨x1, gR, hR, h⟩ := bind_some h
  obtain ⟨cw, gc2, hc2, h⟩ := bind_some h
  simp only [getCond, Option.some.injEq, Prod.mk.injEq] at hc2
  obtain ⟨rfl, rfl⟩ := hc2
  obtain ⟨x0, gQ, hQ, h⟩ := bind_some h
  obtain ⟨⟨lz, yes, nuh⟩, gS, hS, h⟩ := bind_some h
  obtain ⟨lz', gP, hP, h⟩ := bind_some h
  simp only [liftO] at hP
  obtain ⟨lw, hw, hP⟩ := Option.map_eq_some_iff.mp hP
  simp only [Prod.mk.injEq] at hP
  obtain ⟨rfl, rfl⟩ := hP
  obtain ⟨xc, gC, hC, h⟩ := bind_some h
  refine ⟨s0, s1, x1, x0, xc, lz, lw, yes, nuh, gF, gR, gQ, gS, gC, hF, hR, hQ, hS, hw, hC, fun hbig => ?_⟩
  rw [softLess_noSoft, hbig] at h
  exact h

/-- **At a goal with no entry, `%6` is phase S.** -/
theorem runLC_six_nextE (env : CallEnv) (sup : Option Nomm) (c a b : Nomm) {L : Lazy S} (he : entries L = [])
    (th : Jmp) (region : List Nat) :
    (runLC env sup (Nomm.n6 c a b) (CGoalL.next L th) region : CM Map (NextL S)) =
      sixNextSimpleC env.cod (runLC env sup c) (runLC env sup a) (runLC env sup b) c L th region := by
  have hf := entries_nil_flat he
  have eL : L = mk L.sure [] [] := by
    rcases L with ⟨s, F, B⟩
    obtain ⟨h1, _⟩ := hf
    simp only [fork_mk] at h1
    subst h1
    cases B with
    | nil => rfl
    | cons e B => cases e; simp [entries, bondEntries] at he
  rw [eL]
  simp only [runLC]
  exact sixNextLC_fork_free env.cod _ _ _ c a b 2 L.sure th region

/-- **The tag clause of a run under a goal with no entry**: every key it adds
to `cond` has a tag with its region as a suffix. -/
abbrev TagLS (env : CallEnv) (nm : Nomm) : Prop :=
  ∀ {sup : Option Nomm} {L : Lazy S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    entries L = [] → sixCount nm ≤ 255 → 1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    runLC env sup nm (CGoalL.next L th) region g0 = some (nex, g1) → CondTag region g0.cond g1.cond

/-- **`+sect` of phase S threads nothing** when both branches meet the tag
clause from the states the run gives them (`sect_specV`). -/
theorem sect_specS {nex0 nex1 : NextL S} {o0 o1 rid : Nat} {region : List Nat} {cb cw : Map (Nat × List Nat)}
    {g g' : Gen Map} {lz : Lazy S} {yes nuh : Nat} (hd : g.drop = false)
    (t1 : CondTag (rid :: region) cb cw) (t0 : CondTag (rid :: region) cw g.cond)
    (h : sect nex0 nex1 o0 o1 (rid :: region) cb cw g = some ((lz, yes, nuh), g')) :
    yes = g.bo ∧ nuh = g.bo + 1 ∧ nex0.th.args = [] ∧ nex1.th.args = [] ∧
    lz = mk Sure.bunt [((g.bo, nex0.laz), (g.bo + 1, nex1.laz))] [] ∧
    SameBlocks (sixGenL g nex0.th nex1.th (rid :: region)) g' :=
  sect_specV hd (sect_h0 t0) (sect_h1 t1) h

end Comp
end SkaModel
end Formalization
