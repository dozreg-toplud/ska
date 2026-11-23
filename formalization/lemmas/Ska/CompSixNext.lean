import lemmas.Ska.CompNestPick

/-!
# `%6` for a goal `%next`: the simpler branch taken apart

`sixNextL_ofSure` (in `CompLazyRun.lean`): on a fork-free goal the case `%6`
for `%next` takes its simpler branch, `sixNextSimple`.  Here
`sixNextSimple_apart` takes that branch apart into its steps, for a pure
test (so `+past-fork` changes nothing) and a fork that is not big (so
`+lazy-shut` does not fire): `+fork-sure` of the goal's sure need into two
fresh blocks, the no branch and then the yes branch compiled in a new
region for the two forked needs, `+sect`, the test compiled for `%pick`,
and `+copy` of the fork into the test's need.

This is the first step of the proof of `%6` under `%next`.  The rest is
not proved: see the notes of the report of this track and the finding
recorded at `sixNextL`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **`sixNextSimple` taken apart.** -/
theorem sixNextSimple_apart {rp rq rr : CGoalL S → List Nat → CM Map (NextL S)} {p : Nomm}
    (hp : p.pure = true) {laz : Lazy S} {th : Jmp} {region : List Nat} {g0 g9 : Gen Map} {nex : NextL S}
    (h : sixNextSimple rp rq rr p laz th region g0 = some (nex, g9)) :
    ∃ (s0 s1 : Sure S) (x1 x0 xc : NextL S) (lz : Lazy S) (yes nuh : Nat) (gF gR gQ gS gC : Gen Map),
      forkSure laz.sure th.there g0.bo (g0.bo + 1) { g0 with bo := g0.bo + 1 + 1 } = some ((s0, s1), gF) ∧
      rr (CGoalL.next (ofSure s1) (jmp0 (g0.bo + 1))) (gF.id :: region) { gF with id := gF.id + 1 } =
        some (x1, gR) ∧
      rq (CGoalL.next (ofSure s0) (jmp0 g0.bo)) (gF.id :: region) gR = some (x0, gQ) ∧
      sect x0 x1 g0.bo (g0.bo + 1) (gF.id :: region) gF.cond gR.cond gQ = some ((lz, yes, nuh), gS) ∧
      rp (CGoalL.pick (jmp0 yes) (jmp0 nuh)) region gS = some (xc, gC) ∧
      (lazyBig lz = false → copyL xc lz gC = some (nex, g9)) := by
  simp only [sixNextSimple] at h
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
  simp only [liftO, pastFork_pure _ _ hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hP
  obtain ⟨rfl, rfl⟩ := hP
  obtain ⟨xc, gC, hC, h⟩ := bind_some h
  refine ⟨s0, s1, x1, x0, xc, lz, yes, nuh, gF, gR, gQ, gS, gC, hF, hR, hQ, hS, hC, fun hbig => ?_⟩
  rw [softLess_noSoft, hbig] at h
  exact h

end Comp
end SkaModel
end Formalization
