import lemmas.Ska.CompRunLC

/-!
# The fuel `3` of `sixNextLC`

The Hoon's case `%6` of `+run` under a goal `%next` runs itself again with
no bound: after `+leap` (on the rest it returned), after `+kerf` (on a goal
with one register and no fork).  The model `sixNextLC` runs it again at most
twice (`runLC` passes the fuel `3`) and crashes when the fuel is out.

`LeapTwice laz q r`: `+leap` of the rest that `+leap` returned is `~`.  Under
it the fuel `3` is as good as any larger fuel (`sixNextLC_fuel`), so the
model is the Hoon's unbounded recursion.  `LeapTwice` is proved, not here
(this file is imported by the proof): `leap_twice` of `Ska/CompLeapTwice.lean`
for passes with nonzero product axes, and `leapTwice_noAx0` of
`Ska/CompLeapTwiceRun.lean` for every lazy need on branches with
`Bake.NoAx0` (with `sixNextLC_fuel_tw`, the fuel `3` without the
hypothesis).  It had held on the real compiler over 726 formulas
(`tools/hoon/leaptwice.py`, 2026-11-27: 708 leaps, 174 of them with a rest
that still forks or bonds, never a second leap).

`sixNextLC_fork_free`: on a goal with no fork and no bond (as after `+kerf`)
any fuel from `1` on gives phase S (`sixNextSimpleC`).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- `+leap` of the rest that `+leap` returned is `~` (proved on branches with
`Bake.NoAx0`: `leapTwice_noAx0`). -/
def LeapTwice (laz : Lazy S) (q r : Nomm) : Prop :=
  ∀ rest bys, leap laz q r = some (some (rest, bys)) → leap rest q r = some Option.none

theorem small_empty : HoonSet.small (HoonSet.empty : S) = true :=
  (HoonSet.small_iff _).2 fun x hx => absurd hx (HoonSet.mem_empty x)

theorem noneEquivalentL_bunt : noneEquivalentL (mk (Sure.bunt : Sure S) [] []) = true := by
  simp [noneEquivalentL, Sure.bunt, small_empty, noneForks, noneBonds]

/-- On a goal with no fork and no bond, any fuel from `1` on is phase S. -/
theorem sixNextLC_fork_free [HoonMapKeys Map] (cod : Bell → Option Bool)
    (rp rq rr : CGoalL S → List Nat → CM Map (NextL S)) (p q r : Nomm) (n : Nat) (s : Sure S)
    (th : Jmp) (region : List Nat) :
    sixNextLC cod rp rq rr p q r (n + 1) (mk s [] []) th region =
      sixNextSimpleC cod rp rq rr p (mk s [] []) th region := by
  simp only [sixNextLC, leap, List.isEmpty_nil, Bool.and_self, if_true, Lazy.fork, Lazy.bond,
    noneEquivalentL_bunt, Bool.not_true]
  rfl

/-- After a `+leap` that gives `~`, any fuel from `2` on gives the same. -/
theorem sixNextLC_leap_none [HoonMapKeys Map] (cod : Bell → Option Bool)
    (rp rq rr : CGoalL S → List Nat → CM Map (NextL S)) (p q r : Nomm) (n m : Nat) (laz : Lazy S)
    (th : Jmp) (region : List Nat) (h : leap laz q r = some Option.none) :
    sixNextLC cod rp rq rr p q r (n + 2) laz th region =
      sixNextLC cod rp rq rr p q r (m + 2) laz th region := by
  rw [sixNextLC.eq_2 (fuel := n + 1), sixNextLC.eq_2 (fuel := m + 1)]
  simp only [h, ofSure, sixNextLC_fork_free]

/-- Under `LeapTwice`, the fuel `3` is as good as any larger one. -/
theorem sixNextLC_fuel [HoonMapKeys Map] (cod : Bell → Option Bool)
    (rp rq rr : CGoalL S → List Nat → CM Map (NextL S)) (p q r : Nomm) (k : Nat) (laz : Lazy S)
    (th : Jmp) (region : List Nat) (h : LeapTwice laz q r) :
    sixNextLC cod rp rq rr p q r (k + 3) laz th region =
      sixNextLC cod rp rq rr p q r 3 laz th region := by
  cases hl : leap laz q r with
  | none => simp only [sixNextLC, hl]
  | some l =>
    cases l with
    | none => exact sixNextLC_leap_none cod rp rq rr p q r (k + 1) 1 laz th region hl
    | some x =>
      obtain ⟨rest, bys⟩ := x
      have h2 := h rest bys hl
      rw [sixNextLC.eq_2 (fuel := k + 2), sixNextLC.eq_2 (fuel := 2)]
      simp only [hl]
      rw [sixNextLC_leap_none cod rp rq rr p q r k 0 rest th region h2]

end Comp
end SkaModel
end Formalization
