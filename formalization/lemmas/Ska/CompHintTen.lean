import lemmas.Ska.CompHintDirectReg

/-!
# The run of `[10 [a v] q]` with a kept value, step by step (README Gaps 24.20)

The model half of `%10` in the hinted classes, as `CompHintTenCheck.lean`
checks it on the model:
* `runLCH_n10_next`: the run under `%next L th` is `+into` at `a`, `+past`
  of the recipient over `v`, `v` under `%next don`, `+past` of `v`'s result
  over `q`, `q` under `%next` of the recipient's past, `+copy`.
* `pastL_park`: `+past` of `⟨ofSure r, j⟩` over a hinted `v`, when `r`
  asks something, is `+lazy-bound` of it (the block `hop j`, tagged, `r`
  parked in a bond at it).
* **`runLCH_n10_kept`**: the run of `[10 [a v] [0 1]]` under `%next (ofSure
  sur) th` with `v` hinted and the recipient asking something (the case of
  `spotArm`'s `%10` and of `d20`): `+into` (`into`, both parts `ofSure`),
  `+lazy-bound` of the recipient, `v` under `%next (ofSure d) (jmp0 o')`,
  `+copy` of the parked recipient with `v`'s result.

What is left for `%10` in `SurGBT RegLike` (the premise `Hten` of
`regGBT_spotArm5`): the `RunOKGBT` of that composition, from `v`'s
`RunOKGBT` at `%next d (jmp0 o')` (`v` in `SurGBT` at the donor need), the
fill of the parked recipient at `o'` (the agreement at its entry), the
`%con`s of the `+into` block, and the entries of the copy.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]
variable {snd : Nomm → NeedOrd → Bool}

/-- **The run of `[10 [a v] q]` under `%next L th`, step by step.** -/
theorem runLCH_n10_next {env : CallEnv} {sup : Option Nomm} {a : Nat} {v q : Nomm} {L : Lazy S} {th : Jmp}
    {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (h : runLCH (S := S) (Map := Map) env snd true sup (Nomm.n10 a v q) (CGoalL.next L th) region g0 =
      some (nex, g1)) :
    ∃ don rec o g2 nexR g3 nexDon g4 nexDon' g5 nexRec g6,
      intoL (⟨L, th⟩ : NextL S) a g0 = some ((don, rec, o), g2) ∧
      pastL env.cod ⟨rec, jmp0 o⟩ v region g2 = some (nexR, g3) ∧
      runLCH (S := S) (Map := Map) env snd true sup v (CGoalL.next don nexR.th) region g3 = some (nexDon, g4) ∧
      pastL env.cod nexDon q region g4 = some (nexDon', g5) ∧
      runLCH (S := S) (Map := Map) env snd true sup q (CGoalL.next nexR.laz nexDon'.th) region g5 =
        some (nexRec, g6) ∧
      copyL nexRec nexDon'.laz g6 = some (nex, g1) := by
  simp only [runLCH] at h
  obtain ⟨n0, ga, h0, h⟩ := bind_some h
  simp only [simpleNextL, pure_apply, Option.some.injEq, Prod.mk.injEq] at h0
  obtain ⟨rfl, rfl⟩ := h0
  obtain ⟨⟨don, rec, o⟩, g2, h2, h⟩ := bind_some h
  obtain ⟨nexR, g3, h3, h⟩ := bind_some h
  obtain ⟨nexDon, g4, h4, h⟩ := bind_some h
  obtain ⟨nexDon', g5, h5, h⟩ := bind_some h
  obtain ⟨nexRec, g6, h6, h⟩ := bind_some h
  exact ⟨don, rec, o, g2, nexR, g3, nexDon, g4, nexDon', g5, nexRec, g6, h2, h3, h4, h5, h6, h⟩

/-- **`+past` over a hinted nomm, of a need that asks something, is
`+lazy-bound`.** -/
theorem pastL_park (cod : Bell → Option Bool) {v : Nomm} (hv : hinted cod v = some true) (r : Sure S) (j : Jmp)
    (region : List Nat) (hr : ¬ (r.ned = Need.none ∧ HoonSet.small r.lok = true)) (hj : j.args = []) :
    (pastL cod (⟨ofSure r, j⟩ : NextL S) v region : CM Map (NextL S)) = lazyBound ⟨ofSure r, j⟩ region := by
  funext g
  unfold pastL lazyBound
  have hn : ¬ ((ofSure r : Lazy S).sure.ned = Need.none ∧ HoonSet.small (ofSure r : Lazy S).sure.lok = true ∧
      (ofSure r : Lazy S).fork.isEmpty = true) := fun ⟨a, b, _⟩ => hr ⟨a, b⟩
  rw [if_neg hn, hv]
  simp only [hj, ↓reduceIte, bind_apply, emit_apply, Option.bind_some]
  rfl

/-- **The run of `[10 [a v] [0 1]]` with a hinted value under `%next (ofSure
sur) th`**, when the recipient asks something (`spotArm`'s `%10`, `d20`):
`+into` at `a` (the block `o`, the donor `d`, the recipient `r`), `+lazy-bound`
of `⟨ofSure r, jmp0 o⟩` (the block `o'`, the result `nb`), `v` under `%next
(ofSure d) nb.th`, `+copy` of `nb` with `v`'s result. -/
theorem runLCH_n10_kept {env : CallEnv} {sup : Option Nomm} {a : Nat} {v : Nomm} (hv : hinted env.cod v = some true)
    {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (h : runLCH (S := S) (Map := Map) env snd true sup (Nomm.n10 a v (Nomm.n0 1)) (CGoalL.next (ofSure sur) th)
      region g0 = some (nex, g1)) :
    ∃ d r o g2 nb g3 nexDon g4,
      into (⟨sur, th⟩ : Next S) a g0 = some ((d, r, o), g2) ∧
      ((r.ned = Need.none ∧ HoonSet.small r.lok = true ∧ nb = ⟨ofSure r, jmp0 o⟩ ∧ g3 = g2) ∨
        (¬ (r.ned = Need.none ∧ HoonSet.small r.lok = true) ∧
          lazyBound (⟨ofSure r, jmp0 o⟩ : NextL S) region g2 = some (nb, g3))) ∧
      runLCH (S := S) (Map := Map) env snd true sup v (CGoalL.next (ofSure d) nb.th) region g3 = some (nexDon, g4) ∧
      copyL ⟨nb.laz, nexDon.th⟩ nexDon.laz g4 = some (nex, g1) := by
  obtain ⟨don, rec, o, g2, nexR, g3, nexDon, g4, nexDon', g5, nexRec, g6, h2, h3, h4, h5, h6, h7⟩ :=
    runLCH_n10_next h
  rw [intoL_mk, map_apply] at h2
  obtain ⟨⟨⟨d, r, o'⟩, g2'⟩, hs2, e2⟩ := Option.map_eq_some_iff.mp h2
  simp only [Prod.mk.injEq] at e2
  obtain ⟨⟨e2a, e2b, e2c⟩, e2d⟩ := e2
  subst e2a e2b e2c e2d
  rw [pastL_pure _ _ (show (Nomm.n0 1).pure = true from rfl), pure_apply] at h5
  simp only [Option.some.injEq, Prod.mk.injEq] at h5
  obtain ⟨rfl, rfl⟩ := h5
  obtain ⟨rfl, rfl⟩ := runLCH_n0_one h6
  refine ⟨d, r, o', g2', nexR, g3, _, _, hs2, ?_, h4, h7⟩
  by_cases hr : r.ned = Need.none ∧ HoonSet.small r.lok = true
  · left
    unfold pastL at h3
    rw [if_pos ⟨hr.1, hr.2, rfl⟩, pure_apply] at h3
    simp only [Option.some.injEq, Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl⟩ := h3
    exact ⟨hr.1, hr.2, rfl, rfl⟩
  · right
    rw [pastL_park env.cod hv r (jmp0 o') region hr rfl] at h3
    exact ⟨hr, h3⟩

end Comp
end SkaModel
end Formalization
