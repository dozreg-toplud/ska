import lemmas.Compiler.CompRunShapeInd
import lemmas.Compiler.CompRunShapeNone

/-!
# `+run-shape`: the case `[3 p]`, and the induction over five cases (track A, 2026-11-27)

`?:  &(?=(%next -.goal) (laze-none-equivalent laz.goal))  $(nomm p.nomm)
$(nomm p.nomm, goal [%next this])`: the run of `p` on the same goal when it is a `%next`
whose `laze` is none-equivalent (`lne_all`), else on `[%next this]`.

* **`rs_n3W`**: the case from the two runs of `p`.
* `RsCls5`: the nomms built of `[0 a]`, `[1 k]`, `[3 p]`, `[4 p]`, `[7 p q]`;
  `runShape_nz5`: the invariant `LzNZ` over them.
* **`rs_cls5`**: on every nomm of `RsCls5`, every `sup`, state and goal of `GoalNZ`, the gate
  of `+run-shape` is `runShape`, under `CompIn ctx` alone.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

theorem rs_disp_n3 (t s goal sup D : Noun) :
    nock (rsS s (C (A 3) t) goal sup D) rsDol = nock (rsS s (C (A 3) t) goal sup D) rsK3 := by
  nock_open rsDol
  simp [nock_exec, rsS, rsCoreG, rsTc, rsT]

/-- **The case `[3 p]`** from the run of `p` on the goal and on `[%next this]`. -/
theorem rs_n3W (hc : CompIn ctx) (env : ShapeEnv) (p : Nomm) (sup : Option Nomm) (goal : GoalS CSet)
    (st : RSt CSet) (hp1 : RsAt ctx env p sup goal st) (hp2 : RsAt ctx env p sup (GoalS.next thisL) st) :
    RsAt ctx env (Nomm.n3 p) sup goal st := by
  intro y
  simp only [Nomm.toNoun]
  rw [rs_push, rs_disp_n3]
  have h1 := hp1 y
  have h2 := hp2 y
  simp only [rsCoreG, rsDoor, GoalS.toNoun, thisL_noun] at h1 h2
  nock_open rsK3
  cases goal with
  | pick =>
    simp only [GoalS.toNoun] at h1
    simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, GoalS.toNoun]
    exact h2
  | done =>
    simp only [GoalS.toNoun] at h1
    simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, GoalS.toNoun]
    exact h2
  | next l =>
    have hl := lne_all hc (rsGenNoun st y) l
    cases e : noneEq l
    · rw [e] at hl
      simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, GoalS.toNoun, lne_at', lneArm, hl, e, loob]
      exact h2
    · rw [e] at hl
      simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, GoalS.toNoun, lne_at', lneArm, hl, e, loob]
      exact h1

/-- The nomms built of the cases linked so far: `[0 a]`, `[1 k]`, `[3 p]`, `[4 p]`, `[7 p q]`. -/
def RsCls5 : Nomm → Prop
  | Nomm.n0 _ => True
  | Nomm.n1 _ => True
  | Nomm.n3 p => RsCls5 p
  | Nomm.n4 p => RsCls5 p
  | Nomm.n7 p q => RsCls5 p ∧ RsCls5 q
  | _ => False

/-- **What a run of `RsCls5` returns looks at no axis `0`** when its goal does not. -/
theorem runShape_nz5 (env : ShapeEnv) : ∀ (n : Nomm), RsCls5 n → ∀ sup (goal : GoalS CSet) st l st1,
    GoalNZ goal → runShape env sup n goal st = some (l, st1) → LzNZ l
  | Nomm.n0 a, _, sup, goal, st, l, st1, hg, e => runShape_nz env (Nomm.n0 a) trivial sup goal st l st1 hg e
  | Nomm.n1 k, _, sup, goal, st, l, st1, hg, e => runShape_nz env (Nomm.n1 k) trivial sup goal st l st1 hg e
  | Nomm.n3 p, hp, sup, goal, st, l, st1, hg, e => by
    cases goal with
    | next l0 =>
      by_cases hn : noneEq l0 = true
      · simp only [runShape, hn, if_true] at e; exact runShape_nz5 env p hp sup _ st l st1 hg e
      · simp only [runShape, hn] at e
        exact runShape_nz5 env p hp sup (GoalS.next thisL) st l st1 lzNZ_thisL e
    | pick =>
      simp only [runShape] at e; exact runShape_nz5 env p hp sup (GoalS.next thisL) st l st1 lzNZ_thisL e
    | done =>
      simp only [runShape] at e; exact runShape_nz5 env p hp sup (GoalS.next thisL) st l st1 lzNZ_thisL e
  | Nomm.n4 p, hp, sup, goal, st, l, st1, hg, e => by
    simp only [runShape] at e
    exact runShape_nz5 env p hp sup (GoalS.next thisL) st l st1 lzNZ_thisL e
  | Nomm.n7 p q, ⟨hp, hq⟩, sup, goal, st, l, st1, hg, e => by
    simp only [runShape, bind, StateT.bind] at e
    cases e1 : runShape env (some p) q goal st with
    | none => rw [e1] at e; cases e
    | some r =>
      obtain ⟨l1, st2⟩ := r
      rw [e1] at e
      exact runShape_nz5 env p hp sup (GoalS.next l1) st2 l st1
        (runShape_nz5 env q hq (some p) goal st l1 st2 hg e1) e

/-- **The induction over the five cases linked so far**: on every nomm of `RsCls5`, every `sup`,
state and goal of `GoalNZ` (`%done` and `%pick` are), the gate of `+run-shape` is `runShape`,
under `CompIn ctx` alone. -/
theorem rs_cls5 (hc : CompIn ctx) (env : ShapeEnv) :
    ∀ (n : Nomm), RsCls5 n → ∀ sup goal st, GoalNZ goal → RsAt ctx env n sup goal st
  | Nomm.n0 a, _, sup, goal, st, hg => rs_n0W hc env a sup goal st hg
  | Nomm.n1 k, _, sup, goal, st, _ => rs_n1 env k sup goal st
  | Nomm.n3 p, hp, sup, goal, st, hg =>
    rs_n3W hc env p sup goal st (rs_cls5 hc env p hp sup goal st hg)
      (rs_cls5 hc env p hp sup (GoalS.next thisL) st lzNZ_thisL)
  | Nomm.n4 p, hp, sup, goal, st, _ =>
    rs_n4 env p sup goal st (rs_cls5 hc env p hp sup (GoalS.next thisL) st lzNZ_thisL)
  | Nomm.n7 p q, ⟨hp, hq⟩, sup, goal, st, hg =>
    rs_n7W env p q sup goal st (rs_cls5 hc env q hq (some p) goal st hg)
      (fun l st1 e => rs_cls5 hc env p hp sup (GoalS.next l) st1
        (runShape_nz5 env q hq (some p) goal st l st1 hg e))

/-- **For track I**: the call `(~(run-shape comp gen) nomm [%done ~] ~)` of the sweeps, on every
nomm of `RsCls5`, from every state, is `runShape env none nomm GoalS.done`. -/
theorem rs_done5 (hc : CompIn ctx) (env : ShapeEnv) (n : Nomm) (hn : RsCls5 n) (st : RSt CSet) (y : RsRest) :
    nock (rsCoreG n.toNoun (GoalS.done : GoalS CSet).toNoun (A 0) (rsDoor st y ctx)) rsGate
      = (runShape env Option.none n GoalS.done st).map fun p => C p.1.toNoun (rsGenNoun p.2 y) :=
  rs_cls5 hc env n hn Option.none GoalS.done st trivial y

end Compiler
end Formalization
