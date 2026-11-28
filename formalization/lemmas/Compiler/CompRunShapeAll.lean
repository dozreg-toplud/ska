import lemmas.Compiler.CompRunShapeECases

/-!
# `+run-shape`: the induction on `RsAtE` with both `%2`s and `%6` under `%done` / `%pick` (track A, 2026-11-28)

The cases of `CompRunShapeECases.lean` (on `RsAtE`: the rests `y` of `gen` of a property `E`), the
direct `%2` (`rs_n2dW`) and `[0 a]`, `[1 k]` (lifted by `rsAtE_of`) by induction:

* `RsClsE`: the nomms built of `[0 a]`, `[1 k]`, `[2 p q ~]`, `[2 p q [~ b k]]`, `[3 p]`, `[4 p]`,
  `[5 p q]`, `[7 p q]`, cons, `[10 [a v] q]`: linked on every goal of `GoalNZ`.
* `RsTailE`: those, and `[6 p q r]` where it gets `%done` or `%pick` (the goal of `q` of `[7 p q]`,
  of the branches and of the test of a `%6` under `%done` / `%pick`): linked on `%done` and `%pick`.
  (`%6` under `[%next laz]`, `sixShape`, is not linked yet.)
* `ShapeOK ctx env E sup n`: `ShapeCall` at every rest of `E`, for every direct call of `n` with the
  `sup` it is run under (`[7 p q]` runs `q` under `[~ p]`).
* `runShape_nzE`, `runShape_nzT`: the runs keep `LzNZ`.
* **`rs_clsE`**, **`rs_tailE`**, **`rs_doneE`** (the sweeps' call under `[%done ~]`, `sup` `~`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun}

/-- The nomms linked on every goal of `GoalNZ`. -/
def RsClsE : Nomm → Prop
  | Nomm.n0 _ => True
  | Nomm.n1 _ => True
  | Nomm.n3 p => RsClsE p
  | Nomm.n4 p => RsClsE p
  | Nomm.n7 p q => RsClsE p ∧ RsClsE q
  | Nomm.cons p q => RsClsE p ∧ RsClsE q
  | Nomm.n5 p q => RsClsE p ∧ RsClsE q
  | Nomm.n10 _ v q => RsClsE v ∧ RsClsE q
  | Nomm.n2 p q _ => RsClsE p ∧ RsClsE q
  | _ => False

/-- The nomms linked on `%done` and `%pick`: `RsClsE`, and `%6` where it gets `%done` / `%pick`. -/
def RsTailE : Nomm → Prop
  | Nomm.n6 p q r => RsTailE p ∧ RsTailE q ∧ RsTailE r
  | Nomm.n7 p q => RsClsE p ∧ RsTailE q
  | Nomm.cons p q => RsClsE (Nomm.cons p q)
  | Nomm.n0 a => RsClsE (Nomm.n0 a)
  | Nomm.n1 k => RsClsE (Nomm.n1 k)
  | Nomm.n2 p q i => RsClsE (Nomm.n2 p q i)
  | Nomm.n3 p => RsClsE (Nomm.n3 p)
  | Nomm.n4 p => RsClsE (Nomm.n4 p)
  | Nomm.n5 p q => RsClsE (Nomm.n5 p q)
  | Nomm.n10 a v q => RsClsE (Nomm.n10 a v q)
  | _ => False

/-- **What the direct calls read of the door** (`ShapeCall`) at every rest of `E`, for every direct
call of `n`, with the `sup` it runs under. -/
def ShapeOK (ctx : Noun) (env : ShapeEnv) (E : RsRest → Prop) : Option Nomm → Nomm → Prop
  | sup, Nomm.n2 p q (some (b, k)) =>
    (∀ y, E y → ShapeCall ctx env p q b k sup y) ∧ ShapeOK ctx env E sup p ∧ ShapeOK ctx env E sup q
  | sup, Nomm.n2 p q Option.none => ShapeOK ctx env E sup p ∧ ShapeOK ctx env E sup q
  | sup, Nomm.n7 p q => ShapeOK ctx env E sup p ∧ ShapeOK ctx env E (some p) q
  | sup, Nomm.n6 p q r => ShapeOK ctx env E sup p ∧ ShapeOK ctx env E sup q ∧ ShapeOK ctx env E sup r
  | sup, Nomm.n3 p => ShapeOK ctx env E sup p
  | sup, Nomm.n4 p => ShapeOK ctx env E sup p
  | sup, Nomm.cons p q => ShapeOK ctx env E sup p ∧ ShapeOK ctx env E sup q
  | sup, Nomm.n5 p q => ShapeOK ctx env E sup p ∧ ShapeOK ctx env E sup q
  | sup, Nomm.n10 _ v q => ShapeOK ctx env E sup v ∧ ShapeOK ctx env E sup q
  | _, _ => True

theorem goalNZ_of {goal : GoalS CSet} (h : goal = GoalS.done ∨ goal = GoalS.pick) : GoalNZ goal := by
  rcases h with rfl | rfl <;> trivial

/-- **What a run of `RsClsE` returns looks at no axis `0`** when its goal does not. -/
theorem runShape_nzE (env : ShapeEnv) : ∀ (n : Nomm), RsClsE n → ∀ sup (goal : GoalS CSet) st l st1,
    GoalNZ goal → runShape env sup n goal st = some (l, st1) → LzNZ l
  | Nomm.n0 a, _, sup, goal, st, l, st1, hg, e => runShape_nz env (Nomm.n0 a) trivial sup goal st l st1 hg e
  | Nomm.n1 k, _, sup, goal, st, l, st1, hg, e => runShape_nz env (Nomm.n1 k) trivial sup goal st l st1 hg e
  | Nomm.n3 p, hp, sup, goal, st, l, st1, hg, e => by
    cases goal with
    | next l0 =>
      by_cases hn : noneEq l0 = true
      · simp only [runShape, hn, if_true] at e; exact runShape_nzE env p hp sup _ st l st1 hg e
      · simp only [runShape, hn] at e
        exact runShape_nzE env p hp sup (GoalS.next thisL) st l st1 lzNZ_thisL e
    | pick =>
      simp only [runShape] at e; exact runShape_nzE env p hp sup (GoalS.next thisL) st l st1 lzNZ_thisL e
    | done =>
      simp only [runShape] at e; exact runShape_nzE env p hp sup (GoalS.next thisL) st l st1 lzNZ_thisL e
  | Nomm.n4 p, hp, sup, goal, st, l, st1, hg, e => by
    simp only [runShape] at e
    exact runShape_nzE env p hp sup (GoalS.next thisL) st l st1 lzNZ_thisL e
  | Nomm.n7 p q, ⟨hp, hq⟩, sup, goal, st, l, st1, hg, e => by
    simp only [runShape, bind, StateT.bind] at e
    cases e1 : runShape env (some p) q goal st with
    | none => rw [e1] at e; cases e
    | some r =>
      obtain ⟨l1, st2⟩ := r
      rw [e1] at e
      exact runShape_nzE env p hp sup (GoalS.next l1) st2 l st1
        (runShape_nzE env q hq (some p) goal st l1 st2 hg e1) e
  | Nomm.cons p q, ⟨hp, hq⟩, sup, goal, st, l, st1, hg, e => by
    have hrp : ∀ g st l st1, GoalNZ g → runShape env sup p g st = some (l, st1) → LzNZ l :=
      fun g st l st1 hg e => runShape_nzE env p hp sup g st l st1 hg e
    have hrq : ∀ g st l st1, GoalNZ g → runShape env sup q g st = some (l, st1) → LzNZ l :=
      fun g st l st1 hg e => runShape_nzE env q hq sup g st l st1 hg e
    cases goal with
    | next laz =>
      simp only [runShape] at e; exact consNext_nz env _ _ p q hrp hrq laz hg st l st1 e
    | done =>
      simp only [runShape] at e; exact consNext_nz env _ _ p q hrp hrq thisL lzNZ_thisL st l st1 e
    | pick =>
      simp only [runShape] at e
      obtain ⟨l2, s1, e1, e⟩ := sm_bind_some e
      obtain ⟨l2', s2, e2, e⟩ := sm_bind_some e
      obtain ⟨l1, s3, e3, e⟩ := sm_bind_some e
      have h2 := hrq (GoalS.next noneL) _ _ _ lzNZ_noneL e1
      exact lazeCopyEnd_nz (hrp (GoalS.next noneL) _ _ _ lzNZ_noneL e3) (lazePast_nz env l2 p _ l2' s2 h2 e2) e
  | Nomm.n10 a v q, ⟨hv, hq⟩, sup, goal, st, l, st1, hg, e =>
    tenNz env a v q sup goal hg
      (fun g st l st1 hg e => runShape_nzE env v hv sup g st l st1 hg e)
      (fun g st l st1 hg e => runShape_nzE env q hq sup g st l st1 hg e) st l st1 e
  | Nomm.n5 p q, ⟨hp, hq⟩, sup, goal, st, l, st1, hg, e => by
    simp only [runShape] at e
    obtain ⟨l2, s1, e1, e⟩ := sm_bind_some e
    obtain ⟨l2', s2, e2, e⟩ := sm_bind_some e
    obtain ⟨l1, s3, e3, e⟩ := sm_bind_some e
    have h2 := runShape_nzE env q hq sup (GoalS.next thisL) _ _ _ lzNZ_thisL e1
    exact lazeCopyEnd_nz (runShape_nzE env p hp sup (GoalS.next thisL) _ _ _ lzNZ_thisL e3)
      (lazePast_nz env l2 p _ l2' s2 h2 e2) e
  | Nomm.n2 p q Option.none, ⟨hp, hq⟩, sup, goal, st, l, st1, hg, e => by
    simp only [runShape] at e
    obtain ⟨l2, s1, e1, e⟩ := sm_bind_some e
    obtain ⟨l2', s2, e2, e⟩ := sm_bind_some e
    obtain ⟨l1, s3, e3, e⟩ := sm_bind_some e
    have h2 := runShape_nzE env q hq sup (GoalS.next thisL) _ _ _ lzNZ_thisL e1
    exact lazeCopyEnd_nz (runShape_nzE env p hp sup (GoalS.next thisL) _ _ _ lzNZ_thisL e3)
      (lazePast_nz env l2 p _ l2' s2 h2 e2) e
  | Nomm.n2 p q (some (b, k)), ⟨hp, hq⟩, sup, goal, st, l, st1, hg, e =>
    twoNz env p q b k sup goal
      (fun g st l st1 hg e => runShape_nzE env p hp sup g st l st1 hg e)
      (fun g st l st1 hg e => runShape_nzE env q hq sup g st l st1 hg e) st l st1 e

/-- **What a run of `RsTailE` under `%done` or `%pick` returns looks at no axis `0`.** -/
theorem runShape_nzT (env : ShapeEnv) : ∀ (n : Nomm), RsTailE n → ∀ sup (goal : GoalS CSet) st l st1,
    (goal = GoalS.done ∨ goal = GoalS.pick) → runShape env sup n goal st = some (l, st1) → LzNZ l
  | Nomm.n6 p q r, ⟨hp, hq, hr⟩, sup, goal, st, l, st1, hnn, e =>
    runShape_n6DP_nz env sup p q r goal hnn
      (fun st l st1 e => runShape_nzT env p hp sup GoalS.pick st l st1 (Or.inr rfl) e)
      (fun st l st1 e => runShape_nzT env q hq sup goal st l st1 hnn e)
      (fun st l st1 e => runShape_nzT env r hr sup goal st l st1 hnn e) st l st1 e
  | Nomm.n7 p q, ⟨hp, hq⟩, sup, goal, st, l, st1, hnn, e => by
    simp only [runShape, bind, StateT.bind] at e
    cases e1 : runShape env (some p) q goal st with
    | none => rw [e1] at e; cases e
    | some r =>
      obtain ⟨l1, st2⟩ := r
      rw [e1] at e
      exact runShape_nzE env p hp sup (GoalS.next l1) st2 l st1
        (runShape_nzT env q hq (some p) goal st l1 st2 hnn e1) e
  | Nomm.cons p q, h, sup, goal, st, l, st1, hnn, e => runShape_nzE env _ h sup goal st l st1 (goalNZ_of hnn) e
  | Nomm.n0 a, h, sup, goal, st, l, st1, hnn, e => runShape_nzE env _ h sup goal st l st1 (goalNZ_of hnn) e
  | Nomm.n1 k, h, sup, goal, st, l, st1, hnn, e => runShape_nzE env _ h sup goal st l st1 (goalNZ_of hnn) e
  | Nomm.n2 p q i, h, sup, goal, st, l, st1, hnn, e => runShape_nzE env _ h sup goal st l st1 (goalNZ_of hnn) e
  | Nomm.n3 p, h, sup, goal, st, l, st1, hnn, e => runShape_nzE env _ h sup goal st l st1 (goalNZ_of hnn) e
  | Nomm.n4 p, h, sup, goal, st, l, st1, hnn, e => runShape_nzE env _ h sup goal st l st1 (goalNZ_of hnn) e
  | Nomm.n5 p q, h, sup, goal, st, l, st1, hnn, e => runShape_nzE env _ h sup goal st l st1 (goalNZ_of hnn) e
  | Nomm.n10 a v q, h, sup, goal, st, l, st1, hnn, e => runShape_nzE env _ h sup goal st l st1 (goalNZ_of hnn) e

section
variable (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
  (env : ShapeEnv) (hcn : CodeNomms env.cod cod) (E : RsRest → Prop)
include hc h7 hcode hcn

/-- **The induction on `RsAtE`**: on every nomm of `RsClsE` whose direct calls are in the code table
(`CallCode`) and read the door as `ShapeCall` says at the rests of `E` (`ShapeOK`), every `sup`, state
and goal of `GoalNZ`, the gate of `+run-shape` is `runShape` at every rest of `E`. -/
theorem rs_clsE : ∀ (n : Nomm), RsClsE n → CallCode cod (shapeCE env) n → ∀ sup, ShapeOK ctx env E sup n →
    ∀ goal st, GoalNZ goal → RsAtE ctx env E n sup goal st
  | Nomm.n0 a, _, _, sup, _, goal, st, hg => rsAtE_of (rs_n0W hc env a sup goal st hg)
  | Nomm.n1 k, _, _, sup, _, goal, st, _ => rsAtE_of (rs_n1 env k sup goal st)
  | Nomm.n3 p, hp, hcc, sup, hs, goal, st, hg =>
    rs_n3E hc env p sup goal st (rs_clsE p hp hcc sup hs goal st hg)
      (rs_clsE p hp hcc sup hs (GoalS.next thisL) st lzNZ_thisL)
  | Nomm.n4 p, hp, hcc, sup, hs, goal, st, _ =>
    rs_n4E env p sup goal st (rs_clsE p hp hcc sup hs (GoalS.next thisL) st lzNZ_thisL)
  | Nomm.n7 p q, ⟨hp, hq⟩, ⟨hcp, hcq⟩, sup, ⟨hsp, hsq⟩, goal, st, hg =>
    rs_n7E env p q sup goal st (rs_clsE q hq hcq (some p) hsq goal st hg)
      (fun l st1 e => rs_clsE p hp hcp sup hsp (GoalS.next l) st1
        (runShape_nzE env q hq (some p) goal st l st1 hg e))
  | Nomm.cons p q, ⟨hp, hq⟩, ⟨hcp, hcq⟩, sup, ⟨hsp, hsq⟩, goal, st, hg =>
    rs_consE hc h7 hcode env p q sup goal hg st hcp hcq
      (fun l st1 hl => rs_clsE q hq hcq sup hsq (GoalS.next l) st1 hl)
      (fun l st1 hl => rs_clsE p hp hcp sup hsp (GoalS.next l) st1 hl)
  | Nomm.n10 a v q, ⟨hv, hq⟩, ⟨hcv, hcq⟩, sup, ⟨hsv, hsq⟩, goal, st, hg =>
    rs_n10E hc h7 hcode env a v q sup goal hg st hcv hcq
      (fun l st1 hl => rs_clsE q hq hcq sup hsq (GoalS.next l) st1 hl)
      (fun l st1 hl => rs_clsE v hv hcv sup hsv (GoalS.next l) st1 hl)
  | Nomm.n5 p q, ⟨hp, hq⟩, ⟨hcp, hcq⟩, sup, ⟨hsp, hsq⟩, goal, st, _ =>
    rs_n5E hc h7 hcode env p q sup goal st hcp
      (fun st1 => rs_clsE q hq hcq sup hsq (GoalS.next thisL) st1 lzNZ_thisL)
      (fun st1 => rs_clsE p hp hcp sup hsp (GoalS.next thisL) st1 lzNZ_thisL)
  | Nomm.n2 p q Option.none, ⟨hp, hq⟩, ⟨_, hcp, hcq⟩, sup, ⟨hsp, hsq⟩, goal, st, _ =>
    rs_n2iE hc h7 hcode env p q sup goal st hcp
      (fun st1 => rs_clsE q hq hcq sup hsq (GoalS.next thisL) st1 lzNZ_thisL)
      (fun st1 => rs_clsE p hp hcp sup hsp (GoalS.next thisL) st1 lzNZ_thisL)
  | Nomm.n2 p q (some (b, k)), ⟨hp, hq⟩, hcc, sup, ⟨hsc, hsp, hsq⟩, goal, st, _ =>
    rs_n2dW hc h7 hcode env hcn p q b k sup goal st E hcc hsc
      (fun l st1 hl => rs_clsE q hq hcc.2.2 sup hsq (GoalS.next l) st1 hl)
      (fun l st1 hl => rs_clsE p hp hcc.2.1 sup hsp (GoalS.next l) st1 hl)

/-- **The induction on `%done` and `%pick`**: `rs_clsE`, and `%6` under those goals. -/
theorem rs_tailE : ∀ (n : Nomm), RsTailE n → CallCode cod (shapeCE env) n → ∀ sup, ShapeOK ctx env E sup n →
    ∀ (goal : GoalS CSet) st, (goal = GoalS.done ∨ goal = GoalS.pick) → RsAtE ctx env E n sup goal st
  | Nomm.n6 p q r, ⟨hp, hq, hr⟩, ⟨hcp, hcq, hcr⟩, sup, ⟨hsp, hsq, hsr⟩, goal, st, hnn =>
    rs_n6DPE hc h7 hcode env p q r sup goal hnn st hcp
      (fun st1 => rs_tailE r hr hcr sup hsr goal st1 hnn)
      (fun st1 => rs_tailE q hq hcq sup hsq goal st1 hnn)
      (fun st1 => rs_tailE p hp hcp sup hsp GoalS.pick st1 (Or.inr rfl))
  | Nomm.n7 p q, ⟨hp, hq⟩, ⟨hcp, hcq⟩, sup, ⟨hsp, hsq⟩, goal, st, hnn =>
    rs_n7E env p q sup goal st (rs_tailE q hq hcq (some p) hsq goal st hnn)
      (fun l st1 e => rs_clsE hc h7 hcode env hcn E p hp hcp sup hsp (GoalS.next l) st1
        (runShape_nzT env q hq (some p) goal st l st1 hnn e))
  | Nomm.cons p q, h, hcc, sup, hs, goal, st, hnn => rs_clsE hc h7 hcode env hcn E _ h hcc sup hs goal st (goalNZ_of hnn)
  | Nomm.n0 a, h, hcc, sup, hs, goal, st, hnn => rs_clsE hc h7 hcode env hcn E _ h hcc sup hs goal st (goalNZ_of hnn)
  | Nomm.n1 k, h, hcc, sup, hs, goal, st, hnn => rs_clsE hc h7 hcode env hcn E _ h hcc sup hs goal st (goalNZ_of hnn)
  | Nomm.n2 p q i, h, hcc, sup, hs, goal, st, hnn => rs_clsE hc h7 hcode env hcn E _ h hcc sup hs goal st (goalNZ_of hnn)
  | Nomm.n3 p, h, hcc, sup, hs, goal, st, hnn => rs_clsE hc h7 hcode env hcn E _ h hcc sup hs goal st (goalNZ_of hnn)
  | Nomm.n4 p, h, hcc, sup, hs, goal, st, hnn => rs_clsE hc h7 hcode env hcn E _ h hcc sup hs goal st (goalNZ_of hnn)
  | Nomm.n5 p q, h, hcc, sup, hs, goal, st, hnn => rs_clsE hc h7 hcode env hcn E _ h hcc sup hs goal st (goalNZ_of hnn)
  | Nomm.n10 a v q, h, hcc, sup, hs, goal, st, hnn =>
    rs_clsE hc h7 hcode env hcn E _ h hcc sup hs goal st (goalNZ_of hnn)

/-- **For track I**: the sweeps' call `(~(run-shape comp gen) nomm [%done ~] ~)` on every nomm of
`RsTailE` whose direct calls are in the code table and read the door as `ShapeCall` says at the
rests of `E`, from every state, at every rest of `E`, is `runShape env none nomm GoalS.done`. -/
theorem rs_doneE (n : Nomm) (hn : RsTailE n) (hcc : CallCode cod (shapeCE env) n)
    (hs : ShapeOK ctx env E Option.none n) (st : RSt CSet) (y : RsRest) (hy : E y) :
    nock (rsCoreG n.toNoun (GoalS.done : GoalS CSet).toNoun (A 0) (rsDoor st y ctx)) rsGate
      = (runShape env Option.none n GoalS.done st).map fun p => C p.1.toNoun (rsGenNoun p.2 y) :=
  rs_tailE hc h7 hcode env hcn E n hn hcc Option.none hs GoalS.done st (Or.inl rfl) y hy

end

end Compiler
end Formalization
