import lemmas.Compiler.CompRunShapeAll
import lemmas.Compiler.CompRunShapeSixN

/-!
# `+run-shape`: the induction with `%6` on every goal (track A, 2026-11-28)

`RsClsE6 env`: the nomms of `RsClsE` and `[6 p q r]` on every goal, where the branches have no
`%10` at axis `0` (`Bake.NoAx0`, for `+laze-leaps`), `!&((sound q ned) (sound r ned))` returns on
every need (for `+laze-soft-fork`), and the fuel `sixFuel` covers the runs on the same nomm from every
`laz` of `LzNZ` (`SixDeep`; `sixDeep_of_idem`).  `%6` under `[%next laz]` is `rs_n6NE`, under `%done`
and `%pick` `rs_n6DPE`.

* `runShape_nzE6`, **`rs_clsE6`**, **`rs_doneE6`** (the sweeps' call under `[%done ~]`, `sup` `~`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun}

/-- The nomms linked on every goal of `GoalNZ`, with `%6`. -/
def RsClsE6 (env : ShapeEnv) : Nomm → Prop
  | Nomm.n0 _ => True
  | Nomm.n1 _ => True
  | Nomm.n3 p => RsClsE6 env p
  | Nomm.n4 p => RsClsE6 env p
  | Nomm.n7 p q => RsClsE6 env p ∧ RsClsE6 env q
  | Nomm.cons p q => RsClsE6 env p ∧ RsClsE6 env q
  | Nomm.n5 p q => RsClsE6 env p ∧ RsClsE6 env q
  | Nomm.n10 _ v q => RsClsE6 env v ∧ RsClsE6 env q
  | Nomm.n2 p q _ => RsClsE6 env p ∧ RsClsE6 env q
  | Nomm.n6 p q r => RsClsE6 env p ∧ RsClsE6 env q ∧ RsClsE6 env r ∧ Bake.NoAx0 q ∧ Bake.NoAx0 r ∧
      (∀ ned, unsS env q r ned ≠ Option.none) ∧ (∀ laz, LzNZ laz → SixDeep q r sixFuel laz)
  | _ => False

theorem runShape_nzE6 (env : ShapeEnv) : ∀ (n : Nomm), RsClsE6 env n → ∀ sup (goal : GoalS CSet) st l st1,
    GoalNZ goal → runShape env sup n goal st = some (l, st1) → LzNZ l
  | Nomm.n0 a, _, sup, goal, st, l, st1, hg, e => runShape_nz env (Nomm.n0 a) trivial sup goal st l st1 hg e
  | Nomm.n1 k, _, sup, goal, st, l, st1, hg, e => runShape_nz env (Nomm.n1 k) trivial sup goal st l st1 hg e
  | Nomm.n3 p, hp, sup, goal, st, l, st1, hg, e => by
    cases goal with
    | next l0 =>
      by_cases hn : noneEq l0 = true
      · simp only [runShape, hn, if_true] at e; exact runShape_nzE6 env p hp sup _ st l st1 hg e
      · simp only [runShape, hn] at e
        exact runShape_nzE6 env p hp sup (GoalS.next thisL) st l st1 lzNZ_thisL e
    | pick =>
      simp only [runShape] at e; exact runShape_nzE6 env p hp sup (GoalS.next thisL) st l st1 lzNZ_thisL e
    | done =>
      simp only [runShape] at e; exact runShape_nzE6 env p hp sup (GoalS.next thisL) st l st1 lzNZ_thisL e
  | Nomm.n4 p, hp, sup, goal, st, l, st1, hg, e => by
    simp only [runShape] at e
    exact runShape_nzE6 env p hp sup (GoalS.next thisL) st l st1 lzNZ_thisL e
  | Nomm.n7 p q, ⟨hp, hq⟩, sup, goal, st, l, st1, hg, e => by
    simp only [runShape, bind, StateT.bind] at e
    cases e1 : runShape env (some p) q goal st with
    | none => rw [e1] at e; cases e
    | some r =>
      obtain ⟨l1, st2⟩ := r
      rw [e1] at e
      exact runShape_nzE6 env p hp sup (GoalS.next l1) st2 l st1
        (runShape_nzE6 env q hq (some p) goal st l1 st2 hg e1) e
  | Nomm.cons p q, ⟨hp, hq⟩, sup, goal, st, l, st1, hg, e => by
    have hrp : ∀ g st l st1, GoalNZ g → runShape env sup p g st = some (l, st1) → LzNZ l :=
      fun g st l st1 hg e => runShape_nzE6 env p hp sup g st l st1 hg e
    have hrq : ∀ g st l st1, GoalNZ g → runShape env sup q g st = some (l, st1) → LzNZ l :=
      fun g st l st1 hg e => runShape_nzE6 env q hq sup g st l st1 hg e
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
      (fun g st l st1 hg e => runShape_nzE6 env v hv sup g st l st1 hg e)
      (fun g st l st1 hg e => runShape_nzE6 env q hq sup g st l st1 hg e) st l st1 e
  | Nomm.n5 p q, ⟨hp, hq⟩, sup, goal, st, l, st1, hg, e => by
    simp only [runShape] at e
    obtain ⟨l2, s1, e1, e⟩ := sm_bind_some e
    obtain ⟨l2', s2, e2, e⟩ := sm_bind_some e
    obtain ⟨l1, s3, e3, e⟩ := sm_bind_some e
    have h2 := runShape_nzE6 env q hq sup (GoalS.next thisL) _ _ _ lzNZ_thisL e1
    exact lazeCopyEnd_nz (runShape_nzE6 env p hp sup (GoalS.next thisL) _ _ _ lzNZ_thisL e3)
      (lazePast_nz env l2 p _ l2' s2 h2 e2) e
  | Nomm.n2 p q Option.none, ⟨hp, hq⟩, sup, goal, st, l, st1, hg, e => by
    simp only [runShape] at e
    obtain ⟨l2, s1, e1, e⟩ := sm_bind_some e
    obtain ⟨l2', s2, e2, e⟩ := sm_bind_some e
    obtain ⟨l1, s3, e3, e⟩ := sm_bind_some e
    have h2 := runShape_nzE6 env q hq sup (GoalS.next thisL) _ _ _ lzNZ_thisL e1
    exact lazeCopyEnd_nz (runShape_nzE6 env p hp sup (GoalS.next thisL) _ _ _ lzNZ_thisL e3)
      (lazePast_nz env l2 p _ l2' s2 h2 e2) e
  | Nomm.n2 p q (some (b, k)), ⟨hp, hq⟩, sup, goal, st, l, st1, hg, e =>
    twoNz env p q b k sup goal
      (fun g st l st1 hg e => runShape_nzE6 env p hp sup g st l st1 hg e)
      (fun g st l st1 hg e => runShape_nzE6 env q hq sup g st l st1 hg e) st l st1 e
  | Nomm.n6 p q r, ⟨hp, hq, hr, hq0, hr0, _, _⟩, sup, goal, st, l, st1, hg, e => by
    have hrp : ∀ g st l st1, GoalNZ g → runShape env sup p g st = some (l, st1) → LzNZ l :=
      fun g st l st1 hg e => runShape_nzE6 env p hp sup g st l st1 hg e
    have hrq : ∀ g st l st1, GoalNZ g → runShape env sup q g st = some (l, st1) → LzNZ l :=
      fun g st l st1 hg e => runShape_nzE6 env q hq sup g st l st1 hg e
    have hrr : ∀ g st l st1, GoalNZ g → runShape env sup r g st = some (l, st1) → LzNZ l :=
      fun g st l st1 hg e => runShape_nzE6 env r hr sup g st l st1 hg e
    cases goal with
    | next laz =>
      exact sixShape_nz env _ _ _ p q r hq0 hr0 hrp hrq hrr sixFuel laz st l st1 hg e
    | done =>
      exact runShape_n6DP_nz env sup p q r GoalS.done (Or.inl rfl) (fun st l st1 e => hrp GoalS.pick st l st1 trivial e)
        (fun st l st1 e => hrq GoalS.done st l st1 trivial e) (fun st l st1 e => hrr GoalS.done st l st1 trivial e) st l st1 e
    | pick =>
      exact runShape_n6DP_nz env sup p q r GoalS.pick (Or.inr rfl) (fun st l st1 e => hrp GoalS.pick st l st1 trivial e)
        (fun st l st1 e => hrq GoalS.pick st l st1 trivial e) (fun st l st1 e => hrr GoalS.pick st l st1 trivial e) st l st1 e

section
variable (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
  (env : ShapeEnv) (hcn : CodeNomms env.cod cod) (E : RsRest → Prop)
include hc h7 hcode hcn

/-- **The induction on `RsAtE` with `%6`**: `rs_clsE` and `%6` on every goal of `GoalNZ`. -/
theorem rs_clsE6 : ∀ (n : Nomm), RsClsE6 env n → CallCode cod (shapeCE env) n → ∀ sup, ShapeOK ctx env E sup n →
    ∀ goal st, GoalNZ goal → RsAtE ctx env E n sup goal st
  | Nomm.n0 a, _, _, sup, _, goal, st, hg => rsAtE_of (rs_n0W hc env a sup goal st hg)
  | Nomm.n1 k, _, _, sup, _, goal, st, _ => rsAtE_of (rs_n1 env k sup goal st)
  | Nomm.n3 p, hp, hcc, sup, hs, goal, st, hg =>
    rs_n3E hc env p sup goal st (rs_clsE6 p hp hcc sup hs goal st hg)
      (rs_clsE6 p hp hcc sup hs (GoalS.next thisL) st lzNZ_thisL)
  | Nomm.n4 p, hp, hcc, sup, hs, goal, st, _ =>
    rs_n4E env p sup goal st (rs_clsE6 p hp hcc sup hs (GoalS.next thisL) st lzNZ_thisL)
  | Nomm.n7 p q, ⟨hp, hq⟩, ⟨hcp, hcq⟩, sup, ⟨hsp, hsq⟩, goal, st, hg =>
    rs_n7E env p q sup goal st (rs_clsE6 q hq hcq (some p) hsq goal st hg)
      (fun l st1 e => rs_clsE6 p hp hcp sup hsp (GoalS.next l) st1
        (runShape_nzE6 env q hq (some p) goal st l st1 hg e))
  | Nomm.cons p q, ⟨hp, hq⟩, ⟨hcp, hcq⟩, sup, ⟨hsp, hsq⟩, goal, st, hg =>
    rs_consE hc h7 hcode env p q sup goal hg st hcp hcq
      (fun l st1 hl => rs_clsE6 q hq hcq sup hsq (GoalS.next l) st1 hl)
      (fun l st1 hl => rs_clsE6 p hp hcp sup hsp (GoalS.next l) st1 hl)
  | Nomm.n10 a v q, ⟨hv, hq⟩, ⟨hcv, hcq⟩, sup, ⟨hsv, hsq⟩, goal, st, hg =>
    rs_n10E hc h7 hcode env a v q sup goal hg st hcv hcq
      (fun l st1 hl => rs_clsE6 q hq hcq sup hsq (GoalS.next l) st1 hl)
      (fun l st1 hl => rs_clsE6 v hv hcv sup hsv (GoalS.next l) st1 hl)
  | Nomm.n5 p q, ⟨hp, hq⟩, ⟨hcp, hcq⟩, sup, ⟨hsp, hsq⟩, goal, st, _ =>
    rs_n5E hc h7 hcode env p q sup goal st hcp
      (fun st1 => rs_clsE6 q hq hcq sup hsq (GoalS.next thisL) st1 lzNZ_thisL)
      (fun st1 => rs_clsE6 p hp hcp sup hsp (GoalS.next thisL) st1 lzNZ_thisL)
  | Nomm.n2 p q Option.none, ⟨hp, hq⟩, ⟨_, hcp, hcq⟩, sup, ⟨hsp, hsq⟩, goal, st, _ =>
    rs_n2iE hc h7 hcode env p q sup goal st hcp
      (fun st1 => rs_clsE6 q hq hcq sup hsq (GoalS.next thisL) st1 lzNZ_thisL)
      (fun st1 => rs_clsE6 p hp hcp sup hsp (GoalS.next thisL) st1 lzNZ_thisL)
  | Nomm.n2 p q (some (b, k)), ⟨hp, hq⟩, hcc, sup, ⟨hsc, hsp, hsq⟩, goal, st, _ =>
    rs_n2dW hc h7 hcode env hcn p q b k sup goal st E hcc hsc
      (fun l st1 hl => rs_clsE6 q hq hcc.2.2 sup hsq (GoalS.next l) st1 hl)
      (fun l st1 hl => rs_clsE6 p hp hcc.2.1 sup hsp (GoalS.next l) st1 hl)
  | Nomm.n6 p q r, ⟨hp, hq, hr, hq0, hr0, hun, hdeep⟩, ⟨hcp, hcq, hcr⟩, sup, ⟨hsp, hsq, hsr⟩, goal, st, hg => by
    cases goal with
    | next laz =>
      exact rs_n6NE hc h7 hcode env hcn p q r sup laz hg st hcp hq0 hr0 hun (hdeep laz hg)
        (fun g st1 hg1 => rs_clsE6 r hr hcr sup hsr g st1 hg1)
        (fun g st1 hg1 => rs_clsE6 q hq hcq sup hsq g st1 hg1)
        (fun g st1 hg1 => rs_clsE6 p hp hcp sup hsp g st1 hg1)
    | done =>
      exact rs_n6DPE hc h7 hcode env p q r sup GoalS.done (Or.inl rfl) st hcp
        (fun st1 => rs_clsE6 r hr hcr sup hsr GoalS.done st1 trivial)
        (fun st1 => rs_clsE6 q hq hcq sup hsq GoalS.done st1 trivial)
        (fun st1 => rs_clsE6 p hp hcp sup hsp GoalS.pick st1 trivial)
    | pick =>
      exact rs_n6DPE hc h7 hcode env p q r sup GoalS.pick (Or.inr rfl) st hcp
        (fun st1 => rs_clsE6 r hr hcr sup hsr GoalS.pick st1 trivial)
        (fun st1 => rs_clsE6 q hq hcq sup hsq GoalS.pick st1 trivial)
        (fun st1 => rs_clsE6 p hp hcp sup hsp GoalS.pick st1 trivial)

/-- **For track I**: the sweeps' call `(~(run-shape comp gen) nomm [%done ~] ~)` on every nomm of
`RsClsE6 env` whose direct calls are in the code table and read the door as `ShapeCall` says at the
rests of `E`, from every state, at every rest of `E`, is `runShape env none nomm GoalS.done`. -/
theorem rs_doneE6 (n : Nomm) (hn : RsClsE6 env n) (hcc : CallCode cod (shapeCE env) n)
    (hs : ShapeOK ctx env E Option.none n) (st : RSt CSet) (y : RsRest) (hy : E y) :
    nock (rsCoreG n.toNoun (GoalS.done : GoalS CSet).toNoun (A 0) (rsDoor st y ctx)) rsGate
      = (runShape env Option.none n GoalS.done st).map fun p => C p.1.toNoun (rsGenNoun p.2 y) :=
  rs_clsE6 hc h7 hcode env hcn E n hn hcc Option.none hs GoalS.done st trivial y hy

end

end Compiler
end Formalization
