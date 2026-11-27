import lemmas.Compiler.CompRunShapeSeven
import lemmas.Compiler.CompRunShapeInto

/-!
# `+run-shape`: the case `[10 [a v] q]`, and the induction over eight cases (track A, 2026-11-27)

`+laze-into` of the goal's `laze` at `a` (`lzi_all`) gives the donor and the recipient;
`+laze-past` of the recipient over `v`, the run of `v` on the donor, `+laze-past` of its `laze`
over `q`, the run of `q` on the recipient, `+laze-copy` of the two.

* **`rs_n10W`**: the case, from the runs of `v` and `q` on goals of `LzNZ`.
* `tenNz`: the case keeps `LzNZ` (`lazeInto_nz`, `lazePast_nz`, `lazeCopy_nz`).
* `RsCls8`, `runShape_nz8`, **`rs_cls8`**, **`rs_done8`**: `RsCls7` and its lemmas with `%10`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

theorem rs_disp_n10 (t s goal sup D : Noun) :
    nock (rsS s (C (A 10) t) goal sup D) rsDol = nock (rsS s (C (A 10) t) goal sup D) rsK10 := by
  nock_open rsDol
  simp [nock_exec, rsS, rsCoreG, rsTc, rsT]

/-- **The case `[10 [a v] q]` keeps `LzNZ`**, given that its two runs do. -/
theorem tenNz (env : ShapeEnv) (a : Nat) (v q : Nomm) (sup : Option Nomm) (goal : GoalS CSet) (hg : GoalNZ goal)
    (hrv : ∀ g st l st1, GoalNZ g → runShape env sup v g st = some (l, st1) → LzNZ l)
    (hrq : ∀ g st l st1, GoalNZ g → runShape env sup q g st = some (l, st1) → LzNZ l)
    (st : RSt CSet) (l : Laze CSet) (st1 : RSt CSet)
    (e : runShape env sup (Nomm.n10 a v q) goal st = some (l, st1)) : LzNZ l := by
  simp only [runShape] at e
  cases e1 : lazeInto a (simpleS goal) with
  | none => simp [e1, liftS, bind, StateT.bind] at e
  | some dr =>
    obtain ⟨don, rec⟩ := dr
    obtain ⟨dnz, rnz⟩ := lazeInto_nz a (simpleS goal) (simpleS_nz goal hg) don rec e1
    cases e2 : lazePast env rec v st with
    | none => simp [e1, e2, liftS, bind, StateT.bind] at e
    | some r2 =>
      obtain ⟨rec', s2⟩ := r2
      have h1 := lazePast_nz env rec v st rec' s2 rnz e2
      cases e3 : runShape env sup v (GoalS.next don) s2 with
      | none => simp [e1, e2, e3, liftS, bind, StateT.bind] at e
      | some r3 =>
        obtain ⟨ld, s3⟩ := r3
        have h2 := hrv (GoalS.next don) s2 ld s3 dnz e3
        cases e4 : lazePast env ld q s3 with
        | none => simp [e1, e2, e3, e4, liftS, bind, StateT.bind] at e
        | some r4 =>
          obtain ⟨ld', s4⟩ := r4
          have h3 := lazePast_nz env ld q s3 ld' s4 h2 e4
          cases e5 : runShape env sup q (GoalS.next rec') s4 with
          | none => simp [e1, e2, e3, e4, e5, liftS, bind, StateT.bind] at e
          | some r5 =>
            obtain ⟨lr, s5⟩ := r5
            have h4 := hrq (GoalS.next rec') s4 lr s5 h1 e5
            cases e6 : lazeCopy lr ld' with
            | none => simp [e1, e2, e3, e4, e5, e6, liftS, bind, StateT.bind] at e
            | some c =>
              simp [e1, e2, e3, e4, e5, e6, liftS, bind, StateT.bind] at e
              rw [← e.1]; exact lazeCopy_nz lr ld' c h4 h3 e6

section
variable (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
include hc h7 hcode

/-- **The case `[10 [a v] q]`** on every goal of `GoalNZ`. -/
theorem rs_n10W (env : ShapeEnv) (a : Nat) (v q : Nomm) (sup : Option Nomm) (goal : GoalS CSet)
    (hg : GoalNZ goal) (st : RSt CSet) (hcv : CallCode cod (shapeCE env) v) (hcq : CallCode cod (shapeCE env) q)
    (hq : ∀ l st1, LzNZ l → RsAt ctx env q sup (GoalS.next l) st1)
    (hv : ∀ l st1, LzNZ l → RsAt ctx env v sup (GoalS.next l) st1) :
    RsAt ctx env (Nomm.n10 a v q) sup goal st := by
  intro y
  simp only [Nomm.toNoun]
  rw [rs_push, rs_disp_n10]
  have hsi := lzi_all hc h7 (rsGenNoun st y) a (simpleS goal) (simpleS_nz goal hg)
  unfold rsK10
  cases e1 : lazeInto a (simpleS goal) with
  | none =>
    rw [e1] at hsi
    simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, GoalS.toNoun, rsSimpleN, liftS, bind, StateT.bind,
      lzi_at', lzi_arm, hsi, e1]
  | some dr =>
    obtain ⟨don, rec⟩ := dr
    rw [e1] at hsi
    simp only [Option.map_some] at hsi
    obtain ⟨dnz, rnz⟩ := lazeInto_nz a (simpleS goal) (simpleS_nz goal hg) don rec e1
    have hpa1 := lzp_gate h7 hcode env v hcv st y rec
    simp only [rsDoor] at hpa1
    cases e2 : lazePast env rec v st with
    | none =>
      rw [e2] at hpa1
      simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, GoalS.toNoun, rsSimpleN, liftS, bind, StateT.bind,
        lzi_at', lzi_arm, hsi, e1, lzp_at', lzpArm, hpa1, e2]
    | some r2 =>
      obtain ⟨rec', st1⟩ := r2
      rw [e2] at hpa1
      have hv' := hv don st1 dnz y
      simp only [rsCoreG, rsDoor, GoalS.toNoun] at hv'
      cases e3 : runShape env sup v (GoalS.next don) st1 with
      | none =>
        rw [e3] at hv'
        simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, GoalS.toNoun, rsSimpleN, liftS, bind, StateT.bind,
          lzi_at', lzi_arm, hsi, e1, lzp_at', lzpArm, hpa1, e2, hv', e3]
      | some r3 =>
        obtain ⟨ld, st2⟩ := r3
        rw [e3] at hv'
        have hpa2 := lzp_gate h7 hcode env q hcq st2 y ld
        simp only [rsDoor] at hpa2
        cases e4 : lazePast env ld q st2 with
        | none =>
          rw [e4] at hpa2
          simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, GoalS.toNoun, rsSimpleN, liftS, bind, StateT.bind,
            lzi_at', lzi_arm, hsi, e1, lzp_at', lzpArm, hpa1, e2, hv', e3, hpa2, e4]
        | some r4 =>
          obtain ⟨ld', st3⟩ := r4
          rw [e4] at hpa2
          have hq' := hq rec' st3 (lazePast_nz env rec v st rec' st1 rnz e2) y
          simp only [rsCoreG, rsDoor, GoalS.toNoun] at hq'
          cases e5 : runShape env sup q (GoalS.next rec') st3 with
          | none =>
            rw [e5] at hq'
            simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, GoalS.toNoun, rsSimpleN, liftS, bind, StateT.bind,
              lzi_at', lzi_arm, hsi, e1, lzp_at', lzpArm, hpa1, e2, hv', e3, hpa2, e4, hq', e5]
          | some r5 =>
            obtain ⟨lr, st4⟩ := r5
            rw [e5] at hq'
            have hlc := lc_all hc h7 (rsGenNoun st4 y) lr ld'
            cases e6 : lazeCopy lr ld' with
            | none =>
              rw [e6] at hlc
              simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, GoalS.toNoun, rsSimpleN, liftS, bind, StateT.bind,
                lzi_at', lzi_arm, hsi, e1, lzp_at', lzpArm, hpa1, e2, hv', e3, hpa2, e4, hq', e5, lc_at', lc_arm,
                hlc, e6]
            | some l =>
              rw [e6] at hlc
              simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, GoalS.toNoun, rsSimpleN, liftS, bind, StateT.bind,
                lzi_at', lzi_arm, hsi, e1, lzp_at', lzpArm, hpa1, e2, hv', e3, hpa2, e4, hq', e5, lc_at', lc_arm,
                hlc, e6]

end

/-- The nomms built of the cases linked so far: `[0 a]`, `[1 k]`, `[3 p]`, `[4 p]`,
`[7 p q]`, cons, `[5 p q]`, `[10 [a v] q]`. -/
def RsCls8 : Nomm → Prop
  | Nomm.n0 _ => True
  | Nomm.n1 _ => True
  | Nomm.n3 p => RsCls8 p
  | Nomm.n4 p => RsCls8 p
  | Nomm.n7 p q => RsCls8 p ∧ RsCls8 q
  | Nomm.cons p q => RsCls8 p ∧ RsCls8 q
  | Nomm.n5 p q => RsCls8 p ∧ RsCls8 q
  | Nomm.n10 _ v q => RsCls8 v ∧ RsCls8 q
  | _ => False

/-- **What a run of `RsCls8` returns looks at no axis `0`** when its goal does not. -/
theorem runShape_nz8 (env : ShapeEnv) : ∀ (n : Nomm), RsCls8 n → ∀ sup (goal : GoalS CSet) st l st1,
    GoalNZ goal → runShape env sup n goal st = some (l, st1) → LzNZ l
  | Nomm.n0 a, _, sup, goal, st, l, st1, hg, e => runShape_nz env (Nomm.n0 a) trivial sup goal st l st1 hg e
  | Nomm.n1 k, _, sup, goal, st, l, st1, hg, e => runShape_nz env (Nomm.n1 k) trivial sup goal st l st1 hg e
  | Nomm.n3 p, hp, sup, goal, st, l, st1, hg, e => by
    cases goal with
    | next l0 =>
      by_cases hn : noneEq l0 = true
      · simp only [runShape, hn, if_true] at e; exact runShape_nz8 env p hp sup _ st l st1 hg e
      · simp only [runShape, hn] at e
        exact runShape_nz8 env p hp sup (GoalS.next thisL) st l st1 lzNZ_thisL e
    | pick =>
      simp only [runShape] at e; exact runShape_nz8 env p hp sup (GoalS.next thisL) st l st1 lzNZ_thisL e
    | done =>
      simp only [runShape] at e; exact runShape_nz8 env p hp sup (GoalS.next thisL) st l st1 lzNZ_thisL e
  | Nomm.n4 p, hp, sup, goal, st, l, st1, hg, e => by
    simp only [runShape] at e
    exact runShape_nz8 env p hp sup (GoalS.next thisL) st l st1 lzNZ_thisL e
  | Nomm.n7 p q, ⟨hp, hq⟩, sup, goal, st, l, st1, hg, e => by
    simp only [runShape, bind, StateT.bind] at e
    cases e1 : runShape env (some p) q goal st with
    | none => rw [e1] at e; cases e
    | some r =>
      obtain ⟨l1, st2⟩ := r
      rw [e1] at e
      exact runShape_nz8 env p hp sup (GoalS.next l1) st2 l st1
        (runShape_nz8 env q hq (some p) goal st l1 st2 hg e1) e
  | Nomm.cons p q, ⟨hp, hq⟩, sup, goal, st, l, st1, hg, e => by
    have hrp : ∀ g st l st1, GoalNZ g → runShape env sup p g st = some (l, st1) → LzNZ l :=
      fun g st l st1 hg e => runShape_nz8 env p hp sup g st l st1 hg e
    have hrq : ∀ g st l st1, GoalNZ g → runShape env sup q g st = some (l, st1) → LzNZ l :=
      fun g st l st1 hg e => runShape_nz8 env q hq sup g st l st1 hg e
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
      (fun g st l st1 hg e => runShape_nz8 env v hv sup g st l st1 hg e)
      (fun g st l st1 hg e => runShape_nz8 env q hq sup g st l st1 hg e) st l st1 e
  | Nomm.n5 p q, ⟨hp, hq⟩, sup, goal, st, l, st1, hg, e => by
    simp only [runShape] at e
    obtain ⟨l2, s1, e1, e⟩ := sm_bind_some e
    obtain ⟨l2', s2, e2, e⟩ := sm_bind_some e
    obtain ⟨l1, s3, e3, e⟩ := sm_bind_some e
    have h2 := runShape_nz8 env q hq sup (GoalS.next thisL) _ _ _ lzNZ_thisL e1
    exact lazeCopyEnd_nz (runShape_nz8 env p hp sup (GoalS.next thisL) _ _ _ lzNZ_thisL e3) (lazePast_nz env l2 p _ l2' s2 h2 e2) e

/-- **The induction over the eight cases linked so far**: on every nomm of `RsCls8` whose
direct calls are in the code table (`CallCode`), every `sup`, state and goal of `GoalNZ`
(`%done` and `%pick` are), the gate of `+run-shape` is `runShape`. -/
theorem rs_cls8 (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) {cod : Noun}
    (hcode : slot? 52 ctx = some cod) (env : ShapeEnv) :
    ∀ (n : Nomm), RsCls8 n → CallCode cod (shapeCE env) n → ∀ sup goal st, GoalNZ goal →
      RsAt ctx env n sup goal st
  | Nomm.n0 a, _, _, sup, goal, st, hg => rs_n0W hc env a sup goal st hg
  | Nomm.n1 k, _, _, sup, goal, st, _ => rs_n1 env k sup goal st
  | Nomm.n3 p, hp, hcc, sup, goal, st, hg =>
    rs_n3W hc env p sup goal st (rs_cls8 hc h7 hcode env p hp hcc sup goal st hg)
      (rs_cls8 hc h7 hcode env p hp hcc sup (GoalS.next thisL) st lzNZ_thisL)
  | Nomm.n4 p, hp, hcc, sup, goal, st, _ =>
    rs_n4 env p sup goal st (rs_cls8 hc h7 hcode env p hp hcc sup (GoalS.next thisL) st lzNZ_thisL)
  | Nomm.n7 p q, ⟨hp, hq⟩, ⟨hcp, hcq⟩, sup, goal, st, hg =>
    rs_n7W env p q sup goal st (rs_cls8 hc h7 hcode env q hq hcq (some p) goal st hg)
      (fun l st1 e => rs_cls8 hc h7 hcode env p hp hcp sup (GoalS.next l) st1
        (runShape_nz8 env q hq (some p) goal st l st1 hg e))
  | Nomm.cons p q, ⟨hp, hq⟩, ⟨hcp, hcq⟩, sup, goal, st, hg =>
    rs_consW hc h7 hcode env p q sup goal hg st hcp hcq
      (fun l st1 hl => rs_cls8 hc h7 hcode env q hq hcq sup (GoalS.next l) st1 hl)
      (fun l st1 hl => rs_cls8 hc h7 hcode env p hp hcp sup (GoalS.next l) st1 hl)
  | Nomm.n10 a v q, ⟨hv, hq⟩, ⟨hcv, hcq⟩, sup, goal, st, hg =>
    rs_n10W hc h7 hcode env a v q sup goal hg st hcv hcq
      (fun l st1 hl => rs_cls8 hc h7 hcode env q hq hcq sup (GoalS.next l) st1 hl)
      (fun l st1 hl => rs_cls8 hc h7 hcode env v hv hcv sup (GoalS.next l) st1 hl)
  | Nomm.n5 p q, ⟨hp, hq⟩, ⟨hcp, hcq⟩, sup, goal, st, _ =>
    rs_n5W hc h7 hcode env p q sup goal st hcp
      (fun st1 => rs_cls8 hc h7 hcode env q hq hcq sup (GoalS.next thisL) st1 lzNZ_thisL)
      (fun st1 => rs_cls8 hc h7 hcode env p hp hcp sup (GoalS.next thisL) st1 lzNZ_thisL)

/-- **For track I**: the call `(~(run-shape comp gen) nomm [%done ~] ~)` of the sweeps, on every
nomm of `RsCls8` whose direct calls are in the code table, from every state, is
`runShape env none nomm GoalS.done`. -/
theorem rs_done8 (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) {cod : Noun}
    (hcode : slot? 52 ctx = some cod) (env : ShapeEnv) (n : Nomm) (hn : RsCls8 n)
    (hcc : CallCode cod (shapeCE env) n) (st : RSt CSet) (y : RsRest) :
    nock (rsCoreG n.toNoun (GoalS.done : GoalS CSet).toNoun (A 0) (rsDoor st y ctx)) rsGate
      = (runShape env Option.none n GoalS.done st).map fun p => C p.1.toNoun (rsGenNoun p.2 y) :=
  rs_cls8 hc h7 hcode env n hn hcc Option.none GoalS.done st trivial y

end Compiler
end Formalization
