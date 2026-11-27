import lemmas.Compiler.CompRunShapeCons

/-!
# `+run-shape`: the induction over seven cases (track A, 2026-11-27)

The five cases of `rs_cls5` (`[0 a]`, `[1 k]`, `[3 p]`, `[4 p]`, `[7 p q]`) and the two of
`CompRunShapeCons.lean` (cons, `[5 p q]`).

* `RsCls7`: the nomms built of these seven cases.
* `runShape_nz7`: the invariant `LzNZ` over them (with `lazeSplit_nz`, `lazePast_nz`,
  `lazeCopy_nz`).
* **`rs_cls7`**: on every nomm of `RsCls7` whose direct calls are in the code table
  (`CallCode`), every `sup`, state and goal of `GoalNZ`, the gate of `+run-shape` is `runShape`,
  under `CompIn ctx`, `K` at axis `7` of `ctx` and the code table at axis `52` of `ctx`.
* **`rs_done7`**: the sweeps' call `(~(run-shape comp gen) nomm [%done ~] ~)`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

theorem sm_bind_some {α β : Type} {x : SM CSet α} {f : α → SM CSet β} {st : RSt CSet} {r : β × RSt CSet}
    (h : (x >>= f) st = some r) : ∃ a st', x st = some (a, st') ∧ f a st' = some r := by
  simp only [bind, StateT.bind] at h
  cases e : x st with
  | none => rw [e] at h; cases h
  | some p => obtain ⟨a, st'⟩ := p; rw [e] at h; exact ⟨a, st', rfl, h⟩

theorem shLiftS_some {α : Type} {o : Option α} {st : RSt CSet} {r : α × RSt CSet}
    (h : (shLiftS o : SM CSet α) st = some r) : ∃ a, o = some a ∧ r = (a, st) := by
  simp only [shLiftS] at h
  cases e : o with
  | none => rw [e] at h; cases h
  | some a => rw [e] at h; simp only [Option.map_some, Option.some.injEq] at h; exact ⟨a, rfl, h.symm⟩

/-- The end of the cases: `+laze-copy` of two `laze`s of `LzNZ`. -/
theorem lazeCopyEnd_nz {a b l : Laze CSet} {st st1 : RSt CSet} (ha : LzNZ a) (hb : LzNZ b)
    (h : (shLiftS (lazeCopy a b) : SM CSet (Laze CSet)) st = some (l, st1)) : LzNZ l := by
  obtain ⟨c, e, r⟩ := shLiftS_some h
  simp only [Prod.mk.injEq] at r
  rw [r.1]; exact lazeCopy_nz a b c ha hb e

/-- **`consNext` keeps `LzNZ`**, given that its two runs do. -/
theorem consNext_nz (env : ShapeEnv) (rp rq : GoalS CSet → SM CSet (Laze CSet)) (p q : Nomm)
    (hrp : ∀ g st l st1, GoalNZ g → rp g st = some (l, st1) → LzNZ l)
    (hrq : ∀ g st l st1, GoalNZ g → rq g st = some (l, st1) → LzNZ l)
    (laz : Laze CSet) (hl : LzNZ laz) (st : RSt CSet) (l : Laze CSet) (st1 : RSt CSet)
    (e : consNext env rp rq p q laz st = some (l, st1)) : LzNZ l := by
  unfold consNext at e
  cases e1 : lazeSplit laz with
  | none => simp [e1, shLiftS, bind, StateT.bind] at e
  | some ht =>
    obtain ⟨hed, tel⟩ := ht
    obtain ⟨hnz, tnz⟩ := lazeSplit_nz laz hl hed tel e1
    cases e2 : lazePast env hed q st with
    | none => simp [e1, e2, shLiftS, bind, StateT.bind] at e
    | some r2 =>
      obtain ⟨hed', s2⟩ := r2
      have h1 := lazePast_nz env hed q st hed' s2 hnz e2
      cases e3 : rq (GoalS.next tel) s2 with
      | none => simp [e1, e2, e3, shLiftS, bind, StateT.bind] at e
      | some r3 =>
        obtain ⟨l2, s3⟩ := r3
        have h2 := hrq (GoalS.next tel) s2 l2 s3 tnz e3
        cases e4 : lazePast env l2 p s3 with
        | none => simp [e1, e2, e3, e4, shLiftS, bind, StateT.bind] at e
        | some r4 =>
          obtain ⟨l2', s4⟩ := r4
          have h3 := lazePast_nz env l2 p s3 l2' s4 h2 e4
          cases e5 : rp (GoalS.next hed') s4 with
          | none => simp [e1, e2, e3, e4, e5, shLiftS, bind, StateT.bind] at e
          | some r5 =>
            obtain ⟨l1, s5⟩ := r5
            have h4 := hrp (GoalS.next hed') s4 l1 s5 h1 e5
            cases e6 : lazeCopy l1 l2' with
            | none => simp [e1, e2, e3, e4, e5, e6, shLiftS, bind, StateT.bind] at e
            | some c =>
              simp [e1, e2, e3, e4, e5, e6, shLiftS, bind, StateT.bind] at e
              rw [← e.1]; exact lazeCopy_nz l1 l2' c h4 h3 e6

/-- The nomms built of the cases linked so far: `[0 a]`, `[1 k]`, `[3 p]`, `[4 p]`,
`[7 p q]`, cons, `[5 p q]`. -/
def RsCls7 : Nomm → Prop
  | Nomm.n0 _ => True
  | Nomm.n1 _ => True
  | Nomm.n3 p => RsCls7 p
  | Nomm.n4 p => RsCls7 p
  | Nomm.n7 p q => RsCls7 p ∧ RsCls7 q
  | Nomm.cons p q => RsCls7 p ∧ RsCls7 q
  | Nomm.n5 p q => RsCls7 p ∧ RsCls7 q
  | _ => False

/-- **What a run of `RsCls7` returns looks at no axis `0`** when its goal does not. -/
theorem runShape_nz7 (env : ShapeEnv) : ∀ (n : Nomm), RsCls7 n → ∀ sup (goal : GoalS CSet) st l st1,
    GoalNZ goal → runShape env sup n goal st = some (l, st1) → LzNZ l
  | Nomm.n0 a, _, sup, goal, st, l, st1, hg, e => runShape_nz env (Nomm.n0 a) trivial sup goal st l st1 hg e
  | Nomm.n1 k, _, sup, goal, st, l, st1, hg, e => runShape_nz env (Nomm.n1 k) trivial sup goal st l st1 hg e
  | Nomm.n3 p, hp, sup, goal, st, l, st1, hg, e => by
    cases goal with
    | next l0 =>
      by_cases hn : noneEq l0 = true
      · simp only [runShape, hn, if_true] at e; exact runShape_nz7 env p hp sup _ st l st1 hg e
      · simp only [runShape, hn] at e
        exact runShape_nz7 env p hp sup (GoalS.next thisL) st l st1 lzNZ_thisL e
    | pick =>
      simp only [runShape] at e; exact runShape_nz7 env p hp sup (GoalS.next thisL) st l st1 lzNZ_thisL e
    | done =>
      simp only [runShape] at e; exact runShape_nz7 env p hp sup (GoalS.next thisL) st l st1 lzNZ_thisL e
  | Nomm.n4 p, hp, sup, goal, st, l, st1, hg, e => by
    simp only [runShape] at e
    exact runShape_nz7 env p hp sup (GoalS.next thisL) st l st1 lzNZ_thisL e
  | Nomm.n7 p q, ⟨hp, hq⟩, sup, goal, st, l, st1, hg, e => by
    simp only [runShape, bind, StateT.bind] at e
    cases e1 : runShape env (some p) q goal st with
    | none => rw [e1] at e; cases e
    | some r =>
      obtain ⟨l1, st2⟩ := r
      rw [e1] at e
      exact runShape_nz7 env p hp sup (GoalS.next l1) st2 l st1
        (runShape_nz7 env q hq (some p) goal st l1 st2 hg e1) e
  | Nomm.cons p q, ⟨hp, hq⟩, sup, goal, st, l, st1, hg, e => by
    have hrp : ∀ g st l st1, GoalNZ g → runShape env sup p g st = some (l, st1) → LzNZ l :=
      fun g st l st1 hg e => runShape_nz7 env p hp sup g st l st1 hg e
    have hrq : ∀ g st l st1, GoalNZ g → runShape env sup q g st = some (l, st1) → LzNZ l :=
      fun g st l st1 hg e => runShape_nz7 env q hq sup g st l st1 hg e
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
  | Nomm.n5 p q, ⟨hp, hq⟩, sup, goal, st, l, st1, hg, e => by
    simp only [runShape] at e
    obtain ⟨l2, s1, e1, e⟩ := sm_bind_some e
    obtain ⟨l2', s2, e2, e⟩ := sm_bind_some e
    obtain ⟨l1, s3, e3, e⟩ := sm_bind_some e
    have h2 := runShape_nz7 env q hq sup (GoalS.next thisL) _ _ _ lzNZ_thisL e1
    exact lazeCopyEnd_nz (runShape_nz7 env p hp sup (GoalS.next thisL) _ _ _ lzNZ_thisL e3) (lazePast_nz env l2 p _ l2' s2 h2 e2) e

/-- **The induction over the seven cases linked so far**: on every nomm of `RsCls7` whose
direct calls are in the code table (`CallCode`), every `sup`, state and goal of `GoalNZ`
(`%done` and `%pick` are), the gate of `+run-shape` is `runShape`. -/
theorem rs_cls7 (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) {cod : Noun}
    (hcode : slot? 52 ctx = some cod) (env : ShapeEnv) :
    ∀ (n : Nomm), RsCls7 n → CallCode cod (shapeCE env) n → ∀ sup goal st, GoalNZ goal →
      RsAt ctx env n sup goal st
  | Nomm.n0 a, _, _, sup, goal, st, hg => rs_n0W hc env a sup goal st hg
  | Nomm.n1 k, _, _, sup, goal, st, _ => rs_n1 env k sup goal st
  | Nomm.n3 p, hp, hcc, sup, goal, st, hg =>
    rs_n3W hc env p sup goal st (rs_cls7 hc h7 hcode env p hp hcc sup goal st hg)
      (rs_cls7 hc h7 hcode env p hp hcc sup (GoalS.next thisL) st lzNZ_thisL)
  | Nomm.n4 p, hp, hcc, sup, goal, st, _ =>
    rs_n4 env p sup goal st (rs_cls7 hc h7 hcode env p hp hcc sup (GoalS.next thisL) st lzNZ_thisL)
  | Nomm.n7 p q, ⟨hp, hq⟩, ⟨hcp, hcq⟩, sup, goal, st, hg =>
    rs_n7W env p q sup goal st (rs_cls7 hc h7 hcode env q hq hcq (some p) goal st hg)
      (fun l st1 e => rs_cls7 hc h7 hcode env p hp hcp sup (GoalS.next l) st1
        (runShape_nz7 env q hq (some p) goal st l st1 hg e))
  | Nomm.cons p q, ⟨hp, hq⟩, ⟨hcp, hcq⟩, sup, goal, st, hg =>
    rs_consW hc h7 hcode env p q sup goal hg st hcp hcq
      (fun l st1 hl => rs_cls7 hc h7 hcode env q hq hcq sup (GoalS.next l) st1 hl)
      (fun l st1 hl => rs_cls7 hc h7 hcode env p hp hcp sup (GoalS.next l) st1 hl)
  | Nomm.n5 p q, ⟨hp, hq⟩, ⟨hcp, hcq⟩, sup, goal, st, _ =>
    rs_n5W hc h7 hcode env p q sup goal st hcp
      (fun st1 => rs_cls7 hc h7 hcode env q hq hcq sup (GoalS.next thisL) st1 lzNZ_thisL)
      (fun st1 => rs_cls7 hc h7 hcode env p hp hcp sup (GoalS.next thisL) st1 lzNZ_thisL)

/-- **For track I**: the call `(~(run-shape comp gen) nomm [%done ~] ~)` of the sweeps, on every
nomm of `RsCls7` whose direct calls are in the code table, from every state, is
`runShape env none nomm GoalS.done`. -/
theorem rs_done7 (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) {cod : Noun}
    (hcode : slot? 52 ctx = some cod) (env : ShapeEnv) (n : Nomm) (hn : RsCls7 n)
    (hcc : CallCode cod (shapeCE env) n) (st : RSt CSet) (y : RsRest) :
    nock (rsCoreG n.toNoun (GoalS.done : GoalS CSet).toNoun (A 0) (rsDoor st y ctx)) rsGate
      = (runShape env Option.none n GoalS.done st).map fun p => C p.1.toNoun (rsGenNoun p.2 y) :=
  rs_cls7 hc h7 hcode env n hn hcc Option.none GoalS.done st trivial y

end Compiler
end Formalization
