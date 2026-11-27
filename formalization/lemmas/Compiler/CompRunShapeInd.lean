import lemmas.Compiler.CompRunShapeFrom

/-!
# `+run-shape` by induction, without the hypothesis on `+laze-from` (track A, 2026-11-27)

`LazeFromAt` of `CompRunShapeLeaf.lean` is false at the door (a look at axis `0` makes
`+laze-from` loop, `CompRunShapeFrom.lean`), so `rs_n0` and `rs_cls` there hold vacuously.
This file states the cases again on goals whose `laze` looks at no axis `0` (`GoalNZ`), an
invariant of the model (`runShape_nz`: what a run returns has no look at `0` when its goal
has none), and proves them under `CompIn ctx` alone.

* `LazeFromAtW`, **`lazeFromAtW_door`**: the true link of `+laze-from` at the door.
* **`rs_n0W`**: the case `[0 a]` on a goal of `GoalNZ`.
* `rs_n7W`: the case `[7 p q]` where the run of `p` is needed only on the `laze` the run of
  `q` returns.
* `fromSureS_nz`, `lazeFrom_nz`: `+laze-from` keeps `LzNZ`.
* **`runShape_nz`**, **`rs_clsW`**: on every nomm of `RsCls`, every `sup`, state and goal of
  `GoalNZ`, the gate of `+run-shape` is `runShape`; the goal `%done` of track I's sweeps is in
  `GoalNZ`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-- **The link of `+laze-from`** at the door `D`, on every `laze` that looks at no axis `0`. -/
def LazeFromAtW (D : Noun) : Prop :=
  ∃ bat sam c, nock D (C (A 9) (C (A 0x1576a) (C (A 0) (A 1)))) = some (C bat (C sam c)) ∧
    ∀ (a : Nat) (laz : Laze CSet), LzNZ laz →
      nock (C bat (C (C (A a) laz.toNoun) c)) bat = (lazeFrom a laz).map Laze.toNoun

theorem lazeFromAtW_door (hc : CompIn ctx) (st : RSt CSet) (y : RsRest) :
    LazeFromAtW (rsDoor st y ctx) :=
  ⟨lfGate, lfBunt, rsDoor st y ctx, by simp [nock_exec, rsDoor, lf_at, lf_at', lf_arm],
    fun a laz h => lf_all hc _ a laz h⟩

/-- The goal's `laze` looks at no axis `0`. -/
def GoalNZ : GoalS CSet → Prop
  | GoalS.next l => LzNZ l
  | _ => True

theorem lzNZ_nedL (ned : NeedOrd) : LzNZ (nedL ned : Laze CSet) :=
  ⟨fun y hy => absurd hy (HoonSet.mem_empty y), trivial, trivial⟩

theorem lzNZ_noneL : LzNZ (noneL : Laze CSet) :=
  ⟨fun y hy => absurd hy (HoonSet.mem_empty y), trivial, trivial⟩

theorem lzNZ_thisL : LzNZ (thisL : Laze CSet) :=
  ⟨fun y hy => absurd hy (HoonSet.mem_empty y), trivial, trivial⟩

theorem simpleS_nz : ∀ g : GoalS CSet, GoalNZ g → LzNZ (simpleS g)
  | GoalS.next l, h => h
  | GoalS.pick, _ => lzNZ_thisL
  | GoalS.done, _ => lzNZ_thisL

/-- **The case `[0 a]`** on a goal whose `laze` looks at no axis `0`. -/
theorem rs_n0W (hc : CompIn ctx) (env : ShapeEnv) (a : Nat) (sup : Option Nomm) (goal : GoalS CSet)
    (st : RSt CSet) (hg : GoalNZ goal) : RsAt ctx env (Nomm.n0 a) sup goal st := by
  intro y
  simp only [Nomm.toNoun]
  rw [rs_push, rs_disp_n0]
  obtain ⟨bat, sam, c, h9, hgate⟩ := lazeFromAtW_door hc st y
  have hg' := hgate a (simpleS goal) (simpleS_nz goal hg)
  simp only [nock_exec, rsDoor] at h9
  nock_open rsK0
  by_cases h0 : a = 0
  · subst h0
    simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, pure, StateT.pure, noneL_noun]
  · by_cases h1 : a = 1
    · subst h1
      simp [nock_exec, rsS, rsCoreG, rsDoor, runShape, pure, StateT.pure, rsSimpleN, GoalS.toNoun]
    · have h0' : ¬ (0 = a) := fun h => h0 h.symm
      have h1' : ¬ (1 = a) := fun h => h1 h.symm
      cases e : lazeFrom a (simpleS goal) with
      | none =>
        rw [e] at hg'
        simp [nock_exec, rsS, rsCoreG, rsDoor, h0, h1, h0', h1', h9, hg', runShape, liftS, e, rsSimpleN, GoalS.toNoun]
      | some l =>
        rw [e] at hg'
        simp [nock_exec, rsS, rsCoreG, rsDoor, h0, h1, h0', h1', h9, hg', runShape, liftS, e, rsSimpleN, GoalS.toNoun]

/-- **The case `[7 p q]`** from the run of `q` and the run of `p` on the `laze` that `q`
returns. -/
theorem rs_n7W (env : ShapeEnv) (p q : Nomm) (sup : Option Nomm) (goal : GoalS CSet) (st : RSt CSet)
    (hq : RsAt ctx env q (some p) goal st)
    (hp : ∀ l st1, runShape env (some p) q goal st = some (l, st1) → RsAt ctx env p sup (GoalS.next l) st1) :
    RsAt ctx env (Nomm.n7 p q) sup goal st := by
  intro y
  simp only [Nomm.toNoun]
  rw [rs_push, rs_disp_n7]
  have hq' := hq y
  simp only [rsCoreG, supNoun, unitNoun, rsDoor] at hq'
  nock_open rsK7
  cases e : runShape env (some p) q goal st with
  | none =>
    rw [e] at hq'
    simp [nock_exec, rsS, rsCoreG, rsDoor, hq', runShape, e, bind, StateT.bind]
  | some r =>
    obtain ⟨l, st1⟩ := r
    rw [e] at hq'
    have hp' := hp l st1 e y
    simp only [rsCoreG, rsDoor, GoalS.toNoun] at hp'
    simp [nock_exec, rsS, rsCoreG, rsDoor, hq', runShape, e, bind, StateT.bind]
    exact hp'

/-! ## The invariant `LzNZ` -/

theorem fromSureS_nz (axe : Nat) (s s' : SureO CSet) (h : ∀ y ∈ HoonSet.toList s.lok, y ≠ 0)
    (ha : axe ≠ 0) (e : fromSureS axe s = some s') : ∀ y ∈ HoonSet.toList s'.lok, y ≠ 0 := by
  have hrun : ∀ y ∈ HoonSet.toList (setRun (Hoon.pegF axe) s.lok), y ≠ 0 := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := (cs_mem_setRun _ _ _).1 hy
    have := pegF_pos axe (by omega) z (Nat.pos_of_ne_zero (h z hz)); omega
  unfold fromSureS at e
  split at e
  · split at e
    · cases e
    · cases e
      split
      · intro y hy
        rcases (HoonSet.mem_put _ _ _).1 hy with rfl | hy
        · exact ha
        · exact absurd hy (HoonSet.mem_empty y)
      · exact hrun
  · cases e1 : fromOrd axe s.ned with
    | none => rw [e1] at e; cases e
    | some n => rw [e1] at e; cases e; exact hrun

mutual
theorem lazeFrom_nz (axe : Nat) : ∀ (l : Laze CSet), LzNZ l → ∀ l', lazeFrom axe l = some l' → LzNZ l'
  | Laze.mk s f b, ⟨hs, hf, hb⟩, l', e => by
    by_cases a0 : axe = 0
    · simp [lazeFrom, a0] at e
    simp only [lazeFrom, a0, if_false] at e
    cases e1 : fromSureS axe s with
    | none => rw [e1] at e; cases e
    | some sur =>
      rw [e1] at e
      have hsur := fromSureS_nz axe s sur hs a0 e1
      simp only [Option.bind_some] at e
      split at e
      · cases e; exact ⟨hsur, trivial, trivial⟩
      · cases e2 : fromF axe f with
        | none => rw [e2] at e; cases e
        | some fs =>
          cases e3 : fromB axe b with
          | none => rw [e2, e3] at e; cases e
          | some bs =>
            rw [e2, e3] at e; cases e
            exact ⟨hsur, fromF_nz axe f hf fs e2, fromB_nz axe b hb bs e3⟩
theorem fromF_nz (axe : Nat) : ∀ (f : List ((Nat × Laze CSet) × (Nat × Laze CSet))), LzNZF f →
    ∀ fs, fromF axe f = some fs → LzNZF fs
  | [], _, fs, e => by simp only [fromF, Option.some.injEq] at e; subst e; trivial
  | ((oy, y), (on, n)) :: r, ⟨hy, hn, hr⟩, fs, e => by
    simp only [fromF] at e
    cases e1 : lazeFrom axe y with
    | none => rw [e1] at e; cases e
    | some y' =>
      cases e2 : lazeFrom axe n with
      | none => rw [e1, e2] at e; cases e
      | some n' =>
        cases e3 : fromF axe r with
        | none => rw [e1, e2, e3] at e; cases e
        | some r' =>
          rw [e1, e2, e3] at e; cases e
          exact ⟨lazeFrom_nz axe y hy y' e1, lazeFrom_nz axe n hn n' e2, fromF_nz axe r hr r' e3⟩
theorem fromB_nz (axe : Nat) : ∀ (b : List (Nat × Laze CSet)), LzNZB b →
    ∀ bs, fromB axe b = some bs → LzNZB bs
  | [], _, bs, e => by simp only [fromB, Option.some.injEq] at e; subst e; trivial
  | (o, l) :: r, ⟨hl, hr⟩, bs, e => by
    simp only [fromB] at e
    cases e1 : lazeFrom axe l with
    | none => rw [e1] at e; cases e
    | some l' =>
      cases e3 : fromB axe r with
      | none => rw [e1, e3] at e; cases e
      | some r' =>
        rw [e1, e3] at e; cases e
        exact ⟨lazeFrom_nz axe l hl l' e1, fromB_nz axe r hr r' e3⟩
end

/-- **What a run of the class returns looks at no axis `0`** when its goal does not. -/
theorem runShape_nz (env : ShapeEnv) : ∀ (n : Nomm), RsCls n → ∀ sup (goal : GoalS CSet) st l st1,
    GoalNZ goal → runShape env sup n goal st = some (l, st1) → LzNZ l
  | Nomm.n0 a, _, sup, goal, st, l, st1, hg, e => by
    simp only [runShape] at e
    split at e
    · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
      rw [← e.1]; exact lzNZ_noneL
    · split at e
      · simp only [pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
        rw [← e.1]; exact simpleS_nz goal hg
      · simp only [liftS] at e
        cases e1 : lazeFrom a (simpleS goal) with
        | none => rw [e1] at e; cases e
        | some l' =>
          rw [e1] at e
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
          rw [← e.1]; exact lazeFrom_nz a _ (simpleS_nz goal hg) l' e1
  | Nomm.n1 k, _, sup, goal, st, l, st1, hg, e => by
    simp only [runShape, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at e
    rw [← e.1]; exact lzNZ_noneL
  | Nomm.n4 p, hp, sup, goal, st, l, st1, hg, e => by
    simp only [runShape] at e
    exact runShape_nz env p hp sup (GoalS.next thisL) st l st1 lzNZ_thisL e
  | Nomm.n7 p q, ⟨hp, hq⟩, sup, goal, st, l, st1, hg, e => by
    simp only [runShape, bind, StateT.bind] at e
    cases e1 : runShape env (some p) q goal st with
    | none => rw [e1] at e; cases e
    | some r =>
      obtain ⟨l1, st2⟩ := r
      rw [e1] at e
      exact runShape_nz env p hp sup (GoalS.next l1) st2 l st1 (runShape_nz env q hq (some p) goal st l1 st2 hg e1) e

/-- **The induction over the cases linked so far**, with no hypothesis on `+laze-from`: on every
nomm of `RsCls`, every `sup`, state and goal of `GoalNZ` (`%done` and `%pick` are), the gate of
`+run-shape` is `runShape`. -/
theorem rs_clsW (hc : CompIn ctx) (env : ShapeEnv) :
    ∀ (n : Nomm), RsCls n → ∀ sup goal st, GoalNZ goal → RsAt ctx env n sup goal st
  | Nomm.n0 a, _, sup, goal, st, hg => rs_n0W hc env a sup goal st hg
  | Nomm.n1 k, _, sup, goal, st, _ => rs_n1 env k sup goal st
  | Nomm.n4 p, hp, sup, goal, st, _ =>
    rs_n4 env p sup goal st (rs_clsW hc env p hp sup (GoalS.next thisL) st lzNZ_thisL)
  | Nomm.n7 p q, ⟨hp, hq⟩, sup, goal, st, hg =>
    rs_n7W env p q sup goal st (rs_clsW hc env q hq (some p) goal st hg)
      (fun l st1 e => rs_clsW hc env p hp sup (GoalS.next l) st1
        (runShape_nz env q hq (some p) goal st l st1 hg e))

end Compiler
end Formalization
