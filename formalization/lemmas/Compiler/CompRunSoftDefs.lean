import lemmas.Compiler.CompRunSoftArms
import lemmas.Compiler.CompSccOfAnyDefs

/-! # The threaded run link with a non-empty `soft.gen`: the rest predicates (README Gaps 19 (g))

A soft direct call runs `+soft-new` and `+soft-bond` (`CompRunSoftArms.lean`) before the runs
of its formula `q` and subject `p` (lines 4005 to 4055), and the runs of the enclosing cases
that follow it start with the entry in `soft.gen`.  So the class that holds a soft call is
stated in track I's shape `CompRunAtXTS (runLCS env snd ·)` (`CompSccLoopSoft.lean`), where the
soft map is the model's (`x.soft = softMapNoun gs.soft` on the way in, `softMapNoun` of the
model's map on the way out), and the rest predicates say nothing of `soft`.  New names; `Ext`,
`YOk`, `AgreeIP` are unchanged.

* `ExtS`: `Ext` without its `soft` clause (`sofs` kept, `nary` and `sure` only gain);
  `extS_refl`, `extS_trans`, `extS_of_ext`, `extS_soft`.
* `YOkS X Y`: `YOk` without the `NoSoft` clause, and with `X` and `Y` blind to `soft` (the
  shape overwrites the soft field of the rest it returns); `yOkS_ext`.
* `AgreeIPC`: the cache clauses of `AgreeIP` (`agreeIP_iff`), `agreeIPC_soft`.
* **`comp_run_n7TS`**: the case `%7` in the shape: the carried-over form of `comp_run_n7TN`,
  the pattern of a case that does not read `soft`.

Where `+run` reads `soft.gen` (the cases whose copies are not a change of rest predicate):
`+kern` through `+soft-ask` (line 5084, `kernS`: every case that kerns a lazy need, through
`+kerf` and `+lazy-shut`), `%6` through `+soft-fork` (line 5238, `sixNextLCS`) and through
`+soft-less` in `+lazy-big` (line 5275, the `%6` under `%done` / `%pick`), and the direct call
through `~(has by soft.gen) call-block` (line 4046, `withSoft` in `callLS`). -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun}

/-- **`Ext` without its `soft` clause**: `sofs` kept, `nary.cache` (axis `2`) and `sure.cache`
(axis `31`) only gain entries. -/
def ExtS (x x' : GenRest) : Prop :=
  x'.sofs = x.sofs ∧ CacheSub 2 x x' ∧ CacheSub 31 x x'

theorem extS_refl (x : GenRest) : ExtS x x := ⟨rfl, cacheSub_refl 2 x, cacheSub_refl 31 x⟩

theorem extS_trans {x y z : GenRest} (h1 : ExtS x y) (h2 : ExtS y z) : ExtS x z :=
  ⟨h2.1.trans h1.1, cacheSub_trans h1.2.1 h2.2.1, cacheSub_trans h1.2.2 h2.2.2⟩

theorem extS_of_ext {x y : GenRest} (h : Ext x y) : ExtS x y := ⟨h.2.1, h.2.2.1, h.2.2.2⟩

/-- `ExtS` does not see the soft field of its second rest. -/
theorem extS_soft {x y : GenRest} (s : Noun) (h : ExtS x y) : ExtS x { y with soft := s } := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, ?_⟩
  · intro N hN; exact h2 N hN
  · intro N hN; exact h3 N hN

/-- **What a composing case needs of `X` and `Y` with soft calls**: `Y` reflexive and
transitive, `X` kept along `Y`, and both blind to the soft field (the shape `CompRunAtXTS`
returns the rest `{x' with soft := softMapNoun ..}`). -/
structure YOkS (X : GenRest → Noun → Noun → Prop) (Y : GenRest → GenRest → Prop) : Prop where
  refl : ∀ x, Y x x
  trans : ∀ {x y z : GenRest}, Y x y → Y y z → Y x z
  pres : ∀ {x y : GenRest} {mono sup : Noun}, X x mono sup → Y x y → X y mono sup
  softY : ∀ {x y : GenRest} (s : Noun), Y x y → Y x { y with soft := s }
  softX : ∀ {x : GenRest} {mono sup : Noun} (s : Noun), X x mono sup → X { x with soft := s } mono sup

/-- `ExtS` with any `X` blind to `soft` and kept along `ExtS`. -/
theorem yOkS_ext {X : GenRest → Noun → Noun → Prop}
    (hp : ∀ {x y : GenRest} {mono sup : Noun}, X x mono sup → ExtS x y → X y mono sup)
    (hs : ∀ {x : GenRest} {mono sup : Noun} (s : Noun), X x mono sup → X { x with soft := s } mono sup) :
    YOkS X ExtS :=
  ⟨extS_refl, extS_trans, hp, fun s h => extS_soft s h, hs⟩

/-- **The cache clauses of `AgreeIP`** (the soft clause `x.NoSoft` left out). -/
def AgreeIPC (env : CallEnv) (P : Noun → Prop) (x : GenRest) : Prop :=
  ∃ NR MO SC INL SU, x.cache = cacheN NR MO SC INL SU ∧ IsMap mugF NR ∧ IsMap mugF SU ∧
    (∀ (b : Bell) u, getF mugF b.toNoun NR = some (C (A 0) u) →
      (∃ nb, env.need b = some nb ∧ slot? 2 u = some nb.toNoun) ∧ ∃ v, getF mugF b.toNoun SU = some (C (A 0) v)) ∧
    (∀ (b : Bell) v, getF mugF b.toNoun SU = some (C (A 0) v) → ¬ P b.toNoun →
      v = (env.sure b).toNoun ∧ ∃ u, getF mugF b.toNoun NR = some (C (A 0) u))

theorem agreeIP_iff (env : CallEnv) (P : Noun → Prop) (x : GenRest) :
    AgreeIP env P x ↔ x.NoSoft ∧ AgreeIPC env P x := Iff.rfl

/-- `AgreeIPC` does not read `soft`. -/
theorem agreeIPC_soft {env : CallEnv} {P : Noun → Prop} {x : GenRest} (s : Noun) (h : AgreeIPC env P x) :
    AgreeIPC env P { x with soft := s } := h

/-- **The case `%7` of `+run` with soft calls**: `q` with `sup` set to `p` from the rest `x`
(whose soft map is the model's), giving `x1` and the model's map `gs1.soft`, then `p` from
`{x1 with soft := softMapNoun gs1.soft}` with the goal `q` returned. -/
theorem comp_run_n7TS {X : GenRest → Noun → Noun → Prop} {Y : GenRest → GenRest → Prop} (hYk : YOkS X Y)
    (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (msup : Option Nomm) (p q : Nomm) (goal : CGoalL CSet)
    (region : List Nat) (gs : GenSf (TreapMap mugF)) {Xq : GenRest → Noun → Noun → Prop}
    (hq : CompRunAtXTS (runLCS env snd (some p)) ctx Xq Y q goal region gs)
    (hXq : ∀ x mono sup, X x mono sup → Xq x mono (C (A 0) p.toNoun))
    (hp : ∀ nex gs1, runLCS env snd (some p) q goal region gs = some (nex, gs1) →
      CompRunAtXTS (runLCS env snd msup) ctx X Y p nex.goal region gs1) :
    CompRunAtXTS (runLCS env snd msup) ctx X Y (Nomm.n7 p q) goal region gs := by
  intro x mono sup hs hX
  obtain ⟨x1, hy1, h1⟩ := hq x mono (C (A 0) p.toNoun) hs (hXq x mono sup hX)
  simp only [crSubj, compCore] at h1
  simp only [Nomm.toNoun]
  rw [cr_disp_n7]
  cases e : runLCS (S := CSet) (Map := TreapMap mugF) env snd (some p) q goal region gs with
  | none =>
    rw [e] at h1
    refine ⟨x1, hy1, ?_⟩
    simp only [compCore]
    generalize comp.door = Dr at h1 ⊢
    nock_open crK7
    simp [nock_exec, crSubj, cr_bat_dol, h1, runLCS, e, bind, StateT.bind]
  | some r =>
    obtain ⟨nex, gs1⟩ := r
    rw [e] at h1
    obtain ⟨x2, hy2, h2⟩ := hp nex gs1 e { x1 with soft := softMapNoun gs1.soft } mono sup rfl
      (hYk.softX _ (hYk.pres hX hy1))
    refine ⟨x2, hYk.trans (hYk.softY _ hy1) hy2, ?_⟩
    simp only [crSubj, compCore] at h2 h1
    simp only [compCore]
    generalize comp.door = Dr at h1 h2 ⊢
    nock_open crK7
    simp [nock_exec, crSubj, cr_bat_dol, h1, h2, runLCS, e, bind, StateT.bind]

end Compiler
end Formalization
