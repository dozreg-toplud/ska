import lemmas.Compiler.SkaAnalyze

/-!
# The joint induction on the depth of calls

`E j` runs every formula that `FFar` excludes (the batteries and loops of the
core of `+ska-callgraph` whose calls the induction follows) with
`nockW (E (j - 1))`, none at `j = 0`, and every other formula with `nock`.
So `E j` is `nock` on every formula with `FFar` (`E_far`), every run of
`nock` is a run of some `E j` (`E_complete`), and `E j` is below `nock`
(`E_le_nock`).  Every step theorem over an evaluator applies with
`c := E (j - 1)`.

This file also gives the bunt of `identity` that `+cull` computes, over every
evaluator that is `nock` off `FFar` (`bunt_W`): arm `186` of the tail of `ana`
is the mold `moldArm`, which makes the core `[moldBat [identBunt anaTail]]`,
and both the arm and the battery `moldBat` are `FFar`.  `moldBat` has no name
in the generated nouns; `mold_arm_at` ties it to the pill.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon SkaModel.Ana

variable {R : Type}

set_option linter.unusedSimpArgs false

/-! ## The bunt of `identity` over an evaluator -/

/-- The battery of the mold core made by arm `186` of the tail of `ana`. -/
def moldBat : Noun :=
  (C (A 8) (C (C (C (A 8) (C (C (A 7) (C (C (A 0) (A 7)) (C (A 9) (C (A 11) (C (A 0) (A 7)))))) (C (A 9) (C (A 2)
    (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))) (C (C (A 0) (A 26)) (C (A 0) (A 27)))) (C (A 8)
    (C (C (A 5) (C (C (A 0) (A 14)) (C (A 0) (A 2)))) (C (A 0) (A 6))))))

/-- Arm `186` of the tail of `ana`, the mold `identity`:
`[8 [1 identBunt] [[1 moldBat] [0 1]]]`. -/
def moldArm : Noun := C (A 8) (C (C (A 1) identBunt) (C (C (A 1) moldBat) (C (A 0) (A 1))))

theorem mold_arm_at : slot? 186 anaTail = some moldArm := by kernel_rfl

theorem moldArm_far : FFar moldArm := by ffar_disch

theorem moldBat_far : FFar moldBat := by ffar_disch

/-- The mold kicked with its default sample returns the bunt. -/
theorem mold_bat_bunt : nock (C moldBat (C identBunt anaTail)) moldBat = some identBunt :=
  nock_of_evalFuel (fuel := 300) (by kernel_rfl)

theorem mold_arm_run : nock anaTail moldArm = some (C moldBat (C identBunt anaTail)) := by
  unfold moldArm
  simp [nock_exec]

/-- **The bunt of `identity`** in `+cull`, over an evaluator `c` that is
`nock` off `FFar`: the `hbunt` of `cull_runW`. -/
theorem bunt_W (c : Noun → Noun → Option Noun) (hcf : ∀ s f, FFar f → c s f = nock s f) (X : Noun)
    (h : slot? 2047 X = some anaTail) : nockW c X buntF = some identBunt := by
  unfold buntF
  rw [nockW_op7, nockW_op9, nockW_op0, h]
  simp only [Option.bind_some, mold_arm_at, hcf _ _ moldArm_far, mold_arm_run]
  rw [nockW_op9, nockW_op0]
  simp only [slot?_one, Option.bind_some]
  rw [show slot? 2 (C moldBat (C identBunt anaTail)) = some moldBat from rfl]
  simp only [Option.bind_some, hcf _ _ moldBat_far, mold_bat_bunt]

/-! ## The call function -/

/-- The formulas `FFar` excludes, nested at most `j` deep, every other
formula by `nock`. -/
def E : Nat → Noun → Noun → Option Noun
  | 0 => fun s f => if FFar f then nock s f else none
  | j + 1 => fun s f => if FFar f then nock s f else nockW (E j) s f

theorem E_far (j : Nat) {s f : Noun} (h : FFar f) : E j s f = nock s f := by
  cases j <;> simp only [E, if_pos h]

theorem E_zero {s f : Noun} (h : ¬ FFar f) : E 0 s f = none := by simp only [E, if_neg h]

theorem E_succ (j : Nat) {s f : Noun} (h : ¬ FFar f) : E (j + 1) s f = nockW (E j) s f := by
  simp only [E, if_neg h]

theorem E_le_nock : ∀ (j : Nat) (s f : Noun), Below? (E j s f) (nock s f)
  | 0, s, f => by
    by_cases h : FFar f
    · rw [E_far 0 h]; exact Below?.refl _
    · rw [E_zero h]; exact fun _ e => by cases e
  | j + 1, s, f => by
    by_cases h : FFar f
    · rw [E_far _ h]; exact Below?.refl _
    · rw [E_succ j h, nock_eq_nockW]; exact nockW_mono (E_le_nock j) s f

theorem iterN_le_E : ∀ (j : Nat) (s f : Noun), Below? (iterN j s f) (E j s f)
  | 0, _, _ => fun _ h => by simp [iterN] at h
  | j + 1, s, f => by
    by_cases h : FFar f
    · rw [E_far _ h]; exact iterN_sound _ s f
    · rw [E_succ j h, iterN_succ]; exact nockW_mono (iterN_le_E j) s f

/-- Every run of `nock` is a run of some `E j`. -/
theorem E_complete {s f x : Noun} (h : nock s f = some x) : ∃ j, E j s f = some x :=
  let ⟨j, hj⟩ := iterN_complete h
  ⟨j, iterN_le_E j s f x hj⟩

theorem E_hcf (j : Nat) : ∀ s f, FFar f → E j s f = nock s f := fun _ _ h => E_far j h

/-! ## The formulas the induction follows are not `FFar` -/

theorem nf_fol : ¬ FFar fol_loop.battery := fun h => h.1 rfl
theorem nf_res : ¬ FFar fol_loop.resolve := fun h => h.2.1 rfl
theorem nf_dir : ¬ FFar fol_loop.direct := fun h => h.2.2.1 rfl
theorem nf_ana : ¬ FFar ska_analyze.battery := fun h => h.2.2.2.1 rfl
theorem nf_run : ¬ FFar ska_run.battery := fun h => h.2.2.2.2.1 rfl
theorem nf_loop0 : ¬ FFar ska_analyze.loop0 := fun h => h.2.2.2.2.2.1 rfl
theorem nf_loop1 : ¬ FFar ska_analyze.loop1 := fun h => h.2.2.2.2.2.2.1 rfl
theorem nf_swl : ¬ FFar ska_cg.sweep.loop := fun h => h.2.2.2.2.2.2.2.1 rfl
theorem nf_live : ¬ FFar ska_cg.cull.loop := fun h => h.2.2.2.2.2.2.2.2.1 rfl
theorem nf_swb : ¬ FFar ska_cg.sweep.battery := fun h => h.2.2.2.2.2.2.2.2.2.1 rfl
theorem nf_cub : ¬ FFar ska_cg.cull.battery := fun h => h.2.2.2.2.2.2.2.2.2.2 rfl

end Compiler
end Formalization
