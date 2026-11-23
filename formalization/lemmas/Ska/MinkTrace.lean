import lemmas.Ska.Mink

/-!
# `+mink` from a trace

`+mink` only ever pushes frames on the trace it is given, so a run from the
trace `t` is the run from `~` with `t` under the frames of a crash
(`minkF_trace`).  This is what makes an indirect call, which `+eval-top` runs
from an empty trace and whose trace goes on top of the caller's, agree with
`+mink`, which runs it in place.
-/

namespace Formalization
namespace SkaModel

open Nock

/-- `t` under the frames of a crash. -/
def Tone.app (t : Trace) : Tone → Tone
  | Tone.two tr => Tone.two (tr ++ t)
  | x => x

@[simp] theorem Tone.app_zero (t : Trace) (p : Noun) : (Tone.zero p).app t = Tone.zero p := rfl
@[simp] theorem Tone.app_one (t : Trace) (p : Noun) : (Tone.one p).app t = Tone.one p := rfl
@[simp] theorem Tone.app_two (t tr : Trace) : (Tone.two tr).app t = Tone.two (tr ++ t) := rfl

theorem Tone.app_app (t u : Trace) (x : Tone) : (x.app u).app t = x.app (u ++ t) := by
  cases x <;> simp [Tone.app]

theorem tbind_map_app (t : Trace) (x : Option Tone) (k : Noun → Option Tone) :
    tbind (x.map (Tone.app t)) (fun p => (k p).map (Tone.app t)) = (tbind x k).map (Tone.app t) := by
  match x with
  | none => rfl
  | some (Tone.zero p) => rfl
  | some (Tone.one p) => rfl
  | some (Tone.two tr) => rfl

/-- **A run of `+mink` from the trace `t` is the run from `~`, with `t` under
the frames of a crash.** -/
theorem minkF_trace (lib : Lib) (gul : Noun) :
    ∀ (n : Nat) (t : Trace) (s f : Noun),
      minkF lib gul n t s f = (minkF lib gul n [] s f).map (Tone.app t) := by
  intro n
  induction n with
  | zero => intro t s f; rfl
  | succ n ih =>
    intro t s f
    simp only [minkF_succ_eq]
    unfold minkStep
    split
    · rw [ih t, ← tbind_map_app]; congr 1; funext ph
      rw [ih t, ← tbind_map_app]; rfl
    · split <;> rfl
    · rfl
    · rw [ih t, ← tbind_map_app]; congr 1; funext s'
      rw [ih t, ← tbind_map_app]; congr 1; funext f'
      exact ih t _ _
    · rw [ih t, ← tbind_map_app]; rfl
    · rw [ih t, ← tbind_map_app]; congr 1; funext p
      split <;> rfl
    · rw [ih t, ← tbind_map_app]; congr 1; funext x
      rw [ih t, ← tbind_map_app]; rfl
    · rw [ih t, ← tbind_map_app]; congr 1; funext x
      split
      · exact ih t _ _
      · exact ih t _ _
      · rfl
    · rw [ih t, ← tbind_map_app]; congr 1; funext x
      exact ih t _ _
    · rw [ih t, ← tbind_map_app]; congr 1; funext x
      exact ih t _ _
    · rw [ih t, ← tbind_map_app]; congr 1; funext core
      split
      · rfl
      · exact ih t _ _
    · split
      · rfl
      · rw [ih t, ← tbind_map_app]; congr 1; funext x
        rw [ih t, ← tbind_map_app]; congr 1; funext y
        split <;> rfl
    · rw [ih t, ← tbind_map_app]; rfl
    · rw [ih t, ← tbind_map_app]; congr 1; funext c
      split
      · rw [ih ((_, c) :: t), ih [(_, c)]]
        cases minkF lib gul n [] s _ with
        | none => rfl
        | some x => cases x <;> simp [Tone.app, tbind]
      · rw [ih t, ← tbind_map_app]; rfl
    · rw [ih t, ← tbind_map_app]; congr 1; funext r
      rw [ih t, ← tbind_map_app]; congr 1; funext p
      split
      · rfl
      · cases lib.slam gul (C r p) with
        | none => rfl
        | some res =>
          simp only [Option.bind_some]
          cases scryDecode res with
          | none => rfl
          | some d => cases d <;> rfl
    · rfl

end SkaModel
end Formalization
