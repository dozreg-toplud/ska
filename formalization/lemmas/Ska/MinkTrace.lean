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
    · rw [ih t, ← tbind_map_app]; congr 1; funext c
      rw [ih t, ← tbind_map_app]; rfl
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

/-! ## The frames that `+mink` pushes -/

/-- Every frame of the crash trace of `r` is one that `+mink` pushes (the
frame of a dynamic hint, or of a failed scry), or a frame of `t`. -/
def GoodTone (t : Trace) (r : Tone) : Prop :=
  ∀ tr, r = Tone.two tr → ∀ fr ∈ tr, stopTag fr.1 = true ∨ fr ∈ t

theorem tbind_good {t : Trace} {x : Option Tone} {k : Noun → Option Tone} {r : Tone}
    (hx : ∀ r, x = some r → GoodTone t r) (hk : ∀ p r, k p = some r → GoodTone t r)
    (h : tbind x k = some r) : GoodTone t r := by
  rcases tbind_eq_some h with ⟨p, _, hkp⟩ | ⟨hx', _⟩
  · exact hk p r hkp
  · exact hx r hx'

theorem minkF_good (lib : Lib) (gul : Noun) :
    ∀ n t s f r, minkF lib gul n t s f = some r → GoodTone t r := by
  intro n
  induction n with
  | zero => intro t s f r h; simp [minkF] at h
  | succ n ih =>
    intro t s f r h
    rw [minkF_succ_eq] at h
    unfold minkStep at h
    have Z : ∀ p, GoodTone t (Tone.zero p) := fun p tr h => by cases h
    have O : ∀ p, GoodTone t (Tone.one p) := fun p tr h => by cases h
    have T : GoodTone t (Tone.two t) := fun tr h fr hfr => by cases h; exact Or.inr hfr
    have S : ∀ x r', some x = some r' → GoodTone t x → GoodTone t r' := fun x _ h g => by
      cases h; exact g
    have I := fun s f r (h : minkF lib gul n t s f = some r) => ih t s f r h
    split at h
    · exact tbind_good (I _ _) (fun _ _ h => tbind_good (I _ _) (fun _ _ h => S _ _ h (Z _)) h) h
    · split at h
      · exact S _ _ h T
      · exact S _ _ h (Z _)
    · exact S _ _ h (Z _)
    · exact tbind_good (I _ _) (fun _ _ h => tbind_good (I _ _) (fun _ _ h => I _ _ _ h) h) h
    · exact tbind_good (I _ _) (fun _ _ h => S _ _ h (Z _)) h
    · refine tbind_good (I _ _) (fun _ _ h => ?_) h
      split at h
      · exact S _ _ h T
      · exact S _ _ h (Z _)
    · exact tbind_good (I _ _) (fun _ _ h => tbind_good (I _ _) (fun _ _ h => S _ _ h (Z _)) h) h
    · refine tbind_good (I _ _) (fun _ _ h => ?_) h
      split at h
      · exact I _ _ _ h
      · exact I _ _ _ h
      · exact S _ _ h T
    · exact tbind_good (I _ _) (fun _ _ h => ih _ _ _ _ h) h
    · exact tbind_good (I _ _) (fun _ _ h => ih _ _ _ _ h) h
    · refine tbind_good (I _ _) (fun _ _ h => ?_) h
      split at h
      · exact S _ _ h T
      · exact ih _ _ _ _ h
    · split at h
      · exact S _ _ h T
      · refine tbind_good (I _ _) (fun _ _ h => tbind_good (I _ _) (fun _ _ h => ?_) h) h
        split at h
        · exact S _ _ h T
        · exact S _ _ h (Z _)
    · exact tbind_good (I _ _) (fun _ _ h => S _ _ h (Z _)) h
    · rename_i tag _ _
      refine tbind_good (I _ _) (fun c _ h => tbind_good (fun r h' => ?_) (fun _ _ h => S _ _ h (Z _)) h) h
      intro tr hr fr hfr
      rcases ih _ _ _ _ h' tr hr fr hfr with hs | hm
      · exact Or.inl hs
      · split at hm
        · rename_i hst
          rcases List.mem_cons.mp hm with rfl | hm'
          · exact Or.inl hst
          · exact Or.inr hm'
        · exact Or.inr hm
    · exact tbind_good (I _ _) (fun _ _ h => tbind_good (I _ _) (fun _ _ h => S _ _ h (Z _)) h) h
    · refine tbind_good (I _ _) (fun _ _ h => tbind_good (I _ _) (fun _ _ h => ?_) h) h
      split at h
      · exact S _ _ h T
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨_, _, d, _, h⟩ := h
        cases d with
        | block => exact S _ _ h (O _)
        | hunk =>
          refine S _ _ h (fun tr hr fr hfr => ?_)
          cases hr
          rcases List.mem_cons.mp hfr with rfl | hm
          · exact Or.inl (show stopTag Tag.hunk = true by decide)
          · exact Or.inr hm
        | val _ => exact S _ _ h (Z _)
    · exact S _ _ h T

end SkaModel
end Formalization
