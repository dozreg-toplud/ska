import lemmas.Ska.CompHintX
import lemmas.Ska.SockFacts
import lemmas.Ska.Contract

/-!
# What a bell's `less` says of the subject's battery (README Gaps 24.24)

`sockBat less a` is the noun at the axis `a` of every noun of the sock
`less`, when its cape knows all of it (`knownAt`).  `batOK_less`: the
check's `BatOK` of `sockBat less` holds on the subjects that fit `less`,
what the glue has at a bell (`Fits bl.less`).
-/

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

/-- The noun at the axis `a` of every noun that fits the cape `c` over the
data `d`, when the cape knows all of it there. -/
def knownAt : Cape → Noun → Nat → Option Noun
  | Cape.yes, d, a => slot? a d
  | Cape.no, _, _ => Option.none
  | Cape.cell h t, d, a =>
      if 2 ≤ a then
        match d with
        | Noun.cell dh dt => if cap a = 2 then knownAt h dh (mas a) else knownAt t dt (mas a)
        | Noun.atom _ => Option.none
      else Option.none

/-- **The battery a bell's `less` knows.** -/
def sockBat : Sock → Bat
  | Sock.mk c d => knownAt c d
  | Sock.void => noBat

theorem knownAt_isNo : ∀ (c : Cape) (d : Noun) (a : Nat), c.isNo = true → knownAt c d a = Option.none
  | Cape.yes, _, _, h => by simp [Cape.isNo] at h
  | Cape.no, _, _, _ => rfl
  | Cape.cell h t, d, a, hc => by
    simp only [Cape.isNo, Bool.and_eq_true] at hc
    unfold knownAt
    split
    · split
      · rename_i dh dt
        split
        · exact knownAt_isNo h dh _ hc.1
        · exact knownAt_isNo t dt _ hc.2
      · rfl
    · rfl

theorem knownAt_fits : ∀ (c : Cape) (d n : Noun) (a : Nat) (F : Noun), FitsCape c d n →
    knownAt c d a = some F → slot? a n = some F
  | Cape.yes, d, n, a, F, hf, hk => by
    simp only [FitsCape] at hf; subst hf; simpa [knownAt] using hk
  | Cape.no, _, _, _, _, _, hk => by simp [knownAt] at hk
  | Cape.cell h t, d, n, a, F, hf, hk => by
    unfold knownAt at hk
    split at hk
    · rename_i ha
      simp only [FitsCape] at hf
      rcases hf with hno | ⟨dh, dt, nh, nt, rfl, rfl, fh, ft⟩
      · simp only [Bool.and_eq_true] at hno
        split at hk
        · rename_i dh dt
          split at hk
          · rw [knownAt_isNo h dh _ hno.1] at hk; cases hk
          · rw [knownAt_isNo t dt _ hno.2] at hk; cases hk
        · cases hk
      · rw [slot?_cap ha]
        simp only at hk ⊢
        split at hk
        · rename_i hc; rw [if_pos hc]; exact knownAt_fits h dh nh _ F fh hk
        · rename_i hc; rw [if_neg hc]; exact knownAt_fits t dt nt _ F ft hk
    · cases hk

/-- **The glue's half**: on the subjects that fit `less`, `sockBat less` holds. -/
theorem batOK_less (less : Sock) : BatOK (sockBat less) (SkaModel.Fits less) := by
  intro a F hb s hs
  cases less with
  | void => simp [SkaModel.Fits] at hs
  | mk c d => exact knownAt_fits c d s a F hs hb

theorem batOK_noBat (P : Noun → Prop) : BatOK noBat P := fun _ _ h => by cases h

end Comp
end SkaModel
end Formalization
