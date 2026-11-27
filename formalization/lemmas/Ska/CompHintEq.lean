import lemmas.Ska.CompRunLCH
import lemmas.Ska.CompDirectMEq

/-!
# `runLCH` is `runLCM` on nomms without hints (README Gaps 24)

`runLCH_eq`: on a nomm with no `%11`, `%12`, `%mean`, the run with the hint
cases is the run of `CompRunLCM.lean`, so every theorem about `runLCM`
holds of `runLCH` there.  `finishLUCH` and `finishLFCH` are `finishLUCM`
(`+compile-unary`) and the n-ary final pass with `runLCH`, equal to them
without hints (`finishLUCH_eq`, `finishLFCH_eq`).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

private theorem ok_and {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  simpa using h

/-- **Without hints, `runLCH` is `runLCM`.** -/
theorem runLCH_eq [HoonMapKeys Map] (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (mono : Bool) :
    ∀ (nm : Nomm), nm.noHint = true → ∀ (sup : Option Nomm) (goal : CGoalL S) (region : List Nat),
      (runLCH env snd mono sup nm goal region : CM Map (NextL S)) = runLCM env mono sup nm goal region := by
  intro nm
  induction nm with
  | cons p q ihp ihq =>
    intro h sup goal region
    simp only [Nomm.noHint] at h
    obtain ⟨h1, h2⟩ := ok_and h
    have ep : (runLCH env snd mono sup p : CGoalL S → List Nat → CM Map (NextL S)) = runLCM env mono sup p :=
      funext fun g => funext fun rg => ihp h1 sup g rg
    have eq : (runLCH env snd mono sup q : CGoalL S → List Nat → CM Map (NextL S)) = runLCM env mono sup q :=
      funext fun g => funext fun rg => ihq h2 sup g rg
    simp only [runLCH, runLCM, ep, eq] <;> rfl
  | n0 _ => intro _ _ _ _; simp only [runLCH, runLCM] <;> rfl
  | n1 _ => intro _ _ _ _; simp only [runLCH, runLCM] <;> rfl
  | n2 p q info ihp ihq =>
    intro h sup goal region
    simp only [Nomm.noHint] at h
    obtain ⟨h1, h2⟩ := ok_and h
    have ep : (runLCH env snd mono sup p : CGoalL S → List Nat → CM Map (NextL S)) = runLCM env mono sup p :=
      funext fun g => funext fun rg => ihp h1 sup g rg
    have eq : (runLCH env snd mono sup q : CGoalL S → List Nat → CM Map (NextL S)) = runLCM env mono sup q :=
      funext fun g => funext fun rg => ihq h2 sup g rg
    simp only [runLCH, runLCM, ep, eq] <;> rfl
  | n3 p ihp =>
    intro h sup goal region
    simp only [Nomm.noHint] at h
    have ep : (runLCH env snd mono sup p : CGoalL S → List Nat → CM Map (NextL S)) = runLCM env mono sup p :=
      funext fun g => funext fun rg => ihp h sup g rg
    simp only [runLCH, runLCM, ep] <;> rfl
  | n4 p ihp =>
    intro h sup goal region
    simp only [Nomm.noHint] at h
    have ep : (runLCH env snd mono sup p : CGoalL S → List Nat → CM Map (NextL S)) = runLCM env mono sup p :=
      funext fun g => funext fun rg => ihp h sup g rg
    simp only [runLCH, runLCM, ep] <;> rfl
  | n5 p q ihp ihq =>
    intro h sup goal region
    simp only [Nomm.noHint] at h
    obtain ⟨h1, h2⟩ := ok_and h
    have ep : (runLCH env snd mono sup p : CGoalL S → List Nat → CM Map (NextL S)) = runLCM env mono sup p :=
      funext fun g => funext fun rg => ihp h1 sup g rg
    have eq : (runLCH env snd mono sup q : CGoalL S → List Nat → CM Map (NextL S)) = runLCM env mono sup q :=
      funext fun g => funext fun rg => ihq h2 sup g rg
    simp only [runLCH, runLCM, ep, eq] <;> rfl
  | n6 p q r ihp ihq ihr =>
    intro h sup goal region
    simp only [Nomm.noHint] at h
    obtain ⟨h12, h3⟩ := ok_and h
    obtain ⟨h1, h2⟩ := ok_and h12
    have ep : (runLCH env snd mono sup p : CGoalL S → List Nat → CM Map (NextL S)) = runLCM env mono sup p :=
      funext fun g => funext fun rg => ihp h1 sup g rg
    have eq : (runLCH env snd mono sup q : CGoalL S → List Nat → CM Map (NextL S)) = runLCM env mono sup q :=
      funext fun g => funext fun rg => ihq h2 sup g rg
    have er : (runLCH env snd mono sup r : CGoalL S → List Nat → CM Map (NextL S)) = runLCM env mono sup r :=
      funext fun g => funext fun rg => ihr h3 sup g rg
    simp only [runLCH, runLCM, ep, eq, er] <;> rfl
  | n7 p q ihp ihq =>
    intro h sup goal region
    simp only [Nomm.noHint] at h
    obtain ⟨h1, h2⟩ := ok_and h
    have ep : (runLCH env snd mono sup p : CGoalL S → List Nat → CM Map (NextL S)) = runLCM env mono sup p :=
      funext fun g => funext fun rg => ihp h1 sup g rg
    have eq : (runLCH env snd mono (some p) q : CGoalL S → List Nat → CM Map (NextL S)) =
        runLCM env mono (some p) q :=
      funext fun g => funext fun rg => ihq h2 (some p) g rg
    simp only [runLCH, runLCM, ep, eq] <;> rfl
  | n10 a v q ihv ihq =>
    intro h sup goal region
    simp only [Nomm.noHint] at h
    obtain ⟨h1, h2⟩ := ok_and h
    have ev : (runLCH env snd mono sup v : CGoalL S → List Nat → CM Map (NextL S)) = runLCM env mono sup v :=
      funext fun g => funext fun rg => ihv h1 sup g rg
    have eq : (runLCH env snd mono sup q : CGoalL S → List Nat → CM Map (NextL S)) = runLCM env mono sup q :=
      funext fun g => funext fun rg => ihq h2 sup g rg
    simp only [runLCH, runLCM, ev, eq] <;> rfl
  | n11s _ _ _ _ => intro h; simp [Nomm.noHint] at h
  | n11d _ _ _ _ _ _ => intro h; simp [Nomm.noHint] at h
  | n12 _ _ _ _ => intro h; simp [Nomm.noHint] at h
  | mean _ _ _ _ _ _ _ => intro h; simp [Nomm.noHint] at h

variable [HoonMapKeys Map]

/-- `+compile-unary` with `runLCH` (`finishLUCM` with the hint cases). -/
def finishLUCH (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (nm : Nomm) : Option (Straight Map) :=
  (runLCH env snd true Option.none nm (CGoalL.done : CGoalL S) [] gen0).bind fun (nex, g1) =>
    (kerf nex g1).bind fun ((o, sub), g2) =>
      toStraightF g2.cond g2.blocks (Need.this sub) o

theorem finishLUCH_eq (env : CallEnv) (snd : Nomm → NeedOrd → Bool) {nm : Nomm} (h : nm.noHint = true) :
    finishLUCH (S := S) (Map := Map) env snd nm = finishLUCM (S := S) env nm := by
  unfold finishLUCH finishLUCM
  rw [runLCH_eq env snd true nm h]

/-- The n-ary final pass with `runLCH` (`finishLFC` with `runLCM env false`
and the hint cases). -/
def finishLFCH (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (nm : Nomm) (ord : NeedOrd) (less : Cape)
    (bake : Need → Need × List (Nat × Noun)) : Option (Straight Map) :=
  (runLCH env snd false Option.none nm (CGoalL.done : CGoalL S) [] gen0).bind fun (nex, g1) =>
    if nex.th.args ≠ [] then Option.none else
    (needOrdAllocRegs ord g1).bind fun (nedFinal, g2) =>
      let bak := bake nedFinal
      (coerceLazyL nedFinal less nex.th.there nex.laz g2).bind fun (_, g3) =>
        (addOps nex.th.there (bak.2.map fun (r, v) => Pole.imm v r) g3).bind fun (_, g4) =>
          toStraightF g4.cond g4.blocks bak.1 nex.th.there

theorem finishLFCH_eq (env : CallEnv) (snd : Nomm → NeedOrd → Bool) {nm : Nomm} (h : nm.noHint = true)
    (ord : NeedOrd) (less : Cape) (bake : Need → Need × List (Nat × Noun)) :
    finishLFCH (S := S) (Map := Map) env snd nm ord less bake = finishLFC (S := S) env nm ord less bake := by
  rw [finishLFC_eq_M]
  unfold finishLFCH
  rw [runLCH_eq env snd false nm h]

end Comp
end SkaModel
end Formalization
