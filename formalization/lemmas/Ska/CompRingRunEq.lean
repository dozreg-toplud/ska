import lemmas.Ska.CompRingRun
import lemmas.Ska.CompDirectMEq

/-!
# `runLCMR` is `runLCM` where no direct callee has a ring (track K, README Gaps 19 (h))

* `RingFreeN env nm`: every direct callee of `nm` (in the cases `runLCM` recurses into) has
  `env.ring b = none`.
* **`runLCMR_eq`**: under `RingFreeN`, `runLCMR env mono` is `runLCM env mono`, for every
  `sup`, goal and region.  The cases are the same text but for `%2`, where `callLMR_eq`.
  This is the TRANSFER lemma: every theorem about `runLCM` / `runLC` / `finishLUCM` /
  `finishLFC` holds of the new runs on ring-free nomms.
* `runLCR env := runLCMR env false` (the `mono` `|` run, the n-ary one), **`runLCR_eq`**: it is
  `runLC` under `RingFreeN`.
* `finishLUCMR`, `finishLFCR`: `+compile-unary` and the final pass of `+compile-scc-in` on the
  new runs; `finishLUCMR_eq`, `finishLFCR_eq`: they are `finishLUCM`, `finishLFC` under
  `RingFreeN`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- **No direct callee of the nomm has a ring** (in the cases `runLCM` recurses into). -/
def RingFreeN (env : CallEnv) : Nomm → Prop
  | Nomm.cons p q => RingFreeN env p ∧ RingFreeN env q
  | Nomm.n2 p q info => InfoNoRing env info ∧ RingFreeN env p ∧ RingFreeN env q
  | Nomm.n3 p => RingFreeN env p
  | Nomm.n4 p => RingFreeN env p
  | Nomm.n5 p q => RingFreeN env p ∧ RingFreeN env q
  | Nomm.n6 p q r => RingFreeN env p ∧ RingFreeN env q ∧ RingFreeN env r
  | Nomm.n7 p q => RingFreeN env p ∧ RingFreeN env q
  | Nomm.n10 _ v q => RingFreeN env v ∧ RingFreeN env q
  | _ => True

/-- An environment with no ring at all makes every nomm ring-free. -/
theorem ringFreeN_of_none {env : CallEnv} (h : ∀ b, env.ring b = Option.none) : ∀ nm, RingFreeN env nm := by
  intro nm
  induction nm with
  | cons p q ihp ihq => exact ⟨ihp, ihq⟩
  | n2 p q info ihp ihq => exact ⟨fun b _ _ => h b, ihp, ihq⟩
  | n3 p ihp => exact ihp
  | n4 p ihp => exact ihp
  | n5 p q ihp ihq => exact ⟨ihp, ihq⟩
  | n6 p q r ihp ihq ihr => exact ⟨ihp, ihq, ihr⟩
  | n7 p q ihp ihq => exact ⟨ihp, ihq⟩
  | n10 a v q ihv ihq => exact ⟨ihv, ihq⟩
  | n0 _ => trivial
  | n1 _ => trivial
  | n11s _ _ _ _ => trivial
  | n11d _ _ _ _ _ _ => trivial
  | n12 _ _ _ _ => trivial
  | mean _ _ _ _ _ _ _ => trivial

/-- **THE TRANSFER LEMMA: where no direct callee has a ring, `runLCMR` is `runLCM`**, for every
environment, `mono`, `sup`, goal and region. -/
theorem runLCMR_eq [HoonMapKeys Map] (env : CallEnv) (mono : Bool) : ∀ (nm : Nomm), RingFreeN env nm →
    ∀ (sup : Option Nomm) (goal : CGoalL S) (region : List Nat),
      (runLCMR env mono sup nm goal region : CM Map (NextL S)) = runLCM env mono sup nm goal region := by
  intro nm
  induction nm with
  | cons p q ihp ihq =>
    intro h sup goal region
    have ep : (runLCMR env mono sup p : CGoalL S → List Nat → CM Map (NextL S)) = runLCM env mono sup p :=
      funext fun g => funext fun rg => ihp h.1 sup g rg
    have eq : (runLCMR env mono sup q : CGoalL S → List Nat → CM Map (NextL S)) = runLCM env mono sup q :=
      funext fun g => funext fun rg => ihq h.2 sup g rg
    simp only [runLCMR, runLCM, ep, eq] <;> rfl
  | n0 _ => intro _ _ _ _; simp only [runLCMR, runLCM] <;> rfl
  | n1 _ => intro _ _ _ _; simp only [runLCMR, runLCM] <;> rfl
  | n2 p q info ihp ihq =>
    intro h sup goal region
    have ep : (runLCMR env mono sup p : CGoalL S → List Nat → CM Map (NextL S)) = runLCM env mono sup p :=
      funext fun g => funext fun rg => ihp h.2.1 sup g rg
    have eq : (runLCMR env mono sup q : CGoalL S → List Nat → CM Map (NextL S)) = runLCM env mono sup q :=
      funext fun g => funext fun rg => ihq h.2.2 sup g rg
    simp only [runLCMR, runLCM, ep, eq]
    exact callLMR_eq env mono _ _ p q h.1 sup goal region
  | n3 p ihp =>
    intro h sup goal region
    have ep : (runLCMR env mono sup p : CGoalL S → List Nat → CM Map (NextL S)) = runLCM env mono sup p :=
      funext fun g => funext fun rg => ihp h sup g rg
    simp only [runLCMR, runLCM, ep] <;> rfl
  | n4 p ihp =>
    intro h sup goal region
    have ep : (runLCMR env mono sup p : CGoalL S → List Nat → CM Map (NextL S)) = runLCM env mono sup p :=
      funext fun g => funext fun rg => ihp h sup g rg
    simp only [runLCMR, runLCM, ep] <;> rfl
  | n5 p q ihp ihq =>
    intro h sup goal region
    have ep : (runLCMR env mono sup p : CGoalL S → List Nat → CM Map (NextL S)) = runLCM env mono sup p :=
      funext fun g => funext fun rg => ihp h.1 sup g rg
    have eq : (runLCMR env mono sup q : CGoalL S → List Nat → CM Map (NextL S)) = runLCM env mono sup q :=
      funext fun g => funext fun rg => ihq h.2 sup g rg
    simp only [runLCMR, runLCM, ep, eq] <;> rfl
  | n6 p q r ihp ihq ihr =>
    intro h sup goal region
    have ep : (runLCMR env mono sup p : CGoalL S → List Nat → CM Map (NextL S)) = runLCM env mono sup p :=
      funext fun g => funext fun rg => ihp h.1 sup g rg
    have eq : (runLCMR env mono sup q : CGoalL S → List Nat → CM Map (NextL S)) = runLCM env mono sup q :=
      funext fun g => funext fun rg => ihq h.2.1 sup g rg
    have er : (runLCMR env mono sup r : CGoalL S → List Nat → CM Map (NextL S)) = runLCM env mono sup r :=
      funext fun g => funext fun rg => ihr h.2.2 sup g rg
    simp only [runLCMR, runLCM, ep, eq, er] <;> rfl
  | n7 p q ihp ihq =>
    intro h sup goal region
    have ep : (runLCMR env mono sup p : CGoalL S → List Nat → CM Map (NextL S)) = runLCM env mono sup p :=
      funext fun g => funext fun rg => ihp h.1 sup g rg
    have eq : (runLCMR env mono (some p) q : CGoalL S → List Nat → CM Map (NextL S)) = runLCM env mono (some p) q :=
      funext fun g => funext fun rg => ihq h.2 (some p) g rg
    simp only [runLCMR, runLCM, ep, eq] <;> rfl
  | n10 a v q ihv ihq =>
    intro h sup goal region
    have ev : (runLCMR env mono sup v : CGoalL S → List Nat → CM Map (NextL S)) = runLCM env mono sup v :=
      funext fun g => funext fun rg => ihv h.1 sup g rg
    have eq : (runLCMR env mono sup q : CGoalL S → List Nat → CM Map (NextL S)) = runLCM env mono sup q :=
      funext fun g => funext fun rg => ihq h.2 sup g rg
    simp only [runLCMR, runLCM, ev, eq] <;> rfl
  | n11s _ _ _ _ => intro _ _ _ _; simp only [runLCMR, runLCM] <;> rfl
  | n11d _ _ _ _ _ _ => intro _ _ _ _; simp only [runLCMR, runLCM] <;> rfl
  | n12 _ _ _ _ => intro _ _ _ _; simp only [runLCMR, runLCM] <;> rfl
  | mean _ _ _ _ _ _ _ => intro _ _ _ _; simp only [runLCMR, runLCM] <;> rfl

/-- **The `mono` `|` run with rings** (the n-ary run). -/
abbrev runLCR [HoonMapKeys Map] (env : CallEnv) : Option Nomm → Nomm → CGoalL S → List Nat → CM Map (NextL S) :=
  runLCMR env false

/-- **Where no direct callee has a ring, `runLCR` is `runLC`.** -/
theorem runLCR_eq [HoonMapKeys Map] (env : CallEnv) {nm : Nomm} (h : RingFreeN env nm) (sup : Option Nomm)
    (goal : CGoalL S) (region : List Nat) :
    (runLCR env sup nm goal region : CM Map (NextL S)) = runLC env sup nm goal region := by
  rw [runLCR, runLCMR_eq env false nm h, runLCM_false]

variable [HoonMapKeys Map]

/-- **`+compile-unary` with rings**: `finishLUCM` on `runLCMR env true`. -/
def finishLUCMR (env : CallEnv) (nm : Nomm) : Option (Straight Map) :=
  (runLCMR env true Option.none nm (CGoalL.done : CGoalL S) [] gen0).bind fun (nex, g1) =>
    (kerf nex g1).bind fun ((o, sub), g2) =>
      toStraightF g2.cond g2.blocks (Need.this sub) o

theorem finishLUCMR_eq (env : CallEnv) {nm : Nomm} (h : RingFreeN env nm) :
    finishLUCMR (S := S) (Map := Map) env nm = finishLUCM (S := S) env nm := by
  unfold finishLUCMR finishLUCM
  rw [runLCMR_eq env true nm h]

/-- **The final pass of `+compile-scc-in` with rings**: `finishLFC` on `runLCR env`. -/
def finishLFCR (env : CallEnv) (nm : Nomm) (ord : NeedOrd) (less : Cape)
    (bake : Need → Need × List (Nat × Noun)) : Option (Straight Map) :=
  (runLCR env Option.none nm (CGoalL.done : CGoalL S) [] gen0).bind fun (nex, g1) =>
    if nex.th.args ≠ [] then Option.none else
    (needOrdAllocRegs ord g1).bind fun (nedFinal, g2) =>
      let bak := bake nedFinal
      (coerceLazyL nedFinal less nex.th.there nex.laz g2).bind fun (_, g3) =>
        (addOps nex.th.there (bak.2.map fun (r, v) => Pole.imm v r) g3).bind fun (_, g4) =>
          toStraightF g4.cond g4.blocks bak.1 nex.th.there

theorem finishLFCR_eq (env : CallEnv) {nm : Nomm} (h : RingFreeN env nm) (ord : NeedOrd) (less : Cape)
    (bake : Need → Need × List (Nat × Noun)) :
    finishLFCR (S := S) (Map := Map) env nm ord less bake = finishLFC (S := S) env nm ord less bake := by
  unfold finishLFCR finishLFC
  rw [runLCR_eq env h]

end Comp
end SkaModel
end Formalization
