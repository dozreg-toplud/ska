import lemmas.Ska.CompRunLCM
import lemmas.Ska.CompWhole

/-!
# `runLCM` is `runLC` where `mono` is not read, and `finishLUCM`

README Gaps 18 (track J, 2026-11-27).

* `Nomm.noDirect`: no direct call (`%2` with `info = some _`) anywhere.
* `runLCM_eq`: **with `mono` `|`, or on a nomm without a direct call,
  `runLCM env mono` is `runLC env`**, for every `sup`, goal and region.  The
  cases are the same text but for the case `%2`, where `callLM` is `callL`
  when `mono` is `|` or the call is indirect (`callLM_eq`).
* `finishLUCM`: **`+compile-unary`** with `runLCM env true`, the run of
  line 3414 (`(~(run comp gen) & nomm [%done ~] ~ ~)`); exact on direct
  calls with no memo key and no ring (`CompDirectMCheck.lean`).
* `finishLUCM_eq`: without a direct call it is `finishLUC`, so the contract
  theorems of `finishLUC` on classes whose calls are indirect are about the
  real whole-subject code (`CompDirectMTop.lean`).
* `finishLFC_eq_M`: the n-ary top `finishLFC` runs `runLCM env false`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel

open Nock

/-- No direct call (`%2` with a known callee) anywhere in the nomm. -/
def Nomm.noDirect : Nomm → Bool
  | Nomm.cons p q => p.noDirect && q.noDirect
  | Nomm.n0 _ => true
  | Nomm.n1 _ => true
  | Nomm.n2 p q info => info.isNone && p.noDirect && q.noDirect
  | Nomm.n3 p => p.noDirect
  | Nomm.n4 p => p.noDirect
  | Nomm.n5 p q => p.noDirect && q.noDirect
  | Nomm.n6 p q r => p.noDirect && q.noDirect && r.noDirect
  | Nomm.n7 p q => p.noDirect && q.noDirect
  | Nomm.n10 _ v q => v.noDirect && q.noDirect
  | Nomm.n11s _ q _ => q.noDirect
  | Nomm.n11d _ h q _ => h.noDirect && q.noDirect
  | Nomm.n12 p q => p.noDirect && q.noDirect
  | Nomm.mean p _ q _ _ => p.noDirect && q.noDirect

/-- A nomm without `%2` has no direct call. -/
theorem Nomm.noDirect_of_noCall : ∀ (nm : Nomm), nm.noCall = true → nm.noDirect = true := by
  intro nm
  induction nm <;> simp_all [Nomm.noCall, Nomm.noDirect]

namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

private theorem ok_and {mono a b : Bool} (h : (!mono || (a && b)) = true) :
    (!mono || a) = true ∧ (!mono || b) = true := by
  cases mono <;> cases a <;> cases b <;> simp_all

/-- **`callLM` is `callL`** with `mono` `|` or on an indirect call. -/
theorem callLM_eq (env : CallEnv) {mono : Bool} (rp rq : CGoalL S → List Nat → CM Map (NextL S)) (p q : Nomm)
    {info : Option (Bell × Option Noun)} (h : (!mono || info.isNone) = true) (sup : Option Nomm)
    (goal : CGoalL S) (region : List Nat) :
    (callLM env mono rp rq p q info sup goal region : CM Map (NextL S)) = callL env rp rq p q info sup goal region := by
  cases mono with
  | false => rfl
  | true => cases info with
    | none => rfl
    | some _ => simp at h

/-- **With `mono` `|`, or on a nomm without a direct call, `runLCM` is
`runLC`**, for every environment, `sup`, goal and region. -/
theorem runLCM_eq [HoonMapKeys Map] (env : CallEnv) (mono : Bool) : ∀ (nm : Nomm), (!mono || nm.noDirect) = true →
    ∀ (sup : Option Nomm) (goal : CGoalL S) (region : List Nat),
      (runLCM env mono sup nm goal region : CM Map (NextL S)) = runLC env sup nm goal region := by
  intro nm
  induction nm with
  | cons p q ihp ihq =>
    intro h sup goal region
    simp only [Nomm.noDirect] at h
    obtain ⟨h1, h2⟩ := ok_and h
    have ep : (runLCM env mono sup p : CGoalL S → List Nat → CM Map (NextL S)) = runLC env sup p :=
      funext fun g => funext fun rg => ihp h1 sup g rg
    have eq : (runLCM env mono sup q : CGoalL S → List Nat → CM Map (NextL S)) = runLC env sup q :=
      funext fun g => funext fun rg => ihq h2 sup g rg
    simp only [runLCM, runLC, ep, eq] <;> rfl
  | n0 _ => intro _ _ _ _; simp only [runLCM, runLC] <;> rfl
  | n1 _ => intro _ _ _ _; simp only [runLCM, runLC] <;> rfl
  | n2 p q info ihp ihq =>
    intro h sup goal region
    simp only [Nomm.noDirect] at h
    obtain ⟨h12, h3⟩ := ok_and h
    obtain ⟨h1, h2⟩ := ok_and h12
    have ep : (runLCM env mono sup p : CGoalL S → List Nat → CM Map (NextL S)) = runLC env sup p :=
      funext fun g => funext fun rg => ihp h2 sup g rg
    have eq : (runLCM env mono sup q : CGoalL S → List Nat → CM Map (NextL S)) = runLC env sup q :=
      funext fun g => funext fun rg => ihq h3 sup g rg
    simp only [runLCM, runLC, ep, eq]
    exact callLM_eq env _ _ p q h1 sup goal region
  | n3 p ihp =>
    intro h sup goal region
    simp only [Nomm.noDirect] at h
    have ep : (runLCM env mono sup p : CGoalL S → List Nat → CM Map (NextL S)) = runLC env sup p :=
      funext fun g => funext fun rg => ihp h sup g rg
    simp only [runLCM, runLC, ep] <;> rfl
  | n4 p ihp =>
    intro h sup goal region
    simp only [Nomm.noDirect] at h
    have ep : (runLCM env mono sup p : CGoalL S → List Nat → CM Map (NextL S)) = runLC env sup p :=
      funext fun g => funext fun rg => ihp h sup g rg
    simp only [runLCM, runLC, ep] <;> rfl
  | n5 p q ihp ihq =>
    intro h sup goal region
    simp only [Nomm.noDirect] at h
    obtain ⟨h1, h2⟩ := ok_and h
    have ep : (runLCM env mono sup p : CGoalL S → List Nat → CM Map (NextL S)) = runLC env sup p :=
      funext fun g => funext fun rg => ihp h1 sup g rg
    have eq : (runLCM env mono sup q : CGoalL S → List Nat → CM Map (NextL S)) = runLC env sup q :=
      funext fun g => funext fun rg => ihq h2 sup g rg
    simp only [runLCM, runLC, ep, eq] <;> rfl
  | n6 p q r ihp ihq ihr =>
    intro h sup goal region
    simp only [Nomm.noDirect] at h
    obtain ⟨h12, h3⟩ := ok_and h
    obtain ⟨h1, h2⟩ := ok_and h12
    have ep : (runLCM env mono sup p : CGoalL S → List Nat → CM Map (NextL S)) = runLC env sup p :=
      funext fun g => funext fun rg => ihp h1 sup g rg
    have eq : (runLCM env mono sup q : CGoalL S → List Nat → CM Map (NextL S)) = runLC env sup q :=
      funext fun g => funext fun rg => ihq h2 sup g rg
    have er : (runLCM env mono sup r : CGoalL S → List Nat → CM Map (NextL S)) = runLC env sup r :=
      funext fun g => funext fun rg => ihr h3 sup g rg
    simp only [runLCM, runLC, ep, eq, er] <;> rfl
  | n7 p q ihp ihq =>
    intro h sup goal region
    simp only [Nomm.noDirect] at h
    obtain ⟨h1, h2⟩ := ok_and h
    have ep : (runLCM env mono sup p : CGoalL S → List Nat → CM Map (NextL S)) = runLC env sup p :=
      funext fun g => funext fun rg => ihp h1 sup g rg
    have eq : (runLCM env mono (some p) q : CGoalL S → List Nat → CM Map (NextL S)) = runLC env (some p) q :=
      funext fun g => funext fun rg => ihq h2 (some p) g rg
    simp only [runLCM, runLC, ep, eq] <;> rfl
  | n10 a v q ihv ihq =>
    intro h sup goal region
    simp only [Nomm.noDirect] at h
    obtain ⟨h1, h2⟩ := ok_and h
    have ev : (runLCM env mono sup v : CGoalL S → List Nat → CM Map (NextL S)) = runLC env sup v :=
      funext fun g => funext fun rg => ihv h1 sup g rg
    have eq : (runLCM env mono sup q : CGoalL S → List Nat → CM Map (NextL S)) = runLC env sup q :=
      funext fun g => funext fun rg => ihq h2 sup g rg
    simp only [runLCM, runLC, ev, eq] <;> rfl
  | n11s _ _ _ _ => intro _ _ _ _; simp only [runLCM, runLC] <;> rfl
  | n11d _ _ _ _ _ _ => intro _ _ _ _; simp only [runLCM, runLC] <;> rfl
  | n12 _ _ _ _ => intro _ _ _ _; simp only [runLCM, runLC] <;> rfl
  | mean _ _ _ _ _ _ _ => intro _ _ _ _; simp only [runLCM, runLC] <;> rfl

/-- **With `mono` `|`, `runLCM` is `runLC`** on every nomm. -/
theorem runLCM_false [HoonMapKeys Map] (env : CallEnv) (nm : Nomm) (sup : Option Nomm) (goal : CGoalL S)
    (region : List Nat) : (runLCM env false sup nm goal region : CM Map (NextL S)) = runLC env sup nm goal region :=
  runLCM_eq env false nm rfl sup goal region

/-- **With `mono` `&`, on a nomm without a direct call, `runLCM` is
`runLC`.** -/
theorem runLCM_true [HoonMapKeys Map] (env : CallEnv) {nm : Nomm} (h : nm.noDirect = true) (sup : Option Nomm)
    (goal : CGoalL S) (region : List Nat) :
    (runLCM env true sup nm goal region : CM Map (NextL S)) = runLC env sup nm goal region :=
  runLCM_eq env true nm (by simp [h]) sup goal region

variable [HoonMapKeys Map]

/-- **`+compile-unary`** of a function whose nomm is `nm` (lines 3407 to
3419): `run` with `mono` `&` for `[%done ~]` from an empty state (`runLCM
env true`), `+kerf` of its result, `+to-straight` of `[%next [[this+sub ~]
~ ~] ~ o]`. -/
def finishLUCM (env : CallEnv) (nm : Nomm) : Option (Straight Map) :=
  (runLCM env true Option.none nm (CGoalL.done : CGoalL S) [] gen0).bind fun (nex, g1) =>
    (kerf nex g1).bind fun ((o, sub), g2) =>
      toStraightF g2.cond g2.blocks (Need.this sub) o

/-- **Without a direct call, `finishLUCM` is `finishLUC`.** -/
theorem finishLUCM_eq (env : CallEnv) {nm : Nomm} (h : nm.noDirect = true) :
    finishLUCM (S := S) (Map := Map) env nm = finishLUC (S := S) env nm := by
  unfold finishLUCM finishLUC
  rw [runLCM_true env h]

/-- **The n-ary top runs `runLCM` with `mono` `|`**: `finishLFC` is its
text with `runLCM env false` (line 3525). -/
theorem finishLFC_eq_M (env : CallEnv) (nm : Nomm) (ord : NeedOrd) (less : Cape)
    (bake : Need → Need × List (Nat × Noun)) :
    finishLFC (S := S) (Map := Map) env nm ord less bake =
      (runLCM env false Option.none nm (CGoalL.done : CGoalL S) [] gen0).bind fun (nex, g1) =>
        if nex.th.args ≠ [] then Option.none else
        (needOrdAllocRegs ord g1).bind fun (nedFinal, g2) =>
          let bak := bake nedFinal
          (coerceLazyL nedFinal less nex.th.there nex.laz g2).bind fun (_, g3) =>
            (addOps nex.th.there (bak.2.map fun (r, v) => Pole.imm v r) g3).bind fun (_, g4) =>
              toStraightF g4.cond g4.blocks bak.1 nex.th.there := by
  unfold finishLFC
  rw [runLCM_false env nm]

end Comp
end SkaModel
end Formalization
