import lemmas.Compiler.CompRunTags
import lemmas.Compiler.CompRunAllSix

/-!
# The counters, the mode and the tags on the class with `%6`

`km_runLC6`: every run of `SixOk` keeps the counters growing, the mode and
the tags (`KM`), as `km_runLC` on the plain class.  The four phases of
`%6` under `%next` (`sixNextLC` and its fuel: `+leap` then phase L with
`copyAll`, `+kerf` of phase K, `sixNextForkC` with `+fork`, `sixNextSimpleC`
with `+fork-sure`, `+sect`, `+past-fork`, `+lazy-shut`), and the case under
`%done` and `%pick`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

theorem km_getCond : KM (getCond : CM (TreapMap mugF) (TreapMap mugF (Nat × List Nat))) :=
  KM.of_gen fun g x g' h => by
    simp only [getCond, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Nat.le_refl _, Nat.le_refl _, rfl, rfl⟩

theorem km_lazyShut (o : Nat) (laz : Lazy CSet) : KM (lazyShut o laz : CM (TreapMap mugF) (Lazy CSet)) := by
  unfold lazyShut
  exact KM.ite' _ (KM.pure' _) (KM.bind' (km_kern _ _) fun _ => KM.pure' _)

theorem km_copyAll : ∀ (nex : NextL CSet) (bys : List (Lazy CSet)),
    KM (copyAll nex bys : CM (TreapMap mugF) (NextL CSet))
  | nex, [] => by simp only [copyAll]; exact KM.pure' _
  | nex, b :: rest => by simp only [copyAll]; exact KM.bind' (km_copyL _ _) fun n => km_copyAll n rest

section
variable {rp rq rr : CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)}
  (hp : ∀ g r, KM (rp g r)) (hq : ∀ g r, KM (rq g r)) (hr : ∀ g r, KM (rr g r))
include hp hq hr

/-- Phase S under `%next`. -/
theorem km_sixNextSimpleC (cod : Bell → Option Bool) (p : Nomm) (laz : Lazy CSet) (th : Jmp) (region : List Nat) :
    KM (sixNextSimpleC cod rp rq rr p laz th region) := by
  unfold sixNextSimpleC
  refine KM.bind' KM.oo' fun o0 => KM.bind' KM.oo' fun o1 => KM.bind' (km_forkSure _ _ _ _) fun x => ?_
  obtain ⟨s0, s1⟩ := x
  refine KM.bind' KM.idM' fun rid => KM.bind' km_getCond fun cb => KM.bind' (hr _ _) fun nex1 =>
    KM.bind' km_getCond fun cw => KM.bind' (hq _ _) fun nex0 => KM.bind' (km_sect _ _ _ _ _ _ _) fun y => ?_
  obtain ⟨lazy, yes, nuh⟩ := y
  exact KM.bind' (KM.liftO' _) fun lazy => KM.bind' (hp _ _) fun nexCond => KM.ite' _ (km_copyL _ _)
    (KM.bind' (KM.emit' _) fun o => KM.bind' (km_lazyShut _ _) fun lz => km_copyL _ _)

/-- Phase F. -/
theorem km_sixNextForkC (cod : Bell → Option Bool) (p : Nomm) (laz : Lazy CSet) (th : Jmp) (region : List Nat) :
    KM (sixNextForkC cod rp rq rr p laz th region) := by
  unfold sixNextForkC
  refine KM.bind' KM.re' fun rc => KM.bind' (km_forkL _ _) fun x => ?_
  obtain ⟨g0, g1⟩ := x
  refine KM.bind' KM.idM' fun rid => KM.bind' km_getCond fun cb => KM.bind' (hr _ _) fun nex1 =>
    KM.bind' km_getCond fun cw => KM.bind' (hq _ _) fun nex0 => KM.bind' (km_sect _ _ _ _ _ _ _) fun y => ?_
  obtain ⟨lazy, yes, nuh⟩ := y
  exact KM.bind' (KM.liftO' _) fun lazy => KM.bind' (KM.emit' _) fun o => KM.bind' (km_lazyShut _ _) fun lz =>
    KM.bind' (hp _ _) fun nexCond => km_copyL _ _

/-- The case `%6` under `%next`, at every fuel: phases L, K, F, S. -/
theorem km_sixNextLC (cod : Bell → Option Bool) (p q r : Nomm) : ∀ (fuel : Nat) (laz : Lazy CSet) (th : Jmp)
    (region : List Nat), KM (sixNextLC cod rp rq rr p q r fuel laz th region)
  | 0, _, _, _ => by simp only [sixNextLC]; exact KM.fail
  | fuel + 1, laz, th, region => by
    simp only [sixNextLC]
    split
    · exact KM.fail
    · exact KM.bind' (km_sixNextLC cod p q r fuel _ _ _) fun nex => km_copyAll nex _
    · split
      · split
        · refine KM.bind' (km_kerf _) fun x => ?_
          obtain ⟨out, pro⟩ := x
          exact km_sixNextLC cod p q r fuel _ _ _
        · exact km_sixNextForkC hp hq hr cod p laz th region
      · exact km_sixNextSimpleC hp hq hr cod p laz th region

end

/-- **Every run of the class with `%6` keeps the counters growing, the mode
and the tags.** -/
theorem km_runLC6 (env : CallEnv) : ∀ (n : Nomm), SixOk n = true → ∀ (msup : Option Nomm) (goal : CGoalL CSet)
    (region : List Nat), KM (runLC env msup n goal region : CM (TreapMap mugF) (NextL CSet))
  | Nomm.cons p q, h, msup, goal, region => by
    simp only [SixOk, Bool.and_eq_true] at h
    have ihp := km_runLC6 env p h.1
    have ihq := km_runLC6 env q h.2
    simp only [runLC]
    refine KM.bind' (by cases goal <;> kmx) fun goal' => ?_
    cases goal' with
    | pick z o =>
      exact KM.bind' (KM.emit' _) fun _ => KM.bind' (ihq _ _ _) fun _ => KM.bind' (km_pastL _ _ _ _) fun _ =>
        KM.bind' (ihp _ _ _) fun _ => km_copyL _ _
    | done => exact KM.fail
    | next laz th =>
      refine KM.bind' (km_splitL _) fun x => ?_
      obtain ⟨hed, tel, o⟩ := x
      exact KM.bind' (km_pastL _ _ _ _) fun _ => KM.bind' (ihq _ _ _) fun _ => KM.bind' (km_pastL _ _ _ _) fun _ =>
        KM.bind' (ihp _ _ _) fun _ => km_copyL _ _
  | Nomm.n0 ax, _, msup, goal, region => by
    simp only [runLC]
    refine KM.ite' _ (km_bombL _) (KM.bind' (km_simpleNextL _) fun nex => KM.ite' _ (KM.pure' _) ?_)
    split <;> kmx
  | Nomm.n1 k, _, msup, goal, region => by
    simp only [runLC]
    cases goal <;> kmx
  | Nomm.n2 p q Option.none, h, msup, goal, region => by
    simp only [SixOk, Bool.and_eq_true] at h
    have ihp := km_runLC6 env p h.1
    have ihq := km_runLC6 env q h.2
    simp only [runLC, callL]
    refine KM.bind' (km_simpleNextL _) fun nex => KM.bind' (km_kerf _) fun x => ?_
    obtain ⟨out, pro⟩ := x
    exact KM.bind' KM.re' fun _ => KM.bind' KM.re' fun _ => KM.bind' (KM.emit' _) fun _ =>
      KM.bind' (ihq _ _ _) fun _ => KM.bind' (km_pastL _ _ _ _) fun _ => KM.bind' (ihp _ _ _) fun _ => km_copyL _ _
  | Nomm.n3 p, h, msup, goal, region => by
    simp only [SixOk] at h
    have ih := km_runLC6 env p h
    simp only [runLC]
    cases goal with
    | next laz th =>
      refine KM.ite' _ (ih _ _ _) (KM.bind' (km_collapseLazyAtomL _) fun a => ?_)
      rcases a with _ | ⟨r, o⟩
      · exact KM.fail
      · exact KM.bind' (km_forl _ _) fun _ => KM.bind' KM.re' fun _ => KM.bind' (KM.emit' _) fun _ => ih _ _ _
    | pick z o => exact KM.bind' KM.re' fun _ => KM.bind' (KM.emit' _) fun _ => ih _ _ _
    | done =>
      exact KM.bind' km_doneBlocks fun _ => KM.bind' KM.re' fun _ => KM.bind' (KM.emit' _) fun _ => ih _ _ _
  | Nomm.n4 p, h, msup, goal, region => by
    simp only [SixOk] at h
    have ih := km_runLC6 env p h
    simp only [runLC]
    cases goal with
    | next laz th =>
      refine KM.bind' (km_collapseLazyAtomL _) fun a => KM.bind' (by cases a <;> kmx) fun _ => ?_
      exact KM.bind' KM.re' fun _ => KM.bind' (KM.emit' _) fun _ => ih _ _ _
    | pick z o => exact KM.bind' KM.re' fun _ => KM.bind' KM.re' fun _ => KM.bind' (KM.emit' _) fun _ => ih _ _ _
    | done => exact KM.bind' KM.re' fun _ => KM.bind' KM.re' fun _ => KM.bind' (KM.emit' _) fun _ => ih _ _ _
  | Nomm.n5 p q, h, msup, goal, region => by
    simp only [SixOk, Bool.and_eq_true] at h
    have ihp := km_runLC6 env p h.1
    have ihq := km_runLC6 env q h.2
    simp only [runLC]
    refine KM.bind' KM.re' fun _ => KM.bind' KM.re' fun _ => KM.bind' ?_ fun _ =>
      KM.bind' (ihq _ _ _) fun _ => KM.bind' (km_pastL _ _ _ _) fun _ => KM.bind' (ihp _ _ _) fun _ => km_copyL _ _
    cases goal with
    | pick z o => exact KM.emit' _
    | done => exact KM.bind' km_doneBlocks fun _ => KM.emit' _
    | next laz th =>
      refine KM.bind' (km_collapseLazyAtomL _) fun a => ?_
      rcases a with _ | ⟨r, o⟩
      · exact KM.ite' _ (KM.emit' _) KM.fail
      · exact KM.bind' (km_forl _ _) fun _ => KM.emit' _
  | Nomm.n7 p q, h, msup, goal, region => by
    simp only [SixOk, Bool.and_eq_true] at h
    simp only [runLC]
    exact KM.bind' (km_runLC6 env q h.2 _ _ _) fun _ => km_runLC6 env p h.1 _ _ _
  | Nomm.n10 a v q, h, msup, goal, region => by
    simp only [SixOk, Bool.and_eq_true] at h
    have ihv := km_runLC6 env v h.1.2
    have ihq := km_runLC6 env q h.2
    simp only [runLC]
    refine KM.bind' (km_simpleNextL _) fun nx => KM.bind' (km_intoL _ _) fun x => ?_
    obtain ⟨don, rec, o⟩ := x
    exact KM.bind' (km_pastL _ _ _ _) fun _ => KM.bind' (ihv _ _ _) fun _ => KM.bind' (km_pastL _ _ _ _) fun _ =>
      KM.bind' (ihq _ _ _) fun _ => km_copyL _ _
  | Nomm.n6 p q r, h, msup, goal, region => by
    simp only [SixOk, Bool.and_eq_true] at h
    have ihp := km_runLC6 env p h.1.1
    have ihq := km_runLC6 env q h.1.2
    have ihr := km_runLC6 env r h.2
    cases goal with
    | next laz th =>
      simp only [runLC]
      exact km_sixNextLC (fun _ _ => ihp _ _ _) (fun _ _ => ihq _ _ _) (fun _ _ => ihr _ _ _) _ _ _ _ 3 laz th region
    | done =>
      simp only [runLC]
      exact KM.bind' (ihr _ _ _) fun _ => KM.bind' (ihq _ _ _) fun _ => KM.bind' (KM.emit' _) fun _ =>
        KM.bind' (KM.emit' _) fun _ => KM.bind' (KM.setTag' _ _) fun _ => KM.bind' (KM.setTag' _ _) fun _ =>
        KM.ite' _ KM.fail (KM.ite' _ KM.fail (KM.bind' (KM.liftO' _) fun _ => KM.bind' (ihp _ _ _) fun _ =>
        KM.ite' _ (km_copyL _ _) (KM.bind' (KM.emit' _) fun _ => KM.bind' (km_lazyShut _ _) fun _ => km_copyL _ _)))
    | pick z o =>
      simp only [runLC]
      exact KM.bind' (ihr _ _ _) fun _ => KM.bind' (ihq _ _ _) fun _ => KM.bind' (KM.emit' _) fun _ =>
        KM.bind' (KM.emit' _) fun _ => KM.bind' (KM.setTag' _ _) fun _ => KM.bind' (KM.setTag' _ _) fun _ =>
        KM.ite' _ KM.fail (KM.ite' _ KM.fail (KM.bind' (KM.liftO' _) fun _ => KM.bind' (ihp _ _ _) fun _ =>
        KM.ite' _ (km_copyL _ _) (KM.bind' (KM.emit' _) fun _ => KM.bind' (km_lazyShut _ _) fun _ => km_copyL _ _)))
  | Nomm.n2 _ _ (some _), h, _, _, _ => by simp [SixOk] at h
  | Nomm.n11s _ _ _, h, _, _, _ => by simp [SixOk] at h
  | Nomm.n11d _ _ _ _, h, _, _, _ => by simp [SixOk] at h
  | Nomm.n12 _ _, h, _, _, _ => by simp [SixOk] at h
  | Nomm.mean _ _ _ _ _, h, _, _, _ => by simp [SixOk] at h

end Compiler
end Formalization
