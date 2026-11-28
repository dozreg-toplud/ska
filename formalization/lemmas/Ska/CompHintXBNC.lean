import lemmas.Glue.MonoCalls
import lemmas.Ska.CompHintClsGlue

/-!
# A sound check of track C's `NC` on hint-free nomms (README Gaps 24.24)

The glue's hinted class (`InFragHW`, and `InFragHX` on top of it) is
`MonoCalls` on hint-free nomms OR the hinted check.  `MonoCalls` holds
`NCG` (`NC` at level `0`, `sixCount ≤ 255`: track C's class of indirect
calls, `%7`, conses, pure fragments, `%10` among them), but it is a `Prop`;
the tally counted only the hinted check.  This file gives a computable,
sound check of part of it:

* `fragXB` (a sound check of `FragX`: `[0 a]`, `[1 k]`, `%3`, `%4`, `%5`,
  conses, `%6`, `%10` of such parts), `fragXB_sound`;
* `ncChk lv nm` (`some t` when `NC lv t nm`: `[0 a]`, `[1 k]`, the indirect
  call, the cons, `[7 p q]` by `sevenN`, a pure fragment), `ncChk_sound`;
* **`ncG_of_ncChk`**: `NCG` of every member at level `0` with
  `sixCount ≤ 255`; **`monoCalls_of_ncChk`**: such a hint-free member is in
  `noHintM (MonoCalls S lib)` at every bell, so in `InFragHW` and in any
  class `orM (noHintM (MonoCalls S lib)) _`.

`t20` (`[8 [2 [10 [6 1 0] 0 1] 0 10] 1 F]`, hint-free, an indirect call
whose subject holds a `%10`) is a member (`#guard` in the tally).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

variable {S : Type} [HoonSet S]

/-- **A sound check of `FragX`** (no `%7`, no call). -/
def fragXB : Nomm → Bool
  | Nomm.n0 _ => true
  | Nomm.n1 _ => true
  | Nomm.n3 p => fragXB p
  | Nomm.n4 p => fragXB p
  | Nomm.n5 p q => fragXB p && fragXB q
  | Nomm.cons p q => fragXB p && fragXB q
  | Nomm.n6 c a b => fragXB c && fragXB a && fragXB b
  | Nomm.n10 _ v q => fragXB v && fragXB q
  | _ => false

theorem fragXB_sound : ∀ (nm : Nomm), fragXB nm = true → FragX (S := S) nm
  | Nomm.n0 _, _ => FragX.frag fun _ => trivial
  | Nomm.n1 _, _ => FragX.frag fun _ => trivial
  | Nomm.n3 p, h => FragX.three (fragXB_sound p h)
  | Nomm.n4 p, h => FragX.four (fragXB_sound p h)
  | Nomm.n5 p q, h => by
    simp only [fragXB, Bool.and_eq_true] at h
    exact FragX.five (fragXB_sound p h.1) (fragXB_sound q h.2)
  | Nomm.cons p q, h => by
    simp only [fragXB, Bool.and_eq_true] at h
    exact FragX.cons (fragXB_sound p h.1) (fragXB_sound q h.2)
  | Nomm.n6 c a b, h => by
    simp only [fragXB, Bool.and_eq_true] at h
    exact FragX.six (fragXB_sound c h.1.1) (fragXB_sound a h.1.2) (fragXB_sound b h.2)
  | Nomm.n10 _ v q, h => by
    simp only [fragXB, Bool.and_eq_true] at h
    exact FragX.ten (fragXB_sound v h.1) (fragXB_sound q h.2)
  | Nomm.n2 _ _ _, h => by simp [fragXB] at h
  | Nomm.n7 _ _, h => by simp [fragXB] at h
  | Nomm.n11s _ _ _, h => by simp [fragXB] at h
  | Nomm.n11d _ _ _ _, h => by simp [fragXB] at h
  | Nomm.n12 _ _, h => by simp [fragXB] at h
  | Nomm.mean _ _ _ _ _, h => by simp [fragXB] at h

/-- **A sound check of `NC lv t nm`**: `some t` when it holds. -/
def ncChk : Nat → Nomm → Option Bool
  | _, Nomm.n0 _ => some true
  | lv, Nomm.n2 p q Option.none =>
      if (ncChk 0 p).isSome && (ncChk 0 q).isSome && !bareLitQ q then some true else Option.none
  | 0, Nomm.n1 _ => some true
  | 0, Nomm.cons p q =>
      match ncChk (if q.pure then 0 else 1) p, ncChk 0 q with
      | some _, some t' => if q.pure = false && t' = false then Option.none else some true
      | _, _ => Option.none
  | 0, Nomm.n7 p q =>
      match ncChk 0 q, ncChk 0 p with
      | some t, some t' =>
          if q.pure && noSix q && (!(Nomm.n7 p q).pure || fragXB (Nomm.n7 p q)) then some (t' && (t || !p.pure))
          else Option.none
      | _, _ => Option.none
  | lv, nm => if lv = 0 && fragXB nm then some false else Option.none

theorem ncChk_pure {lv : Nat} {nm : Nomm} {t : Bool} (h : (if lv = 0 && fragXB nm then some false else Option.none) = some t) :
    NC (S := S) lv t nm := by
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    cases h; rw [hc.1]
    exact NC.pure (FragU.x (fragXB_sound nm hc.2))
  · cases h

theorem ncChk_sound : ∀ (nm : Nomm) (lv : Nat) (t : Bool), ncChk lv nm = some t → NC (S := S) lv t nm
  | Nomm.n0 a, lv, t, h => by
    simp only [ncChk, Option.some.injEq] at h; subst h; exact NC.n0
  | Nomm.n2 p q Option.none, lv, t, h => by
    simp only [ncChk] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, Option.isSome_iff_exists, Bool.not_eq_true'] at hc
      obtain ⟨⟨⟨tp, hp⟩, ⟨tq, hq⟩⟩, hb⟩ := hc
      cases h
      exact NC.ind (ncChk_sound p 0 tp hp) (ncChk_sound q 0 tq hq) hb
    · cases h
  | Nomm.n2 p q (some i), lv, t, h => by
    cases lv <;> exact ncChk_pure h
  | Nomm.n1 k, lv, t, h => by
    cases lv with
    | zero => simp only [ncChk, Option.some.injEq] at h; subst h; exact NC.n1
    | succ n => exact ncChk_pure h
  | Nomm.cons p q, lv, t, h => by
    cases lv with
    | succ n => exact ncChk_pure h
    | zero =>
      simp only [ncChk] at h
      split at h
      · rename_i tp t' hp hq
        split at h
        · cases h
        · rename_i hc
          cases h
          refine NC.cons (ncChk_sound p _ tp hp) (ncChk_sound q 0 t' hq) (fun hq' => ?_)
          cases t'
          · simp [hq'] at hc
          · rfl
      · cases h
  | Nomm.n7 p q, lv, t, h => by
    cases lv with
    | succ n => exact ncChk_pure h
    | zero =>
      simp only [ncChk] at h
      split at h
      · rename_i tq tp hq hp
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hc
          obtain ⟨⟨hpq, h6⟩, hf⟩ := hc
          cases h
          refine NC.sevenN (ncChk_sound q 0 tq hq) (NoEntF.pure hpq h6) (ncChk_sound p 0 tp hp) (fun hpu => ?_)
          rcases hf with hf | hf
          · rw [hpu] at hf; cases hf
          · exact FragU.x (fragXB_sound _ hf)
        · cases h
      · cases h
  | Nomm.n3 p, lv, t, h => by cases lv <;> exact ncChk_pure h
  | Nomm.n4 p, lv, t, h => by cases lv <;> exact ncChk_pure h
  | Nomm.n5 p q, lv, t, h => by cases lv <;> exact ncChk_pure h
  | Nomm.n6 c a b, lv, t, h => by cases lv <;> exact ncChk_pure h
  | Nomm.n10 a v q, lv, t, h => by cases lv <;> exact ncChk_pure h
  | Nomm.n11s tag q body, lv, t, h => by cases lv <;> exact ncChk_pure h
  | Nomm.n11d tag hh q body, lv, t, h => by cases lv <;> exact ncChk_pure h
  | Nomm.n12 p q, lv, t, h => by cases lv <;> exact ncChk_pure h
  | Nomm.mean p b q body k, lv, t, h => by cases lv <;> exact ncChk_pure h

/-- **`NCG` of a member at level `0`.** -/
theorem ncG_of_ncChk {nm : Nomm} (h : (ncChk 0 nm).isSome = true) (h6 : sixCount nm ≤ 255) : PokeM.NCG S nm := by
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
  exact ⟨⟨t, ncChk_sound nm 0 t ht⟩, h6⟩

end Comp

namespace Glue

variable {S : Type} [Comp.HoonSet S]

/-- **A hint-free member of `ncChk` is in the hint-free part of the glue's
hinted class**, at every bell, environment and table. -/
theorem monoCalls_of_ncChk (lib : Lib) {env : Comp.CallEnv} {N : Needs} {bl : Bell} {nm : Nomm}
    (h : (Comp.ncChk 0 nm).isSome = true) (h6 : Comp.sixCount nm ≤ 255) (hh : nm.noHint = true) :
    noHintM (MonoCalls S lib) env N bl nm :=
  ⟨Or.inl (Comp.ncG_of_ncChk h h6), hh⟩

end Glue
end SkaModel
end Formalization
