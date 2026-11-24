import lemmas.Ska.CompNCJump
import lemmas.Ska.CompNCFour

/-!
# The induction over `NC`

README Gaps 12.22.  `ncOK`: every nomm of `NC lv t` (`CompNC.lean`) meets
`NCOK lv t`, by structural induction on the derivation.  Each case is a
composition proved for every goal of its level: `[0 axe]` (`uokcU`,
`jNew_n0`, `lokc_n0all`), `[1 k]` (`uokcU`, `jNew_n1`), the cons
(`uokc_consEA` with `LOKCS.toBond` for the head, `entNew_consAny`),
`[7 p q]` with `p` at level `2` (`uokc_sevenLA`, `jump_sevenEA`,
`lokcLv_sevenA`) and with `q`'s result without entries (`uokc_sevenA`,
`jump_sevenNA`), the indirect call (`uokc_indDA`, `lokc_indAU`), the
call-free `FragU` (`uokcU`), and the weakenings.

* `hinted_nc`, `fragU_of_nc`, `nc_lv2_shape`: what the class says of a
  nomm's `+hinted`, of a call-free nomm, of a nomm of level `2`.
* `ncOK`: the induction.
* `uokc_of_nc`, `lokc_of_nc`, `bondOKC_of_nc`, `entNew_of_nc`: the
  corollaries; `finishLUC_contractNC`: both halves of the contract.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## What the class says -/

theorem hinted_nc (cod : Bell → Option Bool) {lv : Nat} {t : Bool} {nm : Nomm} (h : NC (S := S) lv t nm) :
    hinted cod nm = some (!nm.pure) := by
  induction h with
  | n0 => rfl
  | n1 => rfl
  | @cons t t' p q _ _ _ ihp ihq =>
    simp only [hinted, Nomm.pure, ihp, ihq]
    cases p.pure <;> cases q.pure <;> rfl
  | sevenE _ _ _ ihq ihp => exact hinted_noDirect_seven ihp ihq
  | sevenN _ _ _ _ ihq ihp => exact hinted_noDirect_seven ihp ihq
  | ind => rfl
  | four hp => rw [hinted_pure cod _ (fragU_pure (FragU.x (FragX.four hp)))]; simp [fragU_pure (FragU.x (FragX.four hp))]
  | n4 _ ih => simpa only [hinted, Nomm.pure] using ih
  | pure hf => rw [hinted_pure cod _ (fragU_pure hf)]; simp [fragU_pure hf]
  | down _ _ ih => exact ih
  | forget _ ih => exact ih

theorem fragU_of_nc {lv : Nat} {t : Bool} {nm : Nomm} (h : NC (S := S) lv t nm) :
    nm.pure = true → FragU (S := S) nm := by
  induction h with
  | n0 => exact fun _ => FragU.x (FragX.frag fun _ => trivial)
  | n1 => exact fun _ => FragU.x (FragX.frag fun _ => trivial)
  | cons _ _ _ ihp ihq =>
    intro e
    simp only [Nomm.pure, Bool.and_eq_true] at e
    exact FragU.cons (ihp e.1) (ihq e.2)
  | sevenE _ _ hu _ _ => exact hu
  | sevenN _ _ _ hu _ _ => exact hu
  | ind => intro e; simp [Nomm.pure] at e
  | four hp => exact fun _ => FragU.x (FragX.four hp)
  | n4 _ ih => exact fun e => FragU.four (ih e)
  | pure hf => exact fun _ => hf
  | down _ _ ih => exact ih
  | forget _ ih => exact ih

/-- **A nomm of level `2` is no cons and no literal.** -/
theorem nc_lv2_shape {lv : Nat} {t : Bool} {nm : Nomm} (h : NC (S := S) lv t nm) :
    2 ≤ lv → (∀ a b, nm ≠ Nomm.cons a b) ∧ ∀ k, nm ≠ Nomm.n1 k := by
  induction h with
  | n0 => intro _; exact ⟨fun _ _ e => (by cases e), fun _ e => (by cases e)⟩
  | n1 => intro l; omega
  | cons => intro l; omega
  | sevenE => intro _; exact ⟨fun _ _ e => (by cases e), fun _ e => (by cases e)⟩
  | sevenN => intro l; omega
  | ind => intro _; exact ⟨fun _ _ e => (by cases e), fun _ e => (by cases e)⟩
  | four => intro l; omega
  | n4 => intro l; omega
  | pure => intro l; omega
  | down _ hl ih => intro l; exact ih (by omega)
  | forget _ ih => exact ih

theorem pure_or_hinted {cod : Bell → Option Bool} {nm : Nomm} (h : hinted cod nm = some (!nm.pure)) :
    nm.pure = true ∨ hinted cod nm = some true := by
  cases e : nm.pure with
  | true => exact Or.inl rfl
  | false => rw [h, e]; exact Or.inr rfl

/-! ## The induction -/

/-- **Every nomm of `NC lv t` meets `NCOK lv t`.** -/
theorem ncOK {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) (env : CallEnv) {lv : Nat} {t : Bool}
    {nm : Nomm} (h : NC (S := S) lv t nm) : NCOK (S := S) (Map := Map) lib code env lv t nm := by
  induction h with
  | @n0 lv axe =>
    intro P f hA
    exact ⟨uokcU hok env (FragU.x (FragX.frag (nm := Nomm.n0 axe) fun _ => trivial)) hA,
      fun _ => ⟨jNew_n0 env _, fun e => by simp [hinted] at e⟩, fun _ => (lokc_n0all hok env hA).toS,
      fun _ => lokc_n0all hok env hA⟩
  | @n1 k =>
    intro P f hA
    exact ⟨uokcU hok env (FragU.x (FragX.frag (nm := Nomm.n1 k) fun _ => trivial)) hA,
      fun _ => ⟨jNew_n1 env _, fun e => by simp [hinted] at e⟩, fun l => absurd l (by omega),
      fun l => absurd l (by omega)⟩
  | @cons t t' p q hp hq hqt ihp ihq =>
    intro P f hA
    have hhq := hinted_nc env.cod hq
    have hhc := hinted_nc env.cod (NC.cons hp hq hqt)
    have qf : hinted env.cod q = some true → q.pure = false := fun hh => by
      rw [hhq] at hh
      cases e : q.pure with
      | false => rfl
      | true => rw [e] at hh; cases hh
    have Bp : ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f p → hinted env.cod q = some true →
        BondOKC (S := S) (Map := Map) lib env P f p := fun hA' hh => by
      have l : 1 ≤ (if q.pure then 0 else 1) := by rw [qf hh]; simp
      exact ((ihp hA').2.2.1 l).toBond
    have ihd : ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f q →
        UOKC (S := S) (Map := Map) lib env P f q ∧
          (hinted env.cod q = some true → EntNew (S := S) (Map := Map) env q) := fun hA' =>
      ⟨(ihq hA').1, fun hh => ((ihq hA').2.1 (hqt (qf hh))).2 hh⟩
    have E : EntNew (S := S) (Map := Map) env (Nomm.cons p q) :=
      entNew_consAny env (fun h => (ihp h).1) Bp ihd hA rfl
    refine ⟨?_, fun _ => ⟨jNew_of_entNew E, fun _ => E⟩, fun l => absurd l (by omega), fun l => absurd l (by omega)⟩
    rcases pure_or_hinted hhc with e | hh
    · exact uokcU hok env (fragU_of_nc (NC.cons hp hq hqt) e) hA
    · exact (uokc_consEA env (fun h => (ihp h).1) Bp ihd hh hA rfl).1
  | @sevenE lv t t' p q hq hp hu ihq ihp =>
    intro P f hA
    have hpc := nc_lv2_shape hp (Nat.le_refl _)
    have hhp := hinted_nc env.cod hp
    have hhq := hinted_nc env.cod hq
    have hh7 := hinted_noDirect_seven hhp hhq
    have Lp : ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f p → LOKC (S := S) (Map := Map) lib env P f p :=
      fun h => (ihp h).2.2.2 (Nat.le_refl _)
    refine ⟨?_, fun ht => ?_, (lokcLv_sevenA env Lp (fun h => ⟨(ihq h).2.2.1, (ihq h).2.2.2⟩) hpc hA rfl).1,
      (lokcLv_sevenA env Lp (fun h => ⟨(ihq h).2.2.1, (ihq h).2.2.2⟩) hpc hA rfl).2⟩
    · rcases pure_or_hinted hh7 with e | hh
      · exact uokcU hok env (hu e) hA
      · exact (uokc_sevenLA (Xq := True) env Lp (fun h => ⟨(ihq h).1, trivial⟩) hpc hh hA rfl).1
    · simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at ht
      obtain ⟨⟨tq, tp⟩, h6⟩ := ht
      exact jump_sevenEA env hhp hhq (fun e => by rcases h6 with h | h <;> simp_all)
        (fun h => ⟨Lp h, ((ihp h).2.1 tp).2⟩) (fun h => ⟨(ihq h).1, (ihq h).2.1 tq⟩) hpc hA rfl
  | @sevenN t t' p q hq hn hp hu ihq ihp =>
    intro P f hA
    have hhp := hinted_nc env.cod hp
    have hhq := hinted_nc env.cod hq
    have hh7 := hinted_noDirect_seven hhp hhq
    have Nq : NoEnt (S := S) (Map := Map) env q := noEnt_of_noEntF env hn
    refine ⟨?_, fun ht => ?_, fun l => absurd l (by omega), fun l => absurd l (by omega)⟩
    · rcases pure_or_hinted hh7 with e | hh
      · exact uokcU hok env (hu e) hA
      · exact (uokc_sevenA (Xp := True) (Xq := True) hok env (fun h => ⟨(ihp h).1, trivial⟩)
          (fun h => ⟨(ihq h).1, trivial⟩) (fun e => ⟨runU_uok lib (fragU_of_nc hp e), trivial⟩) Nq hh hA rfl).1
    · simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at ht
      obtain ⟨tp, tq⟩ := ht
      exact jump_sevenNA env hhp hhq (fun h => (ihp h).2.1 tp)
        (fun h => ⟨(ihq h).1, fun e => (ihq h).2.1 (by rcases tq with x | x <;> simp_all)⟩) Nq hA rfl
  | @ind lv t t' p q hp hq hbl ihp ihq =>
    intro P f hA
    have R := uokc_indDA env (fun h => (ihp h).1) (fun h => (ihq h).1) hbl hA rfl
    have L := lokc_indAU env (fun h => (ihp h).1) (fun h => (ihq h).1) hbl hA rfl
    exact ⟨R.1, fun _ => ⟨jNew_of_entNew R.2, fun _ => R.2⟩, fun _ => L.toS, fun _ => L⟩
  | four hp =>
    intro P f hA
    exact ⟨uokcU hok env (FragU.x (FragX.four hp)) hA, fun e => (by cases e), fun _ => lokcs_n4XA hok env hp hA,
      fun l => absurd l (by omega)⟩
  | @n4 t p hp ihp =>
    intro P f hA
    have hh4 := hinted_nc env.cod (NC.n4 hp)
    refine ⟨?_, fun e => (by cases e), fun l => absurd l (by omega), fun l => absurd l (by omega)⟩
    rcases pure_or_hinted hh4 with e | hh
    · exact uokcU hok env (fragU_of_nc (NC.n4 hp) e) hA
    · exact uokc_fourA env (fun h => (ihp h).1) hh hA rfl
  | pure hf =>
    intro P f hA
    exact ⟨uokcU hok env hf hA, fun e => (by cases e), fun l => absurd l (by omega), fun l => absurd l (by omega)⟩
  | down _ hl ih => exact ih.weak hl id
  | forget _ ih => exact ih.weak (Nat.le_refl _) (fun e => by cases e)

/-! ## The corollaries -/

theorem uokc_of_nc {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) (env : CallEnv) {lv : Nat}
    {t : Bool} {nm : Nomm} (h : NC (S := S) lv t nm) {P : Noun → Prop} {f : Noun} (hA : Annot lib code P f nm) :
    UOKC (S := S) (Map := Map) lib env P f nm :=
  (ncOK hok env h hA).1

theorem lokc_of_nc {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) (env : CallEnv) {t : Bool}
    {nm : Nomm} (h : NC (S := S) 2 t nm) {P : Noun → Prop} {f : Noun} (hA : Annot lib code P f nm) :
    LOKC (S := S) (Map := Map) lib env P f nm :=
  (ncOK hok env h hA).2.2.2 (Nat.le_refl _)

theorem bondOKC_of_nc {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) (env : CallEnv) {t : Bool}
    {nm : Nomm} (h : NC (S := S) 1 t nm) {P : Noun → Prop} {f : Noun} (hA : Annot lib code P f nm) :
    BondOKC (S := S) (Map := Map) lib env P f nm :=
  ((ncOK hok env h hA).2.2.1 (Nat.le_refl _)).toBond

theorem entNew_of_nc {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) (env : CallEnv) {lv : Nat}
    {nm : Nomm} (h : NC (S := S) lv true nm) {P : Noun → Prop} {f : Noun} (hA : Annot lib code P f nm)
    (hh : hinted env.cod nm = some true) : EntNew (S := S) (Map := Map) env nm :=
  ((ncOK (Map := Map) hok env h hA).2.1 rfl).2 hh

/-- **The contract on `NC`** (`finishLUC_contractG`). -/
theorem finishLUC_contractNC {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {bl : Bell}
    {lv : Nat} {t : Bool} {nm : Nomm} (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol nm)
    (hf : NC (S := S) lv t nm) (hcount : sixCount nm ≤ 255) {env : CallEnv} {cd : Straight Map}
    (h : finishLUC (S := S) env nm = some cd) (N : Needs) : cd.need = NeedOrd.this ∧ BellContract lib N bl true cd := by
  have H := finishLUC_contractG lib (uokc_of_nc (Map := Map) hok env hf hA) hcount h N
  refine ⟨H.1, fun s hs args hargs => ?_⟩
  simp only [if_true, Option.some.injEq] at hargs
  subst hargs
  exact H.2 s hs

end Comp
end SkaModel
end Formalization
