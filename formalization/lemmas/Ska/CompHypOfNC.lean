import lemmas.Ska.CompHypOfFragF
import lemmas.Ska.CompNCInd

/-!
# `RawMono` on the class of the induction: `NCG`

README Gaps 12.22.  (b) of `CompHypOf.lean` for the whole-subject version on
`NCG`: the nomms of `NC` at level `0` (`CompNC.lean`, which contains the
call-free `FragU` through `NC.pure`) with at most 255 `%6`, from the
induction `ncOK` (`finishLUC_contractNC`).  The earlier fragments are inside
it: `nc_of_fragI` maps every constructor of `FragI` (`CompFragF.lean`) to
the constructors of `NC`, so `FragUFG ⊆ NCG` (`fragUFG_subNC`) and
`rawMono_fragUFG` is a corollary; the statement of `RawMono` is unchanged.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

variable {S : Type} [HoonSet S]

theorem pure_false_of_hinted {cod : Bell → Option Bool} {nm : Nomm} (h : hinted cod nm = some true) :
    nm.pure = false := by
  cases e : nm.pure with
  | false => rfl
  | true => rw [hinted_pure cod nm e] at h; cases h

/-- A part at the level of a cons head: level `0` when the tail is call-free. -/
theorem nc_head_lv {lv : Nat} {t : Bool} {p q : Nomm} (h : NC (S := S) lv t p)
    (hl : (if q.pure then 0 else 1) ≤ lv) : NC (S := S) (if q.pure then 0 else 1) t p :=
  NC.down h hl

theorem nc_of_fragB {nm : Nomm} (h : FragB (S := S) nm) : ∃ t, NC (S := S) 1 t nm := by
  cases h with
  | n0 _ => exact ⟨true, NC.n0⟩
  | n4 hp => exact ⟨false, NC.four hp⟩

theorem nc_of_fragC {nm : Nomm} (h : FragC (S := S) nm) : NC (S := S) 0 true nm := by
  induction h with
  | ind hp hq hb => exact NC.ind (NC.pure hp) (NC.pure hq) hb
  | @consH p d _ hd ih =>
    exact NC.cons (by rw [fragU_pure hd]; exact ih) (NC.pure hd) (fun e => by rw [fragU_pure hd] at e; cases e)
  | @consT p d hp hd ih =>
    obtain ⟨t, hb⟩ := nc_of_fragB hp
    have e : d.pure = false := pure_false_of_hinted (fragC_hinted (fun _ => Option.none) hd)
    exact NC.cons (t := t) (by rw [e]; exact hb) ih (fun _ => rfl)

theorem nc_of_fragD {nm : Nomm} (h : FragD (S := S) nm) : NC (S := S) 0 true nm := by
  induction h with
  | ind hp hq hb => exact NC.ind (NC.pure hp) (NC.pure hq) hb
  | indS _ hq hb ih => exact NC.ind ih (NC.pure hq) hb
  | indF hp hq ih => exact NC.ind (NC.pure hp) ih (bareLitQ_fragD hq)
  | indSF _ hq ihp ihq => exact NC.ind ihp ihq (bareLitQ_fragD hq)
  | @consH p d _ hd ih =>
    exact NC.cons (by rw [fragU_pure hd]; exact ih) (NC.pure hd) (fun e => by rw [fragU_pure hd] at e; cases e)
  | @consT p d hp hd ih =>
    obtain ⟨t, hb⟩ := nc_of_fragB hp
    have e : d.pure = false := pure_false_of_hinted (fragD_hinted (fun _ => Option.none) hd)
    exact NC.cons (t := t) (by rw [e]; exact hb) ih (fun _ => rfl)

theorem nc_of_fragE {nm : Nomm} (h : FragE (S := S) nm) : NC (S := S) 0 true nm := by
  induction h with
  | d h => exact nc_of_fragD h
  | @consI b c d hb hc hbl hd ih =>
    have e : d.pure = false := pure_false_of_hinted (fragE_hinted (fun _ => Option.none) hd)
    exact NC.cons (t := true) (by rw [e]; exact NC.ind (lv := 1) (NC.pure hb) (NC.pure hc) hbl) ih (fun _ => rfl)

/-- **Every nomm of `FragI t` is in `NC 0 t`.** -/
theorem nc_of_fragI {t : Bool} {nm : Nomm} (h : FragI (S := S) t nm) : NC (S := S) 0 t nm := by
  induction h with
  | e h => exact nc_of_fragE h
  | weak _ ih => exact NC.forget ih
  | indS _ hq hbl ih => exact NC.ind ih (NC.pure hq) hbl
  | indF hp hq ih => exact NC.ind (NC.pure hp) ih (bareLitQ_fragI hq)
  | indSF _ hq ihp ihq => exact NC.ind ihp ihq (bareLitQ_fragI hq)
  | @consH t p d _ hd ih =>
    exact NC.cons (by rw [fragU_pure hd]; exact ih) (NC.pure hd) (fun e => by rw [fragU_pure hd] at e; cases e)
  | @consT p d hp hd ih =>
    obtain ⟨t, hb⟩ := nc_of_fragB hp
    have e : d.pure = false := fragI_not_pure hd
    exact NC.cons (t := t) (by rw [e]; exact hb) ih (fun _ => rfl)
  | @consI b c d hb hc hbl hd ih =>
    have e : d.pure = false := fragI_not_pure hd
    exact NC.cons (t := true) (by rw [e]; exact NC.ind (lv := 1) (NC.pure hb) (NC.pure hc) hbl) ih (fun _ => rfl)
  | @sevenPU t p q hp hq hn ih =>
    have e : p.pure = false := fragI_not_pure hp
    have H := NC.sevenN (NC.pure hq) hn ih (fun x => by simp [Nomm.pure, e] at x)
    simpa [e] using H
  | @sevenPF t t' p q hp hq hn ihp ihq =>
    have e : p.pure = false := fragI_not_pure hp
    have H := NC.sevenN ihq hn ihp (fun x => by simp [Nomm.pure, e] at x)
    simpa [e] using H
  | @sevenJ p q hp hq hn ih =>
    have np : NC (S := S) 0 true p := by cases hp <;> first | exact NC.n0 | exact NC.n1
    have H := NC.sevenN ih hn np (fun x => by simp [Nomm.pure, fragI_not_pure hq] at x)
    simpa using H
  | @sevenU t p q hp hq hn ih =>
    have H := NC.sevenN ih hn (NC.pure hp) (fun x => by simp [Nomm.pure, fragI_not_pure hq] at x)
    simpa using H
  | @sevenL0 t axe q ha hq ih =>
    have H := NC.sevenE ih (NC.n0 (lv := 2) (axe := axe)) (fun x => by simp [Nomm.pure, fragI_not_pure hq] at x)
    simpa [fragI_not_pure hq] using H
  | @sevenLI t b c q hb hc hbl hq ih =>
    have H := NC.sevenE ih (NC.ind (lv := 2) (NC.pure hb) (NC.pure hc) hbl) (fun x => by simp [Nomm.pure] at x)
    simpa [fragI_not_pure hq] using H
  | @sevenLIU b c q hb hc hbl hq =>
    have H := NC.sevenE (NC.pure hq) (NC.ind (lv := 2) (NC.pure hb) (NC.pure hc) hbl) (fun x => by simp [Nomm.pure] at x)
    simpa using H
  | @consS7 p q d hp hq hu hd ih =>
    have np : NC (S := S) 2 true p := by
      cases hp with
      | n0 _ => exact NC.n0
      | ind hb hc hbl => exact NC.ind (NC.pure hb) (NC.pure hc) hbl
    have nq : ∃ t, NC (S := S) 1 t q := by
      cases hq with
      | b hb => exact nc_of_fragB hb
      | ind hb hc hbl => exact ⟨true, NC.ind (NC.pure hb) (NC.pure hc) hbl⟩
    obtain ⟨tq, nq⟩ := nq
    have e : d.pure = false := fragI_not_pure hd
    exact NC.cons (t := tq && true && (!q.pure || noSix q)) (by rw [e]; exact NC.sevenE nq np hu) ih (fun _ => rfl)

end Comp

namespace PokeM

open Nock Ana Bake

variable {M : Type → Type → Type} [Treap M] {Map : Type → Type} [HoonMap Map] [Comp.HoonMapKeys Map]
  [Opt.MapKeys Map] {J H CR : Type}

/-- **The class of the induction** for the whole-subject version: `NC` at
level `0` with at most 255 `%6`. -/
def NCG (S : Type) [Comp.HoonSet S] (nm : Nomm) : Prop := (∃ t, Comp.NC (S := S) 0 t nm) ∧ Comp.sixCount nm ≤ 255

variable {S : Type} [Comp.HoonSet S] (A : Arms M Map J H CR)

/-- **(b) for the whole-subject version on `NCG`** (`finishLUC_contractNC`). -/
theorem rawMono_NCG (lib : Lib) : RawMono S Map lib (NCG S) := by
  intro code bl nm env cd N hok hA hf _ h
  obtain ⟨⟨t, hn⟩, hc⟩ := hf
  exact (Comp.finishLUC_contractNC hok hA hn hc h N).2

/-- **`FragUFG` is inside `NCG`**, so the earlier classes are too. -/
theorem fragUFG_subNC {nm : Nomm} (h : FragUFG S nm) : NCG S nm := by
  refine ⟨?_, h.2⟩
  rcases h.1 with hu | hi
  · exact ⟨false, Comp.NC.pure hu⟩
  · exact ⟨false, Comp.nc_of_fragI hi⟩

/-- **`CompHyp` when every nomm the whole-subject version compiles is in
`NCG`** (and the n-ary version's in `FragUN`). -/
theorem compHyp_of_NCG {lib : Lib} {ref : Ref M Map J H} {D : CompData M Map J H}
    (P : CompRest S A lib ref D (NCG S) (FragUN S)) : CompHyp A lib ref :=
  compHyp_of_pieces (S := S) A ⟨P, rawMono_NCG lib, rawNary_fragU lib⟩

end PokeM
end SkaModel
end Formalization
