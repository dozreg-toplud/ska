import lemmas.Ska.CompConsLC
import lemmas.Ska.CompFragUC

/-!
# The fragment with calls in the parts of calls: `FragD`

README Gaps 12.20.  `FragD` is `FragC` (`CompFragUC.lean`) with the indirect
call whose subject part, formula part or both call (`FragD.indS`,
`FragD.indF`, `FragD.indSF`), and the cons whose head or tail is any nomm of
`FragD` (the tail behind a head of `FragB`).  The joint induction
(`uokc_entNew_of_fragD`) gives `UOKC` and `EntNew` for every `Annot`, through
`uokc_indirectC` and `uokc_consLC`, the two applications of `pairLC_ok`.

* `FragD`, `fragD_hinted`, `fragC_fragD`, `FragUD`.
* `uokc_indDA`, `uokc_consDA`: the call and the cons on every `Annot` (the
  wrappers by `UOKC.wrap`).
* `uokc_entNew_of_fragD`, `uokc_of_fragUD`, `finishLUC_contractUD`.
* Examples with both halves: `indC_example1` (`[2 [2 [0 3] [0 2]] [0 2]]`,
  `%isc` of `CompRunOKLC.lean`), `indC_example2` (`[2 [0 3] [2 [0 1] [0 2]]]`,
  `%ifc`), `indC_example3` (`[[2 [2 [0 3] [0 2]] [0 2]] [0 1]]`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The nomms that call, with calls in the parts of calls.** -/
inductive FragD : Nomm → Prop
  | ind {p q : Nomm} : FragU (S := S) p → FragU (S := S) q → bareLitQ q = false → FragD (Nomm.n2 p q Option.none)
  | indS {p q : Nomm} : FragD p → FragU (S := S) q → bareLitQ q = false → FragD (Nomm.n2 p q Option.none)
  | indF {p q : Nomm} : FragU (S := S) p → FragD q → FragD (Nomm.n2 p q Option.none)
  | indSF {p q : Nomm} : FragD p → FragD q → FragD (Nomm.n2 p q Option.none)
  | consH {p d : Nomm} : FragD p → FragU (S := S) d → FragD (Nomm.cons p d)
  | consT {p d : Nomm} : FragB (S := S) p → FragD d → FragD (Nomm.cons p d)

/-- **The fragment.** -/
def FragUD (S : Type) [HoonSet S] (nm : Nomm) : Prop := FragU (S := S) nm ∨ FragD (S := S) nm

theorem fragD_hinted (cod : Bell → Option Bool) {nm : Nomm} (h : FragD (S := S) nm) : hinted cod nm = some true := by
  induction h with
  | ind _ _ _ => rfl
  | indS _ _ _ _ => rfl
  | indF _ _ _ => rfl
  | indSF _ _ _ _ => rfl
  | consH _ hd ih => simp only [hinted, ih, hinted_pure cod _ (fragU_pure hd)]; rfl
  | consT hp _ ih => simp only [hinted, hinted_pure cod _ (fragU_pure (fragB_fragU hp)), ih]; rfl

theorem bareLitQ_fragD {nm : Nomm} (h : FragD (S := S) nm) : bareLitQ nm = false := by
  cases h <;> rfl

theorem fragC_fragD {nm : Nomm} (h : FragC (S := S) nm) : FragD (S := S) nm := by
  induction h with
  | ind hp hq hb => exact FragD.ind hp hq hb
  | consH _ hd ih => exact FragD.consH ih hd
  | consT hp _ ih => exact FragD.consT hp ih

/-! ## The call and the cons on every `Annot` -/

/-- **The indirect call whose parts meet `UOKC` on every `Annot`**:
`Annot.indirect` gives `uokc_indirectC` and `entNew_indirectC` with
`minkC2_indirect`, the wrappers `UOKC.wrap`, the bare ones are excluded. -/
theorem uokc_indDA {lib : Lib} {code : Bell → Option Nomm} (env : CallEnv) {p q : Nomm}
    (ihp : ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f p → UOKC (S := S) (Map := Map) lib env P f p)
    (ihq : ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f q → UOKC (S := S) (Map := Map) lib env P f q)
    (hbl : bareLitQ q = false) {P : Noun → Prop} {f : Noun} {nm : Nomm} (hA : Annot lib code P f nm) :
    nm = Nomm.n2 p q Option.none →
      UOKC (S := S) (Map := Map) lib env P f nm ∧ EntNew (S := S) (Map := Map) env nm := by
  induction hA with
  | indirect hb hc _ _ =>
    intro e
    cases e
    exact ⟨uokc_indirectC lib env (ihp hb) (ihq hc) (minkC2_indirect lib _ _ _),
      entNew_indirectC lib env (ihp hb) (ihq hc) (minkC2_indirect lib _ _ _)⟩
  | bare hf => intro e; cases e; simp [bareLitQ, hf] at hbl
  | bareLit hf _ => intro e; cases e; simp [bareLitQ, hf] at hbl
  | memo hm _ ih' => intro e; exact ⟨UOKC.wrap (wrapRel_memo hm) (ih' e).1, (ih' e).2⟩
  | six0 hb' _ ih' => intro e; exact ⟨UOKC.wrap (wrapRel_six hb' (Or.inl ⟨rfl, rfl⟩)) (ih' e).1, (ih' e).2⟩
  | six1 hb' _ ih' => intro e; exact ⟨UOKC.wrap (wrapRel_six hb' (Or.inr ⟨rfl, rfl⟩)) (ih' e).1, (ih' e).2⟩
  | cons => intro e; cases e
  | n0 => intro e; cases e
  | n1 => intro e; cases e
  | direct => intro e; cases e
  | inline => intro e; cases e
  | n3 => intro e; cases e
  | n4 => intro e; cases e
  | n5 => intro e; cases e
  | n6 => intro e; cases e
  | n7 => intro e; cases e
  | n8 => intro e; cases e
  | n9 => intro e; cases e
  | n10 => intro e; cases e
  | n11s => intro e; cases e
  | n11d => intro e; cases e
  | mean => intro e; cases e
  | n12 => intro e; cases e
  | crash => intro e; cases e
  | fold => intro e; cases e
  | n8g => intro e; cases e
  | n8l => intro e; cases e

/-- **The cons whose parts may both call on every `Annot`**: `Annot.cons`
gives `uokc_consLC` and `entNew_consLC`, the head under the bond goal by
`bondOKC_of_bondOK` (`FragB`), the wrappers `UOKC.wrap`. -/
theorem uokc_consDA {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) (env : CallEnv) {p d : Nomm}
    (ihp : ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f p → UOKC (S := S) (Map := Map) lib env P f p)
    (ihd : ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f d →
      UOKC (S := S) (Map := Map) lib env P f d ∧ (hinted env.cod d = some true → EntNew (S := S) (Map := Map) env d))
    (hB : hinted env.cod d = some true → FragB (S := S) p) (hh : hinted env.cod (Nomm.cons p d) = some true)
    {P : Noun → Prop} {f : Noun} {nm : Nomm} (hA : Annot lib code P f nm) :
    nm = Nomm.cons p d → UOKC (S := S) (Map := Map) lib env P f nm ∧ EntNew (S := S) (Map := Map) env nm := by
  induction hA with
  | cons hA1 hA2 _ _ =>
    intro e
    cases e
    have Bp : hinted env.cod d = some true → BondOKC (S := S) (Map := Map) lib env _ _ p := fun hd =>
      bondOKC_of_bondOK (runU_uok lib (fragB_fragU (hB hd)))
        (fun s hs gul tm r => mink_pure hok (fragU_pure (fragB_fragU (hB hd))) hA1 hs gul tm r)
        (bondOK_of_fragB lib (hB hd))
    exact ⟨uokc_consLC lib env (ihp hA1) Bp ⟨_, _, rfl⟩ (ihd hA2).1 (ihd hA2).2 hh,
      entNew_consLC lib env (ihp hA1) Bp ⟨_, _, rfl⟩ (ihd hA2).1 (ihd hA2).2⟩
  | memo hm _ ih' => intro e; exact ⟨UOKC.wrap (wrapRel_memo hm) (ih' e).1, (ih' e).2⟩
  | six0 hb' _ ih' => intro e; exact ⟨UOKC.wrap (wrapRel_six hb' (Or.inl ⟨rfl, rfl⟩)) (ih' e).1, (ih' e).2⟩
  | six1 hb' _ ih' => intro e; exact ⟨UOKC.wrap (wrapRel_six hb' (Or.inr ⟨rfl, rfl⟩)) (ih' e).1, (ih' e).2⟩
  | n0 => intro e; cases e
  | n1 => intro e; cases e
  | indirect => intro e; cases e
  | direct => intro e; cases e
  | inline => intro e; cases e
  | n3 => intro e; cases e
  | n4 => intro e; cases e
  | n5 => intro e; cases e
  | n6 => intro e; cases e
  | n7 => intro e; cases e
  | n8 => intro e; cases e
  | n9 => intro e; cases e
  | n10 => intro e; cases e
  | n11s => intro e; cases e
  | n11d => intro e; cases e
  | mean => intro e; cases e
  | n12 => intro e; cases e
  | bare => intro e; cases e
  | crash => intro e; cases e
  | fold => intro e; cases e
  | n8g => intro e; cases e
  | n8l => intro e; cases e
  | bareLit => intro e; cases e

/-! ## The joint induction -/

theorem uokcU {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) (env : CallEnv) {nm : Nomm}
    (h : FragU (S := S) nm) {P : Noun → Prop} {f : Noun} (hA : Annot lib code P f nm) :
    UOKC (S := S) (Map := Map) lib env P f nm :=
  uokc_of_uok lib env (runU_uok lib h) (fun s hs gul tm r => mink_pure hok (fragU_pure h) hA hs gul tm r)

/-- **The joint induction over `FragD`**: every `Annot` of a nomm of `FragD`
meets `UOKC`, and the nomm meets `EntNew`. -/
theorem uokc_entNew_of_fragD {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) (env : CallEnv)
    {nm : Nomm} (hf : FragD (S := S) nm) :
    ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f nm →
      UOKC (S := S) (Map := Map) lib env P f nm ∧ EntNew (S := S) (Map := Map) env nm := by
  induction hf with
  | ind hp hq hbl => exact fun hA => uokc_indDA env (uokcU hok env hp) (uokcU hok env hq) hbl hA rfl
  | indS _ hq hbl ih => exact fun hA => uokc_indDA env (fun h => (ih h).1) (uokcU hok env hq) hbl hA rfl
  | indF hp hq ih => exact fun hA => uokc_indDA env (uokcU hok env hp) (fun h => (ih h).1) (bareLitQ_fragD hq) hA rfl
  | indSF _ hq ihp ihq =>
    exact fun hA => uokc_indDA env (fun h => (ihp h).1) (fun h => (ihq h).1) (bareLitQ_fragD hq) hA rfl
  | consH hp hd ih =>
    intro P f hA
    have nh : hinted env.cod _ = some false := hinted_pure env.cod _ (fragU_pure hd)
    exact uokc_consDA hok env (fun h => (ih h).1)
      (fun h => ⟨uokcU hok env hd h, fun e => by rw [nh] at e; cases e⟩) (fun e => by rw [nh] at e; cases e)
      (by simp only [hinted, fragD_hinted env.cod hp, nh]; rfl) hA rfl
  | consT hp hd ih =>
    intro P f hA
    exact uokc_consDA hok env (uokcU hok env (fragB_fragU hp)) (fun h => ⟨(ih h).1, fun _ => (ih h).2⟩)
      (fun _ => hp)
      (by simp only [hinted, hinted_pure env.cod _ (fragU_pure (fragB_fragU hp)), fragD_hinted env.cod hd]; rfl) hA rfl

/-- **Every `Annot` of a nomm of `FragUD` meets `UOKC`.** -/
theorem uokc_of_fragUD {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) (env : CallEnv) {nm : Nomm}
    (hf : FragUD S nm) {P : Noun → Prop} {f : Noun} (hA : Annot lib code P f nm) :
    UOKC (S := S) (Map := Map) lib env P f nm := by
  rcases hf with h | h
  · exact uokcU hok env h hA
  · exact (uokc_entNew_of_fragD hok env h hA).1

/-- **The contract on `FragUD`** (`finishLUC_contractG`). -/
theorem finishLUC_contractUD {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {bl : Bell}
    {nm : Nomm} (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol nm) (hf : FragUD S nm)
    (hcount : sixCount nm ≤ 255) {env : CallEnv} {cd : Straight Map} (h : finishLUC (S := S) env nm = some cd)
    (N : Needs) : cd.need = NeedOrd.this ∧ BellContract lib N bl true cd := by
  have H := finishLUC_contractG lib (uokc_of_fragUD (Map := Map) hok env hf hA) hcount h N
  refine ⟨H.1, fun s hs args hargs => ?_⟩
  simp only [if_true, Option.some.injEq] at hargs
  subst hargs
  exact H.2 s hs

/-! ## Examples -/

/-- **`[2 [2 [0 3] [0 2]] [0 2]]` end to end** (`%isc`): the subject part
calls, the formula part is parked behind it by `+past`. -/
theorem indC_example1 {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {bl : Bell}
    (hfol : bl.fol = n3 (A 2) (n3 (A 2) (slot 3) (slot 2)) (slot 2)) {env : CallEnv} {cd : Straight Map}
    (h : finishLUC (S := S) env (Nomm.n2 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 2) Option.none) =
      some cd)
    (N : Needs) : cd.need = NeedOrd.this ∧ BellContract lib N bl true cd := by
  have hA : Annot lib code (SkaModel.Fits bl.less) bl.fol
      (Nomm.n2 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 2) Option.none) := by
    rw [hfol]
    exact Annot.indirect (Annot.indirect Annot.n0 Annot.n0) Annot.n0
  have hf : FragUD S (Nomm.n2 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 2) Option.none) :=
    Or.inr (FragD.indS (FragD.ind (FragU.x (FragX.frag fun _ => trivial)) (FragU.x (FragX.frag fun _ => trivial))
      rfl) (FragU.x (FragX.frag fun _ => trivial)) rfl)
  exact finishLUC_contractUD hok hA hf (by decide) h N

/-- **`[2 [0 3] [2 [0 1] [0 2]]]` end to end** (`%ifc`): the formula part
calls, the subject part's register is kept across that call. -/
theorem indC_example2 {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {bl : Bell}
    (hfol : bl.fol = n3 (A 2) (slot 3) (n3 (A 2) (slot 1) (slot 2))) {env : CallEnv} {cd : Straight Map}
    (h : finishLUC (S := S) env (Nomm.n2 (Nomm.n0 3) (Nomm.n2 (Nomm.n0 1) (Nomm.n0 2) Option.none) Option.none) =
      some cd)
    (N : Needs) : cd.need = NeedOrd.this ∧ BellContract lib N bl true cd := by
  have hA : Annot lib code (SkaModel.Fits bl.less) bl.fol
      (Nomm.n2 (Nomm.n0 3) (Nomm.n2 (Nomm.n0 1) (Nomm.n0 2) Option.none) Option.none) := by
    rw [hfol]
    exact Annot.indirect Annot.n0 (Annot.indirect Annot.n0 Annot.n0)
  have hf : FragUD S (Nomm.n2 (Nomm.n0 3) (Nomm.n2 (Nomm.n0 1) (Nomm.n0 2) Option.none) Option.none) :=
    Or.inr (FragD.indF (FragU.x (FragX.frag fun _ => trivial)) (FragD.ind (FragU.x (FragX.frag fun _ => trivial))
      (FragU.x (FragX.frag fun _ => trivial)) rfl))
  exact finishLUC_contractUD hok hA hf (by decide) h N

/-- **`[[2 [2 [0 3] [0 2]] [0 2]] [0 1]]` end to end**: a call with a
calling subject part in the head of a cons. -/
theorem indC_example3 {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {bl : Bell}
    (hfol : bl.fol = C (n3 (A 2) (n3 (A 2) (slot 3) (slot 2)) (slot 2)) (slot 1)) {env : CallEnv}
    {cd : Straight Map}
    (h : finishLUC (S := S) env (Nomm.cons (Nomm.n2 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 2)
      Option.none) (Nomm.n0 1)) = some cd)
    (N : Needs) : cd.need = NeedOrd.this ∧ BellContract lib N bl true cd := by
  have hA : Annot lib code (SkaModel.Fits bl.less) bl.fol
      (Nomm.cons (Nomm.n2 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 2) Option.none) (Nomm.n0 1)) := by
    rw [hfol]
    exact Annot.cons (Annot.indirect (Annot.indirect Annot.n0 Annot.n0) Annot.n0) Annot.n0
  have hf : FragUD S (Nomm.cons (Nomm.n2 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 2) Option.none)
      (Nomm.n0 1)) :=
    Or.inr (FragD.consH (FragD.indS (FragD.ind (FragU.x (FragX.frag fun _ => trivial))
      (FragU.x (FragX.frag fun _ => trivial)) rfl) (FragU.x (FragX.frag fun _ => trivial)) rfl)
      (FragU.x (FragX.frag fun _ => trivial)))
  exact finishLUC_contractUD hok hA hf (by decide) h N

end Comp
end SkaModel
end Formalization
