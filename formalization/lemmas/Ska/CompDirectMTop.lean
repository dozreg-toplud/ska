import lemmas.Ska.CompDirectMEq
import lemmas.Ska.CompFourTop
import lemmas.Ska.CompNCInd

/-!
# The contracts of `finishLUC` are about the real whole-subject code

README Gaps 18 (track J, 2026-11-27).  `finishLUC` runs `runLC`, which has
no `mono`; the real `+compile-unary` is `finishLUCM` (`runLCM env true`).
They agree on nomms without a direct call (`finishLUCM_eq`), and every class
with a contract theorem at the top has only indirect calls: `CallTree`,
`CallTree7`, `CallTreeA`, `TopTree`, `NC` (`*.noDirect` below).  So their
bell contracts hold of `finishLUCM`, the code the Hoon produces:
`finishLUCM_bellContractCallTree7`, `…CallTreeA`, `…TopTree`, `…NC`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

theorem CallTree.noDirect {f : Noun} {nm : Nomm} (h : CallTree f nm) : nm.noDirect = true := by
  induction h <;> simp_all [Nomm.noDirect]

theorem CallTree7.noDirect {f : Noun} {nm : Nomm} (h : CallTree7 f nm) : nm.noDirect = true := by
  induction h <;> simp_all [Nomm.noDirect]

theorem CallTreeA.noDirect {b : Bool} {f : Noun} {nm : Nomm} (h : CallTreeA b f nm) : nm.noDirect = true := by
  induction h <;> simp_all [Nomm.noDirect]

theorem TopTree.noDirect {f : Noun} {nm : Nomm} (h : TopTree f nm) : nm.noDirect = true := by
  induction h with
  | tree hc => exact hc.noDirect
  | seven hp _ ih => simp only [Nomm.noDirect, hp.noDirect, ih, Bool.and_self]

theorem noDirect_of_fragU {nm : Nomm} (h : FragU (S := S) nm) : nm.noDirect = true :=
  Nomm.noDirect_of_noCall nm (Nomm.noCall_of_pure nm (fragU_pure h))

theorem noDirect_of_fragX {nm : Nomm} (h : FragX (S := S) nm) : nm.noDirect = true :=
  Nomm.noDirect_of_noCall nm (Nomm.noCall_of_pure nm (fragX_pure h))

theorem NC.noDirect {lv : Nat} {t : Bool} {nm : Nomm} (h : NC (S := S) lv t nm) : nm.noDirect = true := by
  induction h with
  | four hf => simp only [Nomm.noDirect]; exact noDirect_of_fragX hf
  | pure hf => exact noDirect_of_fragU hf
  | _ => simp_all [Nomm.noDirect]

/-- **The bell contract of `CallTree7` on the real whole-subject code.** -/
theorem finishLUCM_bellContractCallTree7 {lib : Lib} {bl : Bell} {nm : Nomm} (h : CallTree7 bl.fol nm)
    {env : CallEnv} {cd : Straight Map} (hc : finishLUCM (S := S) env nm = some cd) (N : Needs) :
    cd.need = NeedOrd.this ∧ BellContract lib N bl true cd :=
  finishLUC_bellContractCallTree7 (S := S) (Map := Map) h (by rw [← finishLUCM_eq env h.noDirect]; exact hc) N

/-- **The bell contract of `CallTreeA` on the real whole-subject code.** -/
theorem finishLUCM_bellContractCallTreeA {lib : Lib} {bl : Bell} {b : Bool} {nm : Nomm} (h : CallTreeA b bl.fol nm)
    {env : CallEnv} {cd : Straight Map} (hc : finishLUCM (S := S) env nm = some cd) (N : Needs) :
    cd.need = NeedOrd.this ∧ BellContract lib N bl true cd :=
  finishLUC_bellContractCallTreeA (S := S) (Map := Map) h (by rw [← finishLUCM_eq env h.noDirect]; exact hc) N

/-- **The bell contract of `TopTree` on the real whole-subject code.** -/
theorem finishLUCM_bellContractTopTree {lib : Lib} {bl : Bell} {nm : Nomm} (h : TopTree bl.fol nm)
    {env : CallEnv} {cd : Straight Map} (hc : finishLUCM (S := S) env nm = some cd) (N : Needs) :
    cd.need = NeedOrd.this ∧ BellContract lib N bl true cd :=
  finishLUC_bellContractTopTree (S := S) (Map := Map) h (by rw [← finishLUCM_eq env h.noDirect]; exact hc) N

/-- **The contract on `NC` on the real whole-subject code.** -/
theorem finishLUCM_contractNC {lib : Lib} {code : Bell → Option Nomm} (hok : CodeOK lib code) {bl : Bell}
    {lv : Nat} {t : Bool} {nm : Nomm} (hA : Annot lib code (SkaModel.Fits bl.less) bl.fol nm)
    (hf : NC (S := S) lv t nm) (hcount : sixCount nm ≤ 255) {env : CallEnv} {cd : Straight Map}
    (h : finishLUCM (S := S) env nm = some cd) (N : Needs) : cd.need = NeedOrd.this ∧ BellContract lib N bl true cd :=
  finishLUC_contractNC hok hA hf hcount (by rw [← finishLUCM_eq env hf.noDirect]; exact h) N

end Comp
end SkaModel
end Formalization
