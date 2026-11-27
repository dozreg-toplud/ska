import lemmas.Ska.CompHintReg
import lemmas.Ska.CompHintSpotEx

/-!
# Nested spots and spots under `%next`, the dumped cases (README Gaps 24.17)

* `d10` `[11 [%spot [1 0]] [11 [%spot [1 1]] [4 [0 3]]]]` (a spot over a
  spot): `contract_d10` (`regGBT_n11dKept` for the inner, `n11dKept_doneR`
  for the outer).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

def exD10Q : Nomm := Nomm.n4 (Nomm.n0 3)
def exD10QF : Noun := n2 (A 4) (slot 3)
def exD10IF : Noun := n3 (A 11) (C (A tagSpot) (quote (A 1))) exD10QF
def exD10I : Nomm := Nomm.n11d tagSpot (Nomm.n1 (A 1)) exD10Q exD10QF
def exD10 : Nomm := Nomm.n11d tagSpot (Nomm.n1 (A 0)) exD10I exD10IF
def exD10F : Noun := n3 (A 11) (C (A tagSpot) (quote (A 0))) exD10IF

#guard dumped "d10" == some (exD10.toNoun, exD10F)
#guard (finishLUCH (S := LS) (Map := FM) envH sndH exD10).isSome
#guard sndH exD10Q NeedOrd.this
#guard sndH exD10I NeedOrd.this

section
variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The contract at the top of the dumped `d10`**,
`[11 [%spot [1 0]] [11 [%spot [1 1]] [4 [0 3]]]]`: a spot over a spot. -/
theorem contract_d10 (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) {c : Straight Map}
    (hsq : snd exD10Q NeedOrd.this = true) (hsi : snd exD10I NeedOrd.this = true)
    (hc : finishLUCH (S := S) env snd exD10 = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s exD10F [s] c ∧ ContractBwd lib N s exD10F [s] c := by
  have hq : CallTreeHU lib env N (fun _ => True) false exD10QF exD10Q :=
    CallTreeHU.four (b1 := true) (CallTreeHU.base (CallTreeD.n0 3) rfl)
  have RQ : RegGBT (S := S) (Map := Map) snd lib N env (fun _ => True) exD10QF exD10Q := RegGBT.of_loksf
    (lokSHU_callTreeHU (S := S) (Map := Map) (snd := snd) lib env hq).1.1 (by decide)
  have RI : RegGBT (S := S) (Map := Map) snd lib N env (fun _ => True) exD10IF exD10I := regGBT_n11dKept RQ hsq (clueLOKS_n1 lib env _ (A 1)) (by decide) (noBondH_n1 (A 1))
    spot_dynamic spot_stop exD10QF
  have H := finishLUCH_contractN11dKeptR (S := S) (N := N) lib RI hsi (clueLOKS_n1 lib env _ (A 0)) (by decide)
    (noBondH_n1 (A 0)) spot_dynamic spot_stop exD10IF hc
  exact ⟨H.1, fun s => H.2 s trivial⟩

end

end Comp
end SkaModel
end Formalization
