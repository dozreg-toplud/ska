import lemmas.Ska.CompHintSpot
import lemmas.Ska.CompHintFrameEx

/-!
# Spots around calls and in sequence, the dumped cases (README Gaps 24.16)

* `d21` `[11 [%spot [1 0]] [2 [0 3] [0 2]]]` (a spot around an indirect
  call): `contract_d21` (`noBondH_n2_none`).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

def exD21Q : Nomm := Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none
def exD21 : Nomm := Nomm.n11d tagSpot (Nomm.n1 (A 0)) exD21Q (n3 (A 2) (slot 3) (slot 2))
def exD21F : Noun := n3 (A 11) (C (A tagSpot) (quote (A 0))) (n3 (A 2) (slot 3) (slot 2))

#guard dumped "d21" == some (exD21.toNoun, exD21F)
#guard (finishLUCH (S := LS) (Map := FM) envH sndH exD21).isSome
#guard sndH exD21Q NeedOrd.this

def exD14Q : Nomm := Nomm.n4 (Nomm.n0 1)
def exD14 : Nomm := Nomm.n7 (Nomm.n0 3) (Nomm.n11d tagSpot (Nomm.n0 1) exD14Q (n2 (A 4) (slot 1)))
def exD14F : Noun := n3 (A 7) (slot 3) (n3 (A 11) (C (A tagSpot) (slot 1)) (n2 (A 4) (slot 1)))

#guard dumped "d14" == some (exD14.toNoun, exD14F)
#guard (finishLUCH (S := LS) (Map := FM) envH sndH exD14).isSome
#guard sndH exD14Q NeedOrd.this

section
variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

theorem callTreeHU_ind32 {lib : Lib} {env : CallEnv} {N : Needs} :
    CallTreeHU lib env N (fun _ => True) true (n3 (A 2) (slot 3) (slot 2)) exD21Q :=
  CallTreeHU.ind (b1 := true) (b2 := true) (CallTreeHU.base (CallTreeD.n0 3) rfl) (CallTreeHU.base (CallTreeD.n0 2) rfl)

/-- **The contract at the top of the dumped `d21`**, `[11 [%spot [1 0]] [2 [0 3] [0 2]]]`:
a spot around an indirect call. -/
theorem contract_d21 (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) {c : Straight Map}
    (hsnd : snd exD21Q NeedOrd.this = true) (hc : finishLUCH (S := S) env snd exD21 = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s exD21F [s] c ∧ ContractBwd lib N s exD21F [s] c := by
  have H := finishLUCH_contractN11dKeptHU (S := S) (N := N) lib callTreeHU_ind32
    (noBondH_n2_none (noBondH_n0 3) (noBondH_n0 2) (by simp [hinted])) hsnd
    (clueLOKS_n1 lib env _ (A 0)) (by decide) (noBondH_n1 (A 0)) spot_dynamic spot_stop _ hc
  exact ⟨H.1, fun s => H.2 s trivial⟩

/-- **The contract at the top of the dumped `d14`**, `[7 [0 3] [11 [%spot [0 1]] [4 [0 1]]]]`:
a spot after a step of a sequence (`doneAllT_seven`). -/
theorem contract_d14 (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) {c : Straight Map}
    (hsnd : snd exD14Q NeedOrd.this = true) (hc : finishLUCH (S := S) env snd exD14 = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s exD14F [s] c ∧ ContractBwd lib N s exD14F [s] c := by
  have hq : CallTreeHU lib env N (Img lib (fun _ => True) (slot 3)) false (n2 (A 4) (slot 1)) exD14Q :=
    CallTreeHU.four (b1 := true) (CallTreeHU.base (CallTreeD.n0 1) rfl)
  have H := finishLUCH_contractDoneAllT (S := S) (Map := Map) (snd := snd) (N := N) lib
    (doneAllT_seven lib env callTreeHU_n0_3
      (doneAllT_n11dKept (lokSHU_callTreeHU (S := S) (Map := Map) (snd := snd) lib env hq).1.1 (by decide)
        (noBondH_n4 (noBondH_n0 1)) hsnd (clueLOKS_n0 lib env _ 1) (by decide) (noBondH_n0 1)
        spot_dynamic spot_stop _)) hc
  exact ⟨H.1, fun s => H.2 s trivial⟩

end

end Comp
end SkaModel
end Formalization
