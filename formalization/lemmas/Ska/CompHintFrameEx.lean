import lemmas.Ska.CompHintFrame
import lemmas.Ska.CompHintKeepEx
import lemmas.Ska.CompHintFrameCheck

/-!
# The dumped kept dynamic `stopTag` hints at the top (README Gaps 24.15)

* `d01` `[11 [%spot [1 [1 2] 3]] [0 3]]`, `d02` `[11 [%spot [0 2]] [4 [0 3]]]`,
  `d08` `[11 [%hunk [0 2]] [4 [0 3]]]`, `d23` `[11 [%spot [0 6]] [0 3]]`,
  `m01` `[11 [%mean [1 [1 %leaf 120]]] [4 [0 3]]]`: their nomm and formula
  `#guard`ed equal to the dump's, and their contracts at the top, traces
  included (`contract_d01` and the rest), for any `snd` with `+sound` of
  `%this` true on the formula (`sndH` has it, `#guard`).
* `outReasonFrame`: the table of the 39 at the top with these in
  (`#guard`: 10 in).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

theorem spot_dynamic : hintDynamic tagSpot = true := by decide
theorem spot_stop : stopTag tagSpot = true := by decide
theorem hunk_dynamic : hintDynamic Tag.hunk = true := by decide
theorem hunk_stop : stopTag Tag.hunk = true := by decide
theorem mean_dynamic : hintDynamic Tag.mean = true := by decide
theorem mean_stop : stopTag Tag.mean = true := by decide

def exK01 : Noun := C (C (A 1) (A 2)) (A 3)
def exD01 : Nomm := Nomm.n11d tagSpot (Nomm.n1 exK01) (Nomm.n0 3) (slot 3)
def exD01F : Noun := n3 (A 11) (C (A tagSpot) (quote exK01)) (slot 3)
def exD02 : Nomm := Nomm.n11d tagSpot (Nomm.n0 2) (Nomm.n4 (Nomm.n0 3)) (n2 (A 4) (slot 3))
def exD02F : Noun := n3 (A 11) (C (A tagSpot) (slot 2)) (n2 (A 4) (slot 3))
def exD08 : Nomm := Nomm.n11d Tag.hunk (Nomm.n0 2) (Nomm.n4 (Nomm.n0 3)) (n2 (A 4) (slot 3))
def exD08F : Noun := n3 (A 11) (C (A Tag.hunk) (slot 2)) (n2 (A 4) (slot 3))
def exD23 : Nomm := Nomm.n11d tagSpot (Nomm.n0 6) (Nomm.n0 3) (slot 3)
def exD23F : Noun := n3 (A 11) (C (A tagSpot) (slot 6)) (slot 3)
def exKM1 : Noun := C (A 1) (C (A 1717658988) (A 120))
def exM01 : Nomm := Nomm.n11d Tag.mean (Nomm.n1 exKM1) (Nomm.n4 (Nomm.n0 3)) (n2 (A 4) (slot 3))
def exM01F : Noun := n3 (A 11) (C (A Tag.mean) (quote exKM1)) (n2 (A 4) (slot 3))

#guard dumped "d01" == some (exD01.toNoun, exD01F)
#guard dumped "d02" == some (exD02.toNoun, exD02F)
#guard dumped "d08" == some (exD08.toNoun, exD08F)
#guard dumped "d23" == some (exD23.toNoun, exD23F)
#guard dumped "m01" == some (exM01.toNoun, exM01F)
#guard [exD01, exD02, exD08, exD23, exM01].all fun nm => (finishLUCH (S := LS) (Map := FM) envH sndH nm).isSome
#guard sndH (Nomm.n0 3) NeedOrd.this && sndH (Nomm.n4 (Nomm.n0 3)) NeedOrd.this

section
variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

theorem callTreeHU_n0_3 {lib : Lib} {env : CallEnv} {N : Needs} :
    CallTreeHU lib env N (fun _ => True) true (slot 3) (Nomm.n0 3) :=
  CallTreeHU.base (CallTreeD.n0 3) rfl

theorem callTreeHU_four3 {lib : Lib} {env : CallEnv} {N : Needs} :
    CallTreeHU lib env N (fun _ => True) false (n2 (A 4) (slot 3)) (Nomm.n4 (Nomm.n0 3)) :=
  CallTreeHU.four (CallTreeHU.base (CallTreeD.n0 3) rfl)

/-- **The contract at the top of the dumped `d01`**, `[11 [%spot [1 [1 2] 3]] [0 3]]`. -/
theorem contract_d01 (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) {c : Straight Map}
    (hsnd : snd (Nomm.n0 3) NeedOrd.this = true) (hc : finishLUCH (S := S) env snd exD01 = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s exD01F [s] c ∧ ContractBwd lib N s exD01F [s] c := by
  have H := finishLUCH_contractN11dKeptHU (S := S) (N := N) lib callTreeHU_n0_3 (noBondH_n0 3) hsnd
    (clueLOKS_n1 lib env _ exK01) (by decide) (noBondH_n1 exK01) spot_dynamic spot_stop (slot 3) hc
  exact ⟨H.1, fun s => H.2 s trivial⟩

/-- **The contract at the top of the dumped `d02`**, `[11 [%spot [0 2]] [4 [0 3]]]`. -/
theorem contract_d02 (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) {c : Straight Map}
    (hsnd : snd (Nomm.n4 (Nomm.n0 3)) NeedOrd.this = true) (hc : finishLUCH (S := S) env snd exD02 = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s exD02F [s] c ∧ ContractBwd lib N s exD02F [s] c := by
  have H := finishLUCH_contractN11dKeptHU (S := S) (N := N) lib callTreeHU_four3 (noBondH_n4 (noBondH_n0 3)) hsnd
    (clueLOKS_n0 lib env _ 2) (by decide) (noBondH_n0 2) spot_dynamic spot_stop _ hc
  exact ⟨H.1, fun s => H.2 s trivial⟩

/-- **The contract at the top of the dumped `d08`**, `[11 [%hunk [0 2]] [4 [0 3]]]`. -/
theorem contract_d08 (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) {c : Straight Map}
    (hsnd : snd (Nomm.n4 (Nomm.n0 3)) NeedOrd.this = true) (hc : finishLUCH (S := S) env snd exD08 = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s exD08F [s] c ∧ ContractBwd lib N s exD08F [s] c := by
  have H := finishLUCH_contractN11dKeptHU (S := S) (N := N) lib callTreeHU_four3 (noBondH_n4 (noBondH_n0 3)) hsnd
    (clueLOKS_n0 lib env _ 2) (by decide) (noBondH_n0 2) hunk_dynamic hunk_stop _ hc
  exact ⟨H.1, fun s => H.2 s trivial⟩

/-- **The contract at the top of the dumped `d23`**, `[11 [%spot [0 6]] [0 3]]`. -/
theorem contract_d23 (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) {c : Straight Map}
    (hsnd : snd (Nomm.n0 3) NeedOrd.this = true) (hc : finishLUCH (S := S) env snd exD23 = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s exD23F [s] c ∧ ContractBwd lib N s exD23F [s] c := by
  have H := finishLUCH_contractN11dKeptHU (S := S) (N := N) lib callTreeHU_n0_3 (noBondH_n0 3) hsnd
    (clueLOKS_n0 lib env _ 6) (by decide) (noBondH_n0 6) spot_dynamic spot_stop (slot 3) hc
  exact ⟨H.1, fun s => H.2 s trivial⟩

/-- **The contract at the top of the dumped `m01`**, `[11 [%mean [1 [1 %leaf 120]]] [4 [0 3]]]`
(a `%mean` whose clue is safe is `n11d %mean`). -/
theorem contract_m01 (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) {c : Straight Map}
    (hsnd : snd (Nomm.n4 (Nomm.n0 3)) NeedOrd.this = true) (hc : finishLUCH (S := S) env snd exM01 = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s exM01F [s] c ∧ ContractBwd lib N s exM01F [s] c := by
  have H := finishLUCH_contractN11dKeptHU (S := S) (N := N) lib callTreeHU_four3 (noBondH_n4 (noBondH_n0 3)) hsnd
    (clueLOKS_n1 lib env _ exKM1) (by decide) (noBondH_n1 exKM1) mean_dynamic mean_stop _ hc
  exact ⟨H.1, fun s => H.2 s trivial⟩

end

/-! ## The table of the 39 at the top -/

/-- A clue the frame case takes (`clueLOKS_n0`, `clueLOKS_n1`). -/
def clueIn : Nomm → Bool
  | Nomm.n0 _ => true
  | Nomm.n1 _ => true
  | _ => false

/-- A formula the frame case takes: the members of `CallTreeHU` whose
`NoBondH` is proved (`[0 a]`, `[4 p]`, `[7 p q]` over them). -/
def frameFormIn : Nomm → Bool
  | Nomm.n0 _ => true
  | Nomm.n4 p => frameFormIn p
  | Nomm.n7 p q => frameFormIn p && frameFormIn q
  | _ => false

/-- `outReasonTop` with the kept dynamic `stopTag` hint at the top. -/
def outReasonFrame (nm : Nomm) : Option String :=
  match nm with
  | Nomm.n11d tag h q _ =>
      if hintDynamic tag && stopTag tag then
        (if clueIn h && frameFormIn q && (outReason q).isNone then Option.none
         else some "kept dynamic stopTag tag, clue or formula out")
      else outReasonTop nm
  | _ => outReasonTop nm

def reasonsFrame : List (String × Option String) :=
  HintData.all.map fun (n, j) => (n, ((parts j).bind fun (nmN, _, _, _) => nommOf 300 nmN).bind outReasonFrame)

#guard (reasonsFrame.filter fun r => r.2.isNone).map Prod.fst ==
  ["s01", "s02", "s03", "s06", "d01", "d02", "d06", "d08", "d23", "m01"]

end Comp
end SkaModel
end Formalization
