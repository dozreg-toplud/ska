import lemmas.Ska.CompHintReg
import lemmas.Ska.CompHintSpotEx

/-!
# Nested spots and spots under `%next`, the dumped cases (README Gaps 24.17)

* `d10` `[11 [%spot [1 0]] [11 [%spot [1 1]] [4 [0 3]]]]` (a spot over a
  spot): `contract_d10` (`regGBT_n11dKept` for the inner, `n11dKept_doneR`
  for the outer).
* `d19` `[4 [11 [%spot [1 0]] [4 [0 3]]]]` (a spot under the `%next` goal of
  a `%4`): `contract_d19` (`four_doneR`).
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

def exD19K : Nomm := Nomm.n11d tagSpot (Nomm.n1 (A 0)) exD10Q exD10QF
def exD19KF : Noun := n3 (A 11) (C (A tagSpot) (quote (A 0))) exD10QF
def exD19 : Nomm := Nomm.n4 exD19K
def exD19F : Noun := n2 (A 4) exD19KF

#guard dumped "d19" == some (exD19.toNoun, exD19F)
#guard (finishLUCH (S := LS) (Map := FM) envH sndH exD19).isSome

section
variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The contract at the top of the dumped `d19`**,
`[4 [11 [%spot [1 0]] [4 [0 3]]]]`: a spot under the `%next` goal of a
`%4` (`regGBT_n11dKept`, `four_doneR`). -/
theorem contract_d19 (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) {c : Straight Map}
    (hsq : snd exD10Q NeedOrd.this = true) (hc : finishLUCH (S := S) env snd exD19 = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s exD19F [s] c ∧ ContractBwd lib N s exD19F [s] c := by
  have hq : CallTreeHU lib env N (fun _ => True) false exD10QF exD10Q :=
    CallTreeHU.four (b1 := true) (CallTreeHU.base (CallTreeD.n0 3) rfl)
  have RQ : RegGBT (S := S) (Map := Map) snd lib N env (fun _ => True) exD10QF exD10Q := RegGBT.of_loksf
    (lokSHU_callTreeHU (S := S) (Map := Map) (snd := snd) lib env hq).1.1 (by decide)
  have RK : RegGBT (S := S) (Map := Map) snd lib N env (fun _ => True) exD19KF exD19K := regGBT_n11dKept RQ hsq
    (clueLOKS_n1 lib env _ (A 0)) (by decide) (noBondH_n1 (A 0)) spot_dynamic spot_stop exD10QF
  have H := finishLUCH_contractGBT (S := S) (snd := snd) lib N (fun hr => four_doneR lib RK
    (minkC4_four lib _ exD19KF) (by simp [gen0]) rfl upBelow_gen0 clear_gen0 condBelow_gen0 hr) hc
  exact ⟨H.1, fun s => H.2 s trivial⟩

end

/-! ## The table of the 39 at the top -/

/-- A kept dynamic `stopTag` hint in `RegGBT`: the clue as `keptIn`'s, the
formula a member of the frame case or itself such a hint (`regGBT_n11dKept`,
nested at any depth). -/
def keptR : Nomm → Bool
  | Nomm.n11d tag h q _ => hintDynamic tag && stopTag tag && clueIn h &&
      ((frameFormInS q && (outReason q).isNone) || keptR q)
  | _ => false

/-- `outReasonSpot` with nested kept hints (`n11dKept_doneR`) and a kept
hint under a `%4` (`four_doneR`). -/
def outReasonReg (nm : Nomm) : Option String :=
  match nm with
  | Nomm.n11d _ _ _ _ => if keptR nm then Option.none else outReasonSpot nm
  | Nomm.n4 p => if keptR p then Option.none else outReasonSpot nm
  | _ => outReasonSpot nm

def reasonsReg : List (String × Option String) :=
  HintData.all.map fun (n, j) => (n, ((parts j).bind fun (nmN, _, _, _) => nommOf 300 nmN).bind outReasonReg)

#guard (reasonsReg.filter fun r => r.2.isNone).map Prod.fst ==
  ["s01", "s02", "s03", "s06", "d01", "d02", "d06", "d08", "d10", "d14", "d19", "d21", "d23", "m01"]

end Comp
end SkaModel
end Formalization
