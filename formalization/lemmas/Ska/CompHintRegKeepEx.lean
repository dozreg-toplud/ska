import lemmas.Ska.CompHintRegKeep
import lemmas.Ska.CompHintRegEx

/-!
# `RegGBT` under `%4`, kept static hints, quiet dynamic tags: the dumped cases (README Gaps 24.18)

* `s05` `[4 [11 %xray [0 3]]]` (a kept static hint under a `%4`):
  `contract_s05` (`regGBT_n11sKept`, `four_doneR`).
* `d03` `[11 [%slog [1 0 %foo]] [0 3]]`, `d09` `[11 [%xray [0 2]] [4 [0 3]]]`
  (kept dynamic tags that push nothing): `contract_d03`, `contract_d09`
  (`finishLUCH_contractN11dQuietR`; `d09`'s formula through `regGBT_four`).
* `spotArm`'s position 4 with `S3` replaced by `S4` (the largest part of
  `spotArm` in `RegGBT`): `regGBT_spotArm4`, `contract_spotArm4`.
* `outReasonOps`, the table of the 39 at the top (`#guard`: 17 in).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

def tagXray : Nat := HintTag.xray
def tagSlog : Nat := HintTag.slog
theorem xray_static : hintStatic tagXray = true := by decide
theorem xray_dynamic : hintDynamic tagXray = true := by decide
theorem xray_quiet : stopTag tagXray = false := by decide
theorem slog_dynamic : hintDynamic tagSlog = true := by decide
theorem slog_quiet : stopTag tagSlog = false := by decide

def exS05K : Nomm := Nomm.n11s tagXray (Nomm.n0 3) (slot 3)
def exS05KF : Noun := n3 (A 11) (A tagXray) (slot 3)
def exS05 : Nomm := Nomm.n4 exS05K
def exS05F : Noun := n2 (A 4) exS05KF

#guard dumped "s05" == some (exS05.toNoun, exS05F)
#guard (finishLUCH (S := LS) (Map := FM) envH sndH exS05).isSome
#guard sndH (Nomm.n0 3) NeedOrd.this

def exKFoo : Noun := C (A 0) (A 0x6f6f66)
def exD03 : Nomm := Nomm.n11d tagSlog (Nomm.n1 exKFoo) (Nomm.n0 3) (slot 3)
def exD03F : Noun := n3 (A 11) (C (A tagSlog) (quote exKFoo)) (slot 3)

#guard dumped "d03" == some (exD03.toNoun, exD03F)
#guard (finishLUCH (S := LS) (Map := FM) envH sndH exD03).isSome

def exD09 : Nomm := Nomm.n11d tagXray (Nomm.n0 2) (Nomm.n4 (Nomm.n0 3)) (n2 (A 4) (slot 3))
def exD09F : Noun := n3 (A 11) (C (A tagXray) (slot 2)) (n2 (A 4) (slot 3))

#guard dumped "d09" == some (exD09.toNoun, exD09F)
#guard (finishLUCH (S := LS) (Map := FM) envH sndH exD09).isSome
#guard sndH (Nomm.n4 (Nomm.n0 3)) NeedOrd.this

section
variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The contract at the top of the dumped `s05`**, `[4 [11 %xray [0 3]]]`:
a kept static hint under the `%next` goal of a `%4`. -/
theorem contract_s05 (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) {c : Straight Map}
    (hsq : snd (Nomm.n0 3) NeedOrd.this = true) (hc : finishLUCH (S := S) env snd exS05 = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s exS05F [s] c ∧ ContractBwd lib N s exS05F [s] c := by
  have RQ : RegGBT (S := S) (Map := Map) snd lib N env (fun _ => True) (slot 3) (Nomm.n0 3) :=
    RegGBT.of_loksf (clueLOKS_n0 lib env _ 3) (by decide)
  have RK : RegGBT (S := S) (Map := Map) snd lib N env (fun _ => True) exS05KF exS05K :=
    regGBT_n11sKept RQ hsq xray_static (slot 3)
  have H := finishLUCH_contractGBT (S := S) (snd := snd) lib N (fun hr => four_doneR lib RK
    (minkC4_four lib _ exS05KF) (by simp [gen0]) rfl upBelow_gen0 clear_gen0 condBelow_gen0 hr) hc
  exact ⟨H.1, fun s => H.2 s trivial⟩

/-- **The contract at the top of the dumped `d03`**, `[11 [%slog [1 0 %foo]] [0 3]]`. -/
theorem contract_d03 (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) {c : Straight Map}
    (hsq : snd (Nomm.n0 3) NeedOrd.this = true) (hc : finishLUCH (S := S) env snd exD03 = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s exD03F [s] c ∧ ContractBwd lib N s exD03F [s] c := by
  have RQ : RegGBT (S := S) (Map := Map) snd lib N env (fun _ => True) (slot 3) (Nomm.n0 3) :=
    RegGBT.of_loksf (clueLOKS_n0 lib env _ 3) (by decide)
  have H := finishLUCH_contractN11dQuietR (S := S) (N := N) lib RQ hsq (clueLOKS_n1 lib env _ exKFoo) (by decide)
    (noBondH_n1 exKFoo) slog_dynamic slog_quiet (slot 3) hc
  exact ⟨H.1, fun s => H.2 s trivial⟩

/-- **The contract at the top of the dumped `d09`**, `[11 [%xray [0 2]] [4 [0 3]]]`
(the formula in `RegGBT` through `regGBT_four`). -/
theorem contract_d09 (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) {c : Straight Map}
    (hsq : snd (Nomm.n4 (Nomm.n0 3)) NeedOrd.this = true) (hc : finishLUCH (S := S) env snd exD09 = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s exD09F [s] c ∧ ContractBwd lib N s exD09F [s] c := by
  have RQ : RegGBT (S := S) (Map := Map) snd lib N env (fun _ => True) (n2 (A 4) (slot 3)) (Nomm.n4 (Nomm.n0 3)) :=
    regGBT_four (RegGBT.of_loksf (clueLOKS_n0 lib env _ 3) (by decide)) (minkC4_four lib _ (slot 3))
  have H := finishLUCH_contractN11dQuietR (S := S) (N := N) lib RQ hsq (clueLOKS_n0 lib env _ 2) (by decide)
    (noBondH_n0 2) xray_dynamic xray_quiet (n2 (A 4) (slot 3)) hc
  exact ⟨H.1, fun s => H.2 s trivial⟩

/-! ## `spotArm`, position 4 with `S3` replaced by `S4` -/

/-- `S4` of `spotArm` (`CompRunHintCallEx.lean`), its clue `k4` (there
`spotK 108 42 108 45`). -/
def spotS4 (k4 : Noun) : Nomm := Nomm.n11d tagSpot (Nomm.n1 k4) (Nomm.n0 13) (C (A 0) (A 13))
def spotS4F (k4 : Noun) : Noun := n3 (A 11) (C (A tagSpot) (quote k4)) (slot 13)
/-- `S2` of `spotArm` with `S3` replaced by `S4`: `[spot [4 S4]]`, its clue
`k2` (there `spotK 108 36 108 47`), the kept formula `B` any. -/
def spotS2' (k2 k4 B : Noun) : Nomm := Nomm.n11d tagSpot (Nomm.n1 k2) (Nomm.n4 (spotS4 k4)) B
def spotS2'F (k2 k4 : Noun) : Noun := n3 (A 11) (C (A tagSpot) (quote k2)) (n2 (A 4) (spotS4F k4))

/-- **`S4` and `[spot [4 S4]]` are in `RegGBT`** (`regGBT_n11dKept`,
`regGBT_four`, `regGBT_n11dKept`): position 4 of `spotArm` is proved for
any operand of the `%4` in `RegGBT`, here `S4`. -/
theorem regGBT_spotArm4 (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) (k2 k4 B : Noun)
    (h13 : snd (Nomm.n0 13) NeedOrd.this = true) (h4 : snd (Nomm.n4 (spotS4 k4)) NeedOrd.this = true) :
    RegGBT (S := S) (Map := Map) snd lib N env (fun _ => True) (spotS4F k4) (spotS4 k4) ∧
      RegGBT (S := S) (Map := Map) snd lib N env (fun _ => True) (spotS2'F k2 k4) (spotS2' k2 k4 B) := by
  have R13 : RegGBT (S := S) (Map := Map) snd lib N env (fun _ => True) (slot 13) (Nomm.n0 13) :=
    RegGBT.of_loksf (clueLOKS_n0 lib env _ 13) (by decide)
  have R4 : RegGBT (S := S) (Map := Map) snd lib N env (fun _ => True) (spotS4F k4) (spotS4 k4) :=
    regGBT_n11dKept R13 h13 (clueLOKS_n1 lib env _ k4) (by simp [sixCount]) (noBondH_n1 k4) spot_dynamic spot_stop _
  exact ⟨R4, regGBT_n11dKept (regGBT_four R4 (minkC4_four lib _ (spotS4F k4))) h4 (clueLOKS_n1 lib env _ k2)
    (by simp [sixCount]) (noBondH_n1 k2) spot_dynamic spot_stop B⟩

/-- **The contract at the top of `[spot [4 S4]]`**, both halves, traces
included. -/
theorem contract_spotArm4 (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) (k2 k4 B : Noun)
    (h13 : snd (Nomm.n0 13) NeedOrd.this = true) (h4 : snd (Nomm.n4 (spotS4 k4)) NeedOrd.this = true)
    (h2 : snd (spotS2' k2 k4 B) NeedOrd.this = true) {c : Straight Map}
    (hc : finishLUCH (S := S) env snd (spotS2' k2 k4 B) = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s (spotS2'F k2 k4) [s] c ∧
      ContractBwd lib N s (spotS2'F k2 k4) [s] c := by
  have R4 : RegGBT (S := S) (Map := Map) snd lib N env (fun _ => True) (spotS4F k4) (spotS4 k4) :=
    (regGBT_spotArm4 (S := S) (Map := Map) lib env snd N k2 k4 B h13 h4).1
  have H := finishLUCH_contractN11dKeptR (S := S) (N := N) lib (regGBT_four R4 (minkC4_four lib _ (spotS4F k4))) h4
    (clueLOKS_n1 lib env _ k2) (by simp [sixCount]) (noBondH_n1 k2) spot_dynamic spot_stop B hc
  exact ⟨H.1, fun s => H.2 s trivial⟩

end

#guard sndH (Nomm.n0 13) NeedOrd.this
#guard sndH (Nomm.n4 (spotS4 (C (A 0) (C (C (A 108) (A 42)) (C (A 108) (A 45)))))) NeedOrd.this
#guard (finishLUCH (S := LS) (Map := FM) envH sndH
  (spotS2' (C (A 0) (C (C (A 108) (A 36)) (C (A 108) (A 47)))) (C (A 0) (C (C (A 108) (A 42)) (C (A 108) (A 45))))
    (spotS2'F (C (A 0) (C (C (A 108) (A 36)) (C (A 108) (A 47)))) (C (A 0) (C (C (A 108) (A 42)) (C (A 108) (A 45))))))).isSome

/-! ## The table of the 39 at the top -/

/-- A member of `RegGBT` by the constructors proved so far: a member of the
frame case, a kept dynamic hint (`stopTag` or quiet) with a clue as
`keptIn`'s over a member, a kept static hint over a member, `[4 p]` and
`[3 p]` over a member. -/
def regIn : Nomm → Bool
  | Nomm.n11d tag h q _ => hintDynamic tag && clueIn h && regIn q
  | Nomm.n11s tag q _ => hintStatic tag && regIn q
  | Nomm.n4 p => regIn p
  | Nomm.n3 p => regIn p
  | nm => frameFormInS nm && (outReason nm).isNone

/-- `outReasonReg` with every member of `RegGBT` at the top under a kept
dynamic hint (`finishLUCH_contractN11dKeptR`, `finishLUCH_contractN11dQuietR`)
or under `%4` (`four_doneR`). -/
def outReasonOps (nm : Nomm) : Option String :=
  match nm with
  | Nomm.n11d tag _ _ _ => if hintDynamic tag && regIn nm then Option.none else outReasonReg nm
  | Nomm.n4 p => if regIn p then Option.none else outReasonReg nm
  | _ => outReasonReg nm

def reasonsOps : List (String × Option String) :=
  HintData.all.map fun (n, j) => (n, ((parts j).bind fun (nmN, _, _, _) => nommOf 300 nmN).bind outReasonOps)

#guard (reasonsOps.filter fun r => r.2.isNone).map Prod.fst ==
  ["s01", "s02", "s03", "s05", "s06", "d01", "d02", "d03", "d06", "d08", "d09", "d10", "d14", "d19", "d21", "d23",
    "m01"]

end Comp
end SkaModel
end Formalization
