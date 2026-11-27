import lemmas.Ska.CompHintTreeU
import lemmas.Ska.CompHintTreeEx

/-!
# The dumped formulas in `CallTreeHU` (README Gaps 24.13)

* `s02` `[11 %spot [0 3]]`, `s03` `[11 %foo [4 [0 3]]]`, `d06` `[11 [%foo [1
  7]] [4 [0 3]]]`: members of `CallTreeHU` (`callTreeHU_s02` and the rest),
  their nomm and formula `#guard`ed equal to the dump's, `finishLUCH` of each
  `some`, and their contracts at the top (`contract_s02` and the rest).
* `outReason`: the first thing of a nomm the class has no constructor for
  (a syntactic test; the semantic premise `ClueSafe` holds of the constant
  clues of the dump, `ClueSafe.quote`).  `#guard`: of the 39 dumped
  formulas exactly `s02`, `s03`, `d06` have none, and the reason of each
  other one is the table of README Gaps 24.13.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

/-- `%spot`, a tag `hint-dynamic` but not `hint-static`. -/
def tagSpot : Nat := 1953460339
theorem spot_static : hintStatic tagSpot = false := by decide

def exS02 : Nomm := Nomm.n11s tagSpot (Nomm.n0 3) (slot 3)
def exS02F : Noun := n3 (A 11) (A tagSpot) (slot 3)
def exS03 : Nomm := Nomm.n11s tagFoo (Nomm.n4 (Nomm.n0 3)) (n2 (A 4) (slot 3))
def exS03F : Noun := n3 (A 11) (A tagFoo) (n2 (A 4) (slot 3))
def exD06 : Nomm := Nomm.n11d tagFoo (Nomm.n1 (A 7)) (Nomm.n4 (Nomm.n0 3)) (n2 (A 4) (slot 3))
def exD06F : Noun := n3 (A 11) (C (A tagFoo) (C (A 1) (A 7))) (n2 (A 4) (slot 3))

/-- The nomm and the formula of a dumped case. -/
def dumped (n : String) : Option (Noun × Noun) :=
  ((HintData.all.lookup n).bind parts).map fun (nm, _, _, f) => (nm, f)

#guard dumped "s02" == some (exS02.toNoun, exS02F)
#guard dumped "s03" == some (exS03.toNoun, exS03F)
#guard dumped "d06" == some (exD06.toNoun, exD06F)
#guard (finishLUCH (S := LS) (Map := FM) envH sndH exS02).isSome
#guard (finishLUCH (S := LS) (Map := FM) envH sndH exS03).isSome
#guard (finishLUCH (S := LS) (Map := FM) envH sndH exD06).isSome

section
variable {lib : Lib} {env : CallEnv} {N : Needs}

theorem callTreeHU_s02 (P : Noun → Prop) : CallTreeHU lib env N P true exS02F exS02 :=
  CallTreeHU.n11s (slot 3) (CallTreeHU.base (CallTreeD.n0 3) rfl) spot_static

theorem callTreeHU_s03 (P : Noun → Prop) : CallTreeHU lib env N P false exS03F exS03 :=
  CallTreeHU.n11s _ (CallTreeHU.base (CallTreeD.four (CallTreeD.n0 3)) rfl) foo_static

theorem callTreeHU_d06 (P : Noun → Prop) : CallTreeHU lib env N P false exD06F exD06 :=
  CallTreeHU.n11d _ (CallTreeHU.base (CallTreeD.four (CallTreeD.n0 3)) rfl) foo_dynamic rfl
    (ClueSafe.quote lib P (A 7)) rfl rfl

end

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The contract at the top of the dumped `s02`**, `[11 %spot [0 3]]`. -/
theorem contract_s02 (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) {c : Straight Map}
    (hc : finishLUCH (S := S) env snd exS02 = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s exS02F [s] c ∧ ContractBwd lib N s exS02F [s] c := by
  have H := finishLUCH_contractCallTreeHU (S := S) lib (callTreeHU_s02 (env := env) (N := N) (fun _ => True)) hc
  exact ⟨H.1, fun s => H.2 s trivial⟩

/-- **The contract at the top of the dumped `s03`**, `[11 %foo [4 [0 3]]]`. -/
theorem contract_s03 (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) {c : Straight Map}
    (hc : finishLUCH (S := S) env snd exS03 = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s exS03F [s] c ∧ ContractBwd lib N s exS03F [s] c := by
  have H := finishLUCH_contractCallTreeHU (S := S) lib (callTreeHU_s03 (env := env) (N := N) (fun _ => True)) hc
  exact ⟨H.1, fun s => H.2 s trivial⟩

/-- **The contract at the top of the dumped `d06`**, `[11 [%foo [1 7]] [4 [0 3]]]`. -/
theorem contract_d06 (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) {c : Straight Map}
    (hc : finishLUCH (S := S) env snd exD06 = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s exD06F [s] c ∧ ContractBwd lib N s exD06F [s] c := by
  have H := finishLUCH_contractCallTreeHU (S := S) lib (callTreeHU_d06 (env := env) (N := N) (fun _ => True)) hc
  exact ⟨H.1, fun s => H.2 s trivial⟩

/-! ## The table -/

/-- The first part of a nomm (left to right) the class has no constructor
for; `none` when it has one for every part. -/
def outReason : Nomm → Option String
  | Nomm.n0 _ => Option.none
  | Nomm.n1 _ => Option.none
  | Nomm.cons p q => (outReason p).orElse fun _ => outReason q
  | Nomm.n7 p q => (outReason p).orElse fun _ => outReason q
  | Nomm.n5 p q => (outReason p).orElse fun _ => outReason q
  | Nomm.n3 p => outReason p
  | Nomm.n4 p => outReason p
  | Nomm.n2 p q Option.none => (outReason p).orElse fun _ => outReason q
  | Nomm.n2 _ _ (some _) => some "direct call (CallTreeD: only without hints)"
  | Nomm.n6 _ _ _ => some "%6"
  | Nomm.n10 _ _ _ => some "%10"
  | Nomm.n11s tag q _ => if hintStatic tag then some "kept static tag" else outReason q
  | Nomm.n11d tag h q _ =>
      if hintDynamic tag then some (if stopTag tag then "kept dynamic stopTag tag" else "kept dynamic tag")
      else if !safeNomm h then some "unsafe clue" else outReason q
  | Nomm.mean _ _ _ _ _ => some "%mean"
  | Nomm.n12 _ _ => some "%12"

/-- The reason of each dumped case (`none`: in the class). -/
def reasons : List (String × Option String) :=
  HintData.all.map fun (n, j) => (n, ((parts j).bind fun (nmN, _, _, _) => nommOf 300 nmN).bind outReason)

#guard (reasons.filter fun r => r.2.isNone).map Prod.fst == ["s02", "s03", "d06"]
#guard reasons == [("s01", some "kept static tag"), ("s02", none), ("s03", none), ("s04", some "kept static tag"),
  ("s05", some "kept static tag"), ("s06", some "kept static tag"), ("s07", some "kept static tag"),
  ("d01", some "kept dynamic stopTag tag"), ("d02", some "kept dynamic stopTag tag"),
  ("d03", some "kept dynamic tag"), ("d04", some "unsafe clue"), ("d05", some "unsafe clue"), ("d06", none),
  ("d07", some "unsafe clue"), ("d08", some "kept dynamic stopTag tag"), ("d09", some "kept dynamic tag"),
  ("d10", some "kept dynamic stopTag tag"), ("d11", some "kept dynamic stopTag tag"),
  ("d12", some "kept dynamic stopTag tag"), ("d13", some "kept dynamic stopTag tag"),
  ("d14", some "kept dynamic stopTag tag"), ("d15", some "kept dynamic stopTag tag"), ("d16", some "%6"),
  ("d17", some "%6"), ("d18", some "kept dynamic stopTag tag"), ("d19", some "kept dynamic stopTag tag"),
  ("d20", some "%10"), ("d21", some "kept dynamic stopTag tag"), ("d22", some "kept dynamic stopTag tag"),
  ("d23", some "kept dynamic stopTag tag"), ("m01", some "kept dynamic stopTag tag"), ("m02", some "%mean"), ("m03", some "%mean"),
  ("m04", some "%mean"), ("c01", some "%12"), ("c02", some "%12"), ("c03", some "%12"), ("c04", some "%12"),
  ("c05", some "%12")]

end Comp
end SkaModel
end Formalization
