import lemmas.Ska.CompHintKeep
import lemmas.Ska.CompHintNest

/-!
# `NoBondH` on the model; the dumped kept static hints at the top (README Gaps 24.14)

* `noBondN`: a sufficient syntactic test for `NoBondH` (no `+past` that parks:
  the parts of a cons and of a `%5` are not hinted, no kept hint, no `%2`,
  `%6`, `%10`, `%12`, `mean`).  `#guard`: on the 39 dumped nomms and on 30
  more shapes, wherever `noBondN` holds, the run under three goals with no
  bond (`lazy-from-reg`, a pair of registers, `bunt`) has no fork and no bond.
  Where a bond comes out (of the class's shapes): a cons with a hinted head,
  a cons with a hinted tail (under a goal whose head part asks something:
  `+past` of the head's need over the tail), a `%5` whose first part is
  hinted, a kept hint itself.  The indirect call alone, under `%4`/`%7`, or
  as the second part of a `%5` gives none.
* `s01` `[11 %bout [0 3]]` and `s06` `[11 %bout [7 [0 3] [4 [0 1]]]]`: the
  contract at the top (`contract_s01`, `contract_s06`), for any `snd` whose
  `+sound` of `%this` holds for the formula (`#guard`: `sndH` does).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

namespace HintKeep
open HintNest

/-- A sufficient syntactic test for `NoBondH`. -/
def noBondN (cod : Bell → Option Bool) : Nomm → Bool
  | Nomm.n0 _ => true
  | Nomm.n1 _ => true
  | Nomm.n3 p => noBondN cod p
  | Nomm.n4 p => noBondN cod p
  | Nomm.n7 p q => noBondN cod p && noBondN cod q
  | Nomm.cons p q => hinted cod p == some false && hinted cod q == some false && noBondN cod p && noBondN cod q
  | Nomm.n5 p q => hinted cod p == some false && hinted cod q == some false && noBondN cod p && noBondN cod q
  | Nomm.n11s tag q _ => !hintStatic tag && noBondN cod q
  | Nomm.n11d tag h q _ => !hintDynamic tag && safeNomm h && noBondN cod q
  | _ => false

def gS : Gen FM := { gen0 with re := 5, bo := 3 }
def goals : List (CGoalL LS) :=
  [CGoalL.next (ofSure (lazyReg 0)) (jmp0 1),
   CGoalL.next (ofSure ⟨Need.pair (Need.this 0) (Need.this 1), HoonSet.empty⟩) (jmp0 1),
   CGoalL.next (ofSure Sure.bunt) (jmp0 1)]

/-- The run under each goal: `some true` when it has no fork and no bond. -/
def runFree (nm : Nomm) : List (Option Bool) :=
  goals.map fun g => (runLCH (S := LS) (Map := FM) envH sndH true Option.none nm g [] gS).map fun (nex, _) =>
    nex.laz.fork.isEmpty && nex.laz.bond.isEmpty
def allFree (nm : Nomm) : Bool := (runFree nm).all fun r => r != some false
def anyBond (nm : Nomm) : Bool := (runFree nm).any fun r => r == some false

def ind (p q : Nomm) : Nomm := Nomm.n2 p q Option.none
def more : List Nomm := [
  z 3, z 1, z 0, Nomm.n1 (A 7), Nomm.n4 (z 3), Nomm.n3 (z 2), c (z 2) (z 3), c (Nomm.n4 (z 2)) (z 3),
  Nomm.n7 (z 3) (Nomm.n4 (z 1)), Nomm.n7 (c (z 3) (z 2)) (c (z 3) (z 2)), Nomm.n5 (z 2) (z 3),
  Nomm.n11s tagFoo (c (z 2) (z 3)) (A 0), Nomm.n11d tagFoo (Nomm.n1 (A 1)) (Nomm.n4 (z 3)) (A 0),
  c (c (z 2) (z 3)) (Nomm.n4 (z 1)), Nomm.n7 (Nomm.n4 (z 2)) (c (z 1) (z 1)),
  -- with a hinted part
  ind (z 2) (z 3), c (ind (z 2) (z 3)) (z 3), c (z 3) (ind (z 2) (z 3)), Nomm.n5 (ind (z 2) (z 3)) (z 3),
  Nomm.n5 (z 3) (ind (z 2) (z 3)), Nomm.n4 (ind (z 2) (z 3)), Nomm.n7 (ind (z 2) (z 3)) (z 1),
  Nomm.n7 (z 3) (ind (z 2) (z 3)), c (bo (z 2)) (z 3), c (z 2) (bo (z 3)), c (sp (z 2)) (z 3),
  bo (z 3), sp (z 3), Nomm.n4 (bo (z 3)), Nomm.n7 (bo (z 3)) (z 1)]

#guard more.length == 30
-- Wherever `noBondN` holds, the runs have no fork and no bond.
#guard (nm39.map Prod.snd ++ shapes ++ more).all fun nm => !noBondN envH.cod nm || allFree nm
def idx (p : Nomm → Bool) : List Nat := ((List.range 30).zip more).filterMap fun (i, nm) => if p nm then some i else none
-- `noBondN` holds of the 15 shapes without a hinted part.
#guard idx (noBondN envH.cod) == List.range 15
-- A bond comes out of: a cons with a hinted head (16, 23, 25) or a hinted
-- tail (17, 24: under a goal whose head part asks something, not under
-- `bunt`), a `%5` whose first part is hinted (18), a kept hint (26 to 29).
#guard idx anyBond == [16, 17, 18, 23, 24, 25, 26, 27, 28, 29]
#guard runFree (more.getD 17 (z 0)) == [some false, some false, some true]
-- No bond, though `noBondN` fails: the indirect call alone, under `%4`,
-- `%7`, and as the second part of a `%5` (19: `+past` over the first part,
-- which is not hinted, parks nothing).
#guard idx (fun nm => !noBondN envH.cod nm && !anyBond nm) == [15, 19, 20, 21, 22]

end HintKeep

/-! ## `s01`, `s06` -/

def tagBout : Nat := HintTag.bout
theorem bout_static : hintStatic tagBout = true := by decide

def exS01 : Nomm := Nomm.n11s tagBout (Nomm.n0 3) (slot 3)
def exS01F : Noun := n3 (A 11) (A tagBout) (slot 3)
def exS06Q : Nomm := Nomm.n7 (Nomm.n0 3) (Nomm.n4 (Nomm.n0 1))
def exS06QF : Noun := n3 (A 7) (slot 3) (n2 (A 4) (slot 1))
def exS06 : Nomm := Nomm.n11s tagBout exS06Q exS06QF
def exS06F : Noun := n3 (A 11) (A tagBout) exS06QF

#guard dumped "s01" == some (exS01.toNoun, exS01F)
#guard dumped "s06" == some (exS06.toNoun, exS06F)
#guard (finishLUCH (S := LS) (Map := FM) envH sndH exS01).isSome
#guard (finishLUCH (S := LS) (Map := FM) envH sndH exS06).isSome
#guard sndH (Nomm.n0 3) NeedOrd.this && sndH exS06Q NeedOrd.this

section
variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The contract at the top of the dumped `s01`**, `[11 %bout [0 3]]`. -/
theorem contract_s01 (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) {c : Straight Map}
    (hsnd : snd (Nomm.n0 3) NeedOrd.this = true) (hc : finishLUCH (S := S) env snd exS01 = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s exS01F [s] c ∧ ContractBwd lib N s exS01F [s] c := by
  have H := finishLUCH_contractN11sKeptHU (S := S) lib
    (CallTreeHU.base (lib := lib) (env := env) (N := N) (P := fun _ => True) (CallTreeD.n0 3) rfl)
    (noBondH_n0 3) hsnd bout_static (slot 3) hc
  exact ⟨H.1, fun s => H.2 s trivial⟩

/-- **The contract at the top of the dumped `s06`**, `[11 %bout [7 [0 3] [4 [0 1]]]]`. -/
theorem contract_s06 (lib : Lib) (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (N : Needs) {c : Straight Map}
    (hsnd : snd exS06Q NeedOrd.this = true) (hc : finishLUCH (S := S) env snd exS06 = some c) :
    c.need = NeedOrd.this ∧ ∀ s, ContractFwd lib N s exS06F [s] c ∧ ContractBwd lib N s exS06F [s] c := by
  have hq : CallTreeHU lib env N (fun _ => True) false exS06QF exS06Q :=
    CallTreeHU.seven (CallTreeHU.base (CallTreeD.n0 3) rfl)
      (CallTreeHU.four (CallTreeHU.base (CallTreeD.n0 1) rfl))
  have H := finishLUCH_contractN11sKeptHU (S := S) lib hq
    (noBondH_n7 (noBondH_n0 3) (noBondH_n4 (noBondH_n0 1))) hsnd bout_static exS06QF hc
  exact ⟨H.1, fun s => H.2 s trivial⟩

end

end Comp
end SkaModel
end Formalization
