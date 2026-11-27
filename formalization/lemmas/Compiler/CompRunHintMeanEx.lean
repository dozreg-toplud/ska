import lemmas.Compiler.CompRunHintMeanClass
import lemmas.Compiler.CompRunHintMeanCheck

/-!
# The case `%mean` in the class: examples (README Gaps 25)

* `~|`-style hints: `[11 [%mean [[1 bat] [0 1]]] [[0 2] [6 [3 [0 3]] [1 1] [1 2]]]]`
  (`m14` of `tools/hoon/hintmean.hoon`), a cons with a `%6` under a
  deferred `%mean`, as the analysis makes it, with a constant (`k` `some`)
  and without: `PartH` from `CodeAna` and the code entry of the trap's arm.
* `inClass`: the nomms of the dump in `HintOkM`: all 36 entries, the
  direct calls of `R` under a `%mean` and the arms of the five real gates
  with `~_` (three under `!:`, two recursive) among them.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSectionVars false

variable {ctx : Noun}

/-- The body: a cons with a `%6` inside. -/
def meanBody : Nomm :=
  Nomm.cons (Nomm.n0 2) (Nomm.n6 (Nomm.n3 (Nomm.n0 3)) (Nomm.n0 2) (Nomm.n1 (A 0)))

/-- The trap: `[[1 bat] [0 1]]`. -/
def meanTrap (bat : Noun) : Nomm := Nomm.cons (Nomm.n1 bat) (Nomm.n0 1)

/-- The `%mean` nomm, with the trap's bell `b` and the arm's product `k`. -/
def meanEx (bat : Noun) (b : Bell) (body : Noun) (k : Option Noun) : Nomm :=
  Nomm.mean (meanTrap bat) b meanBody body k

/-- **A deferred `%mean` around a cons with a `%6`**, constant or not,
linked on every goal from the facts of the analysis. -/
example (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod) (hana : CodeAna cod)
    (env : CallEnv) (E : GenRest → Prop) (bat body : Noun) (b : Bell) (k : Option Noun)
    (hcd : k.isSome = true → CodePure cod env b) (msup : Option Nomm) (region : List Nat) :
    PartH env (sfSnd cod) msup ctx (XM E msup) (meanEx bat b body k) region :=
  comp_run_hint_anaM h7 hcode hana env E (meanEx bat b body k) rfl msup region
    ⟨hcd, ⟨trivial, trivial⟩, ⟨trivial, trivial, trivial, trivial⟩⟩

/-- The same at its goal, a `%done` one included. -/
example (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod) (hana : CodeAna cod)
    (env : CallEnv) (E : GenRest → Prop) (bat body n : Noun) (b : Bell) (hcd : CodePure cod env b)
    (msup : Option Nomm) (region : List Nat) (goal : CGoalL CSet) (g : Gen (TreapMap mugF)) (hi : GInv g goal) :
    CompRunAtX (runLCH env (sfSnd cod) true msup) ctx (XM E msup) (meanEx bat b body (some n)) goal region g :=
  comp_run_hint_anaXM h7 hcode hana env E (meanEx bat b body (some n)) rfl msup region
    ⟨fun _ => hcd, ⟨trivial, trivial⟩, ⟨trivial, trivial, trivial, trivial⟩⟩ goal g hi

/-- The entries of the dump whose nomm is in `HintOkM`. -/
def inClass : List String :=
  (MeanData.all.filter fun (_, j) => match partsM j with
    | some (nmN, _) => ((SkaModel.Comp.nommOf 300 nmN).map HintOkM) == some true
    | Option.none => false).map Prod.fst

#guard inClass.length == 36
#guard inClass == MeanData.all.map Prod.fst
#guard ["g01", "g02", "g03", "g04", "g05"].all inClass.contains

end Compiler
end Formalization
