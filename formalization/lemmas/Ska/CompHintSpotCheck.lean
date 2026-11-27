import lemmas.Ska.CompHintNest
import lemmas.Ska.CompHintKeepEx

/-!
# Nested kept hints: the clause that replaces `NoBondH` (README Gaps 24.16)

A kept hint whose formula is a kept hint (`d10`): the formula's result has
a bond, so `NoBondH` fails.  What `n11dKept_done` uses of its formula is the
run under `%next (lazy-from-reg r)` only.  The checks (`#guard`):
* one level (`flatReg`: no fork, the bonds bond-free) holds of a kept hint
  whose formula has `NoBondH`, not of two levels; at any depth, no fork at
  all (`noForkReg`) holds of the nested spots and fails on a spot over a
  `%6` (`d18`: the `%6`'s fork goes inside the bond);
* at the top the nested results have the entries (labels and sure needs) of
  their flattening (`sameEnt`), except `d18`.
-/

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

namespace HintSpot
open HintNest HintKeep

/-- The run under each bond-free goal of `HintKeep.goals`: `some true` when
the result is flat with bond-free bonds (no fork, each bond's lazy with no
fork and no bond). -/
def runFlat (nm : Nomm) : List (Option Bool) :=
  goals.map fun g => (runLCH (S := LS) (Map := FM) envH sndH true Option.none nm g [] gS).map fun (nex, _) =>
    nex.laz.fork.isEmpty && nex.laz.bond.all fun e => e.2.fork.isEmpty && e.2.bond.isEmpty
def flatH (nm : Nomm) : Bool := (runFlat nm).all fun r => r != some false

/-- The labels and sure needs of the result's entries at the top. -/
def entKey (l : Lazy LS) : List (Nat × Need) := (entries l).map fun e => (e.1, e.2.sure.ned)
def sameEnt (nm : Nomm) : Option Bool :=
  (runLCH (S := LS) (Map := FM) envH sndH true Option.none nm CGoalL.done [] gen0).map fun (nex, _) =>
    entKey nex.laz == entKey (flattenL nex.laz)

def nmOf (n : String) : Nomm := ((nm39.lookup n).getD (Nomm.n0 0))
def formOf : Nomm → Option Nomm
  | Nomm.n11d _ _ q _ => some q
  | Nomm.n7 p _ => formOf p
  | _ => Option.none

/-- Kept hints whose formula has `NoBondH`, and one level more. -/
def keptShapes : List Nomm := [sp (z 3), sp (Nomm.n4 (z 3)), bo (z 3), sp (Nomm.n2 (z 3) (z 2) Option.none),
  sp (sp (z 3)), bo (sp (z 3)), sp (bo (Nomm.n4 (z 3)))]

/-- The run under `%next (lazy-from-reg 0)` (the goal a kept hint gives its
formula, `+sound` of `%this` holding): `some true` when the result has no
fork at any depth (`entries` included). -/
def noForkReg (nm : Nomm) : Option Bool :=
  (runLCH (S := LS) (Map := FM) envH sndH true Option.none nm (CGoalL.next (ofSure (lazyReg 0)) (jmp0 1)) [] gS).map
    fun (nex, _) => nex.laz.fork.isEmpty && (entries nex.laz).all fun e => e.2.fork.isEmpty
/-- The same run with a flat result whose bonds have no bond (one level). -/
def flatReg (nm : Nomm) : Option Bool :=
  (runLCH (S := LS) (Map := FM) envH sndH true Option.none nm (CGoalL.next (ofSure (lazyReg 0)) (jmp0 1)) [] gS).map
    fun (nex, _) => nex.laz.fork.isEmpty && nex.laz.bond.all fun e => e.2.fork.isEmpty && e.2.bond.isEmpty

-- `NoBondH` fails on a kept formula (`d10`'s inner spot); the one-level and the
-- any-depth clauses hold
#guard (formOf (nmOf "d10")).map allFree == some false
#guard (formOf (nmOf "d10")).bind flatReg == some true
#guard (formOf (nmOf "d10")).bind noForkReg == some true
#guard (formOf (nmOf "d12")).bind flatReg == some true
-- one level: a kept hint whose formula has `NoBondH`; two levels are deeper
#guard [sp (z 3), sp (Nomm.n4 (z 3)), bo (z 3), sp (Nomm.n2 (z 3) (z 2) Option.none)].all fun nm => flatReg nm == some true
#guard [sp (sp (z 3)), bo (sp (z 3)), sp (bo (Nomm.n4 (z 3)))].all fun nm => flatReg nm == some false
#guard keptShapes.all fun nm => noForkReg nm == some true
-- the spot over a `%6` (`d18`): the formula's result has a fork, inside the bond
#guard (formOf (nmOf "d18")).bind noForkReg == some false
-- at the top, the nested results have the entries (labels, sure needs) of their flattening
#guard ["d10", "d12", "d16", "d17", "s07", "m04"].all fun n => sameEnt (nmOf n) == some true
#guard keptShapes.all fun nm => sameEnt nm == some true
#guard shapes.all fun nm => sameEnt nm == some true
#guard sameEnt (nmOf "d18") == some false

end HintSpot
end Comp
end SkaModel
end Formalization
