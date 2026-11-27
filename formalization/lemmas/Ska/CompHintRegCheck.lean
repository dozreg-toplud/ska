import lemmas.Ska.CompHintSpotCheck

/-!
# The direct call and `%10` under `%next (lazy-from-reg r)`, checked on the model (README Gaps 24.18)

The shape half of `RegOKT` (`CompHintRegOps.lean`: the result flat, its
bonds bond-free) checked before any proof, with `flatReg` and `noForkReg`
of `CompHintSpotCheck.lean` (the run under `%next (lazy-from-reg 0)`):
* `[10 6 [spot [0 13]] [0 1]]` (the `%10` of `spotArm`'s `S3`, its value a
  kept spot) and `[10 6 [0 13] [0 1]]`: flat, no fork; it compiles at the
  top.
* the formula of `d22` (`[8 [1 r] [9 2 [0 1]]]`, a direct call): flat, no
  fork.
* `noBondN` (the syntactic test of `NoBondH`) fails on the `%10` with a kept
  value (its result has the spot's bond), so `RegFT`, not `NoBondH`, is the
  clause the `%10` has to meet.
-/

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

namespace HintSpot
open HintNest HintKeep

def tenS3 : Nomm := Nomm.n10 6 (sp (z 13)) (z 1)

#guard flatReg tenS3 == some true
#guard noForkReg tenS3 == some true
#guard flatReg (Nomm.n10 6 (z 13) (z 1)) == some true
#guard (runLCH (S := LS) (Map := FM) envH sndH true Option.none tenS3 CGoalL.done [] gen0).isSome
#guard (formOf (nmOf "d22")).bind flatReg == some true
#guard (formOf (nmOf "d22")).bind noForkReg == some true
#guard HintKeep.noBondN envH.cod tenS3 == false

end HintSpot

end Comp
end SkaModel
end Formalization
