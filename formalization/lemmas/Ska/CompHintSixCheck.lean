import lemmas.Ska.CompHintDirectReg

/-!
# What `spotArm`'s positions 1 to 3 ask of `%6`, checked on the model (README Gaps 24.20)

No proof here: the shape of the run of `spotArm`'s `%6` (`[6 T [1 0] S2]`,
`T = [6 [3 [0 6]] [1 1] [1 0]]`, `S2 = [spot [4 S3]]`, the recursion
replaced by `d22`'s call) under `%next (lazy-from-reg 0)` (the goal the
kept `S1` gives its formula), with `sh`, the shape of a lazy with labels and
registers erased (`a` when the sure need asks something, `F` the forks, `B`
the bonds):
* the result asks (the sample, for the test), has no bond, and two forks:
  the inner test's (both branches asking nothing) and the outer one, whose
  `yes` lazy is `[1 0]`'s (nothing) and whose `no` lazy is exactly `S2`'s
  own result under `%next (lazy-from-reg 0)`: bonds nested three deep (`S2`'s,
  `S3`'s, the `%10`'s two);
* under the kept `S1` at the top the whole lazy sits in `S1`'s bond (the
  fork inside the bond, as in `d18`, whose formula has one fork and no
  nesting).
So the clause for positions 1 to 3 is a `%6` constructor of `RegGBT`: the
test in the unhinted pick class, the branches in `RegGBT` at the `%6`'s
goal, their results carried as the fork's lazies (bonds inside fork
branches: `entries` already walks them, so `RunOKGBT` states it), then
`regGBT_n11dKept` over it for `S1` (`+sound` of `%this` holds of the `%6`,
`#guard`).
-/

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

namespace HintTen
open HintNest HintKeep HintSpot HintSeven

/-- The shape of a lazy, labels and registers erased. -/
partial def sh (l : Lazy LS) : String :=
  "(" ++ (if l.sure.ned != Need.none then "a" else "_") ++ " F" ++
    String.join (l.fork.map fun ((_, x), (_, y)) => "[" ++ sh x ++ "|" ++ sh y ++ "]") ++ " B" ++
    String.join (l.bond.map fun (_, x) => sh x) ++ ")"

def runSh (nm : Nomm) (G : CGoalL LS) (g : Gen FM) : Option String :=
  (runLCH (S := LS) (Map := FM) envH sndH true Option.none nm G [] g).map fun (nex, _) => sh nex.laz

/-- `spotArm`'s test, `S2` with `d22`'s call for the recursion, the `%6`. -/
def testT : Nomm := Nomm.n6 (Nomm.n3 (Nomm.n0 6)) (Nomm.n1 (A 1)) (Nomm.n1 (A 0))
def s2c : Nomm := Nomm.n11d tagSpot (Nomm.n1 (A 0)) (Nomm.n4 (Nomm.n11d tagSpot (Nomm.n1 (A 0)) (Nomm.n7 tenS3 call22) (A 3))) (A 2)
def six2 : Nomm := Nomm.n6 testT (Nomm.n1 (A 0)) s2c

-- the branch `S2` alone: bonds nested three deep
#guard runSh s2c gReg gS == some "(_ F B(_ F B(_ F B(a F B)(a F B))))"
#guard runSh (Nomm.n1 (A 0)) gReg gS == some "(_ F B)"
-- the `%6`: the test's fork, then the fork whose `no` lazy is `S2`'s result as it is
#guard runSh six2 gReg gS ==
  some ("(a F[(_ F B)|(_ F B)][(_ F B)|" ++ "(_ F B(_ F B(_ F B(a F B)(a F B))))" ++ "] B)")
-- under the kept `S1` at the top: the `%6`'s lazy inside `S1`'s bond
#guard runSh (sp six2) CGoalL.done gen0 ==
  some ("(_ F B(a F[(_ F B)|(_ F B)][(_ F B)|" ++ "(_ F B(_ F B(_ F B(a F B)(a F B))))" ++ "] B))")
-- `d18`: one fork, no nesting
#guard (formOf (nmOf "d18")).bind (fun f => runSh f gReg gS) == some "(a F[(_ F B)|(_ F B)] B)"
-- `+sound` of `%this` holds of the `%6` (the premise of `regGBT_n11dKept` for `S1`)
#guard sndH six2 NeedOrd.this

end HintTen

end Comp
end SkaModel
end Formalization
