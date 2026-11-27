import lemmas.Ska.CompHintSixCheck

/-!
# The premises of the `%6` constructor of `RegGBT`, checked on the model (README Gaps 24.21)

No proof here.  The constructor (`CompHintSixReg.lean`) asks, of a `[6 c a b]`
run under `%next (lazy-from-reg r) th` (phase S: the goal has no entry):
* the test `c` hint-free, without a direct call, with `hinted` `some false`
  (so `+past-fork` leaves the fork as it is and `runLCH` of `c` is `runLC`);
* the branches `a`, `b` in `RegGBT` (they run under `%next (lazy-from-reg r0)`
  and `%next (lazy-from-reg r1)`, the two fresh registers of `+fork-sure`);
* a bound on the entries of the branches' results (`5 + ka + kb ≤ lazyMax`:
  `+lazy-shut` off);
* the tag clause of the branches (`+sect` threads nothing): here the
  stronger fact that their runs leave `cond` as it is.
All are `#guard`ed on `spotArm`'s `%6` (`six2`, `CompHintSixCheck.lean`)
and on `d18`'s `%6`, under `%next (lazy-from-reg 0)` from `gS`.  The proof
does not ask `PickF` of the test (its result under `%pick` flat), which holds
of `d18`'s test and FAILS for `spotArm`'s, whose test `?@` is itself a `%6`
(`[6 [3 [0 6]] [1 1] [1 0]]`) whose result carries its own fork.
-/

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

namespace HintTen
open HintNest HintKeep HintSpot HintSeven

/-- The parts of a `%6`. -/
def sixParts : Nomm → Option (Nomm × Nomm × Nomm)
  | Nomm.n6 c a b => some (c, a, b)
  | _ => Option.none

/-- A branch run under `%next (lazy-from-reg k) (jmp0 j)` from `gS`: the
number of entries of its result and whether `cond` is still empty. -/
def branchRun (nm : Nomm) (k j : Nat) : Option (Nat × Bool) :=
  (runLCH (S := LS) (Map := FM) envH sndH true Option.none nm (CGoalL.next (ofSure (lazyReg k)) (jmp0 j)) [7] gS).map
    fun (nex, g) => ((entries nex.laz).length, g.cond.ks.isEmpty)

/-- The premises of the constructor on a `%6`: the test, the two branches
(entries few, `cond` untouched), and the `%6`'s own run (`cond` untouched). -/
def sixPrem (nm : Nomm) : Option Bool := do
  let (c, a, b) ← sixParts nm
  let (ka, ca) ← branchRun a 5 2
  let (kb, cb) ← branchRun b 6 2
  let (_, cw) ← branchRun nm 0 1
  pure (c.noHint && c.noDirect && c.pure && decide (hinted envH.cod c = some false) &&
    decide (5 + ka + kb ≤ lazyMax) && ca && cb && cw)

def d18six : Nomm := (formOf (nmOf "d18")).getD (Nomm.n0 0)

-- `d18`'s formula is a `%6`, and so is `spotArm`'s
#guard (sixParts d18six).isSome
#guard (sixParts six2).isSome
-- the premises hold on both
#guard sixPrem six2 == some true
#guard sixPrem d18six == some true
-- `S2`'s result has four entries (bonds nested three deep), `[1 0]`'s none
#guard branchRun s2c 5 2 == some (4, true)
#guard branchRun (Nomm.n1 (A 0)) 5 2 == some (0, true)

/-- The test of a `%6` under `%pick (jmp0 1) (jmp0 2)` from `gS`: whether its
result is flat (`PickF`: no fork, no bond). -/
def testFlat (nm : Nomm) : Option Bool := do
  let (c, _, _) ← sixParts nm
  (runLC (S := LS) (Map := FM) envH Option.none c (CGoalL.pick (jmp0 1) (jmp0 2)) [] gS).map
    fun (nex, _) => nex.laz.fork.isEmpty && nex.laz.bond.isEmpty

-- `PickF` holds of `d18`'s test, and FAILS for `spotArm`'s (`?@` compiles to the `%6` `testT`, whose
-- result under `%pick` carries its own fork); `six_nextGBT` does not ask `PickF`
#guard testFlat d18six == some true
#guard testFlat six2 == some false

end HintTen

end Comp
end SkaModel
end Formalization
