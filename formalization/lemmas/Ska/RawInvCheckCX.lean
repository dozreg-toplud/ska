import lemmas.Ska.RawInvCheckC

/-!
# Raw `+comp` output with indirect calls: the wide check

README Gaps 14 (b), track D.  The facts of `RawInvCheckC.lean` on an
enumeration with indirect calls in every position, run through `runLC envR`
(`enumCX`): calls `[2 p q]` over small nomms (`callsC`, with a `%6` among
the parts), each under 18 contexts (`ctxC`: as the subject and as the
formula of a call, as both, in the head, the tail or both halves of a cons,
as the condition and in either branch of a `%6`, under `%7` on either side,
under `%3`, `%4`, on either side of `%5`, as the patch and as the target of
`%10`, before a call), and 8 calls under two contexts.
* The eight fields of `OptIn` (`checkOut`) on both final passes
  (`finishLUC`, `finishLFC`);
* the facts of `StInv` (`okSt`) and `ReadsIn` over the reachable blocks
  (`okReads`) on both;
* on the raw blocks of the top run: `Closed`, `ArityOK`, `TwoNA` (`stB`);
  and the same from states with continuation blocks under `%next`,
  `%pick` and a goal with a bond (`atGoalC`, the statement of the
  run-level induction).
No field fails on any of the 3,960 nomms (both final passes return on all).
-/

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

/-- An indirect call. -/
def ic (p q : Nomm) : Nomm := Nomm.n2 p q Option.none

/-- Small nomms, one with a `%6`. -/
def baseC : List Nomm :=
  [Nomm.n0 1, Nomm.n0 2, Nomm.n0 3, Nomm.n0 6, Nomm.n1 (A 0), Nomm.n4 (Nomm.n0 3),
   Nomm.cons (Nomm.n0 2) (Nomm.n0 3), Nomm.n6 (Nomm.n0 2) (Nomm.n0 3) (Nomm.n0 1),
   Nomm.n3 (Nomm.n0 2), Nomm.n5 (Nomm.n0 2) (Nomm.n0 3), Nomm.n7 (Nomm.n0 3) (Nomm.n0 2),
   Nomm.n10 6 (Nomm.n0 1) (Nomm.n0 7)]

/-- 72 calls over `baseC`. -/
def callsC : List Nomm := (baseC.take 12).flatMap fun p => (baseC.take 6).map fun q => ic p q

/-- 18 contexts. -/
def ctxC (t : Nomm) : List Nomm :=
  [ic t (Nomm.n0 2), ic (Nomm.n0 3) t, ic t t, Nomm.cons t (Nomm.n0 1), Nomm.cons (Nomm.n0 1) t,
   Nomm.cons t t, Nomm.n6 t (Nomm.n0 2) (Nomm.n0 3), Nomm.n6 (Nomm.n0 2) t (Nomm.n0 3),
   Nomm.n6 (Nomm.n0 2) (Nomm.n0 3) t, Nomm.n7 t (Nomm.n0 2), Nomm.n7 (Nomm.n0 2) t, Nomm.n3 t,
   Nomm.n4 t, Nomm.n5 t (Nomm.n0 2), Nomm.n5 (Nomm.n0 3) t, Nomm.n10 6 t (Nomm.n0 1),
   Nomm.n10 2 (Nomm.n0 1) t, Nomm.n7 t (ic (Nomm.n0 3) (Nomm.n0 2))]

def enumCX1 : List Nomm := callsC ++ callsC.flatMap ctxC

def enumCX2 : List Nomm := (callsC.take 8).flatMap fun t => (ctxC t).flatMap ctxC

def runCG (goal : CGoalL LS) (g0 : Comp.Gen FM) (nm : Nomm) : Option (NextL LS × Comp.Gen FM) :=
  runLC envR Option.none nm goal [] g0

def atGoalC (goal : CGoalL LS) (g0 : Comp.Gen FM) (nm : Nomm) : Option Bool :=
  (runCG goal g0 nm).map fun (nex, g) =>
    stB g.blocks && nex.th.args.isEmpty && match g.blocks.f nex.th.there with
      | some b => b.par.isEmpty
      | none => false

def allC (nm : Nomm) : Bool :=
  (runC nm).isSome && (finishLUC (S := LS) (Map := FM) envR nm).isSome && (naryC nm).isSome &&
  okOut (finishLUC (S := LS) (Map := FM) envR nm) && okOut (naryC nm) &&
  okSt (finishLUC (S := LS) (Map := FM) envR nm) && okSt (naryC nm) &&
  okReads (finishLUC (S := LS) (Map := FM) envR nm) && okReads (naryC nm) &&
  (match runC nm with | some (_, g) => stB g.blocks | none => false) &&
  atGoalC (CGoalL.next (ofSure (lazyReg 0)) (jmp0 1)) gY nm == some true &&
  atGoalC (CGoalL.pick (jmp0 1) (jmp0 2)) gP nm == some true

/-- A state with a bond block `1` (tagged, `con 0 1 2, don 2`) behind the
block `2` (`hop 1`). -/
def gB : Comp.Gen FM :=
  ⟨3, 3, 1, false, HoonMap.put (HoonMap.put (HoonMap.empty : FM Blob) 1 ⟨[], [Pole.con 0 1 2], Termin.don 2⟩) 2
    ⟨[], [], Termin.hop (jmp0 1)⟩, HoonMap.put (HoonMap.empty : FM (List Nat)) 1 [0], HoonMap.empty⟩

/-- The goal with the bond: `1` at the entry, `0` at the bond block. -/
def goalB : CGoalL LS := CGoalL.next (mk (lazyReg 1) [] [(1, ofSure (lazyReg 0))]) (jmp0 2)

def runSIP (nm : Nomm) : List Bool := match runC nm with
  | some (nex, g) => let m := g.blocks
    [defOnceB m, noTrB m, parNodupB m, rkDownB m, argsAboveRkB m, liveKB m nex, lazyOKB m nex, xupB m, disjB nex]
  | none => []

def enumCX : List Nomm := enumCX1 ++ enumCX2

#guard enumCX.length == 3960
#guard enumCX.all allC
/- Under a goal with a bond (a tagged lazy block `1`): 3,912 runs return
and every one meets the statement of the induction; 3,888 make proxies
(the `+kern` of a call reads the bond's need through one). -/
#guard (enumCX.filter fun nm => atGoalC goalB gB nm == some false).length == 0
#guard (enumCX.filter fun nm => (runCG goalB gB nm).isSome).length == 3912
#guard (enumCX.filter fun nm => match runCG goalB gB nm with | some (_, g) => hasProxies g.cond | none => false).length == 3888

/-! ## Not vacuous, and the run-level facts of `FragX` that fail

1,014 raw runs and 1,014 n-ary outputs have a jump with arguments; 2,214
top runs return a lazy need with a bond.  Of the facts that `checkRunX`
and `xupB`, `disjB` carry on `FragX` (`defOnceB`, `noTrB`, `parNodupB`,
`rkDownB`, `argsAboveRkB`, `liveKB`, `lazyOKB`, `xupB`, `disjB`), two fail
on raw `runLC` outputs, neither a field of `OptIn`:
* `liveKB` on 336 runs, exactly those whose `cond` has proxies: the
  `+kern` of a call under a lazy need reads the need's lazy blocks through
  proxies, never defined; so a run-level liveness spec with calls must be
  stated modulo `unproxy`;
* `lazyOKB` on 352 runs: the lazy entries are not at distinct labels, as
  in `[6 [2 [0 1] [0 1]] [0 2] [0 3]]` (`enumCX[78]`), where `+past-fork`
  behind the hinted test parks each branch's need in a bond at the branch
  block itself (nodes `(3, [])` and `(3, [1])`). -/
#guard (List.range 9).map (fun k => (enumCX.filter fun nm => (runSIP nm).getD k true == false).length) ==
  [0, 0, 0, 0, 0, 336, 352, 0, 0]
#guard (enumCX.filter fun nm => (runSIP nm).getD 5 true == false &&
  (match runC nm with | some (_, g) => !hasProxies g.cond | none => false)).length == 0
#guard (enumCX.filter fun nm => match runC nm with | some (_, g) => hasProxies g.cond | none => false).length == 336
#guard (enumCX.filter fun nm => match runC nm with | some (_, g) => argsB g.blocks | none => false).length == 1014
#guard (enumCX.filter fun nm => match naryC nm with | some c => argsB c.blocks | none => false).length == 1014
#guard (enumCX.filter fun nm => match runC nm with | some (nex, _) => !nex.laz.bond.isEmpty | none => false).length == 2214
#guard ((runC (enumCX.getD 78 (Nomm.n0 1))).map fun (nex, _) => (nodesOf nex).map fun x => (x.1, x.2.1)) ==
  some [(9, [4]), (3, []), (3, [1]), (4, []), (4, [0])]

end Raw
end SkaModel
end Formalization
