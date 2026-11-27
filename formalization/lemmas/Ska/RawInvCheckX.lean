import lemmas.Ska.RawInvCheck
import lemmas.Ska.CompNestCoerce
import lemmas.Ska.CompGrowU

/-!
# Raw `+comp` output with `%6` anywhere: executable checks

README Gaps 14, the class `FragX` (a `%6` under `%7`, `%4`, `%3`, cons,
`%5`, `%10` and inside another `%6`).  `enumX`: 4,080 nomms, each a `%6`
over the first fragment put into one of 17 contexts.  On all of them:

* the eight fields of `OptIn` hold of the output of both final passes
  (`checkOut` on `finishLF` and `finishLU`);
* the raw blocks of the run for `%done` from `gen0` meet `checkRunX`, the
  candidate run-level invariant for `FragX`: one definition per register
  over all blocks, no trace hint op, distinct parameters per block, jumps
  that go down in the rank `upRk` of `CompGrowU.lean`, arguments above the
  parameters of every block of rank at most the target's, lazy entries at
  distinct labels with no parameter whose needs nothing defines, and
  **no register live at the entry once each lazy entry first defines the
  registers of its sure need** (`liveKF`, the executable form of `LiveK` of
  `RawInvLiveK.lean`).

Three fields of the first fragment's `SI` are false here, with witnesses:
`JDown` (`[4 [6 [0 1] [0 1] [0 1]]]`: the fork blocks hop up to the join),
`Par1` (`[7 [6 [0 1] [0 1] [0 1]] [[0 3] [0 2]]]`: the join of `+fork-need`
has two parameters), and the liveness cut at the lazy entries without the
kills (`[[0 3] [6 [0 6] [0 2] [0 1]]]`: register `1`, which the head's code
defines at the entry, is live at both fork blocks, read after the join by
the `%con`).  So the liveness spec of a run with a lazy result must follow
paths from the entry through the lazy entries, not restart at them.
-/

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

/-! ## Checkers -/

def rkDownB (m : FM Blob) : Bool :=
  (blocksOf m).all fun (k, b) => (getJmps b.fin).all fun j => upRk m j.there < upRk m k

/-- Every argument of a jump is above the parameters of every block whose
rank is at most the target's. -/
def argsAboveRkB (m : FM Blob) : Bool :=
  (blocksOf m).all fun (_, b) => (getJmps b.fin).all fun j => (jmpRegs j).all fun r =>
    (blocksOf m).all fun (z, bz) => !(upRk m z ≤ upRk m j.there) || bz.par.all (· < r)

/-- Liveness with the blocks of `Z` cut (a jump into `Z` reads nothing). -/
def liveCutF (m : FM Blob) (Z : List Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, k => match m.f k with
    | none => []
    | some b =>
      let n := b.body.length
      let here := (List.range (n + 1)).flatMap fun i =>
        let rs := if i < n then (b.body[i]?.map aliasReads).getD [] else finRegs b.fin
        let dd := b.par ++ (b.body.take i).filterMap aliasDst
        rs.filter fun r => ! dd.contains r
      let after := (getJmps b.fin).flatMap fun j =>
        if Z.contains j.there then [] else
        (liveCutF m Z f j.there).filter fun r => ! (blockDefs b).contains r
      (here ++ after).eraseDups

/-- Liveness where the block at a label of `K` first defines the registers
`K` gives it. -/
def liveKF (m : FM Blob) (K : List (Nat × List Nat)) : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, k => match m.f k with
    | none => []
    | some b =>
      let kill := (K.filter (·.1 == k)).flatMap (·.2)
      let n := b.body.length
      let here := (List.range (n + 1)).flatMap fun i =>
        let rs := if i < n then (b.body[i]?.map aliasReads).getD [] else finRegs b.fin
        let dd := b.par ++ (b.body.take i).filterMap aliasDst
        rs.filter fun r => ! dd.contains r
      let after := (getJmps b.fin).flatMap fun j =>
        (liveKF m K f j.there).filter fun r => ! (blockDefs b).contains r
      ((here ++ after).filter fun r => ! kill.contains r).eraseDups

/-- The direct entries of a lazy need. -/
def kids : Lazy LS → List (Nat × Lazy LS)
  | mk _ f b => b ++ f.flatMap fun yn => [yn.1, yn.2]

/-- The lazy entries with the registers of their sure needs and of their
ancestors'. -/
def nodesF : Nat → List Nat → Nat × Lazy LS → List (Nat × List Nat × List Nat)
  | 0, _, _ => []
  | k + 1, A, (o, l) =>
    (o, flattenNeed l.sure.ned, A) :: (kids l).flatMap (nodesF k (A ++ flattenNeed l.sure.ned))

def nodesOf (nex : NextL LS) : List (Nat × List Nat × List Nat) := nodesF 30 [] (nex.th.there, nex.laz)

/-- No register is live at the entry when every lazy entry first defines its
sure need. -/
def liveKB (m : FM Blob) (nex : NextL LS) : Bool :=
  (liveKF m ((nodesOf nex).map fun x => (x.1, x.2.1)) ((blocksOf m).length + 1) nex.th.there).isEmpty

/-- With the cut and no kills: every register live at a lazy entry is in its
need or an ancestor's.  False on `FragX`. -/
def liveCutB (m : FM Blob) (nex : NextL LS) : Bool :=
  let N := nodesOf nex
  N.all fun x => (liveCutF m (N.map (·.1)) ((blocksOf m).length + 1) x.1).all fun r =>
    x.2.1.contains r || x.2.2.contains r

/-- Lazy entries at distinct labels, with no parameter, whose needs nothing
defines. -/
def lazyOKB (m : FM Blob) (nex : NextL LS) : Bool :=
  let N := nodesOf nex
  let D := allDefsL m
  nodupB (N.map (·.1)) && N.all fun x =>
    (match m.f x.1 with | some b => b.par.isEmpty | none => true) && x.2.1.all fun r => ! D.contains r

def runX (nm : Nomm) : Option (NextL LS × Comp.Gen FM) :=
  runL nm (CGoalL.done : CGoalL LS) [] (gen0 : Comp.Gen FM)

/-- The candidate run-level invariant on the raw blocks of a run of
`FragX` for `%done`. -/
def checkRunX (nm : Nomm) : Option Bool :=
  (runX nm).map fun (nex, g) =>
    let m := g.blocks
    defOnceB m && noTrB m && parNodupB m && rkDownB m && argsAboveRkB m && liveKB m nex &&
      lazyOKB m nex && nex.th.args.isEmpty

def naryX (nm : Nomm) : Option (Straight FM) :=
  finishLF (S := LS) (Map := FM) nm NeedOrd.this Cape.no (fun ned => (ned, []))

/-! ## Enumerated nomms -/

def baseX : List Nomm := leaves ++ ((grow leaves).drop 10).take 16

/-- 240 `%6` over the first fragment. -/
def sixes : List Nomm :=
  (baseX.take 10).flatMap fun c => (baseX.take 6).flatMap fun a => (baseX.take 4).map fun b => Nomm.n6 c a b

/-- 17 contexts. -/
def ctxX (t : Nomm) : List Nomm :=
  [Nomm.n7 t (Nomm.n0 1), Nomm.n7 t (Nomm.n0 3), Nomm.n7 t (Nomm.n4 (Nomm.n0 2)),
   Nomm.n7 t (Nomm.cons (Nomm.n0 3) (Nomm.n0 2)), Nomm.n4 t, Nomm.n3 t, Nomm.cons t (Nomm.n0 2),
   Nomm.cons (Nomm.n0 3) t, Nomm.n5 t (Nomm.n0 2), Nomm.n5 (Nomm.n0 3) t, Nomm.n10 6 t (Nomm.n0 1),
   Nomm.n10 2 (Nomm.n0 1) t, Nomm.n7 (Nomm.n0 2) t, Nomm.n6 (Nomm.n0 2) t (Nomm.n0 3),
   Nomm.n6 t (Nomm.n0 2) (Nomm.n1 (A 0)), Nomm.n4 (Nomm.n7 t (Nomm.n0 2)),
   Nomm.cons (Nomm.n7 t (Nomm.n0 1)) (Nomm.n4 t)]

/-- 4,080 nomms of `FragX` with a `%6` below the top. -/
def enumX : List Nomm := sixes.flatMap ctxX

#guard enumX.length == 4080
#guard enumX.all fun nm => (runX nm).isSome && (naryX nm).isSome && (mono nm).isSome
#guard enumX.all fun nm => okOut (naryX nm) && okOut (mono nm)
#guard enumX.all fun nm => okRun (checkRunX nm)

/-! ## The fields of `SI` that fail -/

def exUp : Nomm := Nomm.n4 (Nomm.n6 (Nomm.n0 1) (Nomm.n0 1) (Nomm.n0 1))
def exPar2 : Nomm := Nomm.n7 (Nomm.n6 (Nomm.n0 1) (Nomm.n0 1) (Nomm.n0 1)) (Nomm.cons (Nomm.n0 3) (Nomm.n0 2))
def exCut : Nomm := Nomm.cons (Nomm.n0 3) (Nomm.n6 (Nomm.n0 6) (Nomm.n0 2) (Nomm.n0 1))

#guard ((runX exUp).map fun (_, g) => jdownB g.blocks) == some false
#guard ((runX exPar2).map fun (_, g) => par1B g.blocks) == some false
#guard ((runX exCut).map fun (nex, g) => liveCutB g.blocks nex) == some false
/- In `exCut` register `1` is defined at the entry `10` and read by the
`%con` at `2`, after the join `5`; the fork blocks `6` and `7` reach it. -/
#guard ((runX exCut).map fun (nex, g) =>
  (nex.th.there, (blocksOf g.blocks).find? (·.1 == 2) |>.map fun kb => kb.2.body.flatMap aliasReads)) ==
  some (10, some [1, 2])


/-! ## The prologues of `+coerce-lazy`

The hypotheses of `optIn_toStraight_prep` (`RawInvTopX.lean`) on the
model's final pass: after `+coerce-lazy` every block is the raw block with
ops in front, only at lazy entries; the ops at an entry define the
registers of its sure need and read first only the input registers;
every register is defined once, no trace hint op, no input defined. -/

/-- The registers the ops read before they write them. -/
def readsFirst : List Pole → List Nat
  | [] => []
  | op :: A => aliasReads op ++ (readsFirst A).filter fun r => aliasDst op != some r

/-- The ops in front of `b` in `b'`, if `b'` is `b` with ops in front. -/
def prefixOf (b b' : Blob) : Option (List Pole) :=
  let n := b'.body.length - b.body.length
  if b'.par == b.par && b'.fin == b.fin && b.body.length ≤ b'.body.length && b'.body.drop n == b.body then
    some (b'.body.take n) else none

def checkPrep (nm : Nomm) (ord : NeedOrd) : Option Bool :=
  (runX nm).bind fun (nex, g1) =>
    (needOrdAllocRegs ord g1).bind fun (ned, g2) =>
      (coerceLazyL ned Cape.no nex.th.there nex.laz g2).map fun (_, g3) =>
        let m := g1.blocks
        let m3 := g3.blocks
        let N := nodesOf nex
        let I := flattenNeed ned
        (blocksOf m3).length == (blocksOf m).length &&
        (blocksOf m).all (fun (k, b) => match m3.f k with
          | none => false
          | some b' => match prefixOf b b' with
            | none => false
            | some A =>
              (A.isEmpty || (N.map (·.1)).contains k) &&
              (readsFirst A).all I.contains &&
              (N.filter (·.1 == k)).all fun x => x.2.1.all fun r => (defsOf A).contains r) &&
        defOnceB m3 && noTrB m3 && I.all fun r => ! (allDefsL m3).contains r

#guard enumX.all fun nm => okRun (checkPrep nm NeedOrd.this)
#guard (enumX.take 600).all fun nm =>
  okRun (checkPrep nm (NeedOrd.both NeedOrd.none (NeedOrd.pair NeedOrd.this NeedOrd.none)))

/-! ## The spec of `RawIHX` under `%next` and `%pick`

`RawIHX` (`RawInvIHX.lean`): a run for a fork-free goal leaves live at its
entry, once each entry of its result's lazy tree first defines its sure
need, only registers live at the goal's continuation that the goal does
not name.  Checked from a state whose block `1` reads registers `0` and
`1` (`con 0 1 2, don 2`), for the goal `%next` with need `0` into `1`
(so only `1` may be live, and it is in 3,028 of the 4,320 runs), and for
`%pick` into `1` and `2` (`don 3`), with the other fields of `checkRunX`
and the result's jump: no arguments, to a label from `1` below the end's
`bo`. -/

def gY : Comp.Gen FM :=
  ⟨3, 2, 0, false, HoonMap.put (HoonMap.empty : FM Blob) 1 ⟨[], [Pole.con 0 1 2], Termin.don 2⟩,
    HoonMap.empty, HoonMap.empty⟩

def gP : Comp.Gen FM :=
  ⟨4, 3, 0, false, HoonMap.put (HoonMap.put (HoonMap.empty : FM Blob) 1 ⟨[], [Pole.con 0 1 2], Termin.don 2⟩) 2
    ⟨[], [], Termin.don 3⟩, HoonMap.empty, HoonMap.empty⟩

def liveAtEntry (m : FM Blob) (nex : NextL LS) : List Nat :=
  liveKF m ((nodesOf nex).map fun x => (x.1, x.2.1)) ((blocksOf m).length + 1) nex.th.there

def checkGoalX (goal : CGoal LS) (g0 : Comp.Gen FM) (ok : Nat → Bool) (nm : Nomm) : Option Bool :=
  (runL nm (CGoal.toL goal) [] g0).map fun (nex, g) =>
    let m := g.blocks
    defOnceB m && noTrB m && parNodupB m && rkDownB m && argsAboveRkB m && lazyOKB m nex &&
      nex.th.args.isEmpty && decide (1 ≤ nex.th.there) && decide (nex.th.there < g.bo) &&
      (liveAtEntry m nex).all ok

#guard (sixes ++ enumX).all fun nm =>
  checkGoalX (CGoal.next (lazyReg 0) (jmp0 1)) gY (· == 1) nm == some true
#guard ((sixes ++ enumX).filter fun nm => ((runL nm (CGoal.toL (CGoal.next (lazyReg 0) (jmp0 1) : CGoal LS)) [] gY).map
  fun (nex, g) => (liveAtEntry g.blocks nex).contains 1) == some true).length == 3028
#guard (sixes ++ enumX).all fun nm =>
  checkGoalX (CGoal.pick (jmp0 1) (jmp0 2)) gP (fun r => r == 0 || r == 1 || r == 3) nm == some true


/-! ## The predicate `Xup` and what `optIn_finishLFX_of` asks of the run

`Xup` (`RawInvXup.lean`): the label-order `ArgsAbove`, a block that hops
up has no parameter, no jump with arguments targets a block that hops up;
on all runs of `enumX` and under `%next` and `%pick`, and not vacuous (in
3,360 runs a block hops up and a jump has arguments).  `disjB`, the first
half of `LazOK` (`RawInvFinishX.lean`): the sure needs of the root and of
the entries are pairwise disjoint (the second half, nothing defines them,
is in `lazyOKB`). -/

def hopsUpB (m : FM Blob) (k : Nat) : Bool := match m.f k with
  | some ⟨_, _, Termin.hop j⟩ => decide (k < j.there)
  | _ => false

def xupB (m : FM Blob) : Bool :=
  argsAboveB m &&
  (blocksOf m).all (fun (k, b) => b.par.isEmpty || !hopsUpB m k) &&
  (blocksOf m).all (fun (_, b) => (getJmps b.fin).all fun j => j.args.isEmpty || !hopsUpB m j.there)

def disjB (nex : NextL LS) : Bool := nodupB ((nodesOf nex).flatMap fun x => x.2.1)

#guard enumX.all fun nm => ((runX nm).map fun (nex, g) => xupB g.blocks && disjB nex) == some true
#guard (enumX.filter fun nm => ((runX nm).map fun (_, g) =>
  (blocksOf g.blocks).any (fun (k, _) => hopsUpB g.blocks k) &&
  (blocksOf g.blocks).any (fun (_, b) => (getJmps b.fin).any fun j => !j.args.isEmpty)) == some true).length == 3360
#guard (sixes ++ enumX).all fun nm =>
  ((runL nm (CGoal.toL (CGoal.next (lazyReg 0) (jmp0 1) : CGoal LS)) [] gY).map fun (nex, g) =>
    xupB g.blocks && disjB nex) == some true
#guard (sixes ++ enumX).all fun nm =>
  ((runL nm (CGoal.toL (CGoal.pick (jmp0 1) (jmp0 2) : CGoal LS)) [] gP).map fun (_, g) => xupB g.blocks) == some true


/-- The two instances of `RawInvEApart.lean` (a `%6` under a cons, nested
`%6`s): the final pass succeeds, its output passes the checks, and the run
meets `LazOK` with entries. -/
def exEAp : List Nomm :=
  [Nomm.cons (Nomm.n6 (Nomm.n0 2) (Nomm.n0 3) (Nomm.n0 1)) (Nomm.n0 1),
    Nomm.n6 (Nomm.n0 2) (Nomm.n6 (Nomm.n0 6) (Nomm.n0 3) (Nomm.n0 1)) (Nomm.n1 (A 0))]

#guard exEAp.all fun nm => okOut (naryX nm) &&
  ((runX nm).map fun (nex, g) => disjB nex && lazyOKB g.blocks nex && !(entries nex.laz).isEmpty) == some true

/- The instances of `optIn_finishLUX` (`RawInvWholeX.lean`): the whole-subject
pass succeeds on both, `+kerf` makes a proxy (so `+to-straight` takes its map
path), and the output passes `okOut`.  On all of `enumX` `+kerf` makes a
proxy, and every key of `cond` is a proxy for the register of `+kern`. -/
def kerfX (nm : Nomm) : Option (Nat × Comp.Gen FM) :=
  (runX nm).bind fun (nex, g1) => (kerf (S := LS) (Map := FM) nex g1).map fun ((_, sub), g2) => (sub, g2)

#guard exEAp.all fun nm => (mono nm).isSome && okOut (mono nm) &&
  ((kerfX nm).map fun (_, g2) => hasProxies g2.cond) == some true
#guard enumX.all fun nm => match kerfX nm with
  | some (sub, g2) => hasProxies g2.cond && (HoonMapKeys.keys g2.cond).all fun k =>
      match HoonMap.get g2.cond k with
      | some e => e.1 == sub && sub < k
      | none => false
  | none => true

/-! ## The facts of `StInv` (`Compiler/OptLinkTotalInv.lean`) that `OptIn` lacks

Checked for the optimizer's totality (Gaps 13): `Closed` (every jump
targets a block), `ArityOK` (a jump passes as many arguments as its target
has parameters), a block `0`, and `TwoNA` (two-way ends pass no arguments),
on the output of both final passes over all of `enumX`; the raw blocks of
the run meet `Closed`, `ArityOK` and `TwoNA` too (their labels start at
`1`).  Not vacuous: 3,360 n-ary outputs have a jump with arguments. -/

def twoWayB : Termin → Bool
  | Termin.clq .. | Termin.eqq .. | Termin.brn .. | Termin.brz .. | Termin.lti .. => true
  | _ => false

/-- `Closed`, `ArityOK`, `TwoNA` of a block map. -/
def stB (m : FM Blob) : Bool :=
  (blocksOf m).all fun (_, b) => (getJmps b.fin).all fun j =>
    (match m.f j.there with
      | some b2 => j.args.length == b2.par.length
      | none => false) && (!twoWayB b.fin || j.args.isEmpty)

def okSt (o : Option (Straight FM)) : Bool := match o with
  | some c => stB c.blocks && (c.blocks.f 0).isSome
  | none => true

#guard enumX.all fun nm => okSt (naryX nm) && okSt (mono nm) &&
  match runX nm with | some (_, g) => stB g.blocks | none => true
#guard (enumX.filter fun nm => match naryX nm with
  | some c => (blocksOf c.blocks).any fun (_, b) => (getJmps b.fin).any fun j => !j.args.isEmpty
  | none => false).length == 3360

/-! ## `ReadsIn` (`Compiler/OptLinkTotalAlias.lean`), the field `AliasRetN` adds

Every register a reachable block reads (an op or the end) has a definition
in the map or is one of the `nargs` arguments.  On the output of both final
passes over all of `enumX`.  Over all blocks it fails (560 n-ary outputs):
an unreachable fork block passes a register nothing defines, as in the
output of `enumX[340]`, whose block `2` hops to the join `4` with `[2]` and
no block jumps to `2`.  Not vacuous: 3,396 n-ary outputs have a reachable
block that reads an argument with no definition. -/

def readsInB (c : Straight FM) : Bool :=
  let R := reachF c.blocks ((blocksOf c.blocks).length + 1) 0
  (blocksOf c.blocks).all fun (k, b) => !R.contains k ||
    ((b.body.flatMap aliasReads) ++ finRegs b.fin).all fun r => (allDefsL c.blocks).contains r || r < c.nargs

def okReads (o : Option (Straight FM)) : Bool := match o with
  | some c => readsInB c
  | none => true

#guard enumX.all fun nm => okReads (naryX nm) && okReads (mono nm)
#guard (enumX.filter fun nm => match naryX nm with
  | some c => let R := reachF c.blocks ((blocksOf c.blocks).length + 1) 0
      (blocksOf c.blocks).any fun (k, b) => R.contains k &&
        ((b.body.flatMap aliasReads) ++ finRegs b.fin).any fun r => r < c.nargs && !(allDefsL c.blocks).contains r
  | none => false).length == 3396

end Raw
end SkaModel
end Formalization
