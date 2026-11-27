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

end Raw
end SkaModel
end Formalization
