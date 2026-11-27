import lemmas.Ska.RawInvStep
import lemmas.Ska.CompWhole

/-!
# Raw `+comp` output: executable checks of the invariant

README Gaps 14.  Checkers that evaluate, on the map `FM` and the set `LS` of
`CompCall.lean`, for the eight fields of `OptIn` on the output of the final
pass (`checkOut`), and for the run-level invariant on the raw blocks of a run
for `%done` from `gen0` (`checkRun`): one definition per register over all
blocks, every register live at the run's entry a register of its result's
need, blocks that jump down, at most one parameter, arguments above the
parameters at or below their target, no trace hint op.

`DefFirst` is checked through liveness at block `0` (`liveF`, with fuel the
number of blocks), `Acyclic` and `DownPar` through reachability with the
same fuel.  The `#guard`s: `[10 [6 0 1] 5 [0 6] 0 1]` (a fill of
`+crash-need`: block `3` of the n-ary output is `cel va, imm 0 vb`),
`[4 [3 [0 1]]]` (the join of `+forl`, one parameter), `[[0 2] [0 3]]`, and
the first fragment and `FragX` on enumerated nomms (`enum1`, `enum6`); with
indirect calls `[2 b c]` through `finishLUC envR`.
-/

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp

/-! ## Checkers -/

def blocksOf (m : FM Blob) : List (Nat × Blob) :=
  (m.ks.eraseDups).filterMap fun k => (m.f k).map fun b => (k, b)

def allDefsL (m : FM Blob) : List Nat := (blocksOf m).flatMap fun (_, b) => blockDefs b

def nodupB (l : List Nat) : Bool := l.eraseDups.length == l.length

def defOnceB (m : FM Blob) : Bool := nodupB (allDefsL m)
def parNodupB (m : FM Blob) : Bool := (blocksOf m).all fun (_, b) => nodupB b.par
def par1B (m : FM Blob) : Bool := (blocksOf m).all fun (_, b) => b.par.length ≤ 1
def noLtiB (m : FM Blob) : Bool :=
  (blocksOf m).all fun (_, b) => match b.fin with | Termin.lti .. => false | _ => true
def noTrB (m : FM Blob) : Bool := (blocksOf m).all fun (_, b) => b.body.all (! trOp ·)
def jdownB (m : FM Blob) : Bool := (blocksOf m).all fun (k, b) => (getJmps b.fin).all (·.there < k)

def succs (m : FM Blob) (k : Nat) : List Jmp := match m.f k with | some b => getJmps b.fin | none => []

/-- The labels reachable from `k`, with fuel. -/
def reachF (m : FM Blob) : Nat → Nat → List Nat
  | 0, k => [k]
  | f + 1, k => k :: (succs m k).flatMap fun j => reachF m f j.there

def passOKB (m : FM Blob) : Bool :=
  (blocksOf m).all fun (_, b) => (getJmps b.fin).all fun j =>
    match m.f j.there with
    | some b2 => (jmpRegs j).all fun r => ! b2.par.contains r
    | none => true

def downParB (m : FM Blob) : Bool :=
  let n := (blocksOf m).length + 1
  (blocksOf m).all fun (_, b) => (getJmps b.fin).all fun j =>
    (reachF m n j.there).all fun z => match m.f z with
      | some bz => (jmpRegs j).all fun r => ! bz.par.contains r
      | none => true

def argsAboveB (m : FM Blob) : Bool :=
  (blocksOf m).all fun (_, b) => (getJmps b.fin).all fun j => (jmpRegs j).all fun r =>
    (blocksOf m).all fun (z, bz) => !(z ≤ j.there) || bz.par.all (· < r)

def acyclicB (m : FM Blob) : Bool :=
  let n := (blocksOf m).length + 1
  (blocksOf m).all fun (k, _) => (succs m k).all fun j => ! (reachF m n j.there).contains k

/-- The registers live at block `k`, with fuel. -/
def liveF (m : FM Blob) : Nat → Nat → List Nat
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
        (liveF m f j.there).filter fun r => ! (blockDefs b).contains r
      (here ++ after).eraseDups

def defFirstB (m : FM Blob) : Bool :=
  let D := allDefsL m
  (liveF m ((blocksOf m).length + 1) 0).all fun r => ! D.contains r

/-- The eight fields of `OptIn` (`trimBr` as "no trace hint op"). -/
def checkOut (m : FM Blob) : Bool :=
  parNodupB m && passOKB m && acyclicB m && downParB m && noTrB m && defFirstB m && noLtiB m && defOnceB m

/-- The run-level invariant on the raw blocks of a run for `%done`. -/
def checkRun (nm : Nomm) : Option Bool :=
  (run nm (CGoal.done : CGoal LS) (gen0 : Comp.Gen FM)).map fun (nex, g) =>
    let m := g.blocks
    defOnceB m && jdownB m && par1B m && argsAboveB m && noTrB m &&
      (liveF m ((blocksOf m).length + 1) nex.th.there).all fun r => (flattenNeed nex.laz.ned).contains r

def okOut (o : Option (Straight FM)) : Bool := match o with | some c => checkOut c.blocks | none => true
def okRun (o : Option Bool) : Bool := o.getD true

def nary (nm : Nomm) (ord : NeedOrd) : Option (Straight FM) :=
  finishLF (S := LS) (Map := FM) nm ord Cape.no (fun ned => (ned, []))
def mono (nm : Nomm) : Option (Straight FM) := finishLU (S := LS) (Map := FM) nm

/-! ## Concrete runs -/

/-- `[10 [6 0 1] 5 [0 6] 0 1]`: the fill of `+crash-need` writes `va` only. -/
def exCrash : Nomm := Nomm.n10 6 (Nomm.n0 1) (Nomm.n5 (Nomm.n0 6) (Nomm.n0 1))
/-- `[4 [3 [0 1]]]`: the join of `+forl` has one parameter. -/
def exForl : Nomm := Nomm.n4 (Nomm.n3 (Nomm.n0 1))
/-- `[[0 2] [0 3]]`. -/
def exCons : Nomm := Nomm.cons (Nomm.n0 2) (Nomm.n0 3)

#guard checkRun exCrash == some true
#guard checkRun exForl == some true
#guard checkRun exCons == some true
#guard okOut (mono exCrash) && (mono exCrash).isSome
#guard okOut (nary exCrash (NeedOrd.both NeedOrd.none (NeedOrd.pair NeedOrd.this NeedOrd.none))) &&
  (nary exCrash (NeedOrd.both NeedOrd.none (NeedOrd.pair NeedOrd.this NeedOrd.none))).isSome
#guard okOut (mono exForl) && okOut (nary exForl NeedOrd.this) && (mono exForl).isSome
#guard okOut (mono exCons) && (mono exCons).isSome

/- The raw run of `[4 [3 [0 1]]]`: the join `0w2` has the parameter `v1`,
the branches `0w3`, `0w4` pass `v2`, `v3`. -/
#guard ((run exForl (CGoal.done : CGoal LS) (gen0 : Comp.Gen FM)).map fun (_, g) => g.blocks.f 2) ==
  some (some ⟨[1], [], Termin.hop (jmp0 1)⟩)

/-! ## Enumerated nomms -/

def leaves : List Nomm :=
  [Nomm.n0 1, Nomm.n0 2, Nomm.n0 3, Nomm.n0 6, Nomm.n0 7, Nomm.n0 0, Nomm.n1 (A 0), Nomm.n1 (A 1),
   Nomm.n1 (A 5), Nomm.n1 (C (A 1) (A 2))]

def grow (l : List Nomm) : List Nomm :=
  l ++ l.flatMap (fun p => [Nomm.n3 p, Nomm.n4 p]) ++
  (l.flatMap fun p => (l.take 6).flatMap fun q =>
    [Nomm.cons p q, Nomm.n5 p q, Nomm.n7 p q, Nomm.n10 6 p q, Nomm.n10 2 q p])

def grow6 (l : List Nomm) : List Nomm :=
  l ++ (l.take 12).flatMap fun p => (l.take 8).flatMap fun q => (l.take 5).map fun r => Nomm.n6 p q r

/-- The first fragment: 520 nomms. -/
def enum1 : List Nomm := grow (leaves ++ ((grow leaves).drop 10).take 30)
/-- With `%6`: 360 nomms. -/
def enum6 : List Nomm := grow6 (leaves ++ ((grow leaves).drop 10).take 20)

#guard enum1.all fun nm => okRun (checkRun nm) && okOut (mono nm) && okOut (nary nm NeedOrd.this)
#guard enum6.all fun nm => okOut (mono nm) && okOut (nary nm NeedOrd.this)

/-- With indirect calls. -/
def enumC : List Nomm :=
  (enum6.take 40).flatMap fun p =>
    [Nomm.n2 p (Nomm.n0 2) Option.none, Nomm.cons (Nomm.n2 (Nomm.n0 3) p Option.none) (Nomm.n0 1),
     Nomm.n6 (Nomm.n0 2) (Nomm.n2 p (Nomm.n0 2) Option.none) p]

#guard enumC.all fun nm => okOut (finishLUC (S := LS) (Map := FM) envR nm)

end Raw
end SkaModel
end Formalization
