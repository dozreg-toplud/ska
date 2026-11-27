import lemmas.Ska.RawInvCheckCX

/-!
# The liveness spec of a run with indirect calls: the check

README Gaps 14 (b), track D.  The run-level liveness for `runLC` (the
analogue of `RawIHX` of `RawInvIHX.lean`), checked on the 3,960 nomms of
`enumCX` (2,856 of them in `PlainN`) under the goals of `RawInvCheckCX.lean`:
`%done` from `gen0`, `%next` with need `0` into the block `1` of `gY`,
`%pick` into `1` and `2` of `gP`, and the goal with a bond `goalB` from `gB`
(need `1` at the hop block `2`, a bond at the block `1` with need `0`).

**The statement (candidate 1, `live1`, `live1K`).**  Write `unpB g` for
the blocks of `g` with every register `r` read as `unproxy g.cond r` (a read
through a proxy is a read of the register the proxy stands for).  A run
for `goal` from `g0` to `(nex, g1)`, with kills `K` on the old labels:
every register live at `nex.th.there` in `unpB g1`, each entry of the
result's lazy tree first defining its sure need (kills `K` and `lazK
nex.th.there nex.laz`), is
* for `%next laz th`: live at `th.there` in `unpB g0`, each entry of the
  goal's lazy tree (the root `th.there` with `laz.sure` included) first
  defining its sure need (kills `K` and `lazK th.there laz`);
* for `%pick z o`: live at `z.there` or at `o.there` in `unpB g0` (kills `K`);
* for `%done`: nothing.
It holds on every run under every goal, also with outer kills.  When the
lazy block of a proxy is never forced (the block where `+kern` reads it is
not reached from the entry), the read is on no path from the entry and the
statement says nothing about it; when it is reached, every path to it
passes the definition of the proxied register first (the `%nok` of the
call, which writes `+kern`'s register), so the statement makes that
register not live.

**Candidates that failed.**
* Candidate 0 (`live0`): the same without `unproxy`.  It fails on 336
  runs under `%done` and under `%next`, on 80 under `%pick`, and on every
  run with a proxy in an old block under the bond goal (3,768 of the 3,912
  that return): the proxies are read and never defined, so they are live.

**What replaces "lazy entries at distinct labels".**  Nothing about labels:
`lazyOK2B` (each entry's block has no parameter and no block defines the
registers of an entry's sure need) with `disjB` (the sure needs of the
root and the entries are pairwise disjoint) hold on every top run; that is
`LazOK` of `RawInvFinishX.lean` as it stands (it never asked distinct
labels), and the definitions stay one per register after `unproxy`.

**The shape of the old blocks after a run (`prepOld`).**  Under every
goal, every block of `g0` is in `g1` with ops in front (`Prep`), and the
ops are nonempty only at labels of the goal's lazy entries.  Not vacuous:
under the bond goal 3,888 runs (2,832 in `PlainN`) read a proxy in an old
block, register `1` is live at the result's entry under `%next` in 3,840
runs, some register under `%pick` in 3,168, and 1,926 runs of `PlainN`
return a lazy need with entries under the bond goal.
-/

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

/-- The blocks with every proxy read as its definition. -/
def unpB (g : Comp.Gen FM) : FM Blob := mapVals (renBlob (unproxy g.cond)) g.blocks

/-- The kills of a lazy need entered at `o`: each entry of its lazy tree
first defines the registers of its sure need (the form of `lazK`). -/
def killsOf (o : Nat) (l : Lazy LS) : List (Nat × List Nat) :=
  (nodesF 30 [] (o, l)).map fun x => (x.1, x.2.1)

def fuelOf (g : Comp.Gen FM) : Nat := (blocksOf g.blocks).length + 1

/-- Live at the result's entry, the result's lazy entries killing their needs. -/
def liveRes (m : FM Blob) (g : Comp.Gen FM) (nex : NextL LS) : List Nat :=
  liveKF m (killsOf nex.th.there nex.laz) (fuelOf g) nex.th.there

/-- What may be live at the goal: at its continuation, the goal's own lazy
entries killing their needs (`%next`), at either target (`%pick`). -/
def goalLive (m : FM Blob) (g0 : Comp.Gen FM) : CGoalL LS → List Nat
  | CGoalL.next laz th => liveKF m (killsOf th.there laz) (fuelOf g0) th.there
  | CGoalL.pick z o => liveKF m [] (fuelOf g0) z.there ++ liveKF m [] (fuelOf g0) o.there
  | CGoalL.done => []

/-- Candidate 0: `RawIHX`'s liveness as it is (no unproxy) over lazy goals. -/
def live0 (goal : CGoalL LS) (g0 : Comp.Gen FM) (nm : Nomm) : Option Bool :=
  (runCG goal g0 nm).map fun (nex, g) => (liveRes g.blocks g nex).all (goalLive g0.blocks g0 goal).contains

/-- Candidate 1: modulo `unproxy` on both sides. -/
def live1 (goal : CGoalL LS) (g0 : Comp.Gen FM) (nm : Nomm) : Option Bool :=
  (runCG goal g0 nm).map fun (nex, g) => (liveRes (unpB g) g nex).all (goalLive (unpB g0) g0 goal).contains

def isPlain : Nomm → Bool
  | Nomm.n0 _ => true
  | Nomm.n1 _ => true
  | Nomm.n3 p => isPlain p
  | Nomm.n4 p => isPlain p
  | Nomm.n5 p q => isPlain p && isPlain q
  | Nomm.cons p q => isPlain p && isPlain q
  | Nomm.n7 p q => isPlain p && isPlain q
  | Nomm.n10 _ v q => isPlain v && isPlain q
  | Nomm.n2 p q Option.none => isPlain p && isPlain q
  | _ => false

def goalY : CGoalL LS := CGoalL.next (ofSure (lazyReg 0)) (jmp0 1)
def goalP : CGoalL LS := CGoalL.pick (jmp0 1) (jmp0 2)

def cnt (f : Nomm → Option Bool) (l : List Nomm) : Nat × Nat × Nat :=
  ((l.filter fun nm => f nm == some true).length, (l.filter fun nm => f nm == some false).length,
   (l.filter fun nm => f nm == Option.none).length)

/-- Candidate 1 with outer kills `K` on both sides. -/
def live1K (K : List (Nat × List Nat)) (goal : CGoalL LS) (g0 : Comp.Gen FM) (nm : Nomm) : Option Bool :=
  (runCG goal g0 nm).map fun (nex, g) =>
    let G := match goal with
      | CGoalL.next laz th => liveKF (unpB g0) (K ++ killsOf th.there laz) (fuelOf g0) th.there
      | CGoalL.pick z o => liveKF (unpB g0) K (fuelOf g0) z.there ++ liveKF (unpB g0) K (fuelOf g0) o.there
      | CGoalL.done => []
    (liveKF (unpB g) (K ++ killsOf nex.th.there nex.laz) (fuelOf g) nex.th.there).all G.contains

/-- The labels of the goal's lazy entries. -/
def goalLabs : CGoalL LS → List Nat
  | CGoalL.next laz th => (killsOf th.there laz).map (·.1)
  | _ => []

/-- The old blocks after the run: each is the old block with ops in front,
and ops only at the goal's lazy entries. -/
def prepOld (goal : CGoalL LS) (g0 : Comp.Gen FM) (nm : Nomm) : Option Bool :=
  (runCG goal g0 nm).map fun (_, g) =>
    (blocksOf g0.blocks).all fun (k, b) => match g.blocks.f k with
      | some b' => match prefixOf b b' with
        | some A => A.isEmpty || (goalLabs goal).contains k
        | none => false
      | none => false

/-- Some proxy is read in an old block (a goal's lazy entry). -/
def proxyOld (goal : CGoalL LS) (g0 : Comp.Gen FM) (nm : Nomm) : Bool :=
  match runCG goal g0 nm with
  | some (_, g) => (blocksOf g0.blocks).any fun (k, _) => match g.blocks.f k with
      | some b' => b'.body.any fun op => (aliasReads op).any fun r => (HoonMap.get g.cond r).isSome
      | none => false
  | none => false

/-- `lazyOKB` without the distinct labels. -/
def lazyOK2B (m : FM Blob) (nex : NextL LS) : Bool :=
  let D := allDefsL m
  (nodesOf nex).all fun x =>
    (match m.f x.1 with | some b => b.par.isEmpty | none => true) && x.2.1.all fun r => ! D.contains r

def topOK (nm : Nomm) : Option Bool :=
  (runC nm).map fun (nex, g) => lazyOK2B g.blocks nex && disjB nex && defOnceB (unpB g)

#guard (enumCX.filter isPlain).length == 2856

/-! ## Candidate 1 holds -/

#guard cnt (live1 CGoalL.done gen0) enumCX == (3960, 0, 0)
#guard cnt (live1 goalY gY) enumCX == (3960, 0, 0)
#guard cnt (live1 goalP gP) enumCX == (3960, 0, 0)
#guard cnt (live1 goalB gB) enumCX == (3912, 0, 48)
#guard (goalLive (unpB gY) gY goalY, goalLive (unpB gP) gP goalP, goalLive (unpB gB) gB goalB) ==
  ([1], [0, 1, 3], [])
/- With outer kills. -/
#guard cnt (live1K [(1, [1])] goalY gY) enumCX == (3960, 0, 0)
#guard cnt (live1K [(1, [0])] goalB gB) enumCX == (3912, 0, 48)
#guard cnt (live1K [(1, [1]), (2, [0])] goalP gP) enumCX == (3960, 0, 0)

/-! ## Candidate 0 fails -/

#guard cnt (live0 CGoalL.done gen0) enumCX == (3624, 336, 0)
#guard cnt (live0 goalY gY) enumCX == (3624, 336, 0)
#guard cnt (live0 goalP gP) enumCX == (3880, 80, 0)
#guard cnt (live0 goalB gB) enumCX == (144, 3768, 48)

/-! ## The lazy entries, the old blocks, not vacuous -/

#guard cnt topOK enumCX == (3960, 0, 0)
#guard cnt (prepOld goalY gY) enumCX == (3960, 0, 0)
#guard cnt (prepOld goalB gB) enumCX == (3912, 0, 48)
#guard cnt (prepOld goalP gP) enumCX == (3960, 0, 0)
#guard (enumCX.filter (proxyOld goalB gB)).length == 3888
#guard (enumCX.filter fun nm => isPlain nm && proxyOld goalB gB nm).length == 2832
#guard (enumCX.filter fun nm => ((runCG goalY gY nm).map fun (nex, g) =>
  (liveRes (unpB g) g nex).contains 1) == some true).length == 3840
#guard (enumCX.filter fun nm => ((runCG goalP gP nm).map fun (nex, g) =>
  !(liveRes (unpB g) g nex).isEmpty) == some true).length == 3168
#guard ((enumCX.filter isPlain).filter fun nm => ((runCG goalB gB nm).map fun (nex, _) =>
  !(entries nex.laz).isEmpty) == some true).length == 1926

end Raw
end SkaModel
end Formalization
