import lemmas.Ska.RawInvCLCheckSix

/-!
# `%6`: a rank that is not the label, and the specs of `+fork`, `+fork-sure`, `+sect`

README Gaps 14 (b), track D.  `RawInvCLCheckSix.lean` found that at `%6`
the down clause of `ATS` and the label rank `upRk` fail (`+fork-need`'s
`o0`/`o1` hop UP to the join; `+fork`'s `insertHop` turns an old entry block
into a hop to a new block), while `ATS6` (down or a hop, no cycle) holds.
Here `ksrRun` is `csxRun` (the text of `runLC` with every sub-run wrapped)
with the wrapper `ksrWrap` and with the `%6` arm `ksrSix`, a copy of
`sixNextLC` in which the calls of `+fork` (`forkL`), `+fork-sure` and `+sect`
are checked against their specs.  The modes: `c < 100` a clause before the
sub-run, `100 + c` the clause after (on the result), `200 + c` a relation
between the two states, `300`.. the specs.

**Rank candidates** (`ksrPre1`), at every sub-run of the families of
`RawInvCLCheckSix.lean`:
* (b) `ksrRkB` (the label, but a block with no body that hops ranks one
  above its target) FAILS (`73`): 101 of 2,940 on `csxS2 × csxGoalsL`, the
  witness `csxW2`, 404 of 11,760 on the rest of `sixes`: after `insertHop`
  the entry block `a` is `[par, [], hop oi1]` with `oi1` new (high label),
  so a block that jumped down to `a` now jumps up in rank.
* (c) `ksrRkC` (the label of the nearest block along hops that does not
  end in `hop`) FAILS (`74`) on `csxW2`.
* (a) the HEIGHT `ksrHgt` (the longest jump path to a block with no jump)
  falls along every jump (`75`) iff there is no cycle; with "no dangling
  jump" (`70`: every jump targets a label that has a block) it holds at
  every sub-run, before and after (`70`, `71`, `75`, `76` = `ATS6` and no
  dangling jump; `170` .. `176`): 0 failures on all families.  The
  mutations bite: every jump to a block with no parameter (`90`), the
  height with too little fuel (`92`).
* The frame that makes it inductive (`ksrRel`, 0 failures): an old block
  keeps its jump targets unless it is a goal entry that now hops to a new
  block (`80`; without the exception it fails, `83`); a new block jumps to
  new blocks, to the goal's jump targets, or to old targets of the goal's
  entries (`81`; "new blocks only" fails, `84`); no old block but a goal
  entry reaches a new block except through a goal entry (`82`).
* The clause "no lazy entry is reachable from the goal's jump target"
  (`72`) is FALSE (580 of 2,940 before, all after): it is not needed.

What each step does to "no cycle and no dangling jump": `emit` puts a
block at `bo`, which no block jumps to (no dangling jump), so no cycle
through it; `emir` at a reserved label (`+fork-need`'s `o0`, `o1`, and the
`o0k`/`o1k` of the bonds and forks) is the same, as no block jumps to a
label with no block; `addOps`, `setTag`, `copyTag`, `+sect`'s `jabBlock`
(parameters of the join, arguments of the two ends' hops) keep every jump
target; `insertHop a oi1 oi2` adds the edge `a -> oi1` where `oi1` (the
`brz` on the proxy of the test) reaches only `o0k`, `o1k`, their join and
`oi2`, which holds `a`'s old body and jumps to `a`'s old targets, none of
which reaches `a` (no cycle before).  In the middle of `+fork` the join of a
bond hops to `oi2` before `insertHop` fills it (a dangling jump), so the
invariant is stated at the ends of `+fork` and of the runs, not at every
primitive.

**Specs checked alone** (inside `ksrSix`, at every call whose
precondition holds; coverage modes `310` .. `312` fail exactly there):
* `ksrForkSureSpec` (`301`): reserved `o0`, `o1` (no block, below `bo`)
  and a block at `o`: the old blocks are kept, three new blocks (the join at
  `bo` with `sur`'s registers as parameters and `hop o`, `o0`, `o1` hopping
  to it with the new needs' registers), the new needs fresh, apart, of
  `sur`'s length, no cycle and no dangling jump kept.  0 failures (1,332
  calls on `csxS2 × csxGoalsL`, 258 on `csxS1 × csxGoals7`; in scratch
  5,328 on the rest of `sixes` under `csxGoalsL`, about 4 minutes).
* `ksrForkSpec` (`300`; components `320 + i`): from `ATS6`, no dangling jump
  and no cycle, the halves meet `ATS6` (with the same kills), no dangling
  jump, no cycle, trees apart and fresh, the old blocks change only at the
  goal's entries (ops in front or the `insertHop` shape, `csxPost1 54`), the
  old jumps are kept but at the entries; and what is live at a half's entry
  (killing its tree) is live at the goal, or is the test's register `rc` or
  a register of the OTHER half's tree.  0 failures (416 calls, and 1,664 on
  the rest of `sixes`).  Without the last two exceptions it FAILS (`327`,
  `328`: 208 of 416; with `rc` only, `332`, `333`: 208): the bond's `brz`
  on the proxy of `rc` reaches both kids, and the liveness, blind to the
  test, sees the other half's registers (on a flat goal with one bond at `csxGL`,
  `+fork` alone: half 0 live `[4, 6, 8]`, `rc = 4`, the other half's tree
  `[6, 8]`; scratch).
* `ksrSectSpec` (`302`): from two halves meeting `ATS6` with no dangling
  jump, the fork lazy meets `ATS6` at either new block, no dangling jump,
  the old blocks keep their bodies and jump targets, and what is live at
  the new blocks (killing the fork's trees) is live at the halves' entries.
  0 failures (1,748 calls on `csxS2 × csxGoalsL`, 6,992 on the rest of
  `sixes`, 258 on `csxS1`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

/-! ## Candidates for a rank that is not the label -/

/-- **No dangling jump**: every jump of every block targets a label that
has a block. -/
def ksrNoDangle (m : FM Blob) : Bool :=
  (blocksOf m).all fun (_, b) => (getJmps b.fin).all fun j => (m.f j.there).isSome

/-- The labels reachable from `todo` (zero or more jumps). -/
def ksrReach (m : FM Blob) : Nat → List Nat → List Nat → List Nat
  | 0, seen, _ => seen
  | _ + 1, seen, [] => seen
  | f + 1, seen, k :: todo =>
    if seen.contains k then ksrReach m f seen todo else
    let ts := match m.f k with | some b => (getJmps b.fin).map (·.there) | none => []
    ksrReach m f (k :: seen) (ts ++ todo)

def ksrReachOf (m : FM Blob) (ks : List Nat) : List Nat := ksrReach m (4 * (blocksOf m).length + 8) [] ks

/-- No lazy entry of the goal (other than its jump target) is reachable
from the goal's jump target. -/
def ksrEntUp (goal : CGoalL LS) (g : Comp.Gen FM) : Bool :=
  match goal with
  | CGoalL.next laz th =>
    let R := ksrReachOf g.blocks [th.there]
    (entries laz).all fun e => e.1 == th.there || !R.contains e.1
  | _ => true

/-- (b) The label, but a block with no body that hops gets its target's
rank plus one. -/
def ksrRkB (m : FM Blob) : Nat → Nat → Nat
  | 0, k => 3 * k
  | f + 1, k => match m.f k with
    | some ⟨_, [], Termin.hop t⟩ => ksrRkB m f t.there + 1
    | _ => 3 * k

/-- (c) The label of the nearest block along hops that does not end in
`hop`, plus the number of hops. -/
def ksrRkC (m : FM Blob) : Nat → Nat → Nat
  | 0, k => 3 * k
  | f + 1, k => match m.f k with
    | some ⟨_, _, Termin.hop t⟩ => ksrRkC m f t.there + 1
    | _ => 3 * k

def ksrDesc (m : FM Blob) (rk : Nat → Nat) : Bool :=
  (blocksOf m).all fun (k, b) => (getJmps b.fin).all fun j => rk j.there < rk k

/-- (a) The height: the longest jump path to a block with no jump (or no
block). -/
def ksrHgt (m : FM Blob) : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, k => match m.f k with
    | some b => ((getJmps b.fin).map fun j => ksrHgt m f j.there + 1).foldl max 0
    | none => 0

def ksrFuel (m : FM Blob) : Nat := (blocksOf m).length + 2

/-- The candidate `ATS6` of `RawInvCLCheckSix.lean` (`csxCandPre6`). -/
def ksrCand6 (K : List (Nat × List Nat)) (goal : CGoalL LS) (g : Comp.Gen FM) : Bool :=
  csxCandPre6.all fun c => csxPre1 c K goal g

/-- One clause of the precondition: the old ones (`< 70`), and the new. -/
def ksrPre1 (c : Nat) (K : List (Nat × List Nat)) (goal : CGoalL LS) (g : Comp.Gen FM) : Bool :=
  match c with
  | 70 => ksrNoDangle g.blocks
  | 71 => csxAcyc g.blocks && ksrNoDangle g.blocks
  | 72 => ksrEntUp goal g
  | 73 => ksrDesc g.blocks (ksrRkB g.blocks (ksrFuel g.blocks))
  | 74 => ksrDesc g.blocks (ksrRkC g.blocks (ksrFuel g.blocks))
  | 75 => ksrDesc g.blocks (ksrHgt g.blocks (ksrFuel g.blocks))
  | 76 => ksrCand6 K goal g && ksrNoDangle g.blocks
  | 77 => ksrCand6 K goal g && ksrNoDangle g.blocks && ksrEntUp goal g
  -- mutations: every jump to a block with no parameter; the goal's jump
  -- target reaches no other block; heights with too little fuel
  | 90 => (blocksOf g.blocks).all fun (_, b) => (getJmps b.fin).all fun j =>
      match g.blocks.f j.there with | some bt => bt.par.isEmpty | none => false
  | 91 => (match goal with
      | CGoalL.next _ th => (ksrReachOf g.blocks [th.there]).length ≤ 1
      | _ => true)
  | 92 => ksrDesc g.blocks (ksrHgt g.blocks 2)
  | c => csxPre1 c K goal g

/-- The relations between the states before and after a run. -/
def ksrRel (c : Nat) (goal : CGoalL LS) (g0 g1 : Comp.Gen FM) : Bool :=
  let tg := fun (b : Blob) => (getJmps b.fin).map (·.there)
  let L := goalLabs goal
  let old := fun k => (g0.blocks.f k).isSome
  match c with
  -- an old block keeps its jump targets, or it is a goal entry that now hops
  -- to a new block (`insertHop`)
  | 80 => (blocksOf g1.blocks).all fun (k, b') => match g0.blocks.f k with
      | none => true
      | some b => tg b' == tg b || (L.contains k && match b'.fin with
          | Termin.hop t => !old t.there
          | _ => false)
  -- a new block jumps to new blocks, the goal's jump targets, or the old
  -- targets of the goal's entries
  | 81 => (blocksOf g1.blocks).all fun (k, b) => old k || (tg b).all fun t =>
      !old t || (csxJmps goal).any (·.there == t) ||
        L.any fun e => match g0.blocks.f e with | some be => (tg be).contains t | none => false
  -- no old block reaches a new block in `g1` but through a goal entry
  | 82 => (blocksOf g0.blocks).all fun (k, _) => L.contains k ||
      (ksrReachOf g1.blocks [k]).all fun t => old t || (L.any fun e => (ksrReachOf g1.blocks [k]).contains e)
  -- mutations: no exception at the entries; new blocks jump to new blocks only
  | 83 => (blocksOf g1.blocks).all fun (k, b') => match g0.blocks.f k with
      | none => true
      | some b => tg b' == tg b
  | 84 => (blocksOf g1.blocks).all fun (k, b) => old k || (tg b).all fun t => !old t
  | _ => true

def ksrPre (M : Nat) (K : List (Nat × List Nat)) (goal : CGoalL LS) (g : Comp.Gen FM) : Bool := ksrPre1 M K goal g

def ksrPost (M : Nat) (K : List (Nat × List Nat)) (goal : CGoalL LS) (g0 g1 : Comp.Gen FM) (nex : NextL LS) : Bool :=
  if M < 200 then ksrPre1 (M - 100) K nex.goal g1 else ksrRel (M - 200) goal g0 g1

/-- A sub-run checked at clause `M` (`< 100` before, `100 + c` the clause
`c` after on the result, `200 + c` the relation `c`); the modes from `300`
on check the specs inside `%6` (`ksrSix`) and leave the sub-runs alone. -/
def ksrWrap (M : Nat) (Sel : Nat → Nomm → Bool) (tag : Nat) (nm : Nomm) (K : List (Nat × List Nat))
    (rp : CGoalL LS → List Nat → CM FM (NextL LS)) : CGoalL LS → List Nat → CM FM (NextL LS) := fun goal region g0 =>
  let on := Sel tag nm
  if on && M < 100 && !(ksrPre M K goal g0) then Option.none else
  match rp goal region g0 with
  | some (nex, g1) => if on && 100 ≤ M && M < 300 && !(ksrPost M K goal g0 g1 nex) then Option.none else some (nex, g1)
  | Option.none => Option.none

/-! ## The specs of `+fork`, `+fork-sure`, `+sect`, checked alone -/

def ksrRegs (l : Lazy LS) : List Nat := (nodesF 30 [] (0, l)).flatMap (·.2.1)

/-- **`ForkSureSpec`**: from reserved labels `o0`, `o1` with no block and a
block at `o`: the old blocks are kept; three new blocks: the join `barg`
(`bo`, the parameters of `sur`, `hop o`) and `o0`, `o1` hopping to it with
the new needs' registers; the two new needs are fresh, apart, of the
shape of `sur`'s; no dangling jump and no cycle are kept. -/
def ksrForkSureSpec (sur : Sure LS) (o o0 o1 : Nat) (g0 g1 : Comp.Gen FM) (x : Sure LS × Sure LS) : Bool :=
  let n0 := flattenNeed x.1.ned
  let n1 := flattenNeed x.2.ned
  let barg := g0.bo
  (blocksOf g0.blocks).all (fun (k, b) => g1.blocks.f k == some b) &&
  (blocksOf g1.blocks).all (fun (k, _) => (g0.blocks.f k).isSome || k == barg || k == o0 || k == o1) &&
  g1.blocks.f barg == some ⟨flattenNeed sur.ned, [], Termin.hop (jmp0 o)⟩ &&
  g1.blocks.f o0 == some ⟨[], [], Termin.hop ⟨n0.map some, barg⟩⟩ &&
  g1.blocks.f o1 == some ⟨[], [], Termin.hop ⟨n1.map some, barg⟩⟩ &&
  nodupB (n0 ++ n1) && (n0 ++ n1).all (fun r => g0.re ≤ r && r < g1.re) &&
  n0.length == (flattenNeed sur.ned).length && n1.length == n0.length &&
  (!(csxAcyc g0.blocks && ksrNoDangle g0.blocks) || (csxAcyc g1.blocks && ksrNoDangle g1.blocks))

/-- What is live at the entry of `nex` in `g1`, killing its tree, lies in
what is live at `goal` in `g0` or in `extra`. -/
def ksrLiveIn (K : List (Nat × List Nat)) (goal : CGoalL LS) (g0 g1 : Comp.Gen FM) (nex : NextL LS)
    (extra : List Nat) : Bool :=
  let G := match goal with
    | CGoalL.next laz th => liveKF (unpB g0) (K ++ killsOf th.there laz) (fuelOf g0) th.there
    | CGoalL.pick z o => liveKF (unpB g0) K (fuelOf g0) z.there ++ liveKF (unpB g0) K (fuelOf g0) o.there
    | CGoalL.done => []
  (liveKF (unpB g1) (K ++ killsOf nex.th.there nex.laz) (fuelOf g1) nex.th.there).all fun r =>
    G.contains r || extra.contains r

/-- **`ForkSpec`** (component `i`, or all for `i = 99`): from a goal meeting
`ATS6` with no dangling jump, the two halves meet it at the end (with the
same kills) (0, 1), no dangling jump (2), their trees are apart (3) and
fresh (4), the old blocks change only at the goal's entries (ops in front or
the `insertHop` shape, `csxPost1 54`) (5), the old jumps are kept but at the
entries (`ksrRel 80`) (6), what is live at each half's entry (killing its
tree) is live at the goal (`liveCB`) (7, 8), or is the test's register
`rc` or a register of the OTHER half's tree (9, 10), and no cycle (11);
12, 13: 9, 10 with `rc` only. -/
def ksrForkSpec (i : Nat) (K : List (Nat × List Nat)) (laz : Lazy LS) (th : Jmp) (rc : Nat) (g0 g1 : Comp.Gen FM)
    (x : NextL LS × NextL LS) : Bool :=
  let goal := CGoalL.next laz th
  let R0 := ksrRegs x.1.laz
  let R1 := ksrRegs x.2.laz
  let cs : List Bool := [ksrCand6 K x.1.goal g1, ksrCand6 K x.2.goal g1, ksrNoDangle g1.blocks,
    nodupB (R0 ++ R1), (R0 ++ R1).all (fun r => g0.re ≤ r && r < g1.re),
    csxPost1 54 K goal g0 g1 x.1, ksrRel 80 goal g0 g1,
    liveCB K goal g0 g1 x.1, liveCB K goal g0 g1 x.2,
    ksrLiveIn K goal g0 g1 x.1 (rc :: R1), ksrLiveIn K goal g0 g1 x.2 (rc :: R0), csxAcyc g1.blocks,
    ksrLiveIn K goal g0 g1 x.1 [rc], ksrLiveIn K goal g0 g1 x.2 [rc]]
  if i == 99 then (cs.take 7 ++ (cs.drop 9).take 3).all id else cs.getD i true

/-- **`SectSpec`**: from two halves meeting `ATS6` with no dangling jump,
the fork lazy (root `bunt`, one fork entry at the two new blocks) meets it
at the end at either new block; the old blocks keep their bodies and their
jump targets (the join gets parameters, the two ends' hops get arguments);
and what is live at the new blocks, killing the fork's trees, is live at the
halves' entries. -/
def ksrSectSpec (K : List (Nat × List Nat)) (nex0 nex1 : NextL LS) (g0 g1 : Comp.Gen FM)
    (x : Lazy LS × Nat × Nat) : Bool :=
  let tg := fun (b : Blob) => (getJmps b.fin).map (·.there)
  ksrCand6 K (CGoalL.next x.1 (jmp0 x.2.1)) g1 && ksrCand6 K (CGoalL.next x.1 (jmp0 x.2.2)) g1 &&
  ksrNoDangle g1.blocks &&
  (blocksOf g0.blocks).all (fun (k, b) => match g1.blocks.f k with
    | some b' => b'.body == b.body && tg b' == tg b
    | none => false) &&
  liveCB K nex0.goal g0 g1 ⟨nex0.laz, jmp0 x.2.1⟩ && liveCB K nex1.goal g0 g1 ⟨nex1.laz, jmp0 x.2.2⟩

/-- A spec checked: `none` when the precondition holds and the post fails. -/
def ksrSpec {α : Type} (on : Bool) (pre : Bool) (m : CM FM α) (post : Comp.Gen FM → Comp.Gen FM → α → Bool) :
    CM FM α := fun g0 =>
  match m g0 with
  | some (x, g1) => if on && pre && !(post g0 g1 x) then Option.none else some (x, g1)
  | Option.none => Option.none

def ksrSixFork (M : Nat) (K : List (Nat × List Nat)) (cod : Bell → Option Bool)
    (rp rq rr : CGoalL LS → List Nat → CM FM (NextL LS)) (p : Nomm)
    (laz : Lazy LS) (th : Jmp) (region : List Nat) : CM FM (NextL LS) := do
  let rCond ← re
  let gF ← get
  let (g0, g1) ← ksrSpec (M == 300 || M == 310 || (320 ≤ M && M < 340))
    (ksrCand6 K (CGoalL.next laz th) gF && ksrNoDangle gF.blocks && csxAcyc gF.blocks)
    (forkL ⟨laz, th⟩ rCond) fun a b x =>
      if M == 310 then false else ksrForkSpec (if M == 300 then 99 else M - 320) K laz th rCond a b x
  let rid ← idM
  let rb := rid :: region
  let condBefore ← getCond
  let nex1 ← rr (CGoalL.next g1.laz g1.th) rb
  let condBetween ← getCond
  let nex0 ← rq (CGoalL.next g0.laz g0.th) rb
  let gS ← get
  let (lazy, yes, nuh) ← ksrSpec (M == 302 || M == 312)
    (ksrCand6 K nex0.goal gS && ksrCand6 K nex1.goal gS && ksrNoDangle gS.blocks)
    (sect nex0 nex1 g0.th.there g1.th.there rb condBefore condBetween) fun a b x => M != 312 && ksrSectSpec K nex0 nex1 a b x
  let lazy ← liftO (pastFork cod lazy p)
  let o ← emit ⟨[], [], Termin.brn rCond (jmp0 yes) (jmp0 nuh)⟩
  let lazy ← lazyShut o lazy
  let nexCond ← rp (CGoalL.next (ofSure ⟨Need.this rCond, HoonSet.empty⟩) (jmp0 o)) region
  copyL nexCond lazy

def ksrSixSimple (M : Nat) (K : List (Nat × List Nat)) (cod : Bell → Option Bool)
    (rp rq rr : CGoalL LS → List Nat → CM FM (NextL LS)) (p : Nomm)
    (laz : Lazy LS) (th : Jmp) (region : List Nat) : CM FM (NextL LS) := do
  let o0 ← oo
  let o1 ← oo
  let gF ← get
  let (s0, s1) ← ksrSpec (M == 301 || M == 311)
    ((gF.blocks.f o0).isNone && (gF.blocks.f o1).isNone && (gF.blocks.f th.there).isSome &&
      o0 < gF.bo && o1 < gF.bo && o0 != o1)
    (forkSure laz.sure th.there o0 o1) fun a b x => M != 311 && ksrForkSureSpec laz.sure th.there o0 o1 a b x
  let rid ← idM
  let rb := rid :: region
  let condBefore ← getCond
  let nex1 ← rr (CGoalL.next (ofSure s1) (jmp0 o1)) rb
  let condBetween ← getCond
  let nex0 ← rq (CGoalL.next (ofSure s0) (jmp0 o0)) rb
  let gS ← get
  let (lazy, yes, nuh) ← ksrSpec (M == 302 || M == 312)
    (ksrCand6 K nex0.goal gS && ksrCand6 K nex1.goal gS && ksrNoDangle gS.blocks)
    (sect nex0 nex1 o0 o1 rb condBefore condBetween) fun a b x => M != 312 && ksrSectSpec K nex0 nex1 a b x
  let lazy ← liftO (pastFork cod lazy p)
  let nexCond ← rp (CGoalL.pick (jmp0 yes) (jmp0 nuh)) region
  if !(lazyBig (softLess noSoft lazy)) then copyL nexCond lazy else do
    let o ← emit ⟨[], [], Termin.hop nexCond.th⟩
    let lazy ← lazyShut o lazy
    copyL ⟨nexCond.laz, jmp0 o⟩ lazy

def ksrSix (M : Nat) (K : List (Nat × List Nat)) (cod : Bell → Option Bool)
    (rp rq rr : CGoalL LS → List Nat → CM FM (NextL LS)) (p q r : Nomm) :
    Nat → Lazy LS → Jmp → List Nat → CM FM (NextL LS)
  | 0, _, _, _ => fun _ => Option.none
  | fuel + 1, laz, th, region =>
    match leap laz q r with
    | Option.none => fun _ => Option.none
    | some (some (rest, bys)) => do
      let nex ← ksrSix M K cod rp rq rr p q r fuel rest th region
      copyAll nex bys
    | some Option.none =>
      if !(noneEquivalentL (mk Sure.bunt laz.fork laz.bond)) then
        if (whole q && whole r) || thisOnly laz || lazyBig (softLess noSoft laz) ||
            softFork noSoft (fun _ => false) laz then do
          let (out, pro) ← kerf ⟨laz, th⟩
          ksrSix M K cod rp rq rr p q r fuel (ofSure ⟨Need.this pro, HoonSet.empty⟩) (jmp0 out) region
        else ksrSixFork M K cod rp rq rr p laz th region
      else ksrSixSimple M K cod rp rq rr p laz th region

def ksrRun (M : Nat) (Sel : Nat → Nomm → Bool) (K : List (Nat × List Nat)) (env : CallEnv) : Option Nomm → Nomm → CGoalL LS → List Nat → CM FM (NextL LS)
  | sup, Nomm.cons p q, goal, region => do
      let goal ← (match goal with
        | CGoalL.done => do
            let r ← re
            let o ← emit ⟨[], [], Termin.don r⟩
            pure (CGoalL.next (ofSure (lazyReg r)) (jmp0 o))
        | g => pure g : CM FM (CGoalL LS))
      match goal with
      | CGoalL.pick _ _ => do
          let o ← emit ⟨[], [], Termin.bom Option.none⟩
          let nex2 ← (ksrWrap M Sel 1 q K (ksrRun M Sel K env sup q)) (CGoalL.next (ofSure Sure.bunt) (jmp0 o)) region
          let nex2 ← pastL env.cod nex2 p region
          let nex1 ← (ksrWrap M Sel 2 p K (ksrRun M Sel K env sup p)) (CGoalL.next (ofSure Sure.bunt) nex2.th) region
          copyL nex1 nex2.laz
      | CGoalL.next laz th => do
          let (hed, tel, o) ← splitL ⟨laz, th⟩
          let nexh ← pastL env.cod ⟨hed, jmp0 o⟩ q region
          let nex2 ← (ksrWrap M Sel 3 q K (ksrRun M Sel K env sup q)) (CGoalL.next tel nexh.th) region
          let nex2 ← pastL env.cod nex2 p region
          let nex1 ← (ksrWrap M Sel 4 p K (ksrRun M Sel K env sup p)) (CGoalL.next nexh.laz nex2.th) region
          copyL nex1 nex2.laz
      | CGoalL.done => fun _ => Option.none
  | _, Nomm.n0 ax, goal, _ =>
      if ax = 0 then bombL (match goal with | CGoalL.next _ th => some th.there | _ => Option.none)
      else do
        let nex ← simpleNextL goal
        if ax = 1 then pure nex else
        match fromL ax nex.laz with
        | some laz => pure ⟨laz, nex.th⟩
        | Option.none => fun _ => Option.none
  | _, Nomm.n1 k, goal, _ =>
      match goal with
      | CGoalL.done => do
          let r ← re
          let o ← emit ⟨[], [Pole.imm k r], Termin.don r⟩
          pure ⟨ofSure Sure.bunt, jmp0 o⟩
      | CGoalL.pick z o =>
          if k = A 0 then pure ⟨ofSure Sure.bunt, z⟩
          else if k = A 1 then pure ⟨ofSure Sure.bunt, o⟩
          else bombL Option.none
      | CGoalL.next laz th => do
          let o ← medeL th k laz
          pure ⟨ofSure Sure.bunt, jmp0 o⟩
  | sup, Nomm.n3 p, goal, region =>
      match goal with
      | CGoalL.next laz th =>
          if noneEquivalentL laz then (ksrWrap M Sel 5 p K (ksrRun M Sel K env sup p)) (CGoalL.next laz th) region else do
            let a ← collapseLazyAtomL ⟨laz, th⟩
            match a with
            | Option.none => fun _ => Option.none
            | some (r, o) => do
                let (z, o') ← forl r o
                let r' ← re
                let oc ← emit ⟨[], [], Termin.clq r' (jmp0 z) (jmp0 o')⟩
                (ksrWrap M Sel 6 p K (ksrRun M Sel K env sup p)) (CGoalL.next (ofSure (lazyReg r')) (jmp0 oc)) region
      | CGoalL.pick z o => do
          let r ← re
          let oc ← emit ⟨[], [], Termin.clq r z o⟩
          (ksrWrap M Sel 7 p K (ksrRun M Sel K env sup p)) (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region
      | CGoalL.done => do
          let (o0, o1) ← doneBlocks
          let r ← re
          let oc ← emit ⟨[], [], Termin.clq r (jmp0 o0) (jmp0 o1)⟩
          (ksrWrap M Sel 8 p K (ksrRun M Sel K env sup p)) (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region
  | sup, Nomm.n4 p, goal, region =>
      match goal with
      | CGoalL.done => do
          let pro ← re
          let arg ← re
          let o ← emit ⟨[], [Pole.inc arg pro], Termin.don pro⟩
          (ksrWrap M Sel 9 p K (ksrRun M Sel K env sup p)) (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region
      | CGoalL.pick z o => do
          let pro ← re
          let arg ← re
          let o' ← emit ⟨[], [Pole.inc arg pro], Termin.brn pro z o⟩
          (ksrWrap M Sel 10 p K (ksrRun M Sel K env sup p)) (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o')) region
      | CGoalL.next laz th => do
          let a ← collapseLazyAtomL ⟨laz, th⟩
          let (pro, th') ← (match a with
            | some x => pure x
            | Option.none => do
                let r ← re
                if th.args = [] then pure (r, th.there) else fun _ => Option.none : CM FM (Nat × Nat))
          let arg ← re
          let o ← emit ⟨[], [Pole.inc arg pro], Termin.hop (jmp0 th')⟩
          (ksrWrap M Sel 11 p K (ksrRun M Sel K env sup p)) (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region
  | sup, Nomm.n5 p q, goal, region => do
      let rp ← re
      let rq ← re
      let o ← (match goal with
        | CGoalL.pick z o => emit ⟨[], [], Termin.eqq rp rq z o⟩
        | CGoalL.done => do
            let (o0, o1) ← doneBlocks
            emit ⟨[], [], Termin.eqq rp rq (jmp0 o0) (jmp0 o1)⟩
        | CGoalL.next laz th => do
            let a ← collapseLazyAtomL ⟨laz, th⟩
            match a with
            | Option.none =>
                if th.args = [] then emit ⟨[], [Pole.equ rp rq], Termin.hop (jmp0 th.there)⟩
                else fun _ => Option.none
            | some (r, o) => do
                let (z, o') ← forl r o
                emit ⟨[], [], Termin.eqq rp rq (jmp0 z) (jmp0 o')⟩ : CM FM Nat)
      let nexq ← (ksrWrap M Sel 12 q K (ksrRun M Sel K env sup q)) (CGoalL.next (ofSure (lazyReg rq)) (jmp0 o)) region
      let nexq ← pastL env.cod nexq p region
      let nexp ← (ksrWrap M Sel 13 p K (ksrRun M Sel K env sup p)) (CGoalL.next (ofSure (lazyReg rp)) nexq.th) region
      copyL nexp nexq.laz
  | sup, Nomm.n6 p q r, goal, region =>
      match goal with
      | CGoalL.next laz th => ksrSix M K env.cod ((ksrWrap M Sel 14 p K (ksrRun M Sel K env sup p))) ((ksrWrap M Sel 15 q K (ksrRun M Sel K env sup q))) ((ksrWrap M Sel 16 r K (ksrRun M Sel K env sup r))) p q r 3 laz th region
      | _ => do
          let nex1 ← (ksrWrap M Sel 17 r K (ksrRun M Sel K env sup r)) goal region
          let nex0 ← (ksrWrap M Sel 18 q K (ksrRun M Sel K env sup q)) goal region
          let yes ← emit ⟨[], [], Termin.hop nex0.th⟩
          let nuh ← emit ⟨[], [], Termin.hop nex1.th⟩
          setTag yes region
          setTag nuh region
          if nex0.th.args ≠ [] then fun _ => Option.none else
          if nex1.th.args ≠ [] then fun _ => Option.none else
          let lazy ← liftO (pastFork env.cod (mk Sure.bunt [((yes, nex0.laz), (nuh, nex1.laz))] []) p)
          let nexCond ← (ksrWrap M Sel 19 p K (ksrRun M Sel K env sup p)) (CGoalL.pick (jmp0 yes) (jmp0 nuh)) region
          if !(lazyBig (softLess noSoft lazy)) then copyL nexCond lazy else do
            let o ← emit ⟨[], [], Termin.hop nexCond.th⟩
            let lazy ← lazyShut o lazy
            copyL ⟨nexCond.laz, jmp0 o⟩ lazy
  | sup, Nomm.n7 p q, goal, region => do
      let nex ← (ksrWrap M Sel 20 q K (ksrRun M Sel K env (some p) q)) goal region
      (ksrWrap M Sel 21 p K (ksrRun M Sel K env sup p)) nex.goal region
  | sup, Nomm.n10 a v q, goal, region => do
      let next ← simpleNextL goal
      let (don, rec, o) ← intoL next a
      let nexR ← pastL env.cod ⟨rec, jmp0 o⟩ v region
      let nexDon ← (ksrWrap M Sel 22 v K (ksrRun M Sel K env sup v)) (CGoalL.next don nexR.th) region
      let nexDon ← pastL env.cod nexDon q region
      let nexRec ← (ksrWrap M Sel 23 q K (ksrRun M Sel K env sup q)) (CGoalL.next nexR.laz nexDon.th) region
      copyL nexRec nexDon.laz
  | sup, Nomm.n2 p q info, goal, region =>
      callL env ((ksrWrap M Sel 24 p K (ksrRun M Sel K env sup p))) ((ksrWrap M Sel 25 q K (ksrRun M Sel K env sup q))) p q info sup goal region
  | _, _, _, _ => fun _ => Option.none

def ksrTop (M : Nat) (Sel : Nat → Nomm → Bool) (K : List (Nat × List Nat)) (goal : CGoalL LS) (g0 : Comp.Gen FM)
    (nm : Nomm) : Option (NextL LS × Comp.Gen FM) :=
  ksrWrap M Sel 0 nm K (ksrRun M Sel K envR Option.none nm) goal [] g0

/-- `(runs, top pre fails, base fails, M=0 differs, per mode failures)`. -/
def ksrTally (Sel : Nat → Nomm → Bool) (nms : List Nomm) (gs : List CsxG) (ms : List Nat) :
    Nat × Nat × Nat × Nat × List (Nat × Nat) :=
  let ps := nms.flatMap fun nm => gs.map fun g => (nm, g)
  let rs := ps.map fun (nm, K, goal, g0) =>
    let pre := csxPreAll K goal g0
    let b := (runLC envR Option.none nm goal [] g0 : Option (NextL LS × Comp.Gen FM)).isSome
    (pre, b, (ksrTop 0 Sel K goal g0 nm).isSome != b,
      ms.map fun M => pre && b && !(ksrTop M Sel K goal g0 nm).isSome)
  (rs.length, (rs.filter (!·.1)).length, (rs.filter (!·.2.1)).length, (rs.filter (·.2.2.1)).length,
    (ms.zipIdx.map fun (M, i) => (M, (rs.filter fun r => r.2.2.2.getD i false).length)).filter (·.2 != 0))

def ksrModes : List Nat := [20, 70, 71, 72, 73, 74, 75, 76, 77, 90, 91, 92,
  120, 170, 171, 172, 173, 174, 175, 176, 177, 280, 281, 282, 283, 284, 300, 301, 302]

/-! ## The counts -/

-- `%6` with calls in `enumCX`, the seven goals
#guard ksrTally (fun _ _ => true) csxS1 csxGoals7
    [20, 70, 71, 75, 76, 120, 170, 171, 175, 176, 280, 281, 282, 72, 73, 74, 90, 91, 92, 172, 284, 311, 312] ==
  (420, 0, 0, 0, [(72, 120), (90, 258), (91, 420), (92, 420), (172, 420), (284, 420), (311, 258), (312, 258)])

-- the fork path: track C's `sixes` under the flat goals with bonds
#guard ksrTally (fun _ _ => true) csxS2 csxGoalsL
    [20, 70, 71, 75, 76, 120, 170, 171, 175, 176, 280, 281, 282, 300, 301, 302, 310, 311, 312,
     72, 73, 74, 90, 91, 92, 172, 173, 283, 284, 327, 328, 332, 333] ==
  (2940, 0, 1192, 0, [(310, 416), (311, 1332), (312, 1748), (72, 580), (73, 101), (90, 1624), (91, 1748),
    (92, 1748), (172, 1748), (173, 101), (283, 416), (284, 1748), (327, 208), (328, 208), (332, 208), (333, 208)])

-- from the top: the fork path needs a call (`csxW2`); the ranks (b), (c) fail there
#guard ksrTally (fun _ _ => true) [csxW2, csxW2p] (csxGoals7.take 1)
    [20, 70, 71, 75, 76, 170, 171, 175, 176, 280, 281, 282, 300, 301, 302, 310, 311, 312,
     73, 74, 173, 174, 283, 327, 328, 332, 333] ==
  (2, 0, 0, 0, [(310, 1), (311, 1), (312, 2), (73, 1), (74, 1), (173, 1), (174, 1), (283, 1), (327, 1), (328, 1),
    (332, 1), (333, 1)])

end Raw
end SkaModel
end Formalization
