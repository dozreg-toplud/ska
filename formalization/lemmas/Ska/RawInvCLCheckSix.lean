import lemmas.Ska.RawInvCLCheckIJ
import lemmas.Ska.CompGenCheckB

/-!
# The run-level liveness with calls at a `%6`, checked

README Gaps 14 (b), track D.  `LRL` (`RawInvCLTen.lean`: pre `IL K goal g0 ∧
LG goal g0`, post `JL K nex g1 ∧ LiveC K goal g0 g1 nex`) is proved on
`PlainN` (no `%6`).  Here `csxRun` is `runLC` with EVERY recursive call
wrapped by `csxWrap`, which checks one clause `M` of the pre- or
postcondition (`csxPre1`, `csxPost1`, the clauses of `iB`, `goalLabB`,
`liveCB`, `prepB`, `condGrowB`, `defsB`, `gregB`, `labB` of
`RawInvCLCheckIJ.lean`, split field by field) at the sub-runs that `Sel tag
nm` selects (`tag` is the call site, `14`, `15`, `16` the test, the yes and
the no branch of a `%6` under `%next`).  The runner text is written by the
generator `tools/gen/csxrun.py` from `runLC` (`runLC env sup x` becomes
`csxWrap M Sel tag x K (csxRun M Sel K env sup x)`).

Findings (the full families in scratch, `lake env lean`; the slices below):
* On the `%6` part of `enumCX` (1,104 nomms with `%6` and indirect calls,
  `csxF1`) and on track C's `sixes` (245, with `ind`) under the seven goals,
  every clause holds at every sub-run EXCEPT the clause of `ATS` "every
  block jumps below its label" (`15` before, `35` after): `+fork-need`
  `emir`s the blocks `o0`, `o1` at labels reserved before the join `barg`
  and hops UP to it (5,670 of 7,728 runs, 980 of 1,715).  `Fresh` still
  holds: no goal jumps to a join.  These families only reach the phases `S`
  (`sixNextSimpleC`) and `K` (`+kerf`) of `sixNextLC`.
* The fork path `F` (`sixNextForkC`, phase `F`) is reached from flat goals
  with bonds (`csxGoalsL`: track C's `LSXCheck.lazies` in a state `csxGL`
  that meets the precondition).  There two more clauses fail: `prepB` (the
  old blocks change only by ops in front at the goal's entries): `+fork`'s
  `insertHop` turns an old entry block into `hop oi1` (up) and moves its
  body to a reserved label; and the rank `upRk` of `FragX` no longer falls
  along every jump: an old block that jumps down to that entry block now
  jumps to a hop up (`csxW1` under `csxGoalsL[8]`: `3 -> 2`, ranks `9`,
  `34`).  The jump graph has no cycle (`csxAcyc`), every block that does
  not end in `hop` jumps below its label, and the old blocks change only at
  the goal's entries, by ops in front or by the `insertHop` shape
  (`csxPost1 54`).
* **Candidate** (`55` before, `56` after): `IL` with the down clause of
  `ATS` replaced by "every block not ending in `hop` jumps below its label"
  and "no cycle", and `prepOld` replaced by "ops in front, or the
  `insertHop` shape: the entry block is `[par, [], hop t]` with `t` new and
  some new block is the old body with ops in front".  0 failures on all the
  families; the mutations bite: no parameter anywhere (`19`), `LiveC`
  without the result's kills (`47`).
* The fork path, the rank failure and the `prepB` failure need a CALL: from
  the top (`%done`, `gen0`) `csxW2` (`[7 [6 ind [0 2] [0 3]] [[[0 2] [0 3]]
  ind]]`) reaches `sixNextForkC` (the cons with a call in its tail parks its
  head's need in a bond with `+past`, and the `%6` runs under that bond) and
  fails both; `csxW2p`, the same shape without calls, does not.  On the
  call-free nomms of `all6` (352, under the seven goals) the fork path is
  never taken, so `FragX`'s `upRk` is not contradicted.

| family | runs | base fails | fork path | down fails | rank, `prepB` fail | candidate fails |
|---|---|---|---|---|---|---|
| `csxF1` (`%6` part of `enumCX`), seven goals | 7,728 | 96 | 0 | 5,670 | 0 | 0 |
| `sixes`, seven goals | 1,715 | 0 | 0 | 980 | 0 | 0 |
| `sixes`, `csxGoalsL` (60 flat goals) | 14,700 | 5,960 | 2,040 | 8,740 | 2,080 | 0 |
| `all6` (5,145), seven goals | 36,015 | 740 | 1,065 | | 1,110 | 0 |
| `all6`, the 24 bond goals of `csxGoalsL` at `3` | 123,480 | 31,000 | 11,855 | | | 0 |

(about 40 minutes in all, scratch; the slices below take seconds.)
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

def csxNodes : CGoalL LS → List (Nat × List Nat × List Nat)
  | CGoalL.next laz th => nodesF 30 [] (th.there, laz)
  | _ => []

def csxJmps : CGoalL LS → List Jmp
  | CGoalL.next _ th => [th]
  | CGoalL.pick z o => [z, o]
  | CGoalL.done => []

def csxBlkOK (g : Comp.Gen FM) (k : Nat) : Bool :=
  k < g.bo && match g.blocks.f k with | some b => b.par.isEmpty | none => false

/-- The jump graph has no cycle: peel the blocks whose targets are all
peeled (or have no block). -/
def csxPeel (bl : List (Nat × Blob)) : Nat → List Nat → List (Nat × Blob) → Bool
  | 0, _, rest => rest.isEmpty
  | f + 1, done, rest =>
    let (ok, no) := rest.partition fun (_, b) => (getJmps b.fin).all fun j =>
      done.contains j.there || !(bl.any (·.1 == j.there))
    if ok.isEmpty then no.isEmpty else csxPeel bl f (done ++ ok.map (·.1)) no

def csxAcyc (m : FM Blob) : Bool :=
  let bl := blocksOf m
  csxPeel bl (bl.length + 1) [] bl

/-- One clause of the precondition. -/
def csxPre1 (c : Nat) (K : List (Nat × List Nat)) (goal : CGoalL LS) (g : Comp.Gen FM) : Bool :=
  let N := csxNodes goal
  let D := allDefsL g.blocks
  match c with
  | 1 => atsB g
  | 2 => regsBelowB g
  | 3 => condB goal g
  | 4 => K.all (·.1 < g.bo)
  | 5 => (csxJmps goal).all (·.args.isEmpty)
  | 12 => (csxJmps goal).all fun j => csxBlkOK g j.there
  | 6 => nodupB (N.flatMap (·.2.1))
  | 7 => N.all (·.1 < g.bo)
  | 8 => N.all fun x => match g.blocks.f x.1 with | some b => b.par.isEmpty | none => false
  | 9 => N.all fun x => x.2.1.all (· < g.re)
  | 10 => N.all fun x => x.2.1.all fun r => !D.contains r
  | 11 => goalLabB goal
  | 13 => stB g.blocks
  | 14 => (blocksOf g.blocks).all fun (k, _) => 1 ≤ k && k < g.bo
  | 15 => (blocksOf g.blocks).all fun (k, b) => (getJmps b.fin).all (·.there < k)
  | 16 => !g.drop && 1 ≤ g.bo
  | 17 => rkDownB g.blocks
  | 18 => (blocksOf g.blocks).all fun (k, b) => match b.fin with
      | Termin.hop _ => true
      | f => (getJmps f).all (·.there < k)
  | 19 => (blocksOf g.blocks).all fun (_, b) => b.par.isEmpty
  | 20 => csxAcyc g.blocks
  | _ => true

def csxCandPre : List Nat := [2, 3, 4, 5, 12, 6, 7, 8, 9, 10, 11, 13, 14, 16, 17]

/-- The candidate with `%6`: `ATS` without "every jump goes below its label",
with "every block that does not end in `hop` jumps below its label" and
"the jump graph has no cycle". -/
def csxCandPre6 : List Nat := [2, 3, 4, 5, 12, 6, 7, 8, 9, 10, 11, 13, 14, 16, 18, 20]

def csxPre (c : Nat) (K : List (Nat × List Nat)) (goal : CGoalL LS) (g : Comp.Gen FM) : Bool :=
  if c == 50 then csxCandPre.all fun c => csxPre1 c K goal g
  else if c == 55 then csxCandPre6.all fun c => csxPre1 c K goal g
  else csxPre1 c K goal g

def csxPreAll (K : List (Nat × List Nat)) (goal : CGoalL LS) (g : Comp.Gen FM) : Bool :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12].all fun c => csxPre c K goal g

def csxPost1 (c : Nat) (K : List (Nat × List Nat)) (goal : CGoalL LS) (g0 g1 : Comp.Gen FM) (nex : NextL LS) : Bool :=
  if c < 40 then csxPre1 (c - 20) K nex.goal g1 else
  match c with
  | 40 => liveCB K goal g0 g1 nex
  | 41 => prepB goal g0 g1
  | 42 => condGrowB g0 g1
  | 43 => defsB goal g0 g1
  | 44 => gregB goal g0 nex
  | 45 => labB goal nex
  | 46 => decide (g0.re ≤ g1.re)
  | 47 => (liveKF (unpB g1) K (fuelOf g1) nex.th.there).all fun r =>
      (match goal with
       | CGoalL.next laz th => liveKF (unpB g0) (K ++ killsOf th.there laz) (fuelOf g0) th.there
       | CGoalL.pick z o => liveKF (unpB g0) K (fuelOf g0) z.there ++ liveKF (unpB g0) K (fuelOf g0) o.there
       | CGoalL.done => []).contains r
  | 48 => prepB CGoalL.done g0 g1
  | 49 => (blocksOf g0.blocks).all fun (k, b) => match g1.blocks.f k with
      | some b' => (match prefixOf b b' with | some A => A.isEmpty | none => false) || (goalLabs goal).contains k
      | none => false
  | 54 => (blocksOf g0.blocks).all fun (k, b) => match g1.blocks.f k with
      | some b' => (match prefixOf b b' with
          | some A => A.isEmpty || (goalLabs goal).contains k
          | none => false) ||
        ((goalLabs goal).contains k && b'.par == b.par && b'.body.isEmpty &&
          (match b'.fin with | Termin.hop t => g0.bo ≤ t.there && t.args.isEmpty | _ => false) &&
          (blocksOf g1.blocks).any fun (t', bt) => g0.bo ≤ t' && bt.par.isEmpty &&
            (match prefixOf ⟨[], b.body, b.fin⟩ bt with | some _ => true | none => false))
      | none => false
  | 52 => let G := match goal with
        | CGoalL.next laz th => K ++ killsOf th.there laz
        | _ => K
      (blocksOf g0.blocks).all fun (k, _) =>
        (liveKF (unpB g1) (K ++ killsOf nex.th.there nex.laz) (fuelOf g1) k).all
          (liveKF (unpB g0) G (fuelOf g0) k).contains
  | 53 => let G := match goal with
        | CGoalL.next laz th => K ++ killsOf th.there laz
        | _ => K
      (blocksOf g0.blocks).all fun (k, _) =>
        (liveKF (unpB g1) K (fuelOf g1) k).all (liveKF (unpB g0) G (fuelOf g0) k).contains
  | _ => true

def csxPost (c : Nat) (K : List (Nat × List Nat)) (goal : CGoalL LS) (g0 g1 : Comp.Gen FM) (nex : NextL LS) : Bool :=
  if c == 51 then csxCandPre.all (fun c => csxPre1 c K nex.goal g1) &&
    [40, 41, 42, 43, 44, 45, 46].all (fun c => csxPost1 c K goal g0 g1 nex)
  else if c == 56 then csxCandPre6.all (fun c => csxPre1 c K nex.goal g1) &&
    [40, 42, 43, 44, 45, 46, 54].all (fun c => csxPost1 c K goal g0 g1 nex)
  else csxPost1 c K goal g0 g1 nex

/-- Coverage marks: `60` the fork path of a `%6` on a goal with forks or
bonds (`insertHop`), `61` the fork path, `62` the leap, `63` the kerf. -/
def csxCov (M : Nat) (nm : Nomm) (goal : CGoalL LS) : Bool :=
  match nm, goal with
  | Nomm.n6 _ q r, CGoalL.next laz _ =>
    let ph := SixCheck.phase laz q r
    match M with
    | 60 => ph == "F" && (!laz.fork.isEmpty || !laz.bond.isEmpty)
    | 61 => ph == "F"
    | 62 => ph == "L"
    | 63 => ph == "K"
    | 64 => ph == "S"
    | _ => false
  | _, _ => false

/-- A sub-run checked at clause `M` when `A tag nm`. -/
def csxWrap (M : Nat) (Sel : Nat → Nomm → Bool) (tag : Nat) (nm : Nomm) (K : List (Nat × List Nat))
    (rp : CGoalL LS → List Nat → CM FM (NextL LS)) : CGoalL LS → List Nat → CM FM (NextL LS) := fun goal region g0 =>
  let on := Sel tag nm
  if on && (M < 20 || M == 50 || M == 55) && !(csxPre M K goal g0) then Option.none else
  if on && 60 ≤ M && csxCov M nm goal then Option.none else
  match rp goal region g0 with
  | some (nex, g1) => if on && 20 ≤ M && M < 60 && M != 50 && M != 55 && !(csxPost M K goal g0 g1 nex) then Option.none else some (nex, g1)
  | Option.none => Option.none

def csxRun (M : Nat) (Sel : Nat → Nomm → Bool) (K : List (Nat × List Nat)) (env : CallEnv) : Option Nomm → Nomm → CGoalL LS → List Nat → CM FM (NextL LS)
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
          let nex2 ← (csxWrap M Sel 1 q K (csxRun M Sel K env sup q)) (CGoalL.next (ofSure Sure.bunt) (jmp0 o)) region
          let nex2 ← pastL env.cod nex2 p region
          let nex1 ← (csxWrap M Sel 2 p K (csxRun M Sel K env sup p)) (CGoalL.next (ofSure Sure.bunt) nex2.th) region
          copyL nex1 nex2.laz
      | CGoalL.next laz th => do
          let (hed, tel, o) ← splitL ⟨laz, th⟩
          let nexh ← pastL env.cod ⟨hed, jmp0 o⟩ q region
          let nex2 ← (csxWrap M Sel 3 q K (csxRun M Sel K env sup q)) (CGoalL.next tel nexh.th) region
          let nex2 ← pastL env.cod nex2 p region
          let nex1 ← (csxWrap M Sel 4 p K (csxRun M Sel K env sup p)) (CGoalL.next nexh.laz nex2.th) region
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
          if noneEquivalentL laz then (csxWrap M Sel 5 p K (csxRun M Sel K env sup p)) (CGoalL.next laz th) region else do
            let a ← collapseLazyAtomL ⟨laz, th⟩
            match a with
            | Option.none => fun _ => Option.none
            | some (r, o) => do
                let (z, o') ← forl r o
                let r' ← re
                let oc ← emit ⟨[], [], Termin.clq r' (jmp0 z) (jmp0 o')⟩
                (csxWrap M Sel 6 p K (csxRun M Sel K env sup p)) (CGoalL.next (ofSure (lazyReg r')) (jmp0 oc)) region
      | CGoalL.pick z o => do
          let r ← re
          let oc ← emit ⟨[], [], Termin.clq r z o⟩
          (csxWrap M Sel 7 p K (csxRun M Sel K env sup p)) (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region
      | CGoalL.done => do
          let (o0, o1) ← doneBlocks
          let r ← re
          let oc ← emit ⟨[], [], Termin.clq r (jmp0 o0) (jmp0 o1)⟩
          (csxWrap M Sel 8 p K (csxRun M Sel K env sup p)) (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region
  | sup, Nomm.n4 p, goal, region =>
      match goal with
      | CGoalL.done => do
          let pro ← re
          let arg ← re
          let o ← emit ⟨[], [Pole.inc arg pro], Termin.don pro⟩
          (csxWrap M Sel 9 p K (csxRun M Sel K env sup p)) (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region
      | CGoalL.pick z o => do
          let pro ← re
          let arg ← re
          let o' ← emit ⟨[], [Pole.inc arg pro], Termin.brn pro z o⟩
          (csxWrap M Sel 10 p K (csxRun M Sel K env sup p)) (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o')) region
      | CGoalL.next laz th => do
          let a ← collapseLazyAtomL ⟨laz, th⟩
          let (pro, th') ← (match a with
            | some x => pure x
            | Option.none => do
                let r ← re
                if th.args = [] then pure (r, th.there) else fun _ => Option.none : CM FM (Nat × Nat))
          let arg ← re
          let o ← emit ⟨[], [Pole.inc arg pro], Termin.hop (jmp0 th')⟩
          (csxWrap M Sel 11 p K (csxRun M Sel K env sup p)) (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region
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
      let nexq ← (csxWrap M Sel 12 q K (csxRun M Sel K env sup q)) (CGoalL.next (ofSure (lazyReg rq)) (jmp0 o)) region
      let nexq ← pastL env.cod nexq p region
      let nexp ← (csxWrap M Sel 13 p K (csxRun M Sel K env sup p)) (CGoalL.next (ofSure (lazyReg rp)) nexq.th) region
      copyL nexp nexq.laz
  | sup, Nomm.n6 p q r, goal, region =>
      match goal with
      | CGoalL.next laz th => sixNextLC env.cod ((csxWrap M Sel 14 p K (csxRun M Sel K env sup p))) ((csxWrap M Sel 15 q K (csxRun M Sel K env sup q))) ((csxWrap M Sel 16 r K (csxRun M Sel K env sup r))) p q r 3 laz th region
      | _ => do
          let nex1 ← (csxWrap M Sel 17 r K (csxRun M Sel K env sup r)) goal region
          let nex0 ← (csxWrap M Sel 18 q K (csxRun M Sel K env sup q)) goal region
          let yes ← emit ⟨[], [], Termin.hop nex0.th⟩
          let nuh ← emit ⟨[], [], Termin.hop nex1.th⟩
          setTag yes region
          setTag nuh region
          if nex0.th.args ≠ [] then fun _ => Option.none else
          if nex1.th.args ≠ [] then fun _ => Option.none else
          let lazy ← liftO (pastFork env.cod (mk Sure.bunt [((yes, nex0.laz), (nuh, nex1.laz))] []) p)
          let nexCond ← (csxWrap M Sel 19 p K (csxRun M Sel K env sup p)) (CGoalL.pick (jmp0 yes) (jmp0 nuh)) region
          if !(lazyBig (softLess noSoft lazy)) then copyL nexCond lazy else do
            let o ← emit ⟨[], [], Termin.hop nexCond.th⟩
            let lazy ← lazyShut o lazy
            copyL ⟨nexCond.laz, jmp0 o⟩ lazy
  | sup, Nomm.n7 p q, goal, region => do
      let nex ← (csxWrap M Sel 20 q K (csxRun M Sel K env (some p) q)) goal region
      (csxWrap M Sel 21 p K (csxRun M Sel K env sup p)) nex.goal region
  | sup, Nomm.n10 a v q, goal, region => do
      let next ← simpleNextL goal
      let (don, rec, o) ← intoL next a
      let nexR ← pastL env.cod ⟨rec, jmp0 o⟩ v region
      let nexDon ← (csxWrap M Sel 22 v K (csxRun M Sel K env sup v)) (CGoalL.next don nexR.th) region
      let nexDon ← pastL env.cod nexDon q region
      let nexRec ← (csxWrap M Sel 23 q K (csxRun M Sel K env sup q)) (CGoalL.next nexR.laz nexDon.th) region
      copyL nexRec nexDon.laz
  | sup, Nomm.n2 p q info, goal, region =>
      callL env ((csxWrap M Sel 24 p K (csxRun M Sel K env sup p))) ((csxWrap M Sel 25 q K (csxRun M Sel K env sup q))) p q info sup goal region
  | _, _, _, _ => fun _ => Option.none

def csxTop (M : Nat) (Sel : Nat → Nomm → Bool) (K : List (Nat × List Nat)) (goal : CGoalL LS) (g0 : Comp.Gen FM)
    (nm : Nomm) : Option (NextL LS × Comp.Gen FM) :=
  csxWrap M Sel 0 nm K (csxRun M Sel K envR Option.none nm) goal [] g0

abbrev CsxG := List (Nat × List Nat) × CGoalL LS × Comp.Gen FM

def csxGoals7 : List CsxG :=
  [([], CGoalL.done, gen0), ([], goalY, gY), ([], goalP, gP), ([], goalB, gB),
   ([(1, [1])], goalY, gY), ([(1, [0])], goalB, gB), ([(1, [1]), (2, [0])], goalP, gP)]

def csxModes : List Nat := [13, 14, 15, 16, 33, 34, 35, 36, 1, 2, 3, 4, 5, 12, 6, 7, 8, 9, 10, 11, 21, 22, 23, 24, 25, 32, 26, 27, 28, 29, 30, 31,
  40, 41, 42, 43, 44, 45, 46]

def csxIsSix : Nomm → Bool
  | Nomm.n6 _ _ _ => true
  | _ => false

/-- `(runs, top pre fails, base fails, M=0 differs, per mode failures)`. -/
def csxTally (Sel : Nat → Nomm → Bool) (nms : List Nomm) (gs : List CsxG) (ms : List Nat) :
    Nat × Nat × Nat × Nat × List (Nat × Nat) :=
  let ps := nms.flatMap fun nm => gs.map fun g => (nm, g)
  let rs := ps.map fun (nm, K, goal, g0) =>
    let pre := csxPreAll K goal g0
    let b := (runLC envR Option.none nm goal [] g0 : Option (NextL LS × Comp.Gen FM)).isSome
    (pre, b, (csxTop 0 Sel K goal g0 nm).isSome != b,
      ms.map fun M => pre && b && !(csxTop M Sel K goal g0 nm).isSome)
  (rs.length, (rs.filter (!·.1)).length, (rs.filter (!·.2.1)).length, (rs.filter (·.2.2.1)).length,
    (ms.zipIdx.map fun (M, i) => (M, (rs.filter fun r => r.2.2.2.getD i false).length)).filter (·.2 != 0))

def csxWit (Sel : Nat → Nomm → Bool) (M : Nat) (nms : List Nomm) (gs : List CsxG) : List (Noun × Nat) :=
  ((nms.flatMap fun nm => (gs.zipIdx).map fun g => (nm, g)).filterMap fun (nm, (K, goal, g0), i) =>
    if csxPreAll K goal g0 && (csxTop 0 Sel K goal g0 nm).isSome && !(csxTop M Sel K goal g0 nm).isSome then
      some (nm.toNoun, i) else Option.none).take 3

def csxF1 : List Nomm := enumCX.filter (!isPlain ·)

/-- A state for the flat lazy goals of track C (`LSXCheck.lazies`: registers
`0 ..< 4`, bonds at `1` and `2`): blocks at `1`, `2`, `3` with no parameter,
each tagged. -/
def csxGL : Comp.Gen FM :=
  ⟨4, 4, 1, false,
   HoonMap.put (HoonMap.put (HoonMap.put (HoonMap.empty : FM Blob) 1 ⟨[], [], Termin.bom Option.none⟩) 2
     ⟨[], [], Termin.hop (jmp0 1)⟩) 3 ⟨[], [], Termin.hop (jmp0 2)⟩,
   HoonMap.put (HoonMap.put (HoonMap.put (HoonMap.empty : FM (List Nat)) 1 [0]) 2 [0]) 3 [0], HoonMap.empty⟩

def csxGoalsL : List CsxG :=
  LSXCheck.lazies.flatMap fun L => LSXCheck.jumps.map fun th => ([], CGoalL.next L th, csxGL)

def csxS1 : List Nomm := csxF1.take 60
def csxS2 : List Nomm := SixCheck.sixes.take 49

def csxW1 : Nomm := Nomm.n6 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 2) (Nomm.n0 3)

/-- The jumps that do not fall in `upRk`. -/
def csxBad (m : FM Blob) : List (Nat × Nat × Nat × Nat) :=
  (blocksOf m).flatMap fun (k, b) => (getJmps b.fin).filterMap fun (j : Jmp) =>
    if upRk m j.there < upRk m k then Option.none else some (k, j.there, upRk m k, upRk m j.there)

def csxW1r (goal : CGoalL LS) (g0 : Comp.Gen FM) : Option (List (Nat × Nat × Nat × Nat) × Bool × Bool) :=
  match (runLC envR Option.none csxW1 goal [] g0 : Option (NextL LS × Comp.Gen FM)) with
  | some (_, g1) => some (csxBad g1.blocks, csxAcyc g1.blocks, prepB goal g0 g1)
  | Option.none => Option.none

def csxW2 : Nomm :=
  Nomm.n7 (Nomm.n6 LSXCheck.ind (Nomm.n0 2) (Nomm.n0 3)) (Nomm.cons (Nomm.cons (Nomm.n0 2) (Nomm.n0 3)) LSXCheck.ind)
def csxW2p : Nomm :=
  Nomm.n7 (Nomm.n6 (Nomm.n3 (Nomm.n0 3)) (Nomm.n0 2) (Nomm.n0 3)) (Nomm.cons (Nomm.cons (Nomm.n0 2) (Nomm.n0 3)) (Nomm.n0 2))

#guard csxF1.length == 1104
#guard (csxGoalsL.filter fun (K, goal, g) => csxPreAll K goal g).length == 60

/-! ## `%6` with calls in `enumCX`: only the down clause fails -/

#guard csxTally (fun _ _ => true) csxS1 csxGoals7 [15, 35, 50, 51, 54, 55, 56, 19, 47, 63, 64] ==
  (420, 0, 0, 0, [(15, 258), (35, 258), (19, 258), (47, 420), (63, 108), (64, 150)])
-- the first sub-run whose state has a hop up: the no branch, after `+fork-need`
#guard csxTally (fun t _ => t == 16) csxS1 csxGoals7 [15] == (420, 0, 0, 0, [(15, 258)])

/-! ## The fork path: `prepB` and the rank fail, the candidate holds -/

#guard csxTally (fun _ _ => true) csxS2 csxGoalsL
    [15, 35, 17, 37, 18, 38, 20, 40, 41, 49, 54, 55, 56, 19, 47, 60, 61, 62] ==
  (2940, 0, 1192, 0, [(15, 1748), (35, 1748), (17, 416), (37, 416), (41, 416), (19, 1624), (47, 1748),
    (60, 408), (61, 408), (62, 168)])
#guard (match csxGoalsL[8]? with
  | some (_, goal, g0) => csxW1r goal g0
  | Option.none => Option.none) == some ([(3, 2, 9, 34)], true, false)

/-! ## From the top: the fork path needs a call -/

#guard csxTally (fun _ _ => true) [csxW2, csxW2p] (csxGoals7.take 1) [15, 17, 37, 41, 20, 40, 54, 55, 56, 61] ==
  (2, 0, 0, 0, [(15, 2), (17, 1), (37, 1), (41, 1), (61, 1)])

end Raw
end SkaModel
end Formalization
