import lemmas.Ska.RawInvCLCheck

/-!
# The pre- and postcondition of the run-level liveness with calls, checked at every sub-run

README Gaps 14 (b), track D.  `RawInvCLCheck.lean` checks the liveness spec
`LiveC` on the top runs only.  Here the whole pair `I` / `J` of `LiveRun`
(`RawInvCLSpec.lean`, `RawInvCLIJ.lean`) is checked at EVERY recursive call
of `runLC` on the 2,856 nomms of `enumCX` in `PlainN`: `runLCk` is `runLC`
on the arms of `PlainN` with each recursive call wrapped by `wrapC`, which
fails (returns `none`) when `I` fails before the sub-run or `J`, `LiveC`,
the shape of the old blocks or the growth of `cond` fails after it.  So
`runLCk` returns exactly when `runLC` does iff every check passed at every
sub-run.

The precondition `iB K goal g` (the Prop is `IL` of `RawInvCLIJ.lean`):
* `ATS g`: `drop` false, `1 ≤ bo`, every block at a label in `[1, bo)`,
  meeting the arity of its targets (`stB`), jumping below its label;
* every register a block mentions is below `re`;
* every key of `cond` is below `re`, defined by no block, no register of
  the goal, and stands for a register below `re` that is no key;
* the outer kills `K` lie below `bo`;
* the goal's jumps are `Fresh` (no argument, a block with no parameter)
  below `bo`, its registers below `re`;
* every entry of the goal's lazy tree (the root included) is at a label
  below `bo` with a block with no parameter, and no block defines a
  register of its sure need; the sure needs of the tree are pairwise
  disjoint (`disjB`).
The postcondition `jB K nex g` is `iB K nex.goal g`.  After the run also:
`LiveC` (`live1K` at the sub-run), the old blocks change only by ops in
front at the goal's lazy entries (`prepOld`), `cond` only grows, by
keys from the old `re` on, `re` only grows, and every register defined
after the run was defined before it, is fresh, or is a goal register
(`defsB`: the frame that `%5`, cons, `%10` and `%2` need for their second
run's goal), and a result's lazy tree has bonds and forks at distinct labels
at every node when the goal's has (`labB`: the `LabUniq` that `+copy` needs).
-/

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

/-- Every register an op mentions (reads and the written one). -/
def opRegsB (op : Pole) : List Nat := aliasReads op ++ (aliasDst op).toList

def blobRegsB (b : Blob) : List Nat := b.par ++ b.body.flatMap opRegsB ++ finRegs b.fin

def condKeys (g : Comp.Gen FM) : List Nat := g.cond.ks.eraseDups.filter fun k => (g.cond.f k).isSome

def atsB (g : Comp.Gen FM) : Bool :=
  !g.drop && 1 ≤ g.bo && stB g.blocks && (blocksOf g.blocks).all fun (k, b) =>
    1 ≤ k && k < g.bo && (getJmps b.fin).all (·.there < k)

def regsBelowB (g : Comp.Gen FM) : Bool :=
  (blocksOf g.blocks).all fun (_, b) => (blobRegsB b).all (· < g.re)

def goalRegs : CGoalL LS → List Nat
  | CGoalL.next laz th => (nodesF 30 [] (th.there, laz)).flatMap (·.2.1)
  | _ => []

def condB (goal : CGoalL LS) (g : Comp.Gen FM) : Bool :=
  let D := allDefsL g.blocks
  let G := goalRegs goal
  (condKeys g).all fun k => match g.cond.f k with
    | some v => k < g.re && !D.contains k && !G.contains k && v.1 < g.re && (g.cond.f v.1).isNone
    | none => true

def freshB (g : Comp.Gen FM) (j : Jmp) : Bool :=
  j.args.isEmpty && j.there < g.bo && match g.blocks.f j.there with
    | some b => b.par.isEmpty
    | none => false

def goalB' (goal : CGoalL LS) (g : Comp.Gen FM) : Bool :=
  match goal with
  | CGoalL.next laz th =>
    let D := allDefsL g.blocks
    let N := nodesF 30 [] (th.there, laz)
    freshB g th && nodupB (N.flatMap (·.2.1)) && N.all fun x =>
      x.1 < g.bo && (match g.blocks.f x.1 with | some b => b.par.isEmpty | none => false) &&
      x.2.1.all fun r => r < g.re && !D.contains r
  | CGoalL.pick z o => freshB g z && freshB g o
  | CGoalL.done => true

def iB (K : List (Nat × List Nat)) (goal : CGoalL LS) (g : Comp.Gen FM) : Bool :=
  atsB g && regsBelowB g && condB goal g && K.all (·.1 < g.bo) && goalB' goal g

/-- `cond` only grows, by keys from `re` on. -/
def condGrowB (g0 g1 : Comp.Gen FM) : Bool :=
  (condKeys g0).all (fun k => g1.cond.f k == g0.cond.f k) &&
  (condKeys g1).all fun k => (g0.cond.f k).isSome || g0.re ≤ k

def prepB (goal : CGoalL LS) (g0 g1 : Comp.Gen FM) : Bool :=
  (blocksOf g0.blocks).all fun (k, b) => match g1.blocks.f k with
    | some b' => match prefixOf b b' with
      | some A => A.isEmpty || (goalLabs goal).contains k
      | none => false
    | none => false

def liveCB (K : List (Nat × List Nat)) (goal : CGoalL LS) (g0 g1 : Comp.Gen FM) (nex : NextL LS) : Bool :=
  let G := match goal with
    | CGoalL.next laz th => liveKF (unpB g0) (K ++ killsOf th.there laz) (fuelOf g0) th.there
    | CGoalL.pick z o => liveKF (unpB g0) K (fuelOf g0) z.there ++ liveKF (unpB g0) K (fuelOf g0) o.there
    | CGoalL.done => []
  (liveKF (unpB g1) (K ++ killsOf nex.th.there nex.laz) (fuelOf g1) nex.th.there).all G.contains

/-- **The frame of the definitions**: a register a block defines after the
run was defined before it, is fresh (from the old `re` on), or is a register
of the goal's lazy tree. -/
def defsB (goal : CGoalL LS) (g0 g1 : Comp.Gen FM) : Bool :=
  let D0 := allDefsL g0.blocks
  let G := goalRegs goal
  (allDefsL g1.blocks).all fun y => D0.contains y || g0.re ≤ y || G.contains y

/-- **The result's goal registers**: a register of the result's lazy tree is
one of the goal's or fresh (what composes `defsB` along `%7`). -/
def gregB (goal : CGoalL LS) (g0 : Comp.Gen FM) (nex : NextL LS) : Bool :=
  let G := goalRegs goal
  (goalRegs nex.goal).all fun y => G.contains y || g0.re ≤ y

/-- At every node of the tree the bonds lie at distinct labels and the forks
at distinct `yes` labels (`LabUniq` of `RawInvCLCopy.lean`, which `+copy`
needs of both its trees). -/
def labUniqB : Nat → Lazy LS → Bool
  | 0, _ => true
  | f + 1, mk _ fk bd => nodupB (bd.map (·.1)) && nodupB (fk.map (·.1.1)) &&
      bd.all (fun e => labUniqB f e.2) && fk.all (fun e => labUniqB f e.1.2 && labUniqB f e.2.2)

def goalLabB : CGoalL LS → Bool
  | CGoalL.next laz _ => labUniqB 30 laz
  | _ => true

/-- **`LabUniq` carries**: when the goal's lazy tree has it, the result's has
it.  (Its entry labels lie below `bo` already by `iB`: every entry has a
block, every block lies below `bo`.) -/
def labB (goal : CGoalL LS) (nex : NextL LS) : Bool := !goalLabB goal || labUniqB 30 nex.laz

/-- A sub-run with its checks: `none` when one fails. -/
def wrapC (K : List (Nat × List Nat)) (X : Comp.Gen FM → Bool) (rp : CGoalL LS → List Nat → CM FM (NextL LS)) :
    CGoalL LS → List Nat → CM FM (NextL LS) := fun goal region g0 =>
  if !(iB K goal g0 && X g0) then Option.none else
  match rp goal region g0 with
  | some (nex, g1) =>
    if iB K nex.goal g1 && liveCB K goal g0 g1 nex && prepB goal g0 g1 && condGrowB g0 g1 && defsB goal g0 g1 &&
      gregB goal g0 nex && labB goal nex && g0.re ≤ g1.re then some (nex, g1)
    else Option.none
  | Option.none => Option.none

/-- `runLC` on the arms of `PlainN`, every recursive call checked. -/
def runLCk (K : List (Nat × List Nat)) (X : Comp.Gen FM → Bool) (env : CallEnv) : Option Nomm → Nomm → CGoalL LS → List Nat →
    CM FM (NextL LS)
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
          let nex2 ← wrapC K X (runLCk K X env sup q) (CGoalL.next (ofSure Sure.bunt) (jmp0 o)) region
          let nex2 ← pastL env.cod nex2 p region
          let nex1 ← wrapC K X (runLCk K X env sup p) (CGoalL.next (ofSure Sure.bunt) nex2.th) region
          copyL nex1 nex2.laz
      | CGoalL.next laz th => do
          let (hed, tel, o) ← splitL ⟨laz, th⟩
          let nexh ← pastL env.cod ⟨hed, jmp0 o⟩ q region
          let nex2 ← wrapC K X (runLCk K X env sup q) (CGoalL.next tel nexh.th) region
          let nex2 ← pastL env.cod nex2 p region
          let nex1 ← wrapC K X (runLCk K X env sup p) (CGoalL.next nexh.laz nex2.th) region
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
          if noneEquivalentL laz then wrapC K X (runLCk K X env sup p) (CGoalL.next laz th) region else do
            let a ← collapseLazyAtomL ⟨laz, th⟩
            match a with
            | Option.none => fun _ => Option.none
            | some (r, o) => do
                let (z, o') ← forl r o
                let r' ← re
                let oc ← emit ⟨[], [], Termin.clq r' (jmp0 z) (jmp0 o')⟩
                wrapC K X (runLCk K X env sup p) (CGoalL.next (ofSure (lazyReg r')) (jmp0 oc)) region
      | CGoalL.pick z o => do
          let r ← re
          let oc ← emit ⟨[], [], Termin.clq r z o⟩
          wrapC K X (runLCk K X env sup p) (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region
      | CGoalL.done => do
          let (o0, o1) ← doneBlocks
          let r ← re
          let oc ← emit ⟨[], [], Termin.clq r (jmp0 o0) (jmp0 o1)⟩
          wrapC K X (runLCk K X env sup p) (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region
  | sup, Nomm.n4 p, goal, region =>
      match goal with
      | CGoalL.done => do
          let pro ← re
          let arg ← re
          let o ← emit ⟨[], [Pole.inc arg pro], Termin.don pro⟩
          wrapC K X (runLCk K X env sup p) (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region
      | CGoalL.pick z o => do
          let pro ← re
          let arg ← re
          let o' ← emit ⟨[], [Pole.inc arg pro], Termin.brn pro z o⟩
          wrapC K X (runLCk K X env sup p) (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o')) region
      | CGoalL.next laz th => do
          let a ← collapseLazyAtomL ⟨laz, th⟩
          let (pro, th') ← (match a with
            | some x => pure x
            | Option.none => do
                let r ← re
                if th.args = [] then pure (r, th.there) else fun _ => Option.none : CM FM (Nat × Nat))
          let arg ← re
          let o ← emit ⟨[], [Pole.inc arg pro], Termin.hop (jmp0 th')⟩
          wrapC K X (runLCk K X env sup p) (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region
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
      let nexq ← wrapC K X (runLCk K X env sup q) (CGoalL.next (ofSure (lazyReg rq)) (jmp0 o)) region
      let nexq ← pastL env.cod nexq p region
      let nexp ← wrapC K X (runLCk K X env sup p) (CGoalL.next (ofSure (lazyReg rp)) nexq.th) region
      copyL nexp nexq.laz
  | sup, Nomm.n7 p q, goal, region => do
      let nex ← wrapC K X (runLCk K X env (some p) q) goal region
      wrapC K X (runLCk K X env sup p) nex.goal region
  | sup, Nomm.n10 a v q, goal, region => do
      let next ← simpleNextL goal
      let (don, rec, o) ← intoL next a
      let nexR ← pastL env.cod ⟨rec, jmp0 o⟩ v region
      let nexDon ← wrapC K X (runLCk K X env sup v) (CGoalL.next don nexR.th) region
      let nexDon ← pastL env.cod nexDon q region
      let nexRec ← wrapC K X (runLCk K X env sup q) (CGoalL.next nexR.laz nexDon.th) region
      copyL nexRec nexDon.laz
  | sup, Nomm.n2 p q Option.none, goal, region =>
      callL env (wrapC K X (runLCk K X env sup p)) (wrapC K X (runLCk K X env sup q)) p q Option.none sup goal region
  | _, _, _, _ => fun _ => Option.none

/-- The top run checked: same success as `runLC` iff every check passed. -/
def checkIJ (K : List (Nat × List Nat)) (goal : CGoalL LS) (g0 : Comp.Gen FM) (nm : Nomm) : Bool :=
  (wrapC K (fun _ => true) (runLCk K (fun _ => true) envR Option.none nm) goal [] g0).isSome ==
    (runCG goal g0 nm).isSome

/-- The same with the extra precondition `X` at every sub-run (a mutation:
it must fail where some sub-run starts outside `X`). -/
def checkIJX (X : Comp.Gen FM → Bool) (goal : CGoalL LS) (g0 : Comp.Gen FM) (nm : Nomm) : Bool :=
  (wrapC [] X (runLCk [] X envR Option.none nm) goal [] g0).isSome == (runCG goal g0 nm).isSome

def plainCX : List Nomm := enumCX.filter isPlain

/-! ## The precondition at the four top states -/

#guard iB [] CGoalL.done gen0 && iB [] goalY gY && iB [] goalP gP && iB [] goalB gB
#guard iB [(1, [1])] goalY gY && iB [(1, [0])] goalB gB && iB [(1, [1]), (2, [0])] goalP gP

/-! ## Every sub-run of every run of `PlainN` meets the pair (about 45 s) -/

def badIJ (K : List (Nat × List Nat)) (goal : CGoalL LS) (g0 : Comp.Gen FM) : Nat :=
  (plainCX.filter fun nm => !checkIJ K goal g0 nm).length

#guard plainCX.length == 2856
#guard (badIJ [] CGoalL.done gen0, badIJ [] goalY gY, badIJ [] goalP gP, badIJ [] goalB gB) == (0, 0, 0, 0)
#guard (badIJ [(1, [1])] goalY gY, badIJ [(1, [0])] goalB gB, badIJ [(1, [1]), (2, [0])] goalP gP) == (0, 0, 0)
#guard (plainCX.filter fun nm => (runCG goalB gB nm).isSome).length == 2856

/-! ## The wrapper bites at sub-runs: asking an empty `cond` at every sub-run
fails on the 2,832 runs under the bond goal that read a proxy in an old
block, and on 290 under `%done` (a sub-run after the `+kern` of a call). -/

#guard ((plainCX.filter fun nm => !checkIJX (fun g => (condKeys g).isEmpty) goalB gB nm).length,
  (plainCX.filter fun nm => !checkIJX (fun g => (condKeys g).isEmpty) CGoalL.done gen0 nm).length) == (2832, 290)

/-! ## `labB` is not vacuous and needs its hypothesis: under the four goals
496, 496, 344 and 1,056 top results have a node with two bonds or two forks;
from a goal with two bonds at one label (`goalDup`, which meets `iB`), 832 of
the 2,856 top results have two bonds at one label (the goal's, passed on).
The stronger "all entry labels of the tree distinct" holds on every top
result under `%done`, `%next` and the bond goal. -/

def multiB : Nat → Lazy LS → Bool
  | 0, _ => false
  | f + 1, mk _ fk bd => 2 ≤ bd.length || 2 ≤ fk.length ||
      bd.any (fun e => multiB f e.2) || fk.any (fun e => multiB f e.1.2 || multiB f e.2.2)

def goalDup : CGoalL LS := CGoalL.next (mk (lazyReg 1) [] [(1, ofSure (lazyReg 0)), (1, ofSure (lazyReg 3))]) (jmp0 2)
def gDup : Comp.Gen FM := { gB with re := 4 }

def cntTopL (goal : CGoalL LS) (g0 : Comp.Gen FM) (P : NextL LS → Bool) : Nat :=
  (plainCX.filter fun nm => match runCG goal g0 nm with | some (nex, _) => P nex | none => false).length

#guard iB [] goalDup gDup && !goalLabB goalDup
#guard (cntTopL CGoalL.done gen0 (fun n => multiB 30 n.laz), cntTopL goalY gY (fun n => multiB 30 n.laz),
  cntTopL goalP gP (fun n => multiB 30 n.laz), cntTopL goalB gB (fun n => multiB 30 n.laz)) == (496, 496, 344, 1056)
#guard cntTopL goalDup gDup (fun n => !labUniqB 30 n.laz) == 832
#guard (cntTopL goalB gB (fun n => !nodupB (((nodesF 30 [] (0, n.laz)).map (·.1)).drop 1)),
  cntTopL goalY gY (fun n => !nodupB (((nodesF 30 [] (0, n.laz)).map (·.1)).drop 1)),
  cntTopL CGoalL.done gen0 (fun n => !nodupB (((nodesF 30 [] (0, n.laz)).map (·.1)).drop 1))) == (0, 0, 0)

end Raw
end SkaModel
end Formalization
