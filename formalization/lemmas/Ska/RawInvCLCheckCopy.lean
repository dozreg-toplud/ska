import lemmas.Ska.RawInvCLCheckIJ

/-!
# The spec of `+copy` with calls, checked at every copy

README Gaps 14 (b), track D.  `copyL_spec` (`RawInvCLCopy.lean`) is the
step that closes `%5`, cons, `%10` and the call `%2`: the result `first` of
the second run is merged with the parked result `second` of the first run,
whose continuation is `s2` (the `th.there` of the first run's result after
`+past`).  Here it is checked at EVERY copy of every run of `runLC` on the
2,856 `PlainN` nomms of `enumCX`: `runLCc` is `runLC` on the arms of
`PlainN` with each `copyL` replaced by `copyC`, which fails (returns `none`)
when a hypothesis or the conclusion of the spec fails:

* hypotheses: `IL K first.goal g` (`iB`), `IL K (next second (jmp0 s2)) g`
  (`second` is a goal at the state before the copy), the registers of
  `first`'s tree are apart from those of `second`'s (`apB`), and in both
  trees the bonds of a node lie at distinct labels and its forks at
  distinct `yes` labels (`labUniqF`: without it the spec is false, `gD`);
* conclusion: `IL K nex.goal g'`, and a register live at the result's entry
  in the unproxied blocks after the copy, the result's tree killing its
  needs, is live at `first.th.there` in the unproxied blocks before it with
  the kills `K`, those of `second`'s tree entered at `s2` and those of
  `first`'s tree.

So `runLCc` returns exactly when `runLC` does iff every check passed.
-/

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

/-- The registers of `first`'s tree are apart from those of `second`'s. -/
def apB (first : NextL LS) (second : Lazy LS) (s2 : Nat) : Bool :=
  let G := goalRegs (CGoalL.next second (jmp0 s2))
  (goalRegs first.goal).all fun y => !G.contains y

/-- At every node of the tree the bonds lie at distinct labels and the
forks at distinct `yes` labels (`+copy` merges by label: with two bonds at
one label it drops one, `gD` below). -/
def labUniqF : Nat → Lazy LS → Bool
  | 0, _ => true
  | f + 1, mk _ fk bd => nodupB (bd.map (·.1)) && nodupB (fk.map (·.1.1)) &&
      bd.all (fun e => labUniqF f e.2) && fk.all (fun e => labUniqF f e.1.2 && labUniqF f e.2.2)

/-- The live implication of the spec, with the kills of `second` given by
`KS` (a mutation drops them). -/
def copyLiveB (K KR : List (Nat × List Nat)) (KS : List (Nat × List Nat)) (first : NextL LS) (at0 : Nat)
    (g g' : Comp.Gen FM) (nex : NextL LS) : Bool :=
  (liveKF (unpB g') (K ++ KR) (fuelOf g') nex.th.there).all
    (liveKF (unpB g) (K ++ KS ++ killsOf first.th.there first.laz) (fuelOf g) at0).contains

/-- `+copy` with the checks of its spec; `M` picks the mutation: `0` none,
`1` drop the result's kills before the copy, `2` ask the live registers at
`s2` instead of `first.th.there`. -/
def copyC (M : Nat) (K : List (Nat × List Nat)) (first : NextL LS) (second : Lazy LS) (s2 : Nat) :
    CM FM (NextL LS) := fun g =>
  let hyp := iB K first.goal g && iB K (CGoalL.next second (jmp0 s2)) g && apB first second s2 &&
    labUniqF 30 first.laz && labUniqF 30 second
  if !hyp then Option.none else
  match copyL first second g with
  | some (nex, g') =>
    let KR := if M == 1 then [] else killsOf nex.th.there nex.laz
    let at0 := if M == 2 then s2 else first.th.there
    if iB K nex.goal g' && copyLiveB K KR (killsOf s2 second) first at0 g g' nex then some (nex, g') else Option.none
  | Option.none => Option.none

/-- The indirect branch of `callL` with the checked copy. -/
def callNoneC (M : Nat) (K : List (Nat × List Nat)) (env : CallEnv)
    (rp rq : CGoalL LS → List Nat → CM FM (NextL LS)) (p : Nomm) (goal : CGoalL LS) (region : List Nat) :
    CM FM (NextL LS) := do
  let nex ← simpleNextL goal
  let (out, pro) ← kerf nex
  let rSub ← re
  let rFol ← re
  let o ← emit ⟨[], [Pole.nok rSub rFol pro], Termin.hop (jmp0 out)⟩
  let nexFol ← rq (CGoalL.next (ofSure (lazyReg rFol)) (jmp0 o)) region
  let nexFol ← pastL env.cod nexFol p region
  let nexSub ← rp (CGoalL.next (ofSure (lazyReg rSub)) nexFol.th) region
  copyC M K nexSub nexFol.laz nexFol.th.there

/-- `runLC` on the arms of `PlainN`, every copy checked. -/
def runLCc (M : Nat) (K : List (Nat × List Nat)) (env : CallEnv) : Option Nomm → Nomm → CGoalL LS → List Nat →
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
          let nex2 ← runLCc M K env sup q (CGoalL.next (ofSure Sure.bunt) (jmp0 o)) region
          let nex2 ← pastL env.cod nex2 p region
          let nex1 ← runLCc M K env sup p (CGoalL.next (ofSure Sure.bunt) nex2.th) region
          copyC M K nex1 nex2.laz nex2.th.there
      | CGoalL.next laz th => do
          let (hed, tel, o) ← splitL ⟨laz, th⟩
          let nexh ← pastL env.cod ⟨hed, jmp0 o⟩ q region
          let nex2 ← runLCc M K env sup q (CGoalL.next tel nexh.th) region
          let nex2 ← pastL env.cod nex2 p region
          let nex1 ← runLCc M K env sup p (CGoalL.next nexh.laz nex2.th) region
          copyC M K nex1 nex2.laz nex2.th.there
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
          if noneEquivalentL laz then runLCc M K env sup p (CGoalL.next laz th) region else do
            let a ← collapseLazyAtomL ⟨laz, th⟩
            match a with
            | Option.none => fun _ => Option.none
            | some (r, o) => do
                let (z, o') ← forl r o
                let r' ← re
                let oc ← emit ⟨[], [], Termin.clq r' (jmp0 z) (jmp0 o')⟩
                runLCc M K env sup p (CGoalL.next (ofSure (lazyReg r')) (jmp0 oc)) region
      | CGoalL.pick z o => do
          let r ← re
          let oc ← emit ⟨[], [], Termin.clq r z o⟩
          runLCc M K env sup p (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region
      | CGoalL.done => do
          let (o0, o1) ← doneBlocks
          let r ← re
          let oc ← emit ⟨[], [], Termin.clq r (jmp0 o0) (jmp0 o1)⟩
          runLCc M K env sup p (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region
  | sup, Nomm.n4 p, goal, region =>
      match goal with
      | CGoalL.done => do
          let pro ← re
          let arg ← re
          let o ← emit ⟨[], [Pole.inc arg pro], Termin.don pro⟩
          runLCc M K env sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region
      | CGoalL.pick z o => do
          let pro ← re
          let arg ← re
          let o' ← emit ⟨[], [Pole.inc arg pro], Termin.brn pro z o⟩
          runLCc M K env sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o')) region
      | CGoalL.next laz th => do
          let a ← collapseLazyAtomL ⟨laz, th⟩
          let (pro, th') ← (match a with
            | some x => pure x
            | Option.none => do
                let r ← re
                if th.args = [] then pure (r, th.there) else fun _ => Option.none : CM FM (Nat × Nat))
          let arg ← re
          let o ← emit ⟨[], [Pole.inc arg pro], Termin.hop (jmp0 th')⟩
          runLCc M K env sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region
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
      let nexq ← runLCc M K env sup q (CGoalL.next (ofSure (lazyReg rq)) (jmp0 o)) region
      let nexq ← pastL env.cod nexq p region
      let nexp ← runLCc M K env sup p (CGoalL.next (ofSure (lazyReg rp)) nexq.th) region
      copyC M K nexp nexq.laz nexq.th.there
  | sup, Nomm.n7 p q, goal, region => do
      let nex ← runLCc M K env (some p) q goal region
      runLCc M K env sup p nex.goal region
  | sup, Nomm.n10 a v q, goal, region => do
      let next ← simpleNextL goal
      let (don, rec, o) ← intoL next a
      let nexR ← pastL env.cod ⟨rec, jmp0 o⟩ v region
      let nexDon ← runLCc M K env sup v (CGoalL.next don nexR.th) region
      let nexDon ← pastL env.cod nexDon q region
      let nexRec ← runLCc M K env sup q (CGoalL.next nexR.laz nexDon.th) region
      copyC M K nexRec nexDon.laz nexDon.th.there
  | sup, Nomm.n2 p q Option.none, goal, region =>
      callNoneC M K env (runLCc M K env sup p) (runLCc M K env sup q) p goal region
  | _, _, _, _ => fun _ => Option.none

/-- The top run with every copy checked: same success as `runLC` iff every
check passed. -/
def checkCopy (M : Nat) (K : List (Nat × List Nat)) (goal : CGoalL LS) (g0 : Comp.Gen FM) (nm : Nomm) : Bool :=
  (runLCc M K envR Option.none nm goal [] g0).isSome == (runCG goal g0 nm).isSome

def badCopy (M : Nat) (K : List (Nat × List Nat)) (goal : CGoalL LS) (g0 : Comp.Gen FM) : Nat :=
  (plainCX.filter fun nm => !checkCopy M K goal g0 nm).length

/-! ## Every copy of every run of `PlainN` meets the spec -/

#guard (badCopy 0 [] CGoalL.done gen0, badCopy 0 [] goalY gY, badCopy 0 [] goalP gP, badCopy 0 [] goalB gB) ==
  (0, 0, 0, 0)
#guard (badCopy 0 [(1, [1])] goalY gY, badCopy 0 [(1, [0])] goalB gB, badCopy 0 [(1, [1]), (2, [0])] goalP gP) ==
  (0, 0, 0)

/-! ## Without `labUniqF` the spec is false: `second` with two bonds at the
label `1` (needs `5` and `6`), `first` with one there (need `7`); the copy
merges `7` with `6` and drops `5`, which block `1` reads: live at the
result's entry, killed at `1` on the other side.  Both trees meet `IL` and
are apart. -/

def gD : Comp.Gen FM :=
  ⟨10, 4, 0, false, HoonMap.put (HoonMap.put (HoonMap.put (HoonMap.empty : FM Blob) 1
      ⟨[], [Pole.con 5 6 8, Pole.con 8 7 9], Termin.don 9⟩) 2 ⟨[], [], Termin.hop (jmp0 1)⟩) 3
      ⟨[], [], Termin.hop (jmp0 1)⟩, HoonMap.empty, HoonMap.empty⟩
def firstD : NextL LS := ⟨mk Sure.bunt [] [(1, ofSure (lazyReg 7))], jmp0 2⟩
def secondD : Lazy LS := mk Sure.bunt [] [(1, ofSure (lazyReg 5)), (1, ofSure (lazyReg 6))]

#guard iB [] firstD.goal gD && iB [] (CGoalL.next secondD (jmp0 3)) gD && apB firstD secondD 3 &&
  !labUniqF 30 secondD
#guard match copyL firstD secondD gD with
  | some (nex, g') => iB [] nex.goal g' &&
      !copyLiveB [] (killsOf nex.th.there nex.laz) (killsOf 3 secondD) firstD firstD.th.there gD g' nex &&
      liveKF (unpB g') (killsOf nex.th.there nex.laz) (fuelOf g') nex.th.there == [5]
  | none => false

/-! ## Mutations: without the result's kills the live implication fails on
almost every run (its sure need is read by the code it enters); asking the
live registers at `s2` instead of `first.th.there` still passes (the second
run's code reads only registers it defines or its goal's need), so the
check does not tell the two entries apart. -/

#guard (badCopy 1 [] CGoalL.done gen0, badCopy 1 [] goalY gY, badCopy 1 [] goalP gP, badCopy 1 [] goalB gB) ==
  (2849, 2849, 2847, 2849)
#guard (badCopy 2 [] CGoalL.done gen0, badCopy 2 [] goalY gY, badCopy 2 [] goalP gP, badCopy 2 [] goalB gB) ==
  (0, 0, 0, 0)

end Raw
end SkaModel
end Formalization
