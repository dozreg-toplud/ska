import lemmas.Ska.RawInvCLCheckIJ
import lemmas.Ska.RawInvCLSARunBase
import lemmas.Ska.CompDirectMCheck

/-!
# The run-level specs with DIRECT calls, checked at every sub-run

README Gaps 14 (b), track D.  `RawInvCLCheckIJ.lean` checks the pair `I` /
`J` of the liveness induction (`iB` before every sub-run; `jB`, `liveCB`,
`prepB`, `condGrowB`, `defsB`, `gregB`, `labB` after) on `PlainN` (indirect
calls only).  Here the same wrapper runs on `runLCM env true`, whose `%2`
with a bell is `callDM` (`CompDirectM.lean`: the drop path, and
`monoBlocks` with `+mono-try-call`: the `%clq` blocks to the pessimistic
call `pes`, the `merge` block with a parameter, `jsp` / `csl` / `cal`);
`callLM` takes the two runs as parameters, so the direct call's sub-runs
are wrapped too.  Two more clauses after each sub-run: `re` grows, and the
definition count `SCR` of `RawInvCLSARunBase.lean` (definitions after plus
occurrences in the result's tree at most definitions before plus
occurrences in the goal's tree plus one if fresh).

* `kdcEnumDX`: track G's `enumDX` (`Glue/EntryPathCheck.lean`, copied here
  as `kdcToDirect` so that no Glue file is imported): the 3,960 nomms of
  `enumCX` with every indirect call made direct, to `bellR` and to `bellR2`
  with the formula `[1 R2]`; 7,920 nomms, 5,742 with no `%6` (`kdcNS`),
  all of them with a direct call.
* `kdcRunk cs K env`: the checked run (clauses `cs`); `kdcChkE`: the
  checked run succeeds exactly when `runLCM env true` does.
* Environments: `envD` (G's; every callee impure, so `callDM` takes the
  `monoBlocks` path) and `envDP` (every callee pure: the drop path, taken on
  612, 1,488 and 612 runs under `%done`, `%pick` and the bond goal).

Findings (`#guard`ed below, about 5 minutes):
* **Every clause holds at every sub-run** of the 5,742 nomms under `%done`
  at `gen0`, `goalY`, `goalP` and `goalB`, with `envD` and with `envDP`
  (0 failures); every run succeeds.  On `PlainN` with `envD`: 0 as before.
* **`SAB`** (every register defined once, no trace op, jump arguments
  defined in their block) of the top run's blocks and after the top `+kerf`:
  0 failures on the 5,742.
* The wrapper bites at the direct call's own sub-runs: asking that no block
  ends in `jsp` at a sub-run's start fails on all 1,278 bare direct calls
  under `%done`; asking that no block holds a `csl` fails on all 1,278 under
  `goalB` and `goalY`.
-/

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

/-- `toDirect` of `Glue/EntryPathCheck.lean`. -/
def kdcToDirect (b : Bell) (q0 : Option Nomm) : Nomm → Nomm
  | Nomm.n2 p q Option.none => Nomm.n2 (kdcToDirect b q0 p) (q0.getD (kdcToDirect b q0 q)) (some (b, Option.none))
  | Nomm.n2 p q i => Nomm.n2 (kdcToDirect b q0 p) (kdcToDirect b q0 q) i
  | Nomm.n3 p => Nomm.n3 (kdcToDirect b q0 p)
  | Nomm.n4 p => Nomm.n4 (kdcToDirect b q0 p)
  | Nomm.n5 p q => Nomm.n5 (kdcToDirect b q0 p) (kdcToDirect b q0 q)
  | Nomm.cons p q => Nomm.cons (kdcToDirect b q0 p) (kdcToDirect b q0 q)
  | Nomm.n6 p q r => Nomm.n6 (kdcToDirect b q0 p) (kdcToDirect b q0 q) (kdcToDirect b q0 r)
  | Nomm.n7 p q => Nomm.n7 (kdcToDirect b q0 p) (kdcToDirect b q0 q)
  | Nomm.n10 a v q => Nomm.n10 a (kdcToDirect b q0 v) (kdcToDirect b q0 q)
  | nm => nm

def kdcEnumDX : List Nomm :=
  enumCX.map (kdcToDirect bellR Option.none) ++ enumCX.map (kdcToDirect bellR2 (some (Nomm.n1 nounR2)))

/-- No `%6`, no hint; calls of both kinds. -/
def kdcNoSix : Nomm → Bool
  | Nomm.n0 _ => true
  | Nomm.n1 _ => true
  | Nomm.n3 p => kdcNoSix p
  | Nomm.n4 p => kdcNoSix p
  | Nomm.n5 p q => kdcNoSix p && kdcNoSix q
  | Nomm.cons p q => kdcNoSix p && kdcNoSix q
  | Nomm.n7 p q => kdcNoSix p && kdcNoSix q
  | Nomm.n10 _ v q => kdcNoSix v && kdcNoSix q
  | Nomm.n2 p q _ => kdcNoSix p && kdcNoSix q
  | _ => false

def kdcHasDirect : Nomm → Bool
  | Nomm.n3 p => kdcHasDirect p
  | Nomm.n4 p => kdcHasDirect p
  | Nomm.n5 p q => kdcHasDirect p || kdcHasDirect q
  | Nomm.cons p q => kdcHasDirect p || kdcHasDirect q
  | Nomm.n6 p q r => kdcHasDirect p || kdcHasDirect q || kdcHasDirect r
  | Nomm.n7 p q => kdcHasDirect p || kdcHasDirect q
  | Nomm.n10 _ v q => kdcHasDirect v || kdcHasDirect q
  | Nomm.n2 _ _ (some _) => true
  | Nomm.n2 p q Option.none => kdcHasDirect p || kdcHasDirect q
  | _ => false

/-- The definition count `SCR` of a sub-run. -/
def kdcScrB (goal : CGoalL LS) (g0 g1 : Comp.Gen FM) (nex : NextL LS) : Bool :=
  let D0 := allDefsL g0.blocks
  let D1 := allDefsL g1.blocks
  let R1 := sarR nex.laz
  let R0 := sarG goal
  (D1 ++ R1).all fun y => D1.count y + R1.count y ≤ D0.count y + R0.count y + fr g0.re g1.re y

/-- The post clauses (`10` to `12` are mutations): 1 `jB`, 2 `liveCB`, 3 `prepB`, 4 `condGrowB`, 5 `defsB`, 6 `gregB`, 7 `labB`,
8 `re` grows, 9 `SCR`. -/
def kdcPost (K : List (Nat × List Nat)) (goal : CGoalL LS) (g0 g1 : Comp.Gen FM) (nex : NextL LS) : Nat → Bool
  | 1 => iB K nex.goal g1
  | 2 => liveCB K goal g0 g1 nex
  | 3 => prepB goal g0 g1
  | 4 => condGrowB g0 g1
  | 5 => defsB goal g0 g1
  | 6 => gregB goal g0 nex
  | 7 => labB goal nex
  | 8 => decide (g0.re ≤ g1.re)
  | 9 => kdcScrB goal g0 g1 nex
  | 10 => (blocksOf g1.blocks).all fun (_, b) => b.par.isEmpty
  | 11 => (blocksOf g0.blocks).all fun (_, b) => match b.fin with | Termin.jsp _ _ => false | _ => true
  | 12 => (blocksOf g0.blocks).all fun (_, b) => b.body.all fun p => match p with | Pole.csl .. => false | _ => true
  | _ => true

/-- A sub-run with the clauses `cs` checked (`0`: `iB` before); a post
clause is checked only where `iB` held before. -/
def kdcWrap (cs : List Nat) (K : List (Nat × List Nat)) (rp : CGoalL LS → List Nat → CM FM (NextL LS)) :
    CGoalL LS → List Nat → CM FM (NextL LS) := fun goal region g0 =>
  let pre := iB K goal g0
  if cs.contains 0 && !pre then Option.none else
  match rp goal region g0 with
  | some (nex, g1) =>
    if !pre || cs.all (fun c => c == 0 || kdcPost K goal g0 g1 nex c) then some (nex, g1) else Option.none
  | Option.none => Option.none

/-- `runLCM env true` on the arms with no `%6`, every recursive call checked,
the direct call's sub-runs too (`callLM` takes the runs as parameters). -/
def kdcRunk (cs : List Nat) (K : List (Nat × List Nat)) (env : CallEnv) : Option Nomm → Nomm → CGoalL LS → List Nat →
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
          let nex2 ← kdcWrap cs K (kdcRunk cs K env sup q) (CGoalL.next (ofSure Sure.bunt) (jmp0 o)) region
          let nex2 ← pastL env.cod nex2 p region
          let nex1 ← kdcWrap cs K (kdcRunk cs K env sup p) (CGoalL.next (ofSure Sure.bunt) nex2.th) region
          copyL nex1 nex2.laz
      | CGoalL.next laz th => do
          let (hed, tel, o) ← splitL ⟨laz, th⟩
          let nexh ← pastL env.cod ⟨hed, jmp0 o⟩ q region
          let nex2 ← kdcWrap cs K (kdcRunk cs K env sup q) (CGoalL.next tel nexh.th) region
          let nex2 ← pastL env.cod nex2 p region
          let nex1 ← kdcWrap cs K (kdcRunk cs K env sup p) (CGoalL.next nexh.laz nex2.th) region
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
          if noneEquivalentL laz then kdcWrap cs K (kdcRunk cs K env sup p) (CGoalL.next laz th) region else do
            let a ← collapseLazyAtomL ⟨laz, th⟩
            match a with
            | Option.none => fun _ => Option.none
            | some (r, o) => do
                let (z, o') ← forl r o
                let r' ← re
                let oc ← emit ⟨[], [], Termin.clq r' (jmp0 z) (jmp0 o')⟩
                kdcWrap cs K (kdcRunk cs K env sup p) (CGoalL.next (ofSure (lazyReg r')) (jmp0 oc)) region
      | CGoalL.pick z o => do
          let r ← re
          let oc ← emit ⟨[], [], Termin.clq r z o⟩
          kdcWrap cs K (kdcRunk cs K env sup p) (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region
      | CGoalL.done => do
          let (o0, o1) ← doneBlocks
          let r ← re
          let oc ← emit ⟨[], [], Termin.clq r (jmp0 o0) (jmp0 o1)⟩
          kdcWrap cs K (kdcRunk cs K env sup p) (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region
  | sup, Nomm.n4 p, goal, region =>
      match goal with
      | CGoalL.done => do
          let pro ← re
          let arg ← re
          let o ← emit ⟨[], [Pole.inc arg pro], Termin.don pro⟩
          kdcWrap cs K (kdcRunk cs K env sup p) (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region
      | CGoalL.pick z o => do
          let pro ← re
          let arg ← re
          let o' ← emit ⟨[], [Pole.inc arg pro], Termin.brn pro z o⟩
          kdcWrap cs K (kdcRunk cs K env sup p) (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o')) region
      | CGoalL.next laz th => do
          let a ← collapseLazyAtomL ⟨laz, th⟩
          let (pro, th') ← (match a with
            | some x => pure x
            | Option.none => do
                let r ← re
                if th.args = [] then pure (r, th.there) else fun _ => Option.none : CM FM (Nat × Nat))
          let arg ← re
          let o ← emit ⟨[], [Pole.inc arg pro], Termin.hop (jmp0 th')⟩
          kdcWrap cs K (kdcRunk cs K env sup p) (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region
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
      let nexq ← kdcWrap cs K (kdcRunk cs K env sup q) (CGoalL.next (ofSure (lazyReg rq)) (jmp0 o)) region
      let nexq ← pastL env.cod nexq p region
      let nexp ← kdcWrap cs K (kdcRunk cs K env sup p) (CGoalL.next (ofSure (lazyReg rp)) nexq.th) region
      copyL nexp nexq.laz
  | sup, Nomm.n7 p q, goal, region => do
      let nex ← kdcWrap cs K (kdcRunk cs K env (some p) q) goal region
      kdcWrap cs K (kdcRunk cs K env sup p) nex.goal region
  | sup, Nomm.n10 a v q, goal, region => do
      let next ← simpleNextL goal
      let (don, rec, o) ← intoL next a
      let nexR ← pastL env.cod ⟨rec, jmp0 o⟩ v region
      let nexDon ← kdcWrap cs K (kdcRunk cs K env sup v) (CGoalL.next don nexR.th) region
      let nexDon ← pastL env.cod nexDon q region
      let nexRec ← kdcWrap cs K (kdcRunk cs K env sup q) (CGoalL.next nexR.laz nexDon.th) region
      copyL nexRec nexDon.laz
  | sup, Nomm.n2 p q info, goal, region =>
      callLM env true (kdcWrap cs K (kdcRunk cs K env sup p)) (kdcWrap cs K (kdcRunk cs K env sup q)) p q info sup
        goal region
  | _, _, _, _ => fun _ => Option.none

def kdcRealE (env : CallEnv) (goal : CGoalL LS) (g0 : Comp.Gen FM) (nm : Nomm) : Option (NextL LS × Comp.Gen FM) :=
  runLCM env true Option.none nm goal [] g0

def kdcReal (goal : CGoalL LS) (g0 : Comp.Gen FM) (nm : Nomm) : Option (NextL LS × Comp.Gen FM) :=
  kdcRealE envD goal g0 nm

/-- `envD` with every callee pure: the drop path of `callDM`. -/
def envDP : CallEnv := { envD with pure := fun _ => true }

def kdcChkE (env : CallEnv) (cs : List Nat) (goal : CGoalL LS) (g0 : Comp.Gen FM) (nm : Nomm) : Bool :=
  (kdcWrap cs [] (kdcRunk cs [] env Option.none nm) goal [] g0).isSome == (kdcRealE env goal g0 nm).isSome

def kdcBadE (env : CallEnv) (cs : List Nat) (goal : CGoalL LS) (g0 : Comp.Gen FM) (l : List Nomm) : Nat :=
  (l.filter fun nm => !kdcChkE env cs goal g0 nm).length

/-- The top run checked with the clauses `cs`: same success as `runLCM`. -/
def kdcChk (cs : List Nat) (goal : CGoalL LS) (g0 : Comp.Gen FM) (nm : Nomm) : Bool :=
  (kdcWrap cs [] (kdcRunk cs [] envD Option.none nm) goal [] g0).isSome == (kdcReal goal g0 nm).isSome

def kdcAll : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

def kdcNS : List Nomm := kdcEnumDX.filter kdcNoSix
def kdcNSd : List Nomm := kdcNS.filter kdcHasDirect
def kdcNSi : List Nomm := kdcNS.filter (!kdcHasDirect ·)

def kdcBad (cs : List Nat) (goal : CGoalL LS) (g0 : Comp.Gen FM) (l : List Nomm) : Nat :=
  (l.filter fun nm => !kdcChk cs goal g0 nm).length

def argsHereKB (m : FM Blob) : Bool :=
  (blocksOf m).all fun (_, b) => (getJmps b.fin).all fun j =>
    j.args.all fun a => match a with | some r => (blockDefs b).contains r | none => false

/-- `SAB` of the top run's blocks, and after the top `+kerf`. -/
def kdcSA (nm : Nomm) : Option (Bool × Bool) :=
  (kdcReal CGoalL.done gen0 nm).map fun (nex, g) =>
    (defOnceB g.blocks && noTrB g.blocks && argsHereKB g.blocks,
     match (kerf nex : CM FM (Nat × Nat)) g with
     | some (_, g2) => defOnceB g2.blocks && noTrB g2.blocks && argsHereKB g2.blocks
     | none => false)

def kdcCalls : List Nomm := kdcNSd.filter fun nm => match nm with | Nomm.n2 .. => true | _ => false

/-- Runs whose blocks differ between `envD` and `envDP` (the drop path taken). -/
def kdcDropped (goal : CGoalL LS) (g0 : Comp.Gen FM) (l : List Nomm) : Nat :=
  (l.filter fun nm => match kdcRealE envD goal g0 nm, kdcRealE envDP goal g0 nm with
    | some (_, a), some (_, b) => (blocksOf a.blocks).length != (blocksOf b.blocks).length
    | _, _ => false).length

#guard (kdcEnumDX.length, kdcNS.length, kdcNSd.length, kdcCalls.length) == (7920, 5742, 5742, 1278)
#guard (kdcBad kdcAll CGoalL.done gen0 kdcNSd, kdcBad kdcAll goalY gY kdcNSd) == (0, 0)
#guard (kdcBad kdcAll goalP gP kdcNSd, kdcBad kdcAll goalB gB kdcNSd) == (0, 0)
#guard (kdcBad kdcAll CGoalL.done gen0 plainCX, kdcBad kdcAll goalB gB plainCX) == (0, 0)
#guard ((kdcNSd.filter fun nm => (kdcReal CGoalL.done gen0 nm).isSome).length,
  (kdcNSd.filter fun nm => (kdcReal goalB gB nm).isSome).length) == (5742, 5742)
#guard ((kdcNSd.filterMap kdcSA).length, ((kdcNSd.filterMap kdcSA).filter (!·.1)).length,
  ((kdcNSd.filterMap kdcSA).filter (!·.2)).length) == (5742, 0, 0)
#guard (kdcDropped CGoalL.done gen0 kdcNSd, kdcDropped goalP gP kdcNSd, kdcDropped goalB gB kdcNSd) == (612, 1488, 612)
#guard (kdcBadE envDP kdcAll CGoalL.done gen0 kdcNSd, kdcBadE envDP kdcAll goalY gY kdcNSd) == (0, 0)
#guard (kdcBadE envDP kdcAll goalP gP kdcNSd, kdcBadE envDP kdcAll goalB gB kdcNSd) == (0, 0)
#guard kdcBad [11] CGoalL.done gen0 kdcCalls == 1278
#guard (kdcBad [12] goalB gB kdcCalls, kdcBad [12] goalY gY kdcCalls) == (1278, 1278)

end Raw
end SkaModel
end Formalization
