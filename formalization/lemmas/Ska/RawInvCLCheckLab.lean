import lemmas.Ska.CompGenCheckB
import lemmas.Ska.OptAliasField
import lemmas.Ska.RawInvCLCheckCopy

/-!
# `LabUniq` at every `+copy` beyond `PlainN`, checked

README Gaps 14 (b), track D.  `CopySpecL` (`RawInvCLCopy.lean`) takes
`LabUniq` of both trees: with two bonds at one label in `second`, `+copy`
merges one and drops the other (`gD`).  Here every `copyL` of `runLC` and
`runLCH` (with `%6` in every position, nested `%6`, track J's hint shapes,
goals that are results of other runs) is replaced by `copyK M`, which fails
when its check fails (`M`): `1` `LabUniq` of both inputs; `2` every
register of either input tree is in the output tree or written by an op
the copy added; `3` no register of the inputs is missing while some block
reads it and none defines it; `4` fail at every copy (counts the runs with
a copy); `5` the added ops write distinct registers no block wrote before;
`6` `LabUniq` of the output when both inputs have it; `7` no `mergeRisk`
(a label both sides hold at a merge and one side repeats).  The runner text
between the markers is written by `tools/gen/copyk.py`.

Tally (`tallyK`: runs, base failures, `M = 0` differences, failures per
mode), on track C's families (`CompGenCheck.lean`), run in a scratch file
with `lake env lean` (about 25 minutes in all):

| family | runs | with a copy | failures, modes 1-3, 5-7 |
|---|---|---|---|
| famA: 245 `%6`, flat goals, phases S K F L | 29,400 | 29,400 | 0 |
| famB: `all6` | 154,350 | 154,350 | 0 |
| famC: `sixes ++ brs` under `goalsP` | 75,600 | 74,700 | 0 |
| famH: shapes, flat goals | 2,640 | 2,400 | 0 |
| famH: shapes and `sixesT` under `goalsH` | 46,860 | 45,540 | 0 |
| the generators `gensP`, flat goals | 1,200 | 1,200 | 0 |

So `LabUniq` holds at every copy of these 309,850 runs (307,590 with a
copy), and no copy drops a register.  The labels that repeat in results
(track C: `[7 7 8 8]`, `[10 5 1 8 5 1]`) are at different nodes.  The two
small families are frozen below; on `gD` every check bites.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp
namespace KChk

open Nock Lazy Opt

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

def regsT (l : Lazy S) : List Nat :=
  LSXCheck.regsOf l.sure.ned ++ (entries l).flatMap fun e => LSXCheck.regsOf e.2.sure.ned

def ndB (l : List Nat) : Bool := l.eraseDups.length == l.length

def labUniqG : Nat → Lazy S → Bool
  | 0, _ => true
  | f + 1, mk _ fk bd => ndB (bd.map (·.1)) && ndB (fk.map (·.1.1)) &&
      bd.all (fun e => labUniqG f e.2) && fk.all (fun e => labUniqG f e.1.2 && labUniqG f e.2.2)

/-- A repeated label that the merge of `+copy` reads: at a node where both
sides have bonds (forks), a label of one side that the other has too and
that repeats on either side; then the same below the merged pairs (the last
entry of `second` at the label, as `index` takes it). -/
def mergeRisk : Nat → Lazy S → Lazy S → Bool
  | 0, _, _ => false
  | f + 1, mk _ f1 b1, mk _ f2 b2 =>
    let l1 := b1.map (·.1)
    let l2 := b2.map (·.1)
    let bR := !b1.isEmpty && !b2.isEmpty &&
      ((l1.any fun o => l2.contains o && (l1.count o > 1 || l2.count o > 1)) ||
       b1.any fun (o, l) => match (b2.filter (·.1 == o)).getLast? with
         | some (_, m) => mergeRisk f l m
         | none => false)
    let y1 := f1.map (·.1.1)
    let y2 := f2.map (·.1.1)
    let fR := !f1.isEmpty && !f2.isEmpty &&
      ((y1.any fun o => y2.contains o && (y1.count o > 1 || y2.count o > 1)) ||
       f1.any fun ((oy, y), (_, n)) => match (f2.filter (·.1.1 == oy)).getLast? with
         | some ((_, my), (_, mn)) => mergeRisk f y my || mergeRisk f n mn
         | none => false)
    bR || fR

def blobsOf [HoonMapKeys Map] (g : Gen Map) : List (Nat × Blob) :=
  (HoonMapKeys.keys g.blocks).eraseDups.filterMap fun k => (HoonMap.get g.blocks k).map (k, ·)

/-- The destinations of the ops the copy added (in front of old blocks, or
in fresh blocks). -/
def newDefs [HoonMapKeys Map] (g g' : Gen Map) : List Nat :=
  (blobsOf g').flatMap fun (k, b') => match HoonMap.get g.blocks k with
    | some b => (b'.body.take (b'.body.length - b.body.length)).filterMap aliasDst
    | none => blockDefs b'

def allDefs [HoonMapKeys Map] (g : Gen Map) : List Nat := (blobsOf g).flatMap fun (_, b) => blockDefs b
def allReads [HoonMapKeys Map] (g : Gen Map) : List Nat :=
  (blobsOf g).flatMap fun (_, b) => b.body.flatMap aliasReads ++ finRegs b.fin

/-- The registers of either input tree that are neither in the output tree
nor written by an op the copy added. -/
def missing [HoonMapKeys Map] (first : NextL S) (second : Lazy S) (nex : NextL S) (g g' : Gen Map) : List Nat :=
  let o := regsT nex.laz
  let n := newDefs g g'
  (regsT first.laz ++ regsT second).filter fun r => !o.contains r && !n.contains r

/-- `+copy` with a check; `M`: 0 none, 1 `LabUniq` of both inputs, 2 no
missing register, 3 no missing register that the code reads and nothing
defines, 4 fail at every copy, 5 the added ops write distinct registers no
block wrote before, 6 `LabUniq` kept (inputs `LabUniq` → output `LabUniq`),
7 no `mergeRisk`. -/
def copyK [HoonMapKeys Map] (M : Nat) (first : NextL S) (second : Lazy S) : CM Map (NextL S) := fun g =>
  if M == 4 then Option.none else
  if M == 1 && !(labUniqG 30 first.laz && labUniqG 30 second) then Option.none else
  if M == 7 && mergeRisk 30 first.laz second then Option.none else
  match copyL first second g with
  | Option.none => Option.none
  | some (nex, g') =>
    let ok : Bool := match M with
      | 2 => (missing first second nex g g').isEmpty
      | 3 => let rd := allReads g'
             let df := allDefs g'
             (missing first second nex g g').all fun r => !rd.contains r || df.contains r
      | 5 => let nd := newDefs g g'
             let od := allDefs g
             ndB nd && nd.all fun r => !od.contains r
      | 6 => !(labUniqG 30 first.laz && labUniqG 30 second) || labUniqG 30 nex.laz
      | _ => true
    if ok then some (nex, g') else Option.none

variable [HoonMapKeys Map]

-- BEGIN copyk.py
def copyAllK (M : Nat) (nex : NextL S) : List (Lazy S) → CM Map (NextL S)
  | [] => pure nex
  | b :: rest => do
    let nex ← copyK M nex b
    copyAllK M nex rest

def callLK (M : Nat) (env : CallEnv) (rp rq : CGoalL S → List Nat → CM Map (NextL S)) (p q : Nomm)
    (info : Option (Bell × Option Noun)) (sup : Option Nomm) (goal : CGoalL S) (region : List Nat) :
    CM Map (NextL S) :=
  match info with
  | Option.none => do
      let nex ← simpleNextL goal
      let (out, pro) ← kerf nex
      let rSub ← re
      let rFol ← re
      let o ← emit ⟨[], [Pole.nok rSub rFol pro], Termin.hop (jmp0 out)⟩
      let nexFol ← rq (CGoalL.next (ofSure (lazyReg rFol)) (jmp0 o)) region
      let nexFol ← pastL env.cod nexFol p region
      let nexSub ← rp (CGoalL.next (ofSure (lazyReg rSub)) nexFol.th) region
      copyK M nexSub nexFol.laz
  | some (b, key) =>
      let drop : Option Jmp := match goal with
        | CGoalL.next laz th => if env.pure b && noneEquivalentL laz then some th else Option.none
        | _ => Option.none
      match drop with
      | some th => do
          let nexFol ← (if safeFolFol q then pure ⟨ofSure Sure.bunt, th⟩
            else rq (CGoalL.next (ofSure Sure.bunt) th) region : CM Map (NextL S))
          let nexFol ← pastL env.cod nexFol p region
          let nexSub ← rp (CGoalL.next (ofSure Sure.bunt) nexFol.th) region
          copyK M nexSub nexFol.laz
      | Option.none =>
          match key, env.ring b, env.need b with
          | Option.none, Option.none, some bNed =>
            if env.sof (made p sup) p q b bNed then fun _ => Option.none else do
            let subNed ← needOrdAllocRegs bNed
            let subV := flattenNeed subNed
            let callBlock ← (match goal with
              | CGoalL.done => emit ⟨[], [], Termin.jmp b subV⟩
              | g => do
                  let nex ← simpleNextL g
                  let (out, pro) ← kerf nex
                  emit ⟨[], [Pole.cal b subV pro], Termin.hop (jmp0 out)⟩ : CM Map Nat)
            let nexArg : NextL S := ⟨ofSure ⟨subNed, HoonSet.empty⟩, jmp0 callBlock⟩
            let nexFol ← (if safeFolFol q then pure ⟨ofSure Sure.bunt, nexArg.th⟩
              else rq (CGoalL.next (ofSure Sure.bunt) nexArg.th) region : CM Map (NextL S))
            let nexFol ← pastL env.cod nexFol p region
            let nexSub ← rp (CGoalL.next nexArg.laz nexFol.th) region
            copyK M nexSub nexFol.laz
          | _, _, _ => fun _ => Option.none

def callDMK (M : Nat) (env : CallEnv) (rp rq : CGoalL S → List Nat → CM Map (NextL S)) (p q : Nomm)
    (b : Bell) (key : Option Noun) (goal : CGoalL S) (region : List Nat) : CM Map (NextL S) :=
  let drop : Option Jmp := match goal with
    | CGoalL.next laz th => if env.pure b && noneEquivalentL laz then some th else Option.none
    | _ => Option.none
  match drop with
  | some th => do
      let nexFol ← (if safeFolFol q then pure ⟨ofSure Sure.bunt, th⟩
        else rq (CGoalL.next (ofSure Sure.bunt) th) region : CM Map (NextL S))
      let nexFol ← pastL env.cod nexFol p region
      let nexSub ← rp (CGoalL.next (ofSure Sure.bunt) nexFol.th) region
      copyK M nexSub nexFol.laz
  | Option.none =>
      match key, env.ring b, env.need b with
      | Option.none, Option.none, some bNed => do
        let subNed ← needOrdAllocRegs bNed
        let (subPes, callBlock) ← monoBlocks b subNed goal
        let nexArg : NextL S := ⟨ofSure (lazyReg subPes), jmp0 callBlock⟩
        let nexFol ← (if safeFolFol q then pure ⟨ofSure Sure.bunt, nexArg.th⟩
          else rq (CGoalL.next (ofSure Sure.bunt) nexArg.th) region : CM Map (NextL S))
        let nexFol ← pastL env.cod nexFol p region
        let nexSub ← rp (CGoalL.next nexArg.laz nexFol.th) region
        copyK M nexSub nexFol.laz
      | _, _, _ => fun _ => Option.none

def callLMK (M : Nat) (env : CallEnv) (mono : Bool) (rp rq : CGoalL S → List Nat → CM Map (NextL S)) (p q : Nomm)
    (info : Option (Bell × Option Noun)) (sup : Option Nomm) (goal : CGoalL S) (region : List Nat) :
    CM Map (NextL S) :=
  match mono, info with
  | true, some (b, key) => callDMK M env rp rq p q b key goal region
  | _, _ => callLK M env rp rq p q info sup goal region

def sixNextForkCK (M : Nat) [HoonMapKeys Map] (cod : Bell → Option Bool) (rp rq rr : CGoalL S → List Nat → CM Map (NextL S)) (p : Nomm)
    (laz : Lazy S) (th : Jmp) (region : List Nat) : CM Map (NextL S) := do
  let rCond ← re
  let (g0, g1) ← forkL ⟨laz, th⟩ rCond
  let rid ← idM
  let rb := rid :: region
  let condBefore ← getCond
  let nex1 ← rr (CGoalL.next g1.laz g1.th) rb
  let condBetween ← getCond
  let nex0 ← rq (CGoalL.next g0.laz g0.th) rb
  let (lazy, yes, nuh) ← sect nex0 nex1 g0.th.there g1.th.there rb condBefore condBetween
  let lazy ← liftO (pastFork cod lazy p)
  let o ← emit ⟨[], [], Termin.brn rCond (jmp0 yes) (jmp0 nuh)⟩
  let lazy ← lazyShut o lazy
  let nexCond ← rp (CGoalL.next (ofSure ⟨Need.this rCond, HoonSet.empty⟩) (jmp0 o)) region
  copyK M nexCond lazy

def sixNextSimpleCK (M : Nat) [HoonMapKeys Map] (cod : Bell → Option Bool) (rp rq rr : CGoalL S → List Nat → CM Map (NextL S)) (p : Nomm)
    (laz : Lazy S) (th : Jmp) (region : List Nat) : CM Map (NextL S) := do
  let o0 ← oo
  let o1 ← oo
  let (s0, s1) ← forkSure laz.sure th.there o0 o1
  let rid ← idM
  let rb := rid :: region
  let condBefore ← getCond
  let nex1 ← rr (CGoalL.next (ofSure s1) (jmp0 o1)) rb
  let condBetween ← getCond
  let nex0 ← rq (CGoalL.next (ofSure s0) (jmp0 o0)) rb
  let (lazy, yes, nuh) ← sect nex0 nex1 o0 o1 rb condBefore condBetween
  let lazy ← liftO (pastFork cod lazy p)
  let nexCond ← rp (CGoalL.pick (jmp0 yes) (jmp0 nuh)) region
  if !(lazyBig (softLess noSoft lazy)) then copyK M nexCond lazy else do
    let o ← emit ⟨[], [], Termin.hop nexCond.th⟩
    let lazy ← lazyShut o lazy
    copyK M ⟨nexCond.laz, jmp0 o⟩ lazy

def sixNextLCK (M : Nat) [HoonMapKeys Map] (cod : Bell → Option Bool) (rp rq rr : CGoalL S → List Nat → CM Map (NextL S)) (p q r : Nomm) :
    Nat → Lazy S → Jmp → List Nat → CM Map (NextL S)
  | 0, _, _, _ => fun _ => Option.none
  | fuel + 1, laz, th, region =>
    match leap laz q r with
    | Option.none => fun _ => Option.none
    | some (some (rest, bys)) => do
      let nex ← sixNextLCK M cod rp rq rr p q r fuel rest th region
      copyAllK M nex bys
    | some Option.none =>
      if !(noneEquivalentL (mk Sure.bunt laz.fork laz.bond)) then
        if (whole q && whole r) || thisOnly laz || lazyBig (softLess noSoft laz) ||
            softFork noSoft (fun _ => false) laz then do
          let (out, pro) ← kerf ⟨laz, th⟩
          sixNextLCK M cod rp rq rr p q r fuel (ofSure ⟨Need.this pro, HoonSet.empty⟩) (jmp0 out) region
        else sixNextForkCK M cod rp rq rr p laz th region
      else sixNextSimpleCK M cod rp rq rr p laz th region

def runLCK (M : Nat) [HoonMapKeys Map] (env : CallEnv) : Option Nomm → Nomm → CGoalL S → List Nat → CM Map (NextL S)
  | sup, Nomm.cons p q, goal, region => do
      let goal ← (match goal with
        | CGoalL.done => do
            let r ← re
            let o ← emit ⟨[], [], Termin.don r⟩
            pure (CGoalL.next (ofSure (lazyReg r)) (jmp0 o))
        | g => pure g : CM Map (CGoalL S))
      match goal with
      | CGoalL.pick _ _ => do
          let o ← emit ⟨[], [], Termin.bom Option.none⟩
          let nex2 ← runLCK M env sup q (CGoalL.next (ofSure Sure.bunt) (jmp0 o)) region
          let nex2 ← pastL env.cod nex2 p region
          let nex1 ← runLCK M env sup p (CGoalL.next (ofSure Sure.bunt) nex2.th) region
          copyK M nex1 nex2.laz
      | CGoalL.next laz th => do
          let (hed, tel, o) ← splitL ⟨laz, th⟩
          let nexh ← pastL env.cod ⟨hed, jmp0 o⟩ q region
          let nex2 ← runLCK M env sup q (CGoalL.next tel nexh.th) region
          let nex2 ← pastL env.cod nex2 p region
          let nex1 ← runLCK M env sup p (CGoalL.next nexh.laz nex2.th) region
          copyK M nex1 nex2.laz
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
          if noneEquivalentL laz then runLCK M env sup p (CGoalL.next laz th) region else do
            let a ← collapseLazyAtomL ⟨laz, th⟩
            match a with
            | Option.none => fun _ => Option.none
            | some (r, o) => do
                let (z, o') ← forl r o
                let r' ← re
                let oc ← emit ⟨[], [], Termin.clq r' (jmp0 z) (jmp0 o')⟩
                runLCK M env sup p (CGoalL.next (ofSure (lazyReg r')) (jmp0 oc)) region
      | CGoalL.pick z o => do
          let r ← re
          let oc ← emit ⟨[], [], Termin.clq r z o⟩
          runLCK M env sup p (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region
      | CGoalL.done => do
          let (o0, o1) ← doneBlocks
          let r ← re
          let oc ← emit ⟨[], [], Termin.clq r (jmp0 o0) (jmp0 o1)⟩
          runLCK M env sup p (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region
  | sup, Nomm.n4 p, goal, region =>
      match goal with
      | CGoalL.done => do
          let pro ← re
          let arg ← re
          let o ← emit ⟨[], [Pole.inc arg pro], Termin.don pro⟩
          runLCK M env sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region
      | CGoalL.pick z o => do
          let pro ← re
          let arg ← re
          let o' ← emit ⟨[], [Pole.inc arg pro], Termin.brn pro z o⟩
          runLCK M env sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o')) region
      | CGoalL.next laz th => do
          let a ← collapseLazyAtomL ⟨laz, th⟩
          let (pro, th') ← (match a with
            | some x => pure x
            | Option.none => do
                let r ← re
                if th.args = [] then pure (r, th.there) else fun _ => Option.none : CM Map (Nat × Nat))
          let arg ← re
          let o ← emit ⟨[], [Pole.inc arg pro], Termin.hop (jmp0 th')⟩
          runLCK M env sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region
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
                emit ⟨[], [], Termin.eqq rp rq (jmp0 z) (jmp0 o')⟩ : CM Map Nat)
      let nexq ← runLCK M env sup q (CGoalL.next (ofSure (lazyReg rq)) (jmp0 o)) region
      let nexq ← pastL env.cod nexq p region
      let nexp ← runLCK M env sup p (CGoalL.next (ofSure (lazyReg rp)) nexq.th) region
      copyK M nexp nexq.laz
  | sup, Nomm.n6 p q r, goal, region =>
      match goal with
      | CGoalL.next laz th => sixNextLCK M env.cod (runLCK M env sup p) (runLCK M env sup q) (runLCK M env sup r) p q r 3 laz th region
      | _ => do
          let nex1 ← runLCK M env sup r goal region
          let nex0 ← runLCK M env sup q goal region
          let yes ← emit ⟨[], [], Termin.hop nex0.th⟩
          let nuh ← emit ⟨[], [], Termin.hop nex1.th⟩
          setTag yes region
          setTag nuh region
          if nex0.th.args ≠ [] then fun _ => Option.none else
          if nex1.th.args ≠ [] then fun _ => Option.none else
          let lazy ← liftO (pastFork env.cod (mk Sure.bunt [((yes, nex0.laz), (nuh, nex1.laz))] []) p)
          let nexCond ← runLCK M env sup p (CGoalL.pick (jmp0 yes) (jmp0 nuh)) region
          if !(lazyBig (softLess noSoft lazy)) then copyK M nexCond lazy else do
            let o ← emit ⟨[], [], Termin.hop nexCond.th⟩
            let lazy ← lazyShut o lazy
            copyK M ⟨nexCond.laz, jmp0 o⟩ lazy
  | sup, Nomm.n7 p q, goal, region => do
      let nex ← runLCK M env (some p) q goal region
      runLCK M env sup p nex.goal region
  | sup, Nomm.n10 a v q, goal, region => do
      let next ← simpleNextL goal
      let (don, rec, o) ← intoL next a
      let nexR ← pastL env.cod ⟨rec, jmp0 o⟩ v region
      let nexDon ← runLCK M env sup v (CGoalL.next don nexR.th) region
      let nexDon ← pastL env.cod nexDon q region
      let nexRec ← runLCK M env sup q (CGoalL.next nexR.laz nexDon.th) region
      copyK M nexRec nexDon.laz
  | sup, Nomm.n2 p q info, goal, region =>
      callLK M env (runLCK M env sup p) (runLCK M env sup q) p q info sup goal region
  | _, _, _, _ => fun _ => Option.none

def runLCHK (M : Nat) [HoonMapKeys Map] (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (mono : Bool) : Option Nomm → Nomm → CGoalL S → List Nat → CM Map (NextL S)
  | sup, Nomm.cons p q, goal, region => do
      let goal ← (match goal with
        | CGoalL.done => do
            let r ← re
            let o ← emit ⟨[], [], Termin.don r⟩
            pure (CGoalL.next (ofSure (lazyReg r)) (jmp0 o))
        | g => pure g : CM Map (CGoalL S))
      match goal with
      | CGoalL.pick _ _ => do
          let o ← emit ⟨[], [], Termin.bom Option.none⟩
          let nex2 ← runLCHK M env snd mono sup q (CGoalL.next (ofSure Sure.bunt) (jmp0 o)) region
          let nex2 ← pastL env.cod nex2 p region
          let nex1 ← runLCHK M env snd mono sup p (CGoalL.next (ofSure Sure.bunt) nex2.th) region
          copyK M nex1 nex2.laz
      | CGoalL.next laz th => do
          let (hed, tel, o) ← splitL ⟨laz, th⟩
          let nexh ← pastL env.cod ⟨hed, jmp0 o⟩ q region
          let nex2 ← runLCHK M env snd mono sup q (CGoalL.next tel nexh.th) region
          let nex2 ← pastL env.cod nex2 p region
          let nex1 ← runLCHK M env snd mono sup p (CGoalL.next nexh.laz nex2.th) region
          copyK M nex1 nex2.laz
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
          if noneEquivalentL laz then runLCHK M env snd mono sup p (CGoalL.next laz th) region else do
            let a ← collapseLazyAtomL ⟨laz, th⟩
            match a with
            | Option.none => fun _ => Option.none
            | some (r, o) => do
                let (z, o') ← forl r o
                let r' ← re
                let oc ← emit ⟨[], [], Termin.clq r' (jmp0 z) (jmp0 o')⟩
                runLCHK M env snd mono sup p (CGoalL.next (ofSure (lazyReg r')) (jmp0 oc)) region
      | CGoalL.pick z o => do
          let r ← re
          let oc ← emit ⟨[], [], Termin.clq r z o⟩
          runLCHK M env snd mono sup p (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region
      | CGoalL.done => do
          let (o0, o1) ← doneBlocks
          let r ← re
          let oc ← emit ⟨[], [], Termin.clq r (jmp0 o0) (jmp0 o1)⟩
          runLCHK M env snd mono sup p (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region
  | sup, Nomm.n4 p, goal, region =>
      match goal with
      | CGoalL.done => do
          let pro ← re
          let arg ← re
          let o ← emit ⟨[], [Pole.inc arg pro], Termin.don pro⟩
          runLCHK M env snd mono sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region
      | CGoalL.pick z o => do
          let pro ← re
          let arg ← re
          let o' ← emit ⟨[], [Pole.inc arg pro], Termin.brn pro z o⟩
          runLCHK M env snd mono sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o')) region
      | CGoalL.next laz th => do
          let a ← collapseLazyAtomL ⟨laz, th⟩
          let (pro, th') ← (match a with
            | some x => pure x
            | Option.none => do
                let r ← re
                if th.args = [] then pure (r, th.there) else fun _ => Option.none : CM Map (Nat × Nat))
          let arg ← re
          let o ← emit ⟨[], [Pole.inc arg pro], Termin.hop (jmp0 th')⟩
          runLCHK M env snd mono sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region
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
                emit ⟨[], [], Termin.eqq rp rq (jmp0 z) (jmp0 o')⟩ : CM Map Nat)
      let nexq ← runLCHK M env snd mono sup q (CGoalL.next (ofSure (lazyReg rq)) (jmp0 o)) region
      let nexq ← pastL env.cod nexq p region
      let nexp ← runLCHK M env snd mono sup p (CGoalL.next (ofSure (lazyReg rp)) nexq.th) region
      copyK M nexp nexq.laz
  | sup, Nomm.n6 p q r, goal, region =>
      match goal with
      | CGoalL.next laz th => sixNextLCK M env.cod (runLCHK M env snd mono sup p) (runLCHK M env snd mono sup q) (runLCHK M env snd mono sup r) p q r 3 laz th region
      | _ => do
          let nex1 ← runLCHK M env snd mono sup r goal region
          let nex0 ← runLCHK M env snd mono sup q goal region
          let yes ← emit ⟨[], [], Termin.hop nex0.th⟩
          let nuh ← emit ⟨[], [], Termin.hop nex1.th⟩
          setTag yes region
          setTag nuh region
          if nex0.th.args ≠ [] then fun _ => Option.none else
          if nex1.th.args ≠ [] then fun _ => Option.none else
          let lazy ← liftO (pastFork env.cod (mk Sure.bunt [((yes, nex0.laz), (nuh, nex1.laz))] []) p)
          let nexCond ← runLCHK M env snd mono sup p (CGoalL.pick (jmp0 yes) (jmp0 nuh)) region
          if !(lazyBig (softLess noSoft lazy)) then copyK M nexCond lazy else do
            let o ← emit ⟨[], [], Termin.hop nexCond.th⟩
            let lazy ← lazyShut o lazy
            copyK M ⟨nexCond.laz, jmp0 o⟩ lazy
  | sup, Nomm.n7 p q, goal, region => do
      let nex ← runLCHK M env snd mono (some p) q goal region
      runLCHK M env snd mono sup p nex.goal region
  | sup, Nomm.n10 a v q, goal, region => do
      let next ← simpleNextL goal
      let (don, rec, o) ← intoL next a
      let nexR ← pastL env.cod ⟨rec, jmp0 o⟩ v region
      let nexDon ← runLCHK M env snd mono sup v (CGoalL.next don nexR.th) region
      let nexDon ← pastL env.cod nexDon q region
      let nexRec ← runLCHK M env snd mono sup q (CGoalL.next nexR.laz nexDon.th) region
      copyK M nexRec nexDon.laz
  | sup, Nomm.n2 p q info, goal, region =>
      callLMK M env mono (runLCHK M env snd mono sup p) (runLCHK M env snd mono sup q) p q info sup goal region
  | sup, Nomm.n11s tag q body, goal, region =>
      if !(hintStatic tag) then runLCHK M env snd mono sup q goal region else do
      let nex ← simpleNextL goal
      let nex ← pastIfL snd nex q region
      let epil ← emit ⟨[], [Pole.hse tag body], Termin.hop nex.th⟩
      let nexFol ← runLCHK M env snd mono sup q (CGoalL.next nex.laz (jmp0 epil)) region
      let nexFol ← lazyBound nexFol region
      let prol ← emit ⟨[], [Pole.hsp tag body], Termin.hop nexFol.th⟩
      pure ⟨nexFol.laz, jmp0 prol⟩
  | sup, Nomm.n11d tag h q body, goal, region =>
      if !(hintDynamic tag) then do
        let nexFol ← runLCHK M env snd mono sup q goal region
        if safeNomm h then pure nexFol else do
        let nexFol ← pastL env.cod nexFol h region
        let nexToke ← runLCHK M env snd mono sup h (CGoalL.next (ofSure Sure.bunt) nexFol.th) region
        copyK M nexToke nexFol.laz
      else do
      let nex ← simpleNextL goal
      let nex ← pastIfL snd nex q region
      let toke ← re
      let epil ← emit ⟨[], [Pole.hde tag toke body], Termin.hop nex.th⟩
      let nexFol1 ← runLCHK M env snd mono sup q (CGoalL.next nex.laz (jmp0 epil)) region
      let nexFol2 ← lazyBound nexFol1 region
      let prol ← emit ⟨[], [Pole.hdp tag toke body], Termin.hop nexFol2.th⟩
      let nexToke ← runLCHK M env snd mono sup h (CGoalL.next (ofSure (lazyReg toke)) (jmp0 prol)) region
      copyK M nexToke nexFol2.laz
  | sup, Nomm.mean p b q body k, goal, region =>
      match meanKonst env b k with
      | Option.none =>
          if mono then do
            let nex ← simpleNextL goal
            let nex ← pastIfL snd nex q region
            let toke ← re
            let epil ← emit ⟨[], [Pole.hde Tag.mean toke body], Termin.hop nex.th⟩
            let nexFol1 ← runLCHK M env snd mono sup q (CGoalL.next nex.laz (jmp0 epil)) region
            let nexFol2 ← lazyBound nexFol1 region
            let prol ← emit ⟨[], [Pole.hdp Tag.mean toke body], Termin.hop nexFol2.th⟩
            let nexToke ← runLCHK M env snd mono sup p (CGoalL.next (ofSure (lazyReg toke)) (jmp0 prol)) region
            copyK M nexToke nexFol2.laz
          else fun _ => Option.none
      | some n => do
          let subNed ← needOrdAllocRegs NeedOrd.none
          let nex ← simpleNextL goal
          let nex ← pastIfL snd nex q region
          let epil ← emit ⟨[], [Pole.hce n body], Termin.hop nex.th⟩
          let nexFol1 ← runLCHK M env snd mono sup q (CGoalL.next nex.laz (jmp0 epil)) region
          let nexFol2 ← lazyBound nexFol1 region
          let prol ← emit ⟨[], [Pole.hcp n body], Termin.hop nexFol2.th⟩
          if !(snd p NeedOrd.none) then fun _ => Option.none else do
          let nexTrap ← runLCHK M env snd mono sup p (CGoalL.next (ofSure ⟨subNed, HoonSet.empty⟩) (jmp0 prol)) region
          copyK M nexTrap nexFol2.laz
  | sup, Nomm.n12 p q, goal, region => do
      let nex ← simpleNextL goal
      let (out, pro) ← kerf nex
      let rPath ← re
      let rRef ← re
      let oSpy ← emit ⟨[], [Pole.spy rRef rPath pro], Termin.hop (jmp0 out)⟩
      let nexPath ← runLCHK M env snd mono sup q (CGoalL.next (ofSure (lazyReg rPath)) (jmp0 oSpy)) region
      let nexPath ← pastL env.cod nexPath p region
      let nexRef ← runLCHK M env snd mono sup p (CGoalL.next (ofSure (lazyReg rRef)) nexPath.th) region
      copyK M nexRef nexPath.laz
-- END copyk.py

open SixCheck GenCheck

abbrev RunnerK := Nat → Nomm → CGoalL LS → Gen FM → Option (NextL LS × Gen FM)

def runPK : RunnerK := fun M nm g g0 => runLCK (S := LS) (Map := FM) M envR Option.none nm g [] g0
def runHK : RunnerK := fun M nm g g0 => runLCHK (S := LS) (Map := FM) M envH sndH true Option.none nm g [] g0

def modes : List Nat := [1, 2, 3, 4, 5, 6, 7]

/-- `(runs, base fails, M=0 differs, per mode: runs where the base succeeds and
the checked run fails)`. -/
def tallyK (base : Runner) (run : RunnerK) (nms : List Nomm) (gs : List GenCheck.Goal) : Nat × Nat × Nat × List (Nat × Nat) :=
  let ps : List (Nomm × GenCheck.Goal) := nms.flatMap fun nm => gs.map fun g => (nm, g)
  let rs := ps.map fun (nm, L, th, g) =>
    let b := (base nm (CGoalL.next L th) g).isSome
    (b, (run 0 nm (CGoalL.next L th) g).isSome != b,
      modes.map fun M => b && !(run M nm (CGoalL.next L th) g).isSome)
  (rs.length, (rs.filter (!·.1)).length, (rs.filter (·.2.1)).length,
    modes.zipIdx.map fun (M, i) => (M, (rs.filter fun r => r.2.2.getD i false).length))

def witK (run : RunnerK) (M : Nat) (nms : List Nomm) (gs : List GenCheck.Goal) : Option (Noun × List Nat × Jmp) :=
  ((nms.flatMap fun nm => gs.map fun g => (nm, g) : List (Nomm × GenCheck.Goal))).findSome? fun (nm, L, th, g) =>
    if (run 0 nm (CGoalL.next L th) g).isSome && !(run M nm (CGoalL.next L th) g).isSome then
      some (nm.toNoun, labels L, th) else Option.none

#guard tallyK runH runHK HintNest.shapes (flatGoals LSXCheck.jumps statesH) ==
  (2640, 0, 0, [(1, 0), (2, 0), (3, 0), (4, 2400), (5, 0), (6, 0), (7, 0)])
#guard tallyK GenCheck.runP runPK gensP (flatGoals LSXCheck.jumps statesH) ==
  (1200, 0, 0, [(1, 0), (2, 0), (3, 0), (4, 1200), (5, 0), (6, 0), (7, 0)])

/-! The checks bite on `gD` (`second` with two bonds at label `1`): the copy
succeeds unchecked, and fails under `LabUniq`, the missing register (`5`),
the read one, and `mergeRisk`. -/
#guard [0, 1, 2, 3, 6, 7].map (fun M => (copyK (S := LS) (Map := FM) M Raw.firstD Raw.secondD Raw.gD).isSome) ==
  [true, false, false, false, true, false]

-- The larger families (scratch, `lake env lean`; results in the table above):
-- #eval tallyK GenCheck.runP runPK sixes (flatGoals LSXCheck.jumps statesH)
-- #eval tallyK GenCheck.runP runPK all6 (flatGoals [jmp0 1] [genAtH 4 4])
-- #eval tallyK GenCheck.runP runPK (sixes ++ brs) goalsP
-- #eval tallyK runH runHK (HintNest.shapes ++ sixesT) goalsH

end KChk
end Comp
end SkaModel
end Formalization
