import lemmas.Ska.CompCall

/-!
# `run` with calls: `runLC` (generated)

Written by `tools/gen/runlc.py` from the text of `runL`, `sixNextFork`,
`sixNextSimple` and `sixNextL` of `CompLazyRun.lean`; do not edit by hand.

* `sixNextForkC`, `sixNextSimpleC`, `sixNextLC`: the arms of `%6` for a goal
  `%next` with the code table `cod` that `+hinted` reads (the originals
  pass `noCode`, which answers no callee).
* `runLC env sup`: `runL` with the case `%2` as `callL` (README Gaps 12.9),
  the code table `env.cod` for `+past` and `+past-fork`, and the parameter
  `sup` of `+run`: `some p` when `q` of `[7 p q]` is compiled, inherited
  everywhere else (the Hoon's `$(nomm q.nomm, sup `p.nomm)` and
  `$(nomm ..., goal ...)`, which keeps the sample's `sup`).

On nomms without `%2` it is `runL` (`runLC_eq`, `CompRunLCEq.lean`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

def sixNextForkC [HoonMapKeys Map] (cod : Bell → Option Bool) (rp rq rr : CGoalL S → List Nat → CM Map (NextL S)) (p : Nomm)
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
  copyL nexCond lazy

def sixNextSimpleC [HoonMapKeys Map] (cod : Bell → Option Bool) (rp rq rr : CGoalL S → List Nat → CM Map (NextL S)) (p : Nomm)
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
  if !(lazyBig (softLess noSoft lazy)) then copyL nexCond lazy else do
    let o ← emit ⟨[], [], Termin.hop nexCond.th⟩
    let lazy ← lazyShut o lazy
    copyL ⟨nexCond.laz, jmp0 o⟩ lazy

def sixNextLC [HoonMapKeys Map] (cod : Bell → Option Bool) (rp rq rr : CGoalL S → List Nat → CM Map (NextL S)) (p q r : Nomm) :
    Nat → Lazy S → Jmp → List Nat → CM Map (NextL S)
  | 0, _, _, _ => fun _ => Option.none
  | fuel + 1, laz, th, region =>
    match leap laz q r with
    | Option.none => fun _ => Option.none
    | some (some (rest, bys)) => do
      let nex ← sixNextLC cod rp rq rr p q r fuel rest th region
      copyAll nex bys
    | some Option.none =>
      if !(noneEquivalentL (mk Sure.bunt laz.fork laz.bond)) then
        if (whole q && whole r) || thisOnly laz || lazyBig (softLess noSoft laz) ||
            softFork noSoft (fun _ => false) laz then do
          let (out, pro) ← kerf ⟨laz, th⟩
          sixNextLC cod rp rq rr p q r fuel (ofSure ⟨Need.this pro, HoonSet.empty⟩) (jmp0 out) region
        else sixNextForkC cod rp rq rr p laz th region
      else sixNextSimpleC cod rp rq rr p laz th region

def runLC [HoonMapKeys Map] (env : CallEnv) : Option Nomm → Nomm → CGoalL S → List Nat → CM Map (NextL S)
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
          let nex2 ← runLC env sup q (CGoalL.next (ofSure Sure.bunt) (jmp0 o)) region
          let nex2 ← pastL env.cod nex2 p region
          let nex1 ← runLC env sup p (CGoalL.next (ofSure Sure.bunt) nex2.th) region
          copyL nex1 nex2.laz
      | CGoalL.next laz th => do
          let (hed, tel, o) ← splitL ⟨laz, th⟩
          let nexh ← pastL env.cod ⟨hed, jmp0 o⟩ q region
          let nex2 ← runLC env sup q (CGoalL.next tel nexh.th) region
          let nex2 ← pastL env.cod nex2 p region
          let nex1 ← runLC env sup p (CGoalL.next nexh.laz nex2.th) region
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
          if noneEquivalentL laz then runLC env sup p (CGoalL.next laz th) region else do
            let a ← collapseLazyAtomL ⟨laz, th⟩
            match a with
            | Option.none => fun _ => Option.none
            | some (r, o) => do
                let (z, o') ← forl r o
                let r' ← re
                let oc ← emit ⟨[], [], Termin.clq r' (jmp0 z) (jmp0 o')⟩
                runLC env sup p (CGoalL.next (ofSure (lazyReg r')) (jmp0 oc)) region
      | CGoalL.pick z o => do
          let r ← re
          let oc ← emit ⟨[], [], Termin.clq r z o⟩
          runLC env sup p (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region
      | CGoalL.done => do
          let (o0, o1) ← doneBlocks
          let r ← re
          let oc ← emit ⟨[], [], Termin.clq r (jmp0 o0) (jmp0 o1)⟩
          runLC env sup p (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region
  | sup, Nomm.n4 p, goal, region =>
      match goal with
      | CGoalL.done => do
          let pro ← re
          let arg ← re
          let o ← emit ⟨[], [Pole.inc arg pro], Termin.don pro⟩
          runLC env sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region
      | CGoalL.pick z o => do
          let pro ← re
          let arg ← re
          let o' ← emit ⟨[], [Pole.inc arg pro], Termin.brn pro z o⟩
          runLC env sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o')) region
      | CGoalL.next laz th => do
          let a ← collapseLazyAtomL ⟨laz, th⟩
          let (pro, th') ← (match a with
            | some x => pure x
            | Option.none => do
                let r ← re
                if th.args = [] then pure (r, th.there) else fun _ => Option.none : CM Map (Nat × Nat))
          let arg ← re
          let o ← emit ⟨[], [Pole.inc arg pro], Termin.hop (jmp0 th')⟩
          runLC env sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region
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
      let nexq ← runLC env sup q (CGoalL.next (ofSure (lazyReg rq)) (jmp0 o)) region
      let nexq ← pastL env.cod nexq p region
      let nexp ← runLC env sup p (CGoalL.next (ofSure (lazyReg rp)) nexq.th) region
      copyL nexp nexq.laz
  | sup, Nomm.n6 p q r, goal, region =>
      match goal with
      | CGoalL.next laz th => sixNextLC env.cod (runLC env sup p) (runLC env sup q) (runLC env sup r) p q r 3 laz th region
      | _ => do
          let nex1 ← runLC env sup r goal region
          let nex0 ← runLC env sup q goal region
          let yes ← emit ⟨[], [], Termin.hop nex0.th⟩
          let nuh ← emit ⟨[], [], Termin.hop nex1.th⟩
          setTag yes region
          setTag nuh region
          if nex0.th.args ≠ [] then fun _ => Option.none else
          if nex1.th.args ≠ [] then fun _ => Option.none else
          let lazy ← liftO (pastFork env.cod (mk Sure.bunt [((yes, nex0.laz), (nuh, nex1.laz))] []) p)
          let nexCond ← runLC env sup p (CGoalL.pick (jmp0 yes) (jmp0 nuh)) region
          if !(lazyBig (softLess noSoft lazy)) then copyL nexCond lazy else do
            let o ← emit ⟨[], [], Termin.hop nexCond.th⟩
            let lazy ← lazyShut o lazy
            copyL ⟨nexCond.laz, jmp0 o⟩ lazy
  | sup, Nomm.n7 p q, goal, region => do
      let nex ← runLC env (some p) q goal region
      runLC env sup p nex.goal region
  | sup, Nomm.n10 a v q, goal, region => do
      let next ← simpleNextL goal
      let (don, rec, o) ← intoL next a
      let nexR ← pastL env.cod ⟨rec, jmp0 o⟩ v region
      let nexDon ← runLC env sup v (CGoalL.next don nexR.th) region
      let nexDon ← pastL env.cod nexDon q region
      let nexRec ← runLC env sup q (CGoalL.next nexR.laz nexDon.th) region
      copyL nexRec nexDon.laz
  | sup, Nomm.n2 p q info, goal, region =>
      callL env (runLC env sup p) (runLC env sup q) p q info sup goal region
  | _, _, _, _ => fun _ => Option.none

end Comp
end SkaModel
end Formalization
