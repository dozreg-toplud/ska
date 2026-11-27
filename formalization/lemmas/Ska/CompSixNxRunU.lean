import lemmas.Ska.CompWhole
import lemmas.Ska.CompRunLC

/-!
# `runLC` with every `%6` under `%next` unwrapped (generated)

Written by `tools/gen/sixnxu.py` from the text of `runLC`
(`CompRunLC.lean`); do not edit by hand.  README Gaps 12.36: the semantic
check of `RunOKLT` (`CompSixNxCheck.lean`) runs the whole-subject code made
when every parent reads the UNWRAPPED need of a `%6` under `%next`.

* `unside`, `unwrapL`: a fork side `[bunt ~ [o a]~]` at label `o` is `a`.
* `runLCU`, `finishLUCU`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- A side of a fork, unwrapped when it is the wrapper of `+past-fork`. -/
def unside : Nat × Lazy S → Nat × Lazy S
  | (o, Lazy.mk s [] [(o', a)]) =>
    if decide (s.ned = Need.none) && HoonSet.isEmpty s.lok && decide (o' = o) then (o, a)
    else (o, Lazy.mk s [] [(o', a)])
  | e => e

/-- Every fork side unwrapped. -/
def unwrapL : Lazy S → Lazy S
  | Lazy.mk s f b => Lazy.mk s (f.map fun e => (unside e.1, unside e.2)) b

def runLCU [HoonMapKeys Map] (env : CallEnv) : Option Nomm → Nomm → CGoalL S → List Nat → CM Map (NextL S)
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
          let nex2 ← runLCU env sup q (CGoalL.next (ofSure Sure.bunt) (jmp0 o)) region
          let nex2 ← pastL env.cod nex2 p region
          let nex1 ← runLCU env sup p (CGoalL.next (ofSure Sure.bunt) nex2.th) region
          copyL nex1 nex2.laz
      | CGoalL.next laz th => do
          let (hed, tel, o) ← splitL ⟨laz, th⟩
          let nexh ← pastL env.cod ⟨hed, jmp0 o⟩ q region
          let nex2 ← runLCU env sup q (CGoalL.next tel nexh.th) region
          let nex2 ← pastL env.cod nex2 p region
          let nex1 ← runLCU env sup p (CGoalL.next nexh.laz nex2.th) region
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
          if noneEquivalentL laz then runLCU env sup p (CGoalL.next laz th) region else do
            let a ← collapseLazyAtomL ⟨laz, th⟩
            match a with
            | Option.none => fun _ => Option.none
            | some (r, o) => do
                let (z, o') ← forl r o
                let r' ← re
                let oc ← emit ⟨[], [], Termin.clq r' (jmp0 z) (jmp0 o')⟩
                runLCU env sup p (CGoalL.next (ofSure (lazyReg r')) (jmp0 oc)) region
      | CGoalL.pick z o => do
          let r ← re
          let oc ← emit ⟨[], [], Termin.clq r z o⟩
          runLCU env sup p (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region
      | CGoalL.done => do
          let (o0, o1) ← doneBlocks
          let r ← re
          let oc ← emit ⟨[], [], Termin.clq r (jmp0 o0) (jmp0 o1)⟩
          runLCU env sup p (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region
  | sup, Nomm.n4 p, goal, region =>
      match goal with
      | CGoalL.done => do
          let pro ← re
          let arg ← re
          let o ← emit ⟨[], [Pole.inc arg pro], Termin.don pro⟩
          runLCU env sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region
      | CGoalL.pick z o => do
          let pro ← re
          let arg ← re
          let o' ← emit ⟨[], [Pole.inc arg pro], Termin.brn pro z o⟩
          runLCU env sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o')) region
      | CGoalL.next laz th => do
          let a ← collapseLazyAtomL ⟨laz, th⟩
          let (pro, th') ← (match a with
            | some x => pure x
            | Option.none => do
                let r ← re
                if th.args = [] then pure (r, th.there) else fun _ => Option.none : CM Map (Nat × Nat))
          let arg ← re
          let o ← emit ⟨[], [Pole.inc arg pro], Termin.hop (jmp0 th')⟩
          runLCU env sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region
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
      let nexq ← runLCU env sup q (CGoalL.next (ofSure (lazyReg rq)) (jmp0 o)) region
      let nexq ← pastL env.cod nexq p region
      let nexp ← runLCU env sup p (CGoalL.next (ofSure (lazyReg rp)) nexq.th) region
      copyL nexp nexq.laz
  | sup, Nomm.n6 p q r, goal, region =>
      match goal with
      | CGoalL.next laz th => do
          let nex ← sixNextLC env.cod (runLCU env sup p) (runLCU env sup q) (runLCU env sup r) p q r 3 laz th region
          pure ⟨unwrapL nex.laz, nex.th⟩
      | _ => do
          let nex1 ← runLCU env sup r goal region
          let nex0 ← runLCU env sup q goal region
          let yes ← emit ⟨[], [], Termin.hop nex0.th⟩
          let nuh ← emit ⟨[], [], Termin.hop nex1.th⟩
          setTag yes region
          setTag nuh region
          if nex0.th.args ≠ [] then fun _ => Option.none else
          if nex1.th.args ≠ [] then fun _ => Option.none else
          let lazy ← liftO (pastFork env.cod (mk Sure.bunt [((yes, nex0.laz), (nuh, nex1.laz))] []) p)
          let nexCond ← runLCU env sup p (CGoalL.pick (jmp0 yes) (jmp0 nuh)) region
          if !(lazyBig (softLess noSoft lazy)) then copyL nexCond lazy else do
            let o ← emit ⟨[], [], Termin.hop nexCond.th⟩
            let lazy ← lazyShut o lazy
            copyL ⟨nexCond.laz, jmp0 o⟩ lazy
  | sup, Nomm.n7 p q, goal, region => do
      let nex ← runLCU env (some p) q goal region
      runLCU env sup p nex.goal region
  | sup, Nomm.n10 a v q, goal, region => do
      let next ← simpleNextL goal
      let (don, rec, o) ← intoL next a
      let nexR ← pastL env.cod ⟨rec, jmp0 o⟩ v region
      let nexDon ← runLCU env sup v (CGoalL.next don nexR.th) region
      let nexDon ← pastL env.cod nexDon q region
      let nexRec ← runLCU env sup q (CGoalL.next nexR.laz nexDon.th) region
      copyL nexRec nexDon.laz
  | sup, Nomm.n2 p q info, goal, region =>
      callL env (runLCU env sup p) (runLCU env sup q) p q info sup goal region
  | _, _, _, _ => fun _ => Option.none

/-- `finishLUC` with `runLCU`. -/
def finishLUCU [HoonMapKeys Map] (env : CallEnv) (nm : Nomm) : Option (Straight Map) :=
  (runLCU env Option.none nm (CGoalL.done : CGoalL S) [] gen0).bind fun (nex, g1) =>
    (kerf nex g1).bind fun ((o, sub), g2) =>
      toStraightF g2.cond g2.blocks (Need.this sub) o

end Comp
end SkaModel
end Formalization
