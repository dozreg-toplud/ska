import lemmas.Ska.CompHintArms

/-!
# `run` with hints: `runLCH` (generated)

Written by `tools/gen/runlch.py` from the text of `runLCM`
(`CompRunLCM.lean`); do not edit by hand.  README Gaps 24.

* `runLCH env snd mono sup`: `runLCM env mono sup` with `snd` (`+sound`,
  read by `+past-if` and by the case `%mean`) passed to every recursive run,
  and the cases of `+run` for hints (lines 4269 to 4360), which `runLCM`
  answers with `none`:
  * `n11s`: a tag that is not `hint-static` is `q` alone; a static one gets
    `+simple-next`, `+past-if`, the epilogue `%hse`, `q`, `+lazy-bound`, the
    prologue `%hsp`;
  * `n11d`: a tag that is not `hint-dynamic` is `q`, then (unless
    `+safe-nomm` of the clue) `+past` and the clue run with no need, `+copy`;
    a dynamic one is the static case with a register `toke`, `%hde`, `%hdp`,
    and the clue run last into `toke`;
  * `mean`: with `mono` and no constant (`+mean-konst`) the dynamic case for
    `%mean`; with a constant the same with `%hce`/`%hcp` and the trap run
    with no need; with `mono` `|` and no constant `none` (not modelled: the
    deferred `%mean` with the soft calls of `+soft-new`/`+soft-bond`);
  * `n12`: `+simple-next`, `+kerf`, the block of `%spy`, the path then the
    reference.

On nomms without hints it is `runLCM` (`runLCH_eq`, `CompHintEq.lean`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

def runLCH [HoonMapKeys Map] (env : CallEnv) (snd : Nomm → NeedOrd → Bool) (mono : Bool) : Option Nomm → Nomm → CGoalL S → List Nat → CM Map (NextL S)
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
          let nex2 ← runLCH env snd mono sup q (CGoalL.next (ofSure Sure.bunt) (jmp0 o)) region
          let nex2 ← pastL env.cod nex2 p region
          let nex1 ← runLCH env snd mono sup p (CGoalL.next (ofSure Sure.bunt) nex2.th) region
          copyL nex1 nex2.laz
      | CGoalL.next laz th => do
          let (hed, tel, o) ← splitL ⟨laz, th⟩
          let nexh ← pastL env.cod ⟨hed, jmp0 o⟩ q region
          let nex2 ← runLCH env snd mono sup q (CGoalL.next tel nexh.th) region
          let nex2 ← pastL env.cod nex2 p region
          let nex1 ← runLCH env snd mono sup p (CGoalL.next nexh.laz nex2.th) region
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
          if noneEquivalentL laz then runLCH env snd mono sup p (CGoalL.next laz th) region else do
            let a ← collapseLazyAtomL ⟨laz, th⟩
            match a with
            | Option.none => fun _ => Option.none
            | some (r, o) => do
                let (z, o') ← forl r o
                let r' ← re
                let oc ← emit ⟨[], [], Termin.clq r' (jmp0 z) (jmp0 o')⟩
                runLCH env snd mono sup p (CGoalL.next (ofSure (lazyReg r')) (jmp0 oc)) region
      | CGoalL.pick z o => do
          let r ← re
          let oc ← emit ⟨[], [], Termin.clq r z o⟩
          runLCH env snd mono sup p (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region
      | CGoalL.done => do
          let (o0, o1) ← doneBlocks
          let r ← re
          let oc ← emit ⟨[], [], Termin.clq r (jmp0 o0) (jmp0 o1)⟩
          runLCH env snd mono sup p (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region
  | sup, Nomm.n4 p, goal, region =>
      match goal with
      | CGoalL.done => do
          let pro ← re
          let arg ← re
          let o ← emit ⟨[], [Pole.inc arg pro], Termin.don pro⟩
          runLCH env snd mono sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region
      | CGoalL.pick z o => do
          let pro ← re
          let arg ← re
          let o' ← emit ⟨[], [Pole.inc arg pro], Termin.brn pro z o⟩
          runLCH env snd mono sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o')) region
      | CGoalL.next laz th => do
          let a ← collapseLazyAtomL ⟨laz, th⟩
          let (pro, th') ← (match a with
            | some x => pure x
            | Option.none => do
                let r ← re
                if th.args = [] then pure (r, th.there) else fun _ => Option.none : CM Map (Nat × Nat))
          let arg ← re
          let o ← emit ⟨[], [Pole.inc arg pro], Termin.hop (jmp0 th')⟩
          runLCH env snd mono sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region
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
      let nexq ← runLCH env snd mono sup q (CGoalL.next (ofSure (lazyReg rq)) (jmp0 o)) region
      let nexq ← pastL env.cod nexq p region
      let nexp ← runLCH env snd mono sup p (CGoalL.next (ofSure (lazyReg rp)) nexq.th) region
      copyL nexp nexq.laz
  | sup, Nomm.n6 p q r, goal, region =>
      match goal with
      | CGoalL.next laz th => sixNextLC env.cod (runLCH env snd mono sup p) (runLCH env snd mono sup q) (runLCH env snd mono sup r) p q r 3 laz th region
      | _ => do
          let nex1 ← runLCH env snd mono sup r goal region
          let nex0 ← runLCH env snd mono sup q goal region
          let yes ← emit ⟨[], [], Termin.hop nex0.th⟩
          let nuh ← emit ⟨[], [], Termin.hop nex1.th⟩
          setTag yes region
          setTag nuh region
          if nex0.th.args ≠ [] then fun _ => Option.none else
          if nex1.th.args ≠ [] then fun _ => Option.none else
          let lazy ← liftO (pastFork env.cod (mk Sure.bunt [((yes, nex0.laz), (nuh, nex1.laz))] []) p)
          let nexCond ← runLCH env snd mono sup p (CGoalL.pick (jmp0 yes) (jmp0 nuh)) region
          if !(lazyBig (softLess noSoft lazy)) then copyL nexCond lazy else do
            let o ← emit ⟨[], [], Termin.hop nexCond.th⟩
            let lazy ← lazyShut o lazy
            copyL ⟨nexCond.laz, jmp0 o⟩ lazy
  | sup, Nomm.n7 p q, goal, region => do
      let nex ← runLCH env snd mono (some p) q goal region
      runLCH env snd mono sup p nex.goal region
  | sup, Nomm.n10 a v q, goal, region => do
      let next ← simpleNextL goal
      let (don, rec, o) ← intoL next a
      let nexR ← pastL env.cod ⟨rec, jmp0 o⟩ v region
      let nexDon ← runLCH env snd mono sup v (CGoalL.next don nexR.th) region
      let nexDon ← pastL env.cod nexDon q region
      let nexRec ← runLCH env snd mono sup q (CGoalL.next nexR.laz nexDon.th) region
      copyL nexRec nexDon.laz
  | sup, Nomm.n2 p q info, goal, region =>
      callLM env mono (runLCH env snd mono sup p) (runLCH env snd mono sup q) p q info sup goal region
  | sup, Nomm.n11s tag q body, goal, region =>
      if !(hintStatic tag) then runLCH env snd mono sup q goal region else do
      let nex ← simpleNextL goal
      let nex ← pastIfL snd nex q region
      let epil ← emit ⟨[], [Pole.hse tag body], Termin.hop nex.th⟩
      let nexFol ← runLCH env snd mono sup q (CGoalL.next nex.laz (jmp0 epil)) region
      let nexFol ← lazyBound nexFol region
      let prol ← emit ⟨[], [Pole.hsp tag body], Termin.hop nexFol.th⟩
      pure ⟨nexFol.laz, jmp0 prol⟩
  | sup, Nomm.n11d tag h q body, goal, region =>
      if !(hintDynamic tag) then do
        let nexFol ← runLCH env snd mono sup q goal region
        if safeNomm h then pure nexFol else do
        let nexFol ← pastL env.cod nexFol h region
        let nexToke ← runLCH env snd mono sup h (CGoalL.next (ofSure Sure.bunt) nexFol.th) region
        copyL nexToke nexFol.laz
      else do
      let nex ← simpleNextL goal
      let nex ← pastIfL snd nex q region
      let toke ← re
      let epil ← emit ⟨[], [Pole.hde tag toke body], Termin.hop nex.th⟩
      let nexFol1 ← runLCH env snd mono sup q (CGoalL.next nex.laz (jmp0 epil)) region
      let nexFol2 ← lazyBound nexFol1 region
      let prol ← emit ⟨[], [Pole.hdp tag toke body], Termin.hop nexFol2.th⟩
      let nexToke ← runLCH env snd mono sup h (CGoalL.next (ofSure (lazyReg toke)) (jmp0 prol)) region
      copyL nexToke nexFol2.laz
  | sup, Nomm.mean p b q body k, goal, region =>
      match meanKonst env b k with
      | Option.none =>
          if mono then do
            let nex ← simpleNextL goal
            let nex ← pastIfL snd nex q region
            let toke ← re
            let epil ← emit ⟨[], [Pole.hde Tag.mean toke body], Termin.hop nex.th⟩
            let nexFol1 ← runLCH env snd mono sup q (CGoalL.next nex.laz (jmp0 epil)) region
            let nexFol2 ← lazyBound nexFol1 region
            let prol ← emit ⟨[], [Pole.hdp Tag.mean toke body], Termin.hop nexFol2.th⟩
            let nexToke ← runLCH env snd mono sup p (CGoalL.next (ofSure (lazyReg toke)) (jmp0 prol)) region
            copyL nexToke nexFol2.laz
          else fun _ => Option.none
      | some n => do
          let subNed ← needOrdAllocRegs NeedOrd.none
          let nex ← simpleNextL goal
          let nex ← pastIfL snd nex q region
          let epil ← emit ⟨[], [Pole.hce n body], Termin.hop nex.th⟩
          let nexFol1 ← runLCH env snd mono sup q (CGoalL.next nex.laz (jmp0 epil)) region
          let nexFol2 ← lazyBound nexFol1 region
          let prol ← emit ⟨[], [Pole.hcp n body], Termin.hop nexFol2.th⟩
          if !(snd p NeedOrd.none) then fun _ => Option.none else do
          let nexTrap ← runLCH env snd mono sup p (CGoalL.next (ofSure ⟨subNed, HoonSet.empty⟩) (jmp0 prol)) region
          copyL nexTrap nexFol2.laz
  | sup, Nomm.n12 p q, goal, region => do
      let nex ← simpleNextL goal
      let (out, pro) ← kerf nex
      let rPath ← re
      let rRef ← re
      let oSpy ← emit ⟨[], [Pole.spy rRef rPath pro], Termin.hop (jmp0 out)⟩
      let nexPath ← runLCH env snd mono sup q (CGoalL.next (ofSure (lazyReg rPath)) (jmp0 oSpy)) region
      let nexPath ← pastL env.cod nexPath p region
      let nexRef ← runLCH env snd mono sup p (CGoalL.next (ofSure (lazyReg rRef)) nexPath.th) region
      copyL nexRef nexPath.laz

end Comp
end SkaModel
end Formalization
