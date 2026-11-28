import lemmas.Ska.SccLoopSoft

/-! # `runLCS2`: `runLCS` with `+crash-need` asking at a soft block (README Gaps 21.20)

`+crash-need` (`desk/lib/nock-compilation.hoon` line 5948) is called by `+mede` (`%1` on
`%next`, lines 5881 and 5886: an immediate atom where a cell is needed) and by
`+collapse-lazy-atom` (`%3`, `%4`, `%5` on `%next`, line 5941: the register of the atom).  At a
soft block (`(~(has by soft.gen) o)`) it does not emit `%cel` and the fill but asks `+soft-ask`:
`[src ned]` in front of `req` (for an immediate, after `[%imm n r]` into a new register `r`).
The models `medeL` / `collapseLazyAtomL` of `runLCS` (`crashNeed`) never ask: they emit the
crash in the soft block.  On the real compiler 7 of the 8 extra cases of `sccreal.py --extra`
record such a `req` in the `%done` run (`SccLoopSoft2Check.lean`); `runLCS` leaves it empty.

Every other read of `soft.gen` in `+run` against `runLCS` (unchanged here):
* `+kern` line 5090 `(~(has by soft.gen) o-laz)` → `soft-ask`: `kernS`, same;
* `+soft-ask` line 5233 (`?:  dropping  gen`, `+jab:by`): `softAsk`, same;
* `+soft-fork` line 5244 (bonds at soft blocks, `!&((sound q ned) (sound r ned))`): `softFork`, same;
* `+soft-less` line 5281 (`murn` dropping the bonds at soft blocks): `softLess`, same;
* the call, line 4052 `(~(has by soft.gen) call-block)` → `+soft-bond`: `callLS`, same;
* `+coerce-lazy` line 6836 (in `finish`, not `+run`): `sureLoopS`, same. -/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- **`+crash-need`** (line 5948) reading `soft.gen`: at a soft block `+soft-ask` (for an
immediate after `[%imm n r]` into a new `r`), elsewhere `crashNeed`. -/
def crashNeedS (o : Nat) (atom : Sum Nat Nat) (ned : Need) : CMS Map Unit :=
  match atom with
  | Sum.inr p => withSoft fun sf => if sf o then softAsk o p ned else liftS (crashNeed o (Sum.inr p) ned)
  | Sum.inl n => do
      let r ← liftS re
      withSoft fun sf => if sf o then do liftS (addOps o [Pole.imm (A n) r]); softAsk o r ned
        else liftS (addOps o (Pole.imm (A n) r :: Pole.cel r :: (flattenNeed ned).map fun x => Pole.imm (A 0) x))

/-- The loop of `+mede` (line 5875) with `crashNeedS`. -/
def medeLoopS (o : Nat) : Noun → Need → CMS Map Unit
  | _, Need.none => pure ()
  | som, Need.this r => liftS (addOps o [Pole.imm som r])
  | Noun.atom n, Need.pair p q => crashNeedS o (Sum.inl n) (Need.pair p q)
  | Noun.cell a b, Need.pair p q => do medeLoopS o a p; medeLoopS o b q
  | Noun.atom n, Need.both r h t => crashNeedS o (Sum.inl n) (Need.both r h t)
  | Noun.cell a b, Need.both r h t => do
      liftS (addOps o [Pole.imm (C a b) r])
      medeLoopS o a h
      medeLoopS o b t

/-- **`+mede`** (line 5863) reading `soft.gen`. -/
def medeLS (th : Jmp) (som : Noun) (laz : Lazy S) : CMS Map Nat := do
  let o ← liftS (emit ⟨[], [], Termin.hop th⟩)
  let s ← get
  if s.g.drop then pure o else do
    walkLazyS (fun o sur => do
      let ned ← liftS (sureRequireLook sur)
      medeLoopS o som ned) o laz
    pure o

/-- The gate of `+collapse-lazy-atom` (line 5930) with `crashNeedS`. -/
def collapseGateS (r o : Nat) (oLaz : Nat) (sur : Sure S) : CMS Map Unit := do
  let ned ← liftS (sureRequireLook sur)
  match ned with
  | Need.none => pure ()
  | Need.this r' =>
    if r = r' then pure () else liftS (do
      let src ← (if oLaz = o then pure r else proxy r oLaz : CM Map Nat)
      addOps oLaz [Pole.mov src r'])
  | _ => do
    let src ← liftS (if oLaz = o then pure r else proxy r oLaz : CM Map Nat)
    crashNeedS oLaz (Sum.inr src) ned

/-- The register and block of `+collapse-lazy-atom` (lines 5901 to 5922). -/
def collapseHead (nedSure : Need) (there : Nat) : CM Map (Nat × Nat) :=
  match nedSure with
  | Need.this r => pure (r, there)
  | Need.none => do let r ← re; pure (r, there)
  | Need.pair _ _ => do
      let r ← re
      let o ← emit ⟨[], [], Termin.bom Option.none⟩
      pure (r, o)
  | Need.both r _ _ => do
      let o ← emit ⟨[], [], Termin.bom Option.none⟩
      pure (r, o)

/-- **`+collapse-lazy-atom`** (line 5895) reading `soft.gen`. -/
def collapseLazyAtomLS (nex : NextL S) : CMS Map (Option (Nat × Nat)) := do
  if nex.th.args ≠ [] then fun _ => Option.none else
  if noneEquivalentL nex.laz then pure Option.none else do
  let nedSure ← liftS (sureRequireLook nex.laz.sure)
  let (r, there) ← liftS (collapseHead nedSure nex.th.there)
  let s ← get
  if s.g.drop then pure (some (r, there)) else do
    walkLazyS (collapseGateS r there) there (mk ⟨Need.this r, nex.laz.sure.lok⟩ nex.laz.fork nex.laz.bond)
    pure (some (r, there))

/-- **`+run` at `mono` `|` with soft calls, `+crash-need` asking** (README Gaps 21.20): `runLCS`
with `medeLS` in `%1` on `%next` and `collapseLazyAtomLS` in `%3`, `%4`, `%5`. -/
def runLCS2 [HoonMapKeys Map] (env : CallEnv) (snd : Nomm → NeedOrd → Bool) :
    Option Nomm → Nomm → CGoalL S → List Nat → CMS Map (NextL S)
  | sup, Nomm.cons p q, goal, region => do
      let goal ← (match goal with
        | CGoalL.done => do
            let r ← liftS re
            let o ← liftS (emit ⟨[], [], Termin.don r⟩)
            pure (CGoalL.next (ofSure (lazyReg r)) (jmp0 o))
        | g => pure g : CMS Map (CGoalL S))
      match goal with
      | CGoalL.pick _ _ => do
          let o ← liftS (emit ⟨[], [], Termin.bom Option.none⟩)
          let nex2 ← runLCS2 env snd sup q (CGoalL.next (ofSure Sure.bunt) (jmp0 o)) region
          let nex2 ← liftS (pastL env.cod nex2 p region)
          let nex1 ← runLCS2 env snd sup p (CGoalL.next (ofSure Sure.bunt) nex2.th) region
          liftS (copyL nex1 nex2.laz)
      | CGoalL.next laz th => do
          let (hed, tel, o) ← liftS (splitL ⟨laz, th⟩)
          let nexh ← liftS (pastL env.cod ⟨hed, jmp0 o⟩ q region)
          let nex2 ← runLCS2 env snd sup q (CGoalL.next tel nexh.th) region
          let nex2 ← liftS (pastL env.cod nex2 p region)
          let nex1 ← runLCS2 env snd sup p (CGoalL.next nexh.laz nex2.th) region
          liftS (copyL nex1 nex2.laz)
      | CGoalL.done => fun _ => Option.none
  | sup, Nomm.n0 ax, goal, region => liftS (runLC env sup (Nomm.n0 ax) goal region)
  | sup, Nomm.n1 k, goal, region =>
      match goal with
      | CGoalL.next laz th => do
          let o ← medeLS th k laz
          pure ⟨ofSure Sure.bunt, jmp0 o⟩
      | g => liftS (runLC env sup (Nomm.n1 k) g region)
  | sup, Nomm.n3 p, goal, region =>
      match goal with
      | CGoalL.next laz th =>
          if noneEquivalentL laz then runLCS2 env snd sup p (CGoalL.next laz th) region else do
            let a ← collapseLazyAtomLS ⟨laz, th⟩
            match a with
            | Option.none => fun _ => Option.none
            | some (r, o) => do
                let (z, o') ← liftS (forl r o)
                let r' ← liftS re
                let oc ← liftS (emit ⟨[], [], Termin.clq r' (jmp0 z) (jmp0 o')⟩)
                runLCS2 env snd sup p (CGoalL.next (ofSure (lazyReg r')) (jmp0 oc)) region
      | CGoalL.pick z o => do
          let r ← liftS re
          let oc ← liftS (emit ⟨[], [], Termin.clq r z o⟩)
          runLCS2 env snd sup p (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region
      | CGoalL.done => do
          let (o0, o1) ← liftS doneBlocks
          let r ← liftS re
          let oc ← liftS (emit ⟨[], [], Termin.clq r (jmp0 o0) (jmp0 o1)⟩)
          runLCS2 env snd sup p (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region
  | sup, Nomm.n4 p, goal, region =>
      match goal with
      | CGoalL.done => do
          let pro ← liftS re
          let arg ← liftS re
          let o ← liftS (emit ⟨[], [Pole.inc arg pro], Termin.don pro⟩)
          runLCS2 env snd sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region
      | CGoalL.pick z o => do
          let pro ← liftS re
          let arg ← liftS re
          let o' ← liftS (emit ⟨[], [Pole.inc arg pro], Termin.brn pro z o⟩)
          runLCS2 env snd sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o')) region
      | CGoalL.next laz th => do
          let a ← collapseLazyAtomLS ⟨laz, th⟩
          let (pro, th') ← (match a with
            | some x => pure x
            | Option.none => do
                let r ← liftS re
                if th.args = [] then pure (r, th.there) else fun _ => Option.none : CMS Map (Nat × Nat))
          let arg ← liftS re
          let o ← liftS (emit ⟨[], [Pole.inc arg pro], Termin.hop (jmp0 th')⟩)
          runLCS2 env snd sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region
  | sup, Nomm.n5 p q, goal, region => do
      let rp ← liftS re
      let rq ← liftS re
      let o ← (match goal with
        | CGoalL.pick z o => liftS (emit ⟨[], [], Termin.eqq rp rq z o⟩)
        | CGoalL.done => do
            let (o0, o1) ← liftS doneBlocks
            liftS (emit ⟨[], [], Termin.eqq rp rq (jmp0 o0) (jmp0 o1)⟩)
        | CGoalL.next laz th => do
            let a ← collapseLazyAtomLS ⟨laz, th⟩
            match a with
            | Option.none =>
                if th.args = [] then liftS (emit ⟨[], [Pole.equ rp rq], Termin.hop (jmp0 th.there)⟩)
                else fun _ => Option.none
            | some (r, o) => do
                let (z, o') ← liftS (forl r o)
                liftS (emit ⟨[], [], Termin.eqq rp rq (jmp0 z) (jmp0 o')⟩) : CMS Map Nat)
      let nexq ← runLCS2 env snd sup q (CGoalL.next (ofSure (lazyReg rq)) (jmp0 o)) region
      let nexq ← liftS (pastL env.cod nexq p region)
      let nexp ← runLCS2 env snd sup p (CGoalL.next (ofSure (lazyReg rp)) nexq.th) region
      liftS (copyL nexp nexq.laz)
  | sup, Nomm.n6 p q r, goal, region =>
      match goal with
      | CGoalL.next laz th => sixNextLCS env.cod snd (runLCS2 env snd sup p) (runLCS2 env snd sup q)
          (runLCS2 env snd sup r) p q r 3 laz th region
      | _ => do
          let nex1 ← runLCS2 env snd sup r goal region
          let nex0 ← runLCS2 env snd sup q goal region
          let yes ← liftS (emit ⟨[], [], Termin.hop nex0.th⟩)
          let nuh ← liftS (emit ⟨[], [], Termin.hop nex1.th⟩)
          liftS (setTag yes region)
          liftS (setTag nuh region)
          if nex0.th.args ≠ [] then fun _ => Option.none else
          if nex1.th.args ≠ [] then fun _ => Option.none else
          let lazy ← liftS (liftO (pastFork env.cod (mk Sure.bunt [((yes, nex0.laz), (nuh, nex1.laz))] []) p))
          let nexCond ← runLCS2 env snd sup p (CGoalL.pick (jmp0 yes) (jmp0 nuh)) region
          withSoft fun sf => if !(lazyBig (softLess sf lazy)) then liftS (copyL nexCond lazy) else do
            let o ← liftS (emit ⟨[], [], Termin.hop nexCond.th⟩)
            let lazy ← lazyShutS o lazy
            liftS (copyL ⟨nexCond.laz, jmp0 o⟩ lazy)
  | sup, Nomm.n7 p q, goal, region => do
      let nex ← runLCS2 env snd (some p) q goal region
      runLCS2 env snd sup p nex.goal region
  | sup, Nomm.n10 a v q, goal, region => do
      let next ← liftS (simpleNextL goal)
      let (don, rec, o) ← liftS (intoL next a)
      let nexR ← liftS (pastL env.cod ⟨rec, jmp0 o⟩ v region)
      let nexDon ← runLCS2 env snd sup v (CGoalL.next don nexR.th) region
      let nexDon ← liftS (pastL env.cod nexDon q region)
      let nexRec ← runLCS2 env snd sup q (CGoalL.next nexR.laz nexDon.th) region
      liftS (copyL nexRec nexDon.laz)
  | sup, Nomm.n2 p q info, goal, region =>
      callLS env (runLCS2 env snd sup p) (runLCS2 env snd sup q) p q info sup goal region
  | _, _, _, _ => fun _ => Option.none

end Comp
end SkaModel
end Formalization
