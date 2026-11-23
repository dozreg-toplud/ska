import lemmas.Ska.CompLazyArms
import lemmas.Ska.CompTop

/-!
# `run` over lazy needs with forks and bonds

Goals and `next` over `Lazy`, the arms of `+comp` that take or return a
`next` (`+simple-next`, `+bomb`, `+split`, `+into`, `+copy`, `+past` with its
branch for a hinted nomm, `+lazy-bound`, `+mede`, `+collapse-lazy-atom`
with `+proxy`, `+kern`, `+lazy-shut`), and `runL`, the
model of `run` with the parameter `region` and the case `%6` for the goals
`%done` and `%pick`.

What is modelled of `%6`.  For a goal `%next` the Hoon first tries `+leap`,
then the branch that collapses or forks the goal's need (`+kerf`, `+fork`,
`+sect`), then the simpler branch with `+fork-sure` and `+sect`: none of
these is modelled yet, and `runL` is `none` there.  For `%done` and `%pick`
the Hoon takes the simpler branch with the goal itself for both branches:
the no branch `r` is compiled, then the yes branch `q`, two blocks hop to
their code and are tagged with the region, the lazy need of the subject is
a fork of the two branches' needs at those blocks, `+past-fork` binds them
when the test is hinted, the test `p` is compiled for `%pick` into the two
blocks, and the fork is copied into the test's need, or, when it is big,
met before the test by `+lazy-shut`.  That is all modelled.

`runL_toL` (in `CompLazyAgree.lean`): on the fragment of `CompFrag.lean`,
`runL` on a fork-free goal is `run`.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-! ## Goals -/

/-- `$goal` with a full `need-lazy`. -/
inductive CGoalL (S : Type) where
  | pick (z o : Jmp)
  | done
  | next (laz : Lazy S) (th : Jmp)

def CGoalL.toNoun : CGoalL S → Noun
  | pick z o => C (A 0x6b636970) (C z.toNoun o.toNoun)
  | done => C (A 0x656e6f64) (A 0)
  | next laz th => C (A 0x7478656e) (C laz.toNoun th.toNoun)

/-- `$next` with a full `need-lazy`. -/
structure NextL (S : Type) where
  laz : Lazy S
  th : Jmp

def NextL.goal (n : NextL S) : CGoalL S := CGoalL.next n.laz n.th

/-- A fork-free goal. -/
def CGoal.toL : CGoal S → CGoalL S
  | CGoal.pick z o => CGoalL.pick z o
  | CGoal.done => CGoalL.done
  | CGoal.next laz th => CGoalL.next (ofSure laz) th

/-- A fork-free `next`. -/
def Next.toL (n : Next S) : NextL S := ⟨ofSure n.laz, n.th⟩

theorem CGoal.toNoun_toL (g : CGoal S) : (CGoal.toL g).toNoun = g.toNoun := by
  cases g <;> simp [CGoal.toL, CGoalL.toNoun, CGoal.toNoun, toNoun_ofSure]

theorem Next.goal_toL (n : Next S) : (Next.toL n).goal = CGoal.toL n.goal := rfl

/-! ## The arms that take a `next` -/

/-- `+simple-next`. -/
def simpleNextL (goal : CGoalL S) : CM Map (NextL S) :=
  match goal with
  | CGoalL.next laz th => pure ⟨laz, th⟩
  | CGoalL.done => do
      let r ← re
      let o ← emit ⟨[], [], Termin.don r⟩
      pure ⟨ofSure ⟨Need.this r, HoonSet.empty⟩, jmp0 o⟩
  | CGoalL.pick z o => do
      let r ← re
      let o' ← emit ⟨[], [], Termin.brn r z o⟩
      pure ⟨ofSure ⟨Need.this r, HoonSet.empty⟩, jmp0 o'⟩

/-- `+bomb`. -/
def bombL (miss : Option Nat) : CM Map (NextL S) := do
  let o ← emit ⟨[], [], Termin.bom miss⟩
  pure ⟨ofSure Sure.bunt, jmp0 o⟩

/-- `+split`. -/
def splitL (nex : NextL S) : CM Map (Lazy S × Lazy S × Nat) := do
  let o ← emit ⟨[], [], Termin.hop nex.th⟩
  let (h, t) ← splitLoop nex.laz o
  pure (h, t, o)

/-- `+into`. -/
def intoL (nex : NextL S) (axe : Nat) : CM Map (Lazy S × Lazy S × Nat) := do
  let o ← emit ⟨[], [], Termin.hop nex.th⟩
  let (d, r) ← intoLoopL axe nex.laz o
  pure (d, r, o)

/-- `+copy`. -/
def copyL (first : NextL S) (second : Lazy S) : CM Map (NextL S) := do
  let o ← emit ⟨[], [], Termin.hop first.th⟩
  let laz ← copyLazyL o first.laz second
  pure ⟨laz, jmp0 o⟩

/-- `+past`: when the need asks something and `nom` is hinted, the need is
parked in a bond behind a new block, tagged with the region. -/
def pastL (cod : Bell → Option Bool) (nex : NextL S) (nom : Nomm) (region : List Nat) : CM Map (NextL S) :=
  if nex.laz.sure.ned = Need.none ∧ HoonSet.small nex.laz.sure.lok = true ∧ nex.laz.fork.isEmpty = true then
    pure nex else
  match hinted cod nom with
  | Option.none => fun _ => Option.none
  | some false => pure nex
  | some true => do
    let o ← emit ⟨[], [], Termin.hop nex.th⟩
    setTag o region
    pure ⟨mk Sure.bunt [] ((o, mk nex.laz.sure nex.laz.fork []) :: nex.laz.bond), jmp0 o⟩

/-- `+lazy-bound`. -/
def lazyBound (nex : NextL S) (region : List Nat) : CM Map (NextL S) := do
  let o ← emit ⟨[], [], Termin.hop nex.th⟩
  setTag o region
  if nex.th.args = [] then pure ⟨mk Sure.bunt [] [(o, nex.laz)], jmp0 o⟩ else fun _ => Option.none

/-- `+proxy`: a fresh register to read `r` through in the lazy block `o`,
recorded in `cond` with the region of `o` (`got`: a crash when `o` has no
tag). -/
def proxy (r o : Nat) : CM Map Nat := fun g =>
  let p := g.re
  let g := { g with re := g.re + 1 }
  if g.drop then some (p, g) else
  (HoonMap.get g.tags o).map fun tag => (p, { g with cond := HoonMap.put g.cond p (r, tag) })

/-- `+mede`. -/
def medeL (th : Jmp) (som : Noun) (laz : Lazy S) : CM Map Nat := do
  let o ← emit ⟨[], [], Termin.hop th⟩
  let g ← get
  if g.drop then pure o else do
    walkLazy (fun o sur => do
      let ned ← sureRequireLook sur
      medeLoop o som ned) o laz
    pure o

/-- The gate that `+collapse-lazy-atom` walks the lazy need with: a move
from `r` where a block wants the noun whole, a crash where it wants parts
of it. -/
def collapseGate (r o : Nat) (oLaz : Nat) (sur : Sure S) : CM Map Unit := do
  let ned ← sureRequireLook sur
  match ned with
  | Need.none => pure ()
  | Need.this r' =>
    if r = r' then pure () else do
      let src ← (if oLaz = o then pure r else proxy r oLaz : CM Map Nat)
      addOps oLaz [Pole.mov src r']
  | _ => do
    let src ← (if oLaz = o then pure r else proxy r oLaz : CM Map Nat)
    crashNeed oLaz (Sum.inr src) ned

/-- `+collapse-lazy-atom`. -/
def collapseLazyAtomL (nex : NextL S) : CM Map (Option (Nat × Nat)) := do
  if nex.th.args ≠ [] then fun _ => Option.none else
  if noneEquivalentL nex.laz then pure Option.none else do
  let nedSure ← sureRequireLook nex.laz.sure
  let (r, there) ← (match nedSure with
    | Need.this r => pure (r, nex.th.there)
    | Need.none => do let r ← re; pure (r, nex.th.there)
    | Need.pair _ _ => do
        let r ← re
        let o ← emit ⟨[], [], Termin.bom Option.none⟩
        pure (r, o)
    | Need.both r _ _ => do
        let o ← emit ⟨[], [], Termin.bom Option.none⟩
        pure (r, o) : CM Map (Nat × Nat))
  let g ← get
  if g.drop then pure (some (r, there)) else do
    walkLazy (collapseGate r there) there (mk ⟨Need.this r, nex.laz.sure.lok⟩ nex.laz.fork nex.laz.bond)
    pure (some (r, there))

/-! `+kern-need` is `kernNeed` of `CompTop.lean`. -/

/-- `+kern`: the lazy need met from one register `r`, with the moves and the
taking apart in each lazy block (through a proxy in the blocks other than
`o`).  The soft map is empty, so `+soft-ask` is not reached. -/
def kern (o : Nat) (laz : Lazy S) : CM Map Nat := do
  let r ← re
  let g ← get
  if g.drop then pure r else do
    walkLazy (fun oLaz sur => do
      let ned ← sureRequireLook sur
      if ned = Need.none then pure () else do
      let src ← (if oLaz = o then pure r else proxy r oLaz : CM Map Nat)
      if noSoft oLaz then fun _ => Option.none else do
      let ops ← kernNeed src ned
      addOps oLaz ops) o laz
    pure r

/-- `+lazy-shut`: a big lazy need is met at block `o` from one register. -/
def lazyShut (o : Nat) (laz : Lazy S) : CM Map (Lazy S) :=
  if !(lazyBig (softLess noSoft laz)) then pure laz else do
    let r ← kern o laz
    pure (ofSure ⟨Need.this r, HoonSet.empty⟩)

/-- `+kerf`. -/
def kerf (nex : NextL S) : CM Map (Nat × Nat) := do
  let o ← emit ⟨[], [], Termin.hop nex.th⟩
  let r ← kern o nex.laz
  pure (o, r)

/-- An `Option` as a step of `CM`. -/
def liftO {α : Type} (x : Option α) : CM Map α := fun g => x.map fun a => (a, g)

/-! ## `run` -/

/-- `run` of `+comp` over full lazy needs, with the parameter `region`: the
cases of `CompModel.lean` and `%6` for the goals `%done` and `%pick`.
`none` on the other cases: they are not modelled. -/
def runL : Nomm → CGoalL S → List Nat → CM Map (NextL S)
  | Nomm.cons p q, goal, region => do
      let goal ← (match goal with
        | CGoalL.done => do
            let r ← re
            let o ← emit ⟨[], [], Termin.don r⟩
            pure (CGoalL.next (ofSure (lazyReg r)) (jmp0 o))
        | g => pure g : CM Map (CGoalL S))
      match goal with
      | CGoalL.pick _ _ => do
          let o ← emit ⟨[], [], Termin.bom Option.none⟩
          let nex2 ← runL q (CGoalL.next (ofSure Sure.bunt) (jmp0 o)) region
          let nex2 ← pastL noCode nex2 p region
          let nex1 ← runL p (CGoalL.next (ofSure Sure.bunt) nex2.th) region
          copyL nex1 nex2.laz
      | CGoalL.next laz th => do
          let (hed, tel, o) ← splitL ⟨laz, th⟩
          let nexh ← pastL noCode ⟨hed, jmp0 o⟩ q region
          let nex2 ← runL q (CGoalL.next tel nexh.th) region
          let nex2 ← pastL noCode nex2 p region
          let nex1 ← runL p (CGoalL.next nexh.laz nex2.th) region
          copyL nex1 nex2.laz
      | CGoalL.done => fun _ => Option.none
  | Nomm.n0 ax, goal, _ =>
      if ax = 0 then bombL (match goal with | CGoalL.next _ th => some th.there | _ => Option.none)
      else do
        let nex ← simpleNextL goal
        if ax = 1 then pure nex else
        match fromL ax nex.laz with
        | some laz => pure ⟨laz, nex.th⟩
        | Option.none => fun _ => Option.none
  | Nomm.n1 k, goal, _ =>
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
  | Nomm.n3 p, goal, region =>
      match goal with
      | CGoalL.next laz th =>
          if noneEquivalentL laz then runL p (CGoalL.next laz th) region else do
            let a ← collapseLazyAtomL ⟨laz, th⟩
            match a with
            | Option.none => fun _ => Option.none
            | some (r, o) => do
                let (z, o') ← forl r o
                let r' ← re
                let oc ← emit ⟨[], [], Termin.clq r' (jmp0 z) (jmp0 o')⟩
                runL p (CGoalL.next (ofSure (lazyReg r')) (jmp0 oc)) region
      | CGoalL.pick z o => do
          let r ← re
          let oc ← emit ⟨[], [], Termin.clq r z o⟩
          runL p (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region
      | CGoalL.done => do
          let (o0, o1) ← doneBlocks
          let r ← re
          let oc ← emit ⟨[], [], Termin.clq r (jmp0 o0) (jmp0 o1)⟩
          runL p (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region
  | Nomm.n4 p, goal, region =>
      match goal with
      | CGoalL.done => do
          let pro ← re
          let arg ← re
          let o ← emit ⟨[], [Pole.inc arg pro], Termin.don pro⟩
          runL p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region
      | CGoalL.pick z o => do
          let pro ← re
          let arg ← re
          let o' ← emit ⟨[], [Pole.inc arg pro], Termin.brn pro z o⟩
          runL p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o')) region
      | CGoalL.next laz th => do
          let a ← collapseLazyAtomL ⟨laz, th⟩
          let (pro, th') ← (match a with
            | some x => pure x
            | Option.none => do
                let r ← re
                if th.args = [] then pure (r, th.there) else fun _ => Option.none : CM Map (Nat × Nat))
          let arg ← re
          let o ← emit ⟨[], [Pole.inc arg pro], Termin.hop (jmp0 th')⟩
          runL p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region
  | Nomm.n5 p q, goal, region => do
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
      let nexq ← runL q (CGoalL.next (ofSure (lazyReg rq)) (jmp0 o)) region
      let nexq ← pastL noCode nexq p region
      let nexp ← runL p (CGoalL.next (ofSure (lazyReg rp)) nexq.th) region
      copyL nexp nexq.laz
  | Nomm.n6 p q r, goal, region =>
      match goal with
      | CGoalL.next _ _ => fun _ => Option.none
      | _ => do
          let nex1 ← runL r goal region
          let nex0 ← runL q goal region
          let yes ← emit ⟨[], [], Termin.hop nex0.th⟩
          let nuh ← emit ⟨[], [], Termin.hop nex1.th⟩
          setTag yes region
          setTag nuh region
          if nex0.th.args ≠ [] then fun _ => Option.none else
          if nex1.th.args ≠ [] then fun _ => Option.none else
          let lazy ← liftO (pastFork noCode (mk Sure.bunt [((yes, nex0.laz), (nuh, nex1.laz))] []) p)
          let nexCond ← runL p (CGoalL.pick (jmp0 yes) (jmp0 nuh)) region
          if !(lazyBig (softLess noSoft lazy)) then copyL nexCond lazy else do
            let o ← emit ⟨[], [], Termin.hop nexCond.th⟩
            let lazy ← lazyShut o lazy
            copyL ⟨nexCond.laz, jmp0 o⟩ lazy
  | Nomm.n7 p q, goal, region => do
      let nex ← runL q goal region
      runL p nex.goal region
  | Nomm.n10 a v q, goal, region => do
      let next ← simpleNextL goal
      let (don, rec, o) ← intoL next a
      let nexR ← pastL noCode ⟨rec, jmp0 o⟩ v region
      let nexDon ← runL v (CGoalL.next don nexR.th) region
      let nexDon ← pastL noCode nexDon q region
      let nexRec ← runL q (CGoalL.next nexR.laz nexDon.th) region
      copyL nexRec nexDon.laz
  | _, _, _ => fun _ => Option.none

end Comp
end SkaModel
end Formalization
