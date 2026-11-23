import lemmas.Ska.CompLazyArms
import lemmas.Ska.CompLeap
import lemmas.Ska.CompTop

/-!
# `run` over lazy needs with forks and bonds

Goals and `next` over `Lazy`, the arms of `+comp` that take or return a
`next` (`+simple-next`, `+bomb`, `+split`, `+into`, `+copy`, `+past` with its
branch for a hinted nomm, `+lazy-bound`, `+mede`, `+collapse-lazy-atom`
with `+proxy`, `+kern`, `+lazy-shut`), and `runL`, the
model of `run` with the parameter `region` and the case `%6` for the goals
`%done` and `%pick`.

What is modelled of `%6`.  For `%done` and `%pick` the Hoon takes the
simpler branch with the goal itself for both branches: the no branch `r` is
compiled, then the yes branch `q`, two blocks hop to their code and are
tagged with the region, the lazy need of the subject is a fork of the two
branches' needs at those blocks, `+past-fork` binds them when the test is
hinted, the test `p` is compiled for `%pick` into the two blocks, and the
fork is copied into the test's need, or, when it is big, met before the
test by `+lazy-shut`.  For a goal `%next` (`sixNextL`) the Hoon first tries
`+leap`, and compiles the `%6` again for the rest of the goal's need, then
copies the parts it took out; then, when the goal's need has forks or bonds
that need something, either collapses the goal with `+kerf` and compiles the
`%6` again for one register, or forks the goal on the test's register
(`+fork`) and joins the branches with `+sect`; otherwise it forks the sure
need (`+fork-sure`), compiles the branches in a new region, joins them with
`+sect`, and compiles the test for `%pick`.  All of it is modelled, with
`fuel` bounding how often the case runs itself again (at most twice in a
row in the Hoon) and an empty soft map (`noSoft`, so `+soft-fork` is false).

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

/-! ## The arms of `%6` for a goal `%next` -/

/-- `+id`: a fresh region id. -/
def idM : CM Map Nat := fun g => some (g.id, { g with id := g.id + 1 })

/-- `+copy-tag`: the kids of a lazy block are in its region. -/
def copyTag (frm : Nat) (tos : List Nat) : CM Map Unit := fun g =>
  if g.drop then some ((), g) else
  (HoonMap.get g.tags frm).map fun region =>
    ((), { g with tags := tos.foldl (fun m o => HoonMap.put m o region) g.tags })

/-- `+insert-hop`: `a -> b` becomes `a -> o1 ... o2 -> b`, with the body of
`a` moved to `o2`. -/
def insertHop (a o1 o2 : Nat) : CM Map Unit := fun g =>
  if g.drop then some ((), g) else
  (HoonMap.get g.blocks a).bind fun b =>
  match b.fin with
  | Termin.hop _ =>
    if b.par ≠ [] then Option.none else
    let g := { g with blocks := HoonMap.put g.blocks o2 ⟨[], b.body, b.fin⟩ }
    some ((), { g with blocks := HoonMap.put g.blocks a { b with body := [], fin := Termin.hop ⟨[], o1⟩ } })
  | _ => Option.none

/-- The loop of `+fork-need`: fresh registers of the same shape, twice. -/
def forkNeedGo : Need → CM Map (Need × Need)
  | Need.none => pure (Need.none, Need.none)
  | Need.this _ => do
    let r0 ← re
    let r1 ← re
    pure (Need.this r0, Need.this r1)
  | Need.pair p q => do
    let (h0, h1) ← forkNeedGo p
    let (t0, t1) ← forkNeedGo q
    pure (Need.pair h0 t0, Need.pair h1 t1)
  | Need.both _ h t => do
    let r0 ← re
    let r1 ← re
    let (h0, h1) ← forkNeedGo h
    let (t0, t1) ← forkNeedGo t
    pure (Need.both r0 h0 t0, Need.both r1 h1 t1)

/-- `+fork-need`: two needs of the shape of `ned`, at the blocks `o0` and
`o1`, which hop with their registers to a join block whose parameters are
those of `ned` and which hops to `o`. -/
def forkNeed (ned : Need) (o o0 o1 : Nat) : CM Map (Need × Need) := do
  let (n0, n1) ← forkNeedGo ned
  let barg ← emit ⟨flattenNeed ned, [], Termin.hop (jmp0 o)⟩
  emir o0 ⟨[], [], Termin.hop ⟨(flattenNeed n0).map some, barg⟩⟩
  emir o1 ⟨[], [], Termin.hop ⟨(flattenNeed n1).map some, barg⟩⟩
  pure (n0, n1)

/-- `+fork-sure`. -/
def forkSure (sur : Sure S) (o o0 o1 : Nat) : CM Map (Sure S × Sure S) := do
  let (n0, n1) ← forkNeed sur.ned o o0 o1
  pure (⟨n0, sur.lok⟩, ⟨n1, sur.lok⟩)

mutual
/-- The loop of `+fork`: the lazy need forked on the register `rc`, the
sure part at `o0` and `o1` joining to `o`. -/
def forkLoop (rc : Nat) : Lazy S → Nat → Nat → Nat → CM Map (Lazy S × Lazy S)
  | mk sur fk bd, o, o0, o1 => do
    let (s0, s1) ← forkSure sur o o0 o1
    let (f0, f1) ← forkForks rc fk
    let (b0, b1) ← forkBonds rc bd
    pure (mk s0 f0 b0, mk s1 f1 b1)

/-- Its `spin-split` over the forks: each lazy block of a fork gets a block
that branches on a proxy of `rc` to two kids, which join to the old body. -/
def forkForks (rc : Nat) : List ((Nat × Lazy S) × (Nat × Lazy S)) →
    CM Map (List ((Nat × Lazy S) × (Nat × Lazy S)) × List ((Nat × Lazy S) × (Nat × Lazy S)))
  | [] => pure ([], [])
  | ((oy, y), (on, n)) :: rest => do
    let o0ky ← oo
    let o1ky ← oo
    let o0kn ← oo
    let o1kn ← oo
    let oi2y ← oo
    let oi2n ← oo
    copyTag oy [o0ky, o1ky]
    copyTag on [o0kn, o1kn]
    let (ly0, ly1) ← forkLoop rc y oi2y o0ky o1ky
    let (ln0, ln1) ← forkLoop rc n oi2n o0kn o1kn
    let py ← proxy rc oy
    let pn ← proxy rc on
    let oi1y ← emit ⟨[], [], Termin.brz py (jmp0 o0ky) (jmp0 o1ky)⟩
    let oi1n ← emit ⟨[], [], Termin.brz pn (jmp0 o0kn) (jmp0 o1kn)⟩
    insertHop oy oi1y oi2y
    insertHop on oi1n oi2n
    let (r0, r1) ← forkForks rc rest
    pure ((((o0ky, ly0), (o0kn, ln0)) :: r0), (((o1ky, ly1), (o1kn, ln1)) :: r1))

/-- Its `spin-split` over the bonds. -/
def forkBonds (rc : Nat) : List (Nat × Lazy S) → CM Map (List (Nat × Lazy S) × List (Nat × Lazy S))
  | [] => pure ([], [])
  | (ob, lb) :: rest => do
    let o0k ← oo
    let o1k ← oo
    let oi2 ← oo
    copyTag ob [o0k, o1k]
    let (l0, l1) ← forkLoop rc lb oi2 o0k o1k
    let p ← proxy rc ob
    let oi1 ← emit ⟨[], [], Termin.brz p (jmp0 o0k) (jmp0 o1k)⟩
    insertHop ob oi1 oi2
    let (r0, r1) ← forkBonds rc rest
    pure (((o0k, l0) :: r0), ((o1k, l1) :: r1))
end

/-- `+fork`: the goal's lazy need forked on the register `rc`. -/
def forkL (nex : NextL S) (rc : Nat) : CM Map (NextL S × NextL S) := do
  let o0 ← oo
  let o1 ← oo
  if nex.th.args ≠ [] then fun _ => Option.none else do
  let (l0, l1) ← forkLoop rc nex.laz nex.th.there o0 o1
  pure (⟨l0, jmp0 o0⟩, ⟨l1, jmp0 o1⟩)

/-- `~(dif by a) b`: the entries of `a` whose keys are not in `b`. -/
def difM [HoonMapKeys Map] {ν : Type} (a b : Map ν) : Map ν :=
  (HoonMapKeys.keys b).foldl HoonMap.del a

/-- The accumulator of the `rep`s of `+sect`: `tars`, and the arguments of
the yes and no ends and the parameters of the join. -/
abbrev SectAcc (Map : Type → Type) := Map Nat × List (Option Nat) × List (Option Nat) × List Nat

/-- One step of a `rep` of `+sect` over the proxies `made` that a branch
made (`yes`: the yes branch): a proxy read outside the branch's region is
read through a parameter of the join, which the branch passes its
definition to and the other branch nothing. -/
def sectStep (rid : Nat) (yes : Bool) (made : Map (Nat × List Nat)) (acc : SectAcc Map) (k : Nat) :
    CM Map (SectAcc Map) := fun g =>
  match HoonMap.get made k with
  | Option.none => some (acc, g)
  | some (df, tag) =>
    if tag.any (· == rid) then some (acc, g) else
    match HoonMap.get acc.1 df with
    | some t => some (acc, { g with cond := HoonMap.put g.cond k (t, tag) })
    | Option.none =>
      let tn := g.re
      let g := { g with re := g.re + 1 }
      let acc' : SectAcc Map := if yes
        then (HoonMap.put acc.1 df tn, some df :: acc.2.1, Option.none :: acc.2.2.1, tn :: acc.2.2.2)
        else (HoonMap.put acc.1 df tn, Option.none :: acc.2.1, some df :: acc.2.2.1, tn :: acc.2.2.2)
      some (acc', { g with cond := HoonMap.put g.cond k (tn, tag) })

/-- `~(jab by blocks)` with a gate that may crash. -/
def jabBlock (o : Nat) (f : Blob → Option Blob) : CM Map Unit := fun g =>
  (HoonMap.get g.blocks o).bind fun b => (f b).map fun b' => ((), { g with blocks := HoonMap.put g.blocks o b' })

/-- The `lens-hop` of `+sect`. -/
def lensHop (args : List (Option Nat)) (b : Blob) : Option Blob :=
  match b.fin with
  | Termin.hop t => some { b with fin := Termin.hop { t with args := args } }
  | _ => Option.none

/-- The threading of `+sect` (when not dropping): the proxies the branches
made whose blocks lie outside the branches' region read the join's new
parameters. -/
def sectThread [HoonMapKeys Map] (rid : Nat) (o0end o1end : Nat)
    (condBefore condBetween : Map (Nat × List Nat)) : CM Map Unit := fun g =>
  let made0 := difM g.cond condBetween
  let made1 := difM condBetween condBefore
  (HoonMap.get g.blocks o0end).bind fun b0 => (HoonMap.get g.blocks o1end).bind fun b1 =>
  match b0.fin, b1.fin with
  | Termin.hop t0, Termin.hop t1 =>
    if t0.there ≠ t1.there then Option.none else
    let tgt := t0.there
    (HoonMap.get g.blocks tgt).bind fun bt =>
    (do
      let acc ← (HoonMapKeys.keys made0).foldlM (sectStep rid true made0)
        ((HoonMap.empty, t0.args, t1.args, bt.par) : SectAcc Map)
      let acc ← (HoonMapKeys.keys made1).foldlM (sectStep rid false made1) acc
      jabBlock tgt (fun b => some { b with par := acc.2.2.2 })
      jabBlock o0end (lensHop acc.2.1)
      jabBlock o1end (lensHop acc.2.2.1) : CM Map Unit) g
  | _, _ => Option.none

/-- `+sect`: the blocks where the branches begin, tagged with the region of
the branches, and the fork of their lazy needs. -/
def sect [HoonMapKeys Map] (nex0 nex1 : NextL S) (o0end o1end : Nat) (rb : List Nat)
    (condBefore condBetween : Map (Nat × List Nat)) : CM Map (Lazy S × Nat × Nat) :=
  match rb with
  | [] => fun _ => Option.none
  | rid :: _ => do
    let o0b ← emit ⟨[], [], Termin.hop nex0.th⟩
    let o1b ← emit ⟨[], [], Termin.hop nex1.th⟩
    setTag o0b rb
    setTag o1b rb
    let g ← get
    if g.drop then pure () else sectThread rid o0end o1end condBefore condBetween
    if nex0.th.args ≠ [] then fun _ => Option.none else
    if nex1.th.args ≠ [] then fun _ => Option.none else
    pure (mk Sure.bunt [((o0b, nex0.laz), (o1b, nex1.laz))] [], o0b, o1b)

/-- The `cond` of the state. -/
def getCond : CM Map (Map (Nat × List Nat)) := fun g => some (g.cond, g)

/-- `+copy` of each need of `bys` into `nex`, in order. -/
def copyAll (nex : NextL S) : List (Lazy S) → CM Map (NextL S)
  | [] => pure nex
  | b :: rest => do
    let nex ← copyL nex b
    copyAll nex rest

/-- The branch of the case `%6` for a goal `%next` that forks the goal's
lazy need on the test's register (`+fork`) and joins the branches with
`+sect`. -/
def sixNextFork [HoonMapKeys Map] (rp rq rr : CGoalL S → List Nat → CM Map (NextL S)) (p : Nomm)
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
  let lazy ← liftO (pastFork noCode lazy p)
  let o ← emit ⟨[], [], Termin.brn rCond (jmp0 yes) (jmp0 nuh)⟩
  let lazy ← lazyShut o lazy
  let nexCond ← rp (CGoalL.next (ofSure ⟨Need.this rCond, HoonSet.empty⟩) (jmp0 o)) region
  copyL nexCond lazy

/-- The simpler branch of the case `%6` for a goal `%next`: the sure need
is forked (`+fork-sure`), the branches are compiled in a new region and
joined with `+sect`, and the test is compiled for `%pick`. -/
def sixNextSimple [HoonMapKeys Map] (rp rq rr : CGoalL S → List Nat → CM Map (NextL S)) (p : Nomm)
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
  let lazy ← liftO (pastFork noCode lazy p)
  let nexCond ← rp (CGoalL.pick (jmp0 yes) (jmp0 nuh)) region
  if !(lazyBig (softLess noSoft lazy)) then copyL nexCond lazy else do
    let o ← emit ⟨[], [], Termin.hop nexCond.th⟩
    let lazy ← lazyShut o lazy
    copyL ⟨nexCond.laz, jmp0 o⟩ lazy

/-- **The case `%6` of `run` for a goal `%next laz th`**, with the runs of
the test and the branches as parameters.  `fuel` bounds the times the case
runs itself again with another goal (after `+leap`, after `+kerf`): it does
so at most twice in a row, so `3` is enough (`none` past it, a departure
from the Hoon only where it would loop).

A finding, from runs of `finishLF` and `execEntry` on concrete inputs: when
a `%6` (the outer one) is compiled for a goal whose lazy need has forks, and
one of its branches is again such a `%6` (the inner one), `+sect` of the
inner `%6` reads a proxy made in one inner branch through a new parameter of
the inner join, to which the other inner branch passes `~` (the parameter
is deleted); `+sect` of the outer `%6` then threads that parameter through
the outer join, and the outer branch's end reads it on every path, so on the
path through the other inner branch the code reads a deleted register
(`+read` is `got`: a crash of the interpreter), where `+mink` returns a
value.  Smallest case: `[7 [6 [0 2] [0 2] [6 [0 2] [3 [0 14]] [0 1]]] [6 [1 1]
[0 0] [0 3]]]` on `[1 5 7 8]`, which `+mink` takes to `[5 7 8]`.

On the real compiler (2026-11-23): of 142 formulas on which this model's code
gets stuck, 68 crash the interpreter in the code of `+comp` before
`+optimize` (the others have a constant test or a constant part such as
`[3 [1 1]]`, which `+know` folds and this model does not: checked by hand
on four of them), and none
disagrees with `+mink` after `+optimize`.  The pass that removes the read is
`+remove-empty-middle`, whose `rewrite-hop` bypasses an empty join and
passes `~` through it; without it 16 of the 68 still crash, for example
`[7 [6 [5 [0 3] [1 5]] [0 1] [6 [0 2] [6 [0 2] [1 1] [0 7]] [0 6]]] [6 [0 2]
[0 2] [0 15]]]` on `[1 [0 2] [3 4] 5]` (`+mink`: `0`).  In the other cases
`+alias` folds the inner branch or the passes rescue it together. -/
def sixNextL [HoonMapKeys Map] (rp rq rr : CGoalL S → List Nat → CM Map (NextL S)) (p q r : Nomm) :
    Nat → Lazy S → Jmp → List Nat → CM Map (NextL S)
  | 0, _, _, _ => fun _ => Option.none
  | fuel + 1, laz, th, region =>
    match leap laz q r with
    | Option.none => fun _ => Option.none
    | some (some (rest, bys)) => do
      let nex ← sixNextL rp rq rr p q r fuel rest th region
      copyAll nex bys
    | some Option.none =>
      if !(noneEquivalentL (mk Sure.bunt laz.fork laz.bond)) then
        if (whole q && whole r) || thisOnly laz || lazyBig (softLess noSoft laz) ||
            softFork noSoft (fun _ => false) laz then do
          let (out, pro) ← kerf ⟨laz, th⟩
          sixNextL rp rq rr p q r fuel (ofSure ⟨Need.this pro, HoonSet.empty⟩) (jmp0 out) region
        else sixNextFork rp rq rr p laz th region
      else sixNextSimple rp rq rr p laz th region

/-- **On a fork-free goal the case `%6` takes its simpler branch.** -/
theorem sixNextL_ofSure [HoonMapKeys Map] (rp rq rr : CGoalL S → List Nat → CM Map (NextL S)) (p q r : Nomm)
    (fuel : Nat) (s : Sure S) (th : Jmp) (region : List Nat) :
    sixNextL rp rq rr p q r (fuel + 1) (ofSure s) th region = sixNextSimple rp rq rr p (ofSure s) th region := by
  have hl : leap (ofSure s) q r = some Option.none := by simp [leap, ofSure]
  have hs : HoonSet.small (HoonSet.empty : S) = true :=
    (HoonSet.small_iff _).mpr (fun x hx => absurd hx (HoonSet.mem_empty x))
  have hn : noneEquivalentL (mk (Sure.bunt : Sure S) (ofSure s).fork (ofSure s).bond) = true := by
    simp [noneEquivalentL, ofSure, Sure.bunt, noneForks, noneBonds, hs]
  simp only [sixNextL, hl, hn, Bool.not_true, Bool.false_eq_true, if_false]

/-! ## `run` -/

/-- `run` of `+comp` over full lazy needs, with the parameter `region`: the
cases of `CompModel.lean` and `%6` for every goal.  `none` on the other
cases: they are not modelled. -/
def runL [HoonMapKeys Map] : Nomm → CGoalL S → List Nat → CM Map (NextL S)
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
      | CGoalL.next laz th => sixNextL (runL p) (runL q) (runL r) p q r 3 laz th region
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

/-- **The case `%6` of `runL` for a goal `%next`** is `sixNextL` with the
runs of the test and the branches. -/
theorem runL_n6_next (p q r : Nomm) (laz : Lazy S) (th : Jmp) (region : List Nat) [HoonMapKeys Map] :
    (runL (Nomm.n6 p q r) (CGoalL.next laz th) region : CM Map (NextL S)) =
      sixNextL (runL p) (runL q) (runL r) p q r 3 laz th region := by
  unfold runL; rfl

end Comp
end SkaModel
end Formalization
