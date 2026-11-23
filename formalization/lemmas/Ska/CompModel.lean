import lemmas.Ska.CompSimOps
import lemmas.Ska.SockFacts
import lemmas.Hoon.Axis

/-!
# A model of `+comp` for nomm without calls, hints and forks

The arms of the door `+comp` of `desk/lib/nock-compilation.hoon` that the
cases `[^ *]`, `%0`, `%1`, `%3`, `%4`, `%5` and `%7` of `run` reach, each
as one Lean function with the arm's name, its case order and its order of
allocations, so that the registers and the block labels it hands out are
the Hoon's.

The fragment.  A nomm of these cases has no `%6`, so no lazy need ever has a
fork, and no hint, so none has a bond: every `need-lazy` here is
`[sure ~ ~]`, and the model of `need-lazy` is its `sure`.  Every arm that
tests `&(?=(~ fork.laz) ?=(~ bond.laz))` takes the branch that test selects,
and that branch is what is modelled.  Without calls the state's `soft` map
stays empty, so its tests (`(~(has by soft.gen) o)`) are false; `tags`,
`cond`, `cache` and `sofs` are neither read nor written, and are left out
of `Gen`.  `+past` returns its `next` unchanged when `(hinted nom ...)` is
false, which it is on every nomm of the fragment; it is the identity here.

What `none` means.  A model returns `none` where the Hoon crashes: a failed
`?>` or `?<`, `!!`, `got` on a missing key.

Sets.  A `(set @)` is a treap; its noun depends only on its elements, but
`~(rep in s)` folds in the treap's order, and the registers that
`+sure-require-look` allocates follow that order.  `HoonSet` abstracts the
treap as `HoonMap` does the maps: `toList` is the order of `rep`, and the
laws are about membership only, so the theorems hold for the real treap.
-/

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

/-! ## Sets -/

/-- The operations of `+in` on a `(set @)` that `+comp` uses. -/
class HoonSet (S : Type) where
  empty : S
  /-- The elements, in the order `~(rep in s)` visits them. -/
  toList : S → List Nat
  put : S → Nat → S
  uni : S → S → S
  /-- `=(~ s)`. -/
  isEmpty : S → Bool
  /-- `?=(?(~ [%1 ~ ~]) s)`. -/
  small : S → Bool
  toNoun : S → Noun
  mem_empty (x : Nat) : x ∉ toList empty
  mem_put (s : S) (x y : Nat) : y ∈ toList (put s x) ↔ y = x ∨ y ∈ toList s
  mem_uni (a b : S) (y : Nat) : y ∈ toList (uni a b) ↔ y ∈ toList a ∨ y ∈ toList b
  isEmpty_iff (s : S) : isEmpty s = true ↔ toList s = []
  small_iff (s : S) : small s = true ↔ ∀ x ∈ toList s, x = 1
  toNoun_empty : toNoun empty = A 0

variable {S : Type} [HoonSet S]

/-- `~(run in s)`: the set of the images.  A treap is fixed by its
elements, so the order of the insertions does not matter. -/
def setRun (f : Nat → Nat) (s : S) : S :=
  (HoonSet.toList s).foldr (fun x acc => HoonSet.put acc (f x)) HoonSet.empty

/-- The singleton `[x ~ ~]`. -/
def setOne (x : Nat) : S := HoonSet.put HoonSet.empty x

/-! ## Needs

    +$  need
      $~  [%none ~]
      $^  [p=need q=need]
      $%  [%both r=@uvre h=need t=need]
          [%this r=@uvre]
          [%none ~]
      ==
    +$  sure  [ned=need lok=(set @)]
-/

inductive Need where
  | pair (p q : Need)
  | both (r : Nat) (h t : Need)
  | this (r : Nat)
  | none
  deriving DecidableEq, Repr

def Need.toNoun : Need → Noun
  | pair p q => C p.toNoun q.toNoun
  | both r h t => C (A Tag.both) (C (A r) (C h.toNoun t.toNoun))
  | this r => C (A Tag.this) (A r)
  | none => C (A Tag.none) (A 0)

structure Sure (S : Type) where
  ned : Need
  lok : S

def Sure.toNoun (s : Sure S) : Noun := C s.ned.toNoun (HoonSet.toNoun s.lok)

/-- `*sure`, `[[%none ~] ~]`. -/
def Sure.bunt : Sure S := ⟨Need.none, HoonSet.empty⟩

/-- A fork-free `need-lazy`, `[sure ~ ~]`. -/
def lazyNoun (s : Sure S) : Noun := C s.toNoun (C (A 0) (A 0))

/-- `+cons-need`. -/
def consNeed (a b : Need) : Need :=
  if a = Need.none ∧ b = Need.none then Need.none else Need.pair a b

/-- `+flatten-need`. -/
def flattenNeed : Need → List Nat
  | Need.none => []
  | Need.this r => [r]
  | Need.pair p q => flattenNeed p ++ flattenNeed q
  | Need.both r h t => r :: (flattenNeed h ++ flattenNeed t)

/-- `+none-equivalent` on a fork-free lazy need. -/
def noneEquivalent (s : Sure S) : Bool :=
  decide (s.ned = Need.none) && HoonSet.small s.lok

/-! ## Goals and `next`

    +$  goal
      $%  [%pick z=jmp o=jmp]
          [%done ~]
          [%next laz=need-lazy then=jmp]
      ==
-/

inductive CGoal (S : Type) where
  | pick (z o : Jmp)
  | done
  | next (laz : Sure S) (th : Jmp)

def CGoal.toNoun : CGoal S → Noun
  | pick z o => C (A 0x6b636970) (C z.toNoun o.toNoun)
  | done => C (A 0x656e6f64) (A 0)
  | next laz th => C (A 0x7478656e) (C (lazyNoun laz) th.toNoun)

/-- `$next`: `[%next laz then]`. -/
structure Next (S : Type) where
  laz : Sure S
  /-- `then`. -/
  th : Jmp

def Next.goal (n : Next S) : CGoal S := CGoal.next n.laz n.th

/-- `(lazy-from-reg r)`, `(lazy-from-need this+r)`. -/
def lazyReg (r : Nat) : Sure S := ⟨Need.this r, HoonSet.empty⟩

/-! ## The state

    +$  line-short
      $:  re-gen=@uvre  bo-gen=_`@uwoo`1  id-gen=@uxid  mode=?(%drop %run)
          blocks=(map @uwoo blob)  tags=...  =cond  cache=...  soft=...  sofs=...
      ==
-/

structure Gen (Map : Type → Type) where
  re : Nat
  bo : Nat
  id : Nat
  /-- `?=(%drop mode.gen)`. -/
  drop : Bool
  blocks : Map Blob

variable {Map : Type → Type} [HoonMap Map]

/-- The arms of `+comp` thread `gen`; `none` is a crash. -/
abbrev CM (Map : Type → Type) := StateT (Gen Map) Option

/-- `+re`: a fresh register. -/
def re : CM Map Nat := fun g => some (g.re, { g with re := g.re + 1 })

/-- `+oo`: a fresh block label. -/
def oo : CM Map Nat := fun g => some (g.bo, { g with bo := g.bo + 1 })

/-- `+emir`: put a block, unless dropping. -/
def emir (o : Nat) (b : Blob) : CM Map Unit := fun g =>
  some ((), if g.drop then g else { g with blocks := HoonMap.put g.blocks o b })

/-- `+emit`: a block under a fresh label. -/
def emit (b : Blob) : CM Map Nat := do
  let o ← oo
  emir o b
  pure o

/-- `+add-ops`: put ops in front of the body of block `o`. -/
def addOps (o : Nat) (ops : List Pole) : CM Map Unit := fun g =>
  if g.drop then some ((), g) else
  (HoonMap.get g.blocks o).map fun b =>
    ((), { g with blocks := HoonMap.put g.blocks o { b with body := ops ++ b.body } })

/-- A jump without arguments. -/
def jmp0 (o : Nat) : Jmp := ⟨[], o⟩

/-- `+bomb`. -/
def bomb (miss : Option Nat) : CM Map (Next S) := do
  let o ← emit ⟨[], [], Termin.bom miss⟩
  pure ⟨Sure.bunt, jmp0 o⟩

/-- `+simple-next` (an arm of the `|^` of `run`, reading its goal). -/
def simpleNext (goal : CGoal S) : CM Map (Next S) :=
  match goal with
  | CGoal.next laz th => pure ⟨laz, th⟩
  | CGoal.done => do
      let r ← re
      let o ← emit ⟨[], [], Termin.don r⟩
      pure ⟨⟨Need.this r, HoonSet.empty⟩, jmp0 o⟩
  | CGoal.pick z o => do
      let r ← re
      let o' ← emit ⟨[], [], Termin.brn r z o⟩
      pure ⟨⟨Need.this r, HoonSet.empty⟩, jmp0 o'⟩

/-! ## `+from` -/

/-- The loop of `+from-sure`: the need `ned` of the noun at `axe`, as a
need of the noun that holds it. -/
def fromPath (ned : Need) (axe : Nat) : Need :=
  if _h : axe ≤ 1 then ned
  else if cap axe = 2 then Need.pair (fromPath ned (mas axe)) Need.none
  else Need.pair Need.none (fromPath ned (mas axe))
termination_by axe
decreasing_by all_goals exact mas_lt axe (by omega)

/-- `+from-sure`. -/
def fromSure (axe : Nat) (sur : Sure S) : Option (Sure S) :=
  if axe = 0 then Option.none else
  if sur.ned = Need.none then
    if axe = 1 then Option.none else
    some ⟨Need.none, if HoonSet.isEmpty sur.lok then setOne axe else setRun (Hoon.pegF axe) sur.lok⟩
  else some ⟨fromPath sur.ned axe, setRun (Hoon.pegF axe) sur.lok⟩

/-- `+from` on a fork-free lazy need. -/
def «from» (axe : Nat) (laz : Sure S) : Option (Sure S) := fromSure axe laz

/-! ## `+split` -/

/-- `+must`. -/
def must (ned : Need) : CM Map (Nat × Need) :=
  match ned with
  | Need.both r _ _ => pure (r, ned)
  | Need.this r => pure (r, ned)
  | Need.pair p q => do let r ← re; pure (r, Need.both r p q)
  | Need.none => do let r ← re; pure (r, Need.this r)

/-- `+split-need`. -/
def splitNeed (ned : Need) (o : Nat) : CM Map (Need × Need) :=
  match ned with
  | Need.pair p q => pure (p, q)
  | Need.none => pure (Need.none, Need.none)
  | Need.this r => do
      let h ← re
      let t ← re
      addOps o [Pole.con h t r]
      pure (Need.this h, Need.this t)
  | Need.both r h t => do
      let hed ← must h
      let tel ← must t
      addOps o [Pole.con hed.1 tel.1 r]
      pure (hed.2, tel.2)

/-- The fold of `+split-sure` over the looked-at axes. -/
def splitLok (lok : S) : Option (S × S) :=
  (HoonSet.toList lok).foldl (fun acc axe => acc.bind fun (h, t) =>
    if axe = 0 then Option.none
    else if axe = 1 ∨ axe = 2 ∨ axe = 3 then some (h, t)
    else if cap axe = 2 then some (HoonSet.put h (mas axe), t)
    else some (h, HoonSet.put t (mas axe))) (some (HoonSet.empty, HoonSet.empty))

/-- `+split-sure`. -/
def splitSure (sur : Sure S) (o : Nat) : CM Map (Sure S × Sure S) := fun g =>
  (splitLok sur.lok).bind fun (lh, lt) =>
    (splitNeed sur.ned o g).map fun ((nh, nt), g') => ((⟨nh, lh⟩, ⟨nt, lt⟩), g')

/-- `+split` on a fork-free lazy need. -/
def split (nex : Next S) : CM Map (Sure S × Sure S × Nat) := do
  let o ← emit ⟨[], [], Termin.hop nex.th⟩
  let (h, t) ← splitSure nex.laz o
  pure (h, t, o)

/-! ## `+copy` -/

/-- `+copy-need-make-ops`.  The Hoon walks a work list depth first, head
before tail, and conses the needs of the two halves when it pops them; this
is the same walk as a recursion, with the ops consed in the same order and
the registers allocated in the same order. -/
def copyNeed : Need → Need → List Pole → CM Map (Need × List Pole)
  | Need.none, r, ops => pure (r, ops)
  | l, Need.none, ops => pure (l, ops)
  | Need.this rl, Need.this rr, ops => pure (Need.this rl, Pole.mov rl rr :: ops)
  | Need.this rl, Need.both x h t, ops => pure (Need.both x h t, Pole.mov x rl :: ops)
  | Need.this rl, Need.pair p q, ops => do
      let x ← re
      pure (Need.both x p q, Pole.mov x rl :: ops)
  | Need.both x h t, Need.this rr, ops => pure (Need.both x h t, Pole.mov x rr :: ops)
  | Need.pair p q, Need.this rr, ops => do
      let x ← re
      pure (Need.both x p q, Pole.mov x rr :: ops)
  | Need.both rl hl tl, Need.both x hr tr, ops => do
      let (a, ops) ← copyNeed hl hr (Pole.mov x rl :: ops)
      let (b, ops) ← copyNeed tl tr ops
      pure (Need.both x a b, ops)
  | Need.both rl hl tl, Need.pair p q, ops => do
      let x ← re
      let (a, ops) ← copyNeed hl p (Pole.mov x rl :: ops)
      let (b, ops) ← copyNeed tl q ops
      pure (Need.both x a b, ops)
  | Need.pair pl ql, Need.pair pr qr, ops => do
      let (a, ops) ← copyNeed pl pr ops
      let (b, ops) ← copyNeed ql qr ops
      pure (consNeed a b, ops)
  | Need.pair pl ql, Need.both x h t, ops => do
      let (a, ops) ← copyNeed pl h ops
      let (b, ops) ← copyNeed ql t ops
      pure (Need.both x a b, ops)

/-- `+copy-lazy` on fork-free lazy needs. -/
def copyLazy (o : Nat) (first second : Sure S) : CM Map (Sure S) := do
  let (ned, ops) ← copyNeed first.ned second.ned []
  addOps o ops
  pure ⟨ned, HoonSet.uni first.lok second.lok⟩

/-- `+copy`. -/
def copy (first : Next S) (second : Sure S) : CM Map (Next S) := do
  let o ← emit ⟨[], [], Termin.hop first.th⟩
  let laz ← copyLazy o first.laz second
  pure ⟨laz, jmp0 o⟩

/-! ## Looks, constants and atoms -/

/-- The loop of `+sure-require-look` for one axis. -/
def lookPath (ned : Need) (axe : Nat) : CM Map Need :=
  if _h : axe ≤ 1 then
    match ned with
    | Need.none => do let r ← re; pure (Need.this r)
    | _ => pure ned
  else
    let (here, hd, tl) : Option Nat × Need × Need :=
      match ned with
      | Need.none => (Option.none, Need.none, Need.none)
      | Need.this r => (some r, Need.none, Need.none)
      | Need.pair p q => (Option.none, p, q)
      | Need.both r h t => (some r, h, t)
    do
      let (hr, tr) ← if cap axe = 2 then do let x ← lookPath hd (mas axe); pure (x, tl)
                     else do let x ← lookPath tl (mas axe); pure (hd, x)
      let x := consNeed hr tr
      match here with
      | Option.none => pure x
      | some r => if x = Need.none then pure (Need.this r) else
          match x with
          | Need.pair p q => pure (Need.both r p q)
          | _ => pure (Need.both r Need.none Need.none)
termination_by axe
decreasing_by all_goals exact mas_lt axe (by omega)

/-- `+sure-require-look`: the need with a register for each looked-at axis
the need does not reach. -/
def sureRequireLook (sur : Sure S) : CM Map Need :=
  (HoonSet.toList sur.lok).foldl (fun acc axe => do
    let ned ← acc
    if axe = 1 then pure ned else
    if axe = 0 then fun _ => Option.none else
    lookPath ned axe) (pure sur.ned)

/-- `+crash-need` with an immediate atom (`%&`) or a register (`%|`). -/
def crashNeed (o : Nat) (atom : Sum Nat Nat) (ned : Need) : CM Map Unit :=
  let fill := (flattenNeed ned).map fun x => Pole.imm (A 0) x
  match atom with
  | Sum.inr p => addOps o (Pole.cel p :: fill)
  | Sum.inl n => do
      let r ← re
      addOps o (Pole.imm (A n) r :: Pole.cel r :: fill)

/-- The loop of `+mede`: the constant `som` into the registers of `ned`. -/
def medeLoop (o : Nat) : Noun → Need → CM Map Unit
  | _, Need.none => pure ()
  | som, Need.this r => addOps o [Pole.imm som r]
  | Noun.atom n, Need.pair p q => crashNeed o (Sum.inl n) (Need.pair p q)
  | Noun.cell a b, Need.pair p q => do medeLoop o a p; medeLoop o b q
  | Noun.atom n, Need.both r h t => crashNeed o (Sum.inl n) (Need.both r h t)
  | Noun.cell a b, Need.both r h t => do
      addOps o [Pole.imm (C a b) r]
      medeLoop o a h
      medeLoop o b t

/-- `+mede` on a fork-free lazy need (`+walk-lazy` calls its gate once). -/
def mede (th : Jmp) (som : Noun) (laz : Sure S) : CM Map Nat := do
  let o ← emit ⟨[], [], Termin.hop th⟩
  let g ← get
  if g.drop then pure o else do
    let ned ← sureRequireLook laz
    medeLoop o som ned
    pure o

/-- `+collapse-lazy-atom` on a fork-free lazy need. -/
def collapseLazyAtom (nex : Next S) : CM Map (Option (Nat × Nat)) := do
  if nex.th.args ≠ [] then fun _ => Option.none else
  if noneEquivalent nex.laz then pure Option.none else do
  let nedSure ← sureRequireLook nex.laz
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
    let ned' ← sureRequireLook ⟨Need.this r, nex.laz.lok⟩
    match ned' with
    | Need.none => pure (some (r, there))
    | Need.this r' =>
        if r = r' then pure (some (r, there)) else do
          addOps there [Pole.mov r r']
          pure (some (r, there))
    | _ => do
        crashNeed there (Sum.inr r) ned'
        pure (some (r, there))

/-- `+forl`: a loobean into register `r`, from the two blocks returned. -/
def forl (r o : Nat) : CM Map (Nat × Nat) := do
  let r0 ← re
  let r1 ← re
  let barg ← emit ⟨[r], [], Termin.hop (jmp0 o)⟩
  let if0 ← emit ⟨[], [Pole.imm (A 0) r0], Termin.hop ⟨[some r0], barg⟩⟩
  let if1 ← emit ⟨[], [Pole.imm (A 1) r1], Termin.hop ⟨[some r1], barg⟩⟩
  pure (if0, if1)

/-! ## `run` -/

/-- The goal `%pick` into the two blocks that return `0` and `1`, as the
cases `%3` and `%5` make it for `%done`. -/
def doneBlocks : CM Map (Nat × Nat) := do
  let r0 ← re
  let r1 ← re
  let o0 ← emit ⟨[], [Pole.imm (A 0) r0], Termin.don r0⟩
  let o1 ← emit ⟨[], [Pole.imm (A 1) r1], Termin.don r1⟩
  pure (o0, o1)

/-- `run` of `+comp`, for the cases `[^ *]`, `%0`, `%1`, `%3`, `%4`, `%5`,
`%7` (the parameters `mono`, `region`, `sup` are read by no case of the
fragment).  `none` on the other cases: they are not modelled. -/
def run : Nomm → CGoal S → CM Map (Next S)
  | Nomm.cons p q, goal => do
      let goal ← (match goal with
        | CGoal.done => do
            let r ← re
            let o ← emit ⟨[], [], Termin.don r⟩
            pure (CGoal.next (lazyReg r) (jmp0 o))
        | g => pure g : CM Map (CGoal S))
      match goal with
      | CGoal.pick _ _ => do
          let o ← emit ⟨[], [], Termin.bom Option.none⟩
          let nex2 ← run q (CGoal.next Sure.bunt (jmp0 o))
          let nex1 ← run p (CGoal.next Sure.bunt nex2.th)
          copy nex1 nex2.laz
      | CGoal.next laz th => do
          let (hed, tel, o) ← split ⟨laz, th⟩
          let nexh : Next S := ⟨hed, jmp0 o⟩
          let nex2 ← run q (CGoal.next tel nexh.th)
          let nex1 ← run p (CGoal.next nexh.laz nex2.th)
          copy nex1 nex2.laz
      | CGoal.done => fun _ => Option.none
  | Nomm.n0 ax, goal =>
      if ax = 0 then bomb (match goal with | CGoal.next _ th => some th.there | _ => Option.none)
      else do
        let nex ← simpleNext goal
        if ax = 1 then pure nex else
        match «from» ax nex.laz with
        | some laz => pure ⟨laz, nex.th⟩
        | Option.none => fun _ => Option.none
  | Nomm.n1 k, goal =>
      match goal with
      | CGoal.done => do
          let r ← re
          let o ← emit ⟨[], [Pole.imm k r], Termin.don r⟩
          pure ⟨Sure.bunt, jmp0 o⟩
      | CGoal.pick z o =>
          if k = A 0 then pure ⟨Sure.bunt, z⟩
          else if k = A 1 then pure ⟨Sure.bunt, o⟩
          else bomb Option.none
      | CGoal.next laz th => do
          let o ← mede th k laz
          pure ⟨Sure.bunt, jmp0 o⟩
  | Nomm.n3 p, goal =>
      match goal with
      | CGoal.next laz th =>
          if noneEquivalent laz then run p (CGoal.next laz th) else do
            let a ← collapseLazyAtom ⟨laz, th⟩
            match a with
            | Option.none => fun _ => Option.none
            | some (r, o) => do
                let (z, o') ← forl r o
                let r' ← re
                let oc ← emit ⟨[], [], Termin.clq r' (jmp0 z) (jmp0 o')⟩
                run p (CGoal.next (lazyReg r') (jmp0 oc))
      | CGoal.pick z o => do
          let r ← re
          let oc ← emit ⟨[], [], Termin.clq r z o⟩
          run p (CGoal.next (lazyReg r) (jmp0 oc))
      | CGoal.done => do
          let (o0, o1) ← doneBlocks
          let r ← re
          let oc ← emit ⟨[], [], Termin.clq r (jmp0 o0) (jmp0 o1)⟩
          run p (CGoal.next (lazyReg r) (jmp0 oc))
  | Nomm.n4 p, goal =>
      match goal with
      | CGoal.done => do
          let pro ← re
          let arg ← re
          let o ← emit ⟨[], [Pole.inc arg pro], Termin.don pro⟩
          run p (CGoal.next (lazyReg arg) (jmp0 o))
      | CGoal.pick z o => do
          let pro ← re
          let arg ← re
          let o' ← emit ⟨[], [Pole.inc arg pro], Termin.brn pro z o⟩
          run p (CGoal.next (lazyReg arg) (jmp0 o'))
      | CGoal.next laz th => do
          let a ← collapseLazyAtom ⟨laz, th⟩
          let (pro, th') ← (match a with
            | some x => pure x
            | Option.none => do
                let r ← re
                if th.args = [] then pure (r, th.there) else fun _ => Option.none : CM Map (Nat × Nat))
          let arg ← re
          let o ← emit ⟨[], [Pole.inc arg pro], Termin.hop (jmp0 th')⟩
          run p (CGoal.next (lazyReg arg) (jmp0 o))
  | Nomm.n5 p q, goal => do
      let rp ← re
      let rq ← re
      let o ← (match goal with
        | CGoal.pick z o => emit ⟨[], [], Termin.eqq rp rq z o⟩
        | CGoal.done => do
            let (o0, o1) ← doneBlocks
            emit ⟨[], [], Termin.eqq rp rq (jmp0 o0) (jmp0 o1)⟩
        | CGoal.next laz th => do
            let a ← collapseLazyAtom ⟨laz, th⟩
            match a with
            | Option.none =>
                if th.args = [] then emit ⟨[], [Pole.equ rp rq], Termin.hop (jmp0 th.there)⟩
                else fun _ => Option.none
            | some (r, o) => do
                let (z, o') ← forl r o
                emit ⟨[], [], Termin.eqq rp rq (jmp0 z) (jmp0 o')⟩ : CM Map Nat)
      let nexq ← run q (CGoal.next (lazyReg rq) (jmp0 o))
      let nexp ← run p (CGoal.next (lazyReg rp) nexq.th)
      copy nexp nexq.laz
  | Nomm.n7 p q, goal => do
      let nex ← run q goal
      run p nex.goal
  | _, _ => fun _ => Option.none

end Comp
end SkaModel
end Formalization
