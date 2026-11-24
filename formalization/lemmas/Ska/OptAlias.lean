import lemmas.Ska.OptTopo

/-!
# `+alias`: what it does, what it assumes, and the plan of its proof

`+alias` (`nock-compilation.hoon`, about line 8300, with the arms `rn`,
`join-info`, `join-imms`, `join-reg`, `param-info` at its end) is a symbolic
execution over `topo` that eliminates `%mov`s and other ops by renaming
registers, and folds branches whose test it knows.  It returns
`[folded new]`.

## Step by step

1. The state `gen`: `new` (the blocks made so far), `old` (an eliminated
   register to its alias; `rn r` is `(~(gut by old) r r)`, one lookup, not a
   chase), `info` and `imms` (the facts at the end of each walked block),
   `info-local` and `imms-local` (the facts while a block is walked), `rev`
   (the reverse CFG as a `jug`, edges deleted as branches fold), `folded`.
2. At a block `o` of `topo` with no predecessor left in `rev` that is not
   `0`: it became unreachable; `folded` is set, its edges are deleted from
   `rev`, and it is not put in `new` (so it is dropped).
3. The facts at the start of `o`: at `0`, `*info-reg` for the registers
   `0 .. n-args - 1`; otherwise `join-info` of the `info` of all predecessors
   (an intersection of the maps, joining the facts with `join-reg`; on two
   equal subtrees it returns the subtree as it is, which is not the pointwise
   `join-reg`: `join-reg a a` sets `is-loob` when `has-imm` is a loobean, so a
   model must follow the treap, as `+int:by` with that shortcut).  With one
   predecessor ending in `%brn`, `%brz` or `%clq`, the facts of the test
   register are refined by the side taken (`has-imm` `&`/`|`, `is-loob`,
   `is-cell`); the Hoon asserts (`?>`, `%brn-successor-lost`,
   `%clq-successor-lost`) that `o` is a target of that end.  `imms` likewise
   with `join-imms` (the register sets intersected, empty entries dropped).
4. The parameters keep their names and get `param-info` of the facts of the
   arguments passed on each edge into `o` (an edge passing `~` is skipped, and
   then facts naming registers are dropped).
5. The body (`+roll`, the new body built reversed and flopped): each op reads
   its registers through `rn`.  `%imm n d` is dropped, and `d` aliased, when
   a register already holds `n` (`imms-local`); `%mov s d` is always dropped
   with `d` aliased to `rn s`; `%inc`, `%con`, `%hed`, `%tal` are dropped when
   `dec-of`, `hed-of`/`tel-of`, `has-hed`/`has-tel` name a register with the
   same value; `%cel` when `is-cell` is known, `%lob` when `is-loob` or a
   loobean `has-imm` is known; the others are renamed and record what they
   define.
6. The end: `%clq` on a known cell or atom, `%eqq` of a register with itself,
   `%brn` on a known loobean, `%brz` on a known atom or cell become `%hop` to
   the side taken (`folded` set, the edge to the other side deleted from
   `rev` unless both sides are one block); `%brn` on a register known to be a
   loobean without a known value becomes `%brz` (`folded` set, no edge
   deleted); `%brn` on a known non-loobean value becomes `[%bom ~]` (both
   edges deleted, `folded` not set); the other ends are renamed.  The branches
   assert (`?>`) that their jumps pass no arguments.
7. `o` goes into `new` with its parameters, the new body and the new end,
   and its facts into `info` and `imms`.

## What it assumes

* `topo` lists the reachable blocks with every block before its successors
  and `rev` lists the predecessors (`TopoInv`): the facts of a block are the
  join over all its predecessors, each walked before it.
* An eliminated register is read only after the op that eliminated it, on
  every path (each register has one definition that dominates its reads, as
  in `+comp` output): `rn` renames reads in later blocks too, which is sound
  only if the alias holds the same value wherever the register is read.
* `ReadsOK`: a folded `%clq`, `%eqq`, `%brz`, `%brn` no longer reads its
  register, and a dropped `%cel`, `%lob`, `%inc`, `%con`, `%hed`, `%tal` no
  longer reads its operands.
* `LocalOK`: a dropped `%mov`, `%hed`, `%tal` would have crashed on a missing
  register or an atom.
* For the `DriverRest` field: `DInv` and `TopoInv` of the result with `topo`
  filtered by the blocks that remain.

For termination of `+optimize`, `folded` is set when a branch folds, when a
block is dropped, and also when a `%brn` becomes a `%brz` (step 6), so the
measure of `OptDriver.lean` needs the number of `%brn` ends beside the number
of blocks and two-way ends; `folded` is not set when a `%brn` becomes
`[%bom ~]`.

## Plan of the proof

1. Model the info maps as treaps (`join-info`, `join-imms` follow the shape;
   the facts are a function on keys only through `get`), `join-reg`,
   `param-info` (below), then the per-block transfer function (steps 3 to 7)
   as a function of `gen` and the block, and the walk over `topo`.
2. The facts are sound (`InfoOK`): on every path from the entry, at the
   start of a walked block, every fact of `info` holds of the registers
   (`is-cell`: a cell; `has-imm n`: the value `n`; `hed-of h`: the head of
   the value is in `h`; `dec-of`: one less; and so on), and `old` maps each
   eliminated register to one with the same value wherever it is read.  By
   induction on the path, with `TopoInv` for the join over predecessors and
   the refinement of step 3 at a one-predecessor block.
3. The simulation: the code after runs the renamed ops; the registers after
   are those before read through `rn`, so `Agr` over the set of registers
   that are not eliminated, composed with the renaming `rn` (`RenRel`,
   `execPole_ren` of `CompStraight.lean`), and the dropped ops are matched by
   no step, as in `OptDeadSim.lean` (`DeadI`, `dead_norm`): `LocalOK` runs
   them in the code before.  A folded branch takes the side the facts give,
   by `InfoOK`.  `execPole_agr` and `passLoop_agr` (`OptMiddleAgr.lean`) give
   the steps that agree off the eliminated registers.
4. Keep `EntryOK` (`ReadsOK`, `ArgsOK`, `LocalOK` of the code after from the
   backward simulation, as in `dead_keeps`), and prove `DInv`, `TopoInv` of
   the result (the blocks kept are those walked, their parameters kept, their
   jumps a subset of the old ones: `TargetsSub` of `OptDriverTopo.lean`).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Opt

open Nock

/-- `info-reg`: what `+alias` knows of a register. -/
structure InfoReg where
  isCell : Bool := false
  isLoob : Bool := false
  hedOf : List Nat := []
  telOf : List Nat := []
  hasHed : Option Nat := none
  hasTel : Option Nat := none
  decOf : Option Nat := none
  hasImm : Option Noun := none
  deriving DecidableEq

/-- `?=([~ ?] has-imm)`: a loobean immediate. -/
def InfoReg.loobImm (a : InfoReg) : Bool :=
  match a.hasImm with
  | some (Noun.atom 0) | some (Noun.atom 1) => true
  | _ => false

/-- `join-reg`. -/
def joinReg (a b : InfoReg) : InfoReg where
  isCell := a.isCell && b.isCell
  isLoob := (a.isLoob || a.loobImm) && (b.isLoob || b.loobImm)
  hedOf := a.hedOf.filter (· ∈ b.hedOf)
  telOf := a.telOf.filter (· ∈ b.telOf)
  hasHed := if a.hasHed = b.hasHed then a.hasHed else none
  hasTel := if a.hasTel = b.hasTel then a.hasTel else none
  decOf := if a.decOf = b.decOf then a.decOf else none
  hasImm := if a.hasImm = b.hasImm then a.hasImm else none

/-- `param-info`: the facts of a parameter from the facts of the arguments on
each edge (`none` for an edge that passes `~`). -/
def paramInfo (ins : List (Option InfoReg)) : InfoReg :=
  match ins.filterMap id with
  | [] => {}
  | h :: t =>
    let joined := t.foldl (fun b a => joinReg a b) h
    if (ins.filterMap id).length = ins.length then joined
    else { joined with hedOf := [], telOf := [], hasHed := none, hasTel := none, decOf := none }

end Opt
end SkaModel
end Formalization
