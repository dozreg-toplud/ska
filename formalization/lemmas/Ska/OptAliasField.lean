import lemmas.Ska.OptAliasModel
import lemmas.Ska.OptDriverSwitch

/-!
# The driver's field `alias` for the model, and what its proof must carry

## The statement

`DriverRestS.alias` asks of the pass, at blocks with `DInvT` and `TopoInv`,
that it keep the code (`KeepsB`), `DInvT`, and `TopoInv` of the filtered
`topo`.  For the model that is `AliasFieldM pick`, and
`driverRestS_of_aliasM` turns it into `DriverRestS` with the model as the
pass, so that `optimize_keeps_restS` would hold with no pass assumed.

## `AliasFieldM` is false: the pass needs single assignment

`+alias` renames a read of an eliminated register `d` to `rn d` in every later
block (`old` is global to the walk), which is sound only if the register
`rn d` is not written again between the eliminated op and the read.
`DInvT` does not say that.  Witness (`tools/hoon/aliasssa.hoon`, run on the
real pass): block `0` is `[%mov 0v1 0v2] [%imm 5 0v1]` ending in
`[%hop ~ 0w1]`, block `1` is `[%don 0v2]`, `n-args = 2`.  `+alias` drops the
`%mov` and makes block `1` `[%don 0v1]`; `+eval-blob` with registers
`0v0 = 0`, `0v1 = 7` gives `[%0 7]` before and `[%0 5]` after.  The blocks
have `DInvT` (no parameters, no hints, acyclic) and `TopoInv`, and every
`EntryOK` holds with two arguments, so `KeepsB` fails.  Raw `+comp` output
writes each register once, which is why no formula reaches this.

So the field must assume single assignment, `AliasSSA` (`DefOnce`: every
register has at most one definition, an op's destination or a block's
parameter, over the whole map; `DefFirst`: on every path of blocks from `0`, a
register that has a definition is read only after it).  `DefFirst` cannot be
weakened to "definitions above the argument registers", since `Keeps`
quantifies over every argument list `vals` (`regsOf vals` fills `0 ..`
`|vals| - 1`), so any register may be in the file at the entry.  The
corrected field is `AliasFieldSSA`, which must also give `AliasSSA` of the
result, and the driver must carry `AliasSSA` beside `DInvT` through every
pass (`+remove-hops` writes the parameters of a merged block by `%mov` and
drops them as parameters, `+remove-empty-middle` substitutes arguments,
`+remove-dead-code`, `+trim-trace-hints`, `+remove-useless-branching` only drop
definitions or reads).

## The invariant of the walk a proof would carry (`InfoOK`)

At the start of every walked block `o` and every execution of the code before
that reaches `o` from the entry with the register file `R`:

1. `imms o n ∋ r` gives `R r = some (some n)` (the immediates name only ops'
   destinations, never parameters, so they hold on every path, since the
   join intersects over all predecessors);
2. `info o r = some i` and `R r = some (some v)` give the facts of `i` of
   `v`: `isCell` a cell, `isLoob` `0` or `1`, `hasImm = some n` the value `n`,
   `hasHed = some d` that `R d` holds the head of `v` (`hasTel` the tail),
   `hedOf ∋ x` that `R x` holds a cell whose head is `v` (`telOf` the tail),
   `decOf = some d` that `R d` holds `v + 1`.  Facts hold only where the
   register holds a value, since a parameter passed `~` on one edge is
   poison there and `param-info` keeps `isCell`, `isLoob`, `hasImm` from the
   other edges (it drops only the facts that name registers);
3. `old d = s` for an eliminated `d` (with `d ≠ s`) gives: if the
   definition of `d` ran on the path, `R d = R s`.

It is established block by block in `topo` order: at `0` the facts are
`*info-reg` (no fact); at a join by `TopoInv` (every predecessor in `rev` and
walked before, so a fact of the intersection holds on every incoming path),
at a one-predecessor block by the side the test took (the refinement of
`aliasStart`), at a parameter by `paramInfo` of the facts of the arguments
on every edge (`PassOK` and `ParNodup` of `DInv`: the parameters are written
by the jump, distinct, and none is an argument); then op by op along the body
by the transfer function `aliasOp`, which needs `AliasSSA` so that a fact
about `r` is not invalidated by a later write of `r` or of a register the
fact names.  `ReadsOK` of `EntryOK` makes a register read for real hold a
value (so clause 2 applies at every test that folds and every `%cel`, `%lob`
that is dropped), `LocalOK` makes the dropped `%mov`, `%hed`, `%tal`, `%con`
of the code before succeed, and `ArgsOK` covers the moves of the jumps.

## Why the result keeps `TrimBr`

The pass drops only frameless ops (`%imm`, `%mov`, `%inc`, `%con`, `%hed`,
`%tal`, `%cel`, `%lob`, `%equ`), keeps every hint op, and renames the
registers in `%hdp`, `%hde` (the clue register of `TKey.clue`) and `%hmp`,
`%hme` (the registers of `TKey.defer`).  Under `AliasSSA` every read of a
register `r` is renamed to the same `ρ r`, with `ρ` the final `old` (a read
comes after the definition, in a block walked later, and `old r` is set once),
so the keys of the result are the keys of the input mapped by `ρ`.  The
rename **can merge two keys**: `ρ` is not injective (a `%mov` of a clue
register, two `%imm` of one constant, two `%hed` of one cell give one
register), which is the shape of the bug of `trimbug.hoon`.  `TrimBr` as now
stated (bracketing by equality of the key on top, counted, no distinctness)
survives a merge, since `brOp` compares keys by equality and equality is kept
by any function: `TrimBr bl K` gives `TrimBr bl' (fun o => (K o).map (·.map ρ))`
through `trimBr_of'`, with fewer jumps after a fold and none after `[%bom ~]`.

## What is proved here

Only `driverRestS_of_aliasM` (the field for the model gives `DriverRestS`)
and the definitions.  The soundness of `InfoOK`, the simulation and the
corrected field are open.
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock
variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

set_option linter.unusedSectionVars false

/-- **The field `alias` of `DriverRestS` for the model** (false as stated,
see the header). -/
def AliasFieldM (Map : Type → Type) [HoonMap Map] [MapKeys Map] (pick : List Nat → Nat) : Prop :=
  ∀ n (bl : Map Blob) topo rev f bl', DInvT bl → TopoInv bl topo rev → aliasM pick n bl rev topo = some (f, bl') →
    KeepsB bl bl' ∧ DInvT bl' ∧
      TopoInv bl' (topo.filter fun o => (HoonMap.get bl' o).isSome)
        (revCfg bl' (topo.filter fun o => (HoonMap.get bl' o).isSome))

/-- The field for the model gives the driver's hypothesis with the model as
the pass. -/
theorem driverRestS_of_aliasM {fuel sfuel : Nat} {P : Passes Map} {pick : List Nat → Nat}
    (h : AliasFieldM Map pick) (ha : P.alias = aliasM pick) (ht : P.trim = trimTraceHints)
    (hs : P.switch = switchChains sfuel) : DriverRestS fuel sfuel P :=
  ⟨by rw [ha]; exact h, ht, hs⟩

/-- The register an op writes. -/
def aliasDst : Pole → Option Nat
  | Pole.imm _ d => some d
  | Pole.mov _ d => some d
  | Pole.inc _ d => some d
  | Pole.con _ _ d => some d
  | Pole.hed _ d => some d
  | Pole.tal _ d => some d
  | Pole.spy _ _ d => some d
  | Pole.nok _ _ d => some d
  | Pole.cal _ _ d => some d
  | Pole.caf _ _ d _ => some d
  | Pole.cam _ _ d _ => some d
  | Pole.csl _ _ d => some d
  | Pole.csf _ _ d _ => some d
  | Pole.csm _ _ d _ => some d
  | _ => none

/-- The registers an op reads. -/
def aliasReads (op : Pole) : List Nat :=
  match aliasDst op with
  | some d => (poleRegs op).erase d
  | none => poleRegs op

/-- The definitions of a block: its parameters and the destinations of its
ops. -/
def blockDefs (b : Blob) : List Nat := b.par ++ b.body.filterMap aliasDst

/-- The definitions of the whole map. -/
def allDefs (bl : Map Blob) : List Nat :=
  (MapKeys.keys bl).flatMap fun o => ((HoonMap.get bl o).map blockDefs).getD []

/-- Every register is defined at most once. -/
def DefOnce (bl : Map Blob) : Prop := (allDefs bl).Nodup

/-- A path of blocks from `0` along jumps, the last block first. -/
inductive BPath (bl : Map Blob) : List Nat → Prop
  | start : BPath bl [0]
  | step {p : List Nat} {o : Nat} {b : Blob} {j : Jmp} :
      BPath bl (o :: p) → HoonMap.get bl o = some b → j ∈ getJmps b.fin → BPath bl (j.there :: o :: p)

/-- On every path of blocks from `0`, a register with a definition is read
(by an op at position `i`, or by the end at `i = |body|`) only after it is
defined: by a parameter of the block, an earlier op of it, or an earlier
block of the path. -/
def DefFirst (bl : Map Blob) : Prop :=
  ∀ o p b, BPath bl (o :: p) → HoonMap.get bl o = some b →
    ∀ i r, (r ∈ ((b.body.drop i).head?.map aliasReads).getD [] ∨ (i = b.body.length ∧ r ∈ finRegs b.fin)) →
      r ∈ allDefs bl →
      r ∈ b.par ∨ r ∈ (b.body.take i).filterMap aliasDst ∨
        ∃ o' ∈ p, ∃ b', HoonMap.get bl o' = some b' ∧ r ∈ blockDefs b'

/-- **Single assignment**, the hypothesis `+alias` needs beyond `DInvT`. -/
def AliasSSA (bl : Map Blob) : Prop := DefOnce bl ∧ DefFirst bl

/-- **The corrected field**: under `AliasSSA` the model keeps the code, the
invariants, and `AliasSSA` (open). -/
def AliasFieldSSA (Map : Type → Type) [HoonMap Map] [MapKeys Map] (pick : List Nat → Nat) : Prop :=
  ∀ n (bl : Map Blob) topo rev f bl', DInvT bl → AliasSSA bl → TopoInv bl topo rev →
    aliasM pick n bl rev topo = some (f, bl') →
    KeepsB bl bl' ∧ DInvT bl' ∧ AliasSSA bl' ∧
      TopoInv bl' (topo.filter fun o => (HoonMap.get bl' o).isSome)
        (revCfg bl' (topo.filter fun o => (HoonMap.get bl' o).isSome))

end Opt
end SkaModel
end Formalization
