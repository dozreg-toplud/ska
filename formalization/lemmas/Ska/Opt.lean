import lemmas.Ska.ExecPath

/-!
# `+optimize`: what each pass does, what it assumes, what it must keep

`+optimize` (`nock-compilation.hoon`, about line 9367) loops `+optimize-once`
until no pass says it changed anything, then runs `+switch-chains` once.
`+optimize-once` runs the structural passes `+remove-hops`,
`+remove-useless-branching`, `+remove-empty-middle` to a fixed point
(recomputing `topo` by `+bb-topo` and `rev` by `+rev-cfg` after a change),
then `+alias`, then `+trim-trace-hints`, `+remove-dead-code`, and the three
structural passes once more.  The passes act on `blob` (whose `termin` has no
`%lti`); the Lean models act on `Blob` and `Termin` of `Types.lean`, whose
`Termin` also has `%lti`, which no pass meets before `+switch-chains` (the
models treat it as the Hoon's default case, or as a branch in `getJmps`).

## The passes, from the Hoon

`+remove-useless-branching` (8981, `OptBranch.lean`).  For every block (a
`+rep:by`; the result does not depend on its order, since each new value
depends only on the old map and the flag is an `|`), a `%clq`, `%eqq`, `%brn`
or `%brz` whose two jumps pass no arguments (asserted with `?>`: a crash
otherwise) and whose two target blocks are equal nouns becomes
`[%hop ~ there.z]`.  `%eqq` gets the epilogue `[%equ l r]` and `%brn` gets
`[%lob s]`, which keep the crash on a missing or poisoned register and the
boom of a non-loobean.  `%clq` and `%brz` get no epilogue, so the read of
their test register is dropped: the code before may crash at that read where
the code after goes on.  It assumes nothing of the CFG.

`+remove-hops` (8813, `OptHops.lean`).  Walks `topo`; at a block `o` not
yet merged it follows the `%hop` of the block being built to `o1` as long
as the only predecessor of `o1` in `rev` is `o` (the current end of the
chain; `?<  =(~ pre-o1)` asserts it has one), and appends the body of `o1`,
preceded by one op per argument of the hop: `[%mov a p]` for an argument
`a`, `[%imm 0 p]` for an argument `~`.  The new map holds only the blocks of
`topo` that were not merged; the flag says whether something was merged.  It
assumes that `rev` is the reverse CFG of the blocks reachable from `0` and
that `topo` lists them with every block before its successors (`+bb-topo` on
an acyclic CFG), so that `0` is never merged and a merged block is reached
only through its one predecessor.  **Poison becomes a value**: an argument
`~` poisons its parameter in the code before and writes `0` to it in the
code after.  That is sound because a poisoned register is never really read
on an execution that does not crash (`run_poison`): with `ReadsOK` (every
real read on every path from the entry reads a value), a register the code
before holds poisoned is read for real by no step, only moved, and a move of
`0` where the code before moves poison keeps the registers of the code after
above those of the code before in the order `none ≤ some v` on the unit.

`+remove-empty-middle` (9029, `OptMiddle.lean`).  For every block (a
`+rep:by`, order irrelevant as above), each jump of a branch that passes
nothing to an empty block (no ops, a `%hop` that passes nothing; `?>` asserts
the empty block has no parameters) is redirected to that hop's target,
repeatedly (`rewrite-jump`).  A `%hop` to an empty block that ends in a
`%hop` is redirected to its target when no parameter of the empty block is
mentioned (`readers`, from `+get-regs` of every op and terminator) by any
block but the empty one itself; the arguments of the second hop are those of
the first substituted for the parameters (`rewrite-hop`), so an argument `~`
stays `~`: poison stays poison.  The bypassed blocks stay in the map.  Both
loops end only if the chain of empty blocks is not a cycle (an acyclic CFG).
The parameters of a bypassed block lose their definition, which is sound
because nothing else mentions them.  `+eval-pass` checks that no argument is a
parameter of the target: a substituted argument that is a parameter of the
final target would make the code after crash where the code before ran, so
the preservation statement needs that no such argument occurs (it holds when
a block's parameters are defined only by the jumps into it).

`+remove-dead-code` (8873, `OptDead.lean`).  Walks `rev-topo` (the reverse
of `topo`, so successors first) with one set `saw` of registers for the whole
walk: at each block it adds `+get-regs` of the terminator, then walks the
body from its end, dropping an op whose `+get-reg-safe-assignment` (`%imm`,
`%mov`, `%con`, `%hed`, `%tal`) writes a register not in `saw` and adding
`+get-regs` of every op it keeps.  The new map holds only the blocks of
`rev-topo`.  It assumes that `rev-topo` lists every reachable block after all
its successors (an acyclic CFG).  The ops it may drop can crash in the
interpreter (`%hed`/`%tal` of an atom, `%con` of a poisoned register, `%mov` of
a missing one), so its preservation needs, beyond `ReadsOK`, that no dropped
op crashes on an execution (`LocalOK`, part of `EntryOK`).

`+alias`, `+trim-trace-hints` and `+switch-chains` are parameters of the
driver (`OptDriver.lean`), assumed to keep the semantics.

## The semantic statement

For an entry `(st, vals, t, gul)`, `ReadsOK c` says that every real read on
every path of `c` from the entry reads a value.  A pass from `c` to `c'`
**keeps** `c` (`Keeps c c'`) when `c'` has the need and the argument count of
`c`, its block `0` has the parameters of that of `c` (which `topBody`
checks), and for every entry with `ReadsOK c`, `ArgsOK c` and `LocalOK c`
(`EntryOK`):
`execEntry` of `c'` returns exactly what `execEntry` of `c` returns (the same
product, the same crash with the same trace, the same block on a scry, and
`none` together), and `EntryOK c'` holds.  `ArgsOK` (every register a pending
pass moves is in the file) is there for `+remove-empty-middle`, which drops
such moves (`OptMiddleSim.lean`), and `LocalOK` (no op that
`+get-reg-safe-assignment` names crashes) for `+remove-dead-code`, which drops
such ops (`OptDeadSim.lean`).  `Keeps` is reflexive and transitive
(`keeps_refl`, `keeps_trans`), so the driver composes the passes.  `KeepsR`
is the form with `ReadsOK` alone, in which the simulations of
`+remove-useless-branching` and `+remove-hops` are proved; `keeps_of_R`
adds `ArgsOK` and `LocalOK` kept.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Opt

open Nock

variable {Map : Type → Type} [HoonMap Map]

/-- The keys of a map in the order of `+rep:by` and `+tap:by` (the pre-order
of the treap, for `TreapMap`). -/
class MapKeys (Map : Type → Type) [HoonMap Map] where
  keys : {ν : Type} → Map ν → List Nat
  mem_keys {ν : Type} (m : Map ν) (k : Nat) : k ∈ keys m ↔ (HoonMap.get m k).isSome
  nodup {ν : Type} (m : Map ν) : (keys m).Nodup

/-- `+get-jmps`, with `%lti` a branch. -/
def getJmps : Termin → List Jmp
  | Termin.clq _ z o => [z, o]
  | Termin.eqq _ _ z o => [z, o]
  | Termin.brn _ z o => [z, o]
  | Termin.brz _ z o => [z, o]
  | Termin.lti _ _ z o => [z, o]
  | Termin.hop t => [t]
  | _ => []

/-- `+jmp-regs`. -/
def jmpRegs (j : Jmp) : List Nat := j.args.filterMap id

/-- `+get-regs` of a terminator. -/
def finRegs : Termin → List Nat
  | Termin.clq s z o => s :: (jmpRegs z ++ jmpRegs o)
  | Termin.eqq l r z o => l :: r :: (jmpRegs z ++ jmpRegs o)
  | Termin.brn s z o => s :: (jmpRegs z ++ jmpRegs o)
  | Termin.brz s z o => s :: (jmpRegs z ++ jmpRegs o)
  | Termin.lti _ s z o => s :: (jmpRegs z ++ jmpRegs o)
  | Termin.hop t => jmpRegs t
  | Termin.jmp _ v => v
  | Termin.jmf _ v _ => v
  | Termin.jsp _ s => [s]
  | Termin.jsf _ s _ => [s]
  | Termin.don s => [s]
  | Termin.bom _ => []

/-- `+get-regs` of an op. -/
def poleRegs : Pole → List Nat
  | Pole.imm _ d => [d]
  | Pole.mov s d => [s, d]
  | Pole.inc s d => [s, d]
  | Pole.con h t d => [h, t, d]
  | Pole.hed s d => [s, d]
  | Pole.tal s d => [s, d]
  | Pole.cel p => [p]
  | Pole.lob p => [p]
  | Pole.equ l r => [l, r]
  | Pole.hsp _ _ => []
  | Pole.hse _ _ => []
  | Pole.hdp _ p _ => [p]
  | Pole.hde _ p _ => [p]
  | Pole.hmp _ v _ => v
  | Pole.hme _ v _ => v
  | Pole.hcp _ _ => []
  | Pole.hce _ _ => []
  | Pole.spy e p d => [e, p, d]
  | Pole.nok u f d => [u, f, d]
  | Pole.cal _ v d => d :: v
  | Pole.caf _ v d _ => d :: v
  | Pole.cam _ v d _ => d :: v
  | Pole.csl _ s d => [s, d]
  | Pole.csf _ s d _ => [s, d]
  | Pole.csm _ s d _ => [s, d]

/-! ## The semantic statement -/

section
variable {σ : Type}

/-- Every real read on every path of `c` from the entry reads a value. -/
def ReadsOK (lib : Lib) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (vals : List Noun)
    (t : Trace) : Prop :=
  ∀ es y k, Path.FromEntry (lib := lib) (O := O) (c := c) (gul := gul) st vals t es y →
    Path.ReadsAt gul y k → ∃ v, read k y.regs = some v

/-- Every register a pending pass on a path from the entry moves is there
(`+move` crashes on a register that is not, poison included only when it is
there).  `+remove-empty-middle` needs it: the code before moves the arguments
of a bypassed hop into parameters that nothing reads, and would crash where
the code after, which skips that pass, goes on. -/
def ArgsOK (lib : Lib) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (vals : List Noun)
    (t : Trace) : Prop :=
  ∀ es y k, Path.FromEntry (lib := lib) (O := O) (c := c) (gul := gul) st vals t es y → some k ∈ y.params →
    (HoonMap.get y.regs k).isSome

/-- `+get-reg-safe-assignment`: the register an op of `%imm`, `%mov`, `%con`,
`%hed`, `%tal` writes, the ops `+remove-dead-code` may drop. -/
def safeAssign : Pole → Option Nat
  | Pole.imm _ d => some d
  | Pole.mov _ d => some d
  | Pole.con _ _ d => some d
  | Pole.hed _ d => some d
  | Pole.tal _ d => some d
  | _ => none

/-- No op that `+get-reg-safe-assignment` names crashes on a path from the
entry: a `%hed` or `%tal` finds a cell, a `%con` finds two values, a `%mov`
finds its register in the file (`%imm` never crashes).  On raw `+comp`
output a `%hed` or `%tal` of a register not known to be a cell comes after
the `%cel` op that `+comp` emits as its own op, which booms on an atom, so
on every path that reaches the `%hed` the register holds a cell. -/
def LocalOK (lib : Lib) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (vals : List Noun)
    (t : Trace) : Prop :=
  ∀ es y p rest, Path.FromEntry (lib := lib) (O := O) (c := c) (gul := gul) st vals t es y →
    y.params = [] → y.b.par = [] → y.b.body = p :: rest → (safeAssign p).isSome →
    (execPole lib O gul y.st p y.regs y.t).isSome

end

section
variable {σ : Type}

/-- What `Keeps` assumes of an entry and keeps: `ReadsOK`, `ArgsOK` and
`LocalOK`. -/
def EntryOK (lib : Lib) (O : Oracle σ) (c : Straight Map) (gul : Noun) (st : σ) (vals : List Noun)
    (t : Trace) : Prop :=
  ReadsOK lib O c gul st vals t ∧ ArgsOK lib O c gul st vals t ∧ LocalOK lib O c gul st vals t

end

/-- **A pass from `c` to `c'` keeps `c`**: the same need, argument count and
parameters of block `0`, and on every entry with `ReadsOK` and `ArgsOK`
(`EntryOK`) the same `execEntry`, with `EntryOK` of the code after. -/
def Keeps (c c' : Straight Map) : Prop :=
  c'.need = c.need ∧ c'.nargs = c.nargs ∧
  (HoonMap.get c'.blocks 0).map Blob.par = (HoonMap.get c.blocks 0).map Blob.par ∧
  ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (gul : Noun) (st : σ) (vals : List Noun) (t : Trace),
    EntryOK lib O c gul st vals t →
      execEntry lib O st c' vals t gul = execEntry lib O st c vals t gul ∧ EntryOK lib O c' gul st vals t

/-- `Keeps` with `ReadsOK` alone, the form in which the simulations of
`+remove-useless-branching` and `+remove-hops` are proved first. -/
def KeepsR (c c' : Straight Map) : Prop :=
  c'.need = c.need ∧ c'.nargs = c.nargs ∧
  (HoonMap.get c'.blocks 0).map Blob.par = (HoonMap.get c.blocks 0).map Blob.par ∧
  ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (gul : Noun) (st : σ) (vals : List Noun) (t : Trace),
    ReadsOK lib O c gul st vals t →
      execEntry lib O st c' vals t gul = execEntry lib O st c vals t gul ∧ ReadsOK lib O c' gul st vals t

/-- `KeepsR` with `ArgsOK` and `LocalOK` kept gives `Keeps`. -/
theorem keeps_of_R {c c' : Straight Map} (h : KeepsR c c')
    (ha : ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (gul : Noun) (st : σ) (vals : List Noun) (t : Trace),
      EntryOK lib O c gul st vals t → ArgsOK lib O c' gul st vals t ∧ LocalOK lib O c' gul st vals t) :
    Keeps c c' := by
  obtain ⟨n, a, p, s⟩ := h
  refine ⟨n, a, p, fun lib σ O gul st vals t hE => ?_⟩
  obtain ⟨e, r⟩ := s lib σ O gul st vals t hE.1
  exact ⟨e, r, ha lib σ O gul st vals t hE⟩

theorem keeps_refl (c : Straight Map) : Keeps c c :=
  ⟨rfl, rfl, rfl, fun _ _ _ _ _ _ _ h => ⟨rfl, h⟩⟩

theorem keeps_trans {c c' c'' : Straight Map} (h : Keeps c c') (h' : Keeps c' c'') : Keeps c c'' := by
  obtain ⟨n1, a1, p1, s1⟩ := h
  obtain ⟨n2, a2, p2, s2⟩ := h'
  refine ⟨n2.trans n1, a2.trans a1, p2.trans p1, fun lib σ O gul st vals t hr => ?_⟩
  obtain ⟨e1, r1⟩ := s1 lib σ O gul st vals t hr
  obtain ⟨e2, r2⟩ := s2 lib σ O gul st vals t r1
  exact ⟨e2.trans e1, r2⟩

/-- A pass on the blocks keeps the need and the argument count. -/
def withBlocks (c : Straight Map) (bl : Map Blob) : Straight Map := { c with blocks := bl }

end Opt
end SkaModel
end Formalization
