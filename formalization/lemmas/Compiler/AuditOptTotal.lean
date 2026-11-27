import lemmas.Compiler.OptLinkTotalGate
import lemmas.Ska.OptAliasPlainDriver

/-! `#print axioms` of the converse of `+optimize` (`OptLinkTotal*.lean`),
and checks of the facts it proves and assumes on the example block maps of
`OptAliasPlainDriver.lean` (`xhBlocks`, `xaBlocks`) and `OptAliasWitness.lean`
(`vBlocks`, `wBlocks`), on the map `LM`. -/

open Formalization Compiler SkaModel

#print axioms stable_of_mono
#print axioms bbTopo_stable
#print axioms removeHops_stable
#print axioms removeEmptyMiddle_stable
#print axioms lex_induction
#print axioms rub_isSome
#print axioms rub_inv_step
#print axioms mid_inv_step
#print axioms hops_drop
#print axioms hops_inv_step
#print axioms structLoop_total
#print axioms structEntry_total
#print axioms dead_step
#print axioms structLoop_J
#print axioms optimizeOnce_total
#print axioms optLoop_total
#print axioms optimizeF_total
#print axioms optHalts_of
#print axioms opt_gate_total_of

namespace AuditOptTotal
open Opt

/-- A rank for the examples: the label's distance from the bottom. -/
def ρx (o : Nat) : Nat := 10 - o

-- `+remove-hops` merges block `1` into block `0`: one block fewer.
#guard (mu ρx [0, 1] xhBlocks) == (2, 0, 9)
#guard ((removeHops 10 xhBlocks (revCfg xhBlocks [0, 1]) [0, 1]).map fun r => (r.1, mu ρx [0, 1] r.2)) ==
  some (true, (1, 0, 0))
-- `+alias` folds the `%brn` of block `0` and drops blocks `1` and `2`: the
-- measure falls from three blocks to one.
#guard (mu ρx [0, 1, 2] xaBlocks) == (3, 1, 17)
#guard ((aliasM (fun l => l.headD 0) 1 xaBlocks (revCfg xaBlocks [0, 1, 2]) [0, 1, 2]).map
  fun r => (r.1, mu ρx [0, 1, 2] r.2)) == some (true, (1, 0, 0))
-- `+remove-useless-branching` turns the `%brn` of `xaBlocks`, whose two
-- targets are equal blocks, into a hop: one two-way end fewer.
#guard (removeUselessBranching xaBlocks).map (fun r => (r.1, mu ρx [0, 1, 2] r.2)) == some (true, (3, 0, 9))
#guard (removeEmptyMiddle 10 xaBlocks).map (·.1) == some false
#guard (bbTopo 10 xaBlocks) == some [0, 2, 1]

/-- **A finding on the measure**: `+alias` reports a change (`folded`) when it
turns a `%brn` whose test register is known to be a loob into a `%brz`, which
keeps the blocks, the two-way ends and the targets, so `mu` stays the same
while the loop of `+optimize` goes on (the field `alias` of `PassTotal`
fails here).  The number of `%brn` ends falls, so a measure that counts a
`%brn` above the other two-way ends would decrease. -/
def xbBlocks : LM Blob :=
  ⟨[(0, ⟨[], [Pole.lob 1], Termin.brn 1 ⟨[], 1⟩ ⟨[], 2⟩⟩), (1, ⟨[], [], Termin.don 1⟩),
    (2, ⟨[], [], Termin.don 0⟩)]⟩

#guard (mu ρx [0, 1, 2] xbBlocks) == (3, 1, 17)
#guard ((aliasM (fun l => l.headD 0) 2 xbBlocks (revCfg xbBlocks [0, 1, 2]) [0, 1, 2]).map
  fun r => (r.1, mu ρx [0, 1, 2] r.2, (HoonMap.get r.2 0).map (·.fin))) ==
  some (true, (3, 1, 17), some (Termin.brz 1 ⟨[], 1⟩ ⟨[], 2⟩))

end AuditOptTotal
