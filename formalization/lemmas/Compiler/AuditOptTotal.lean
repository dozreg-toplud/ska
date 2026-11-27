import lemmas.Compiler.OptLinkTotalPass
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
#print axioms optimizeOnce_total
#print axioms optLoop_total
#print axioms optimizeF_total
#print axioms optHalts_of
#print axioms opt_gate_total_of
#print axioms mu_le_pw
#print axioms mu_lt_pw2
#print axioms afin_facts
#print axioms aw_flag
#print axioms alias_zero
#print axioms aliasM_step
#print axioms trimWalk_isSome
#print axioms stInv_shape
#print axioms trim_step
#print axioms stInv_of
#print axioms passTotal_of
#print axioms opt_gate_total

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
#guard (mu ρx [0, 1, 2] xaBlocks) == (3, 2, 17)
#guard ((aliasM (fun l => l.headD 0) 1 xaBlocks (revCfg xaBlocks [0, 1, 2]) [0, 1, 2]).map
  fun r => (r.1, mu ρx [0, 1, 2] r.2)) == some (true, (1, 0, 0))
-- `+remove-useless-branching` turns the `%brn` of `xaBlocks`, whose two
-- targets are equal blocks, into a hop: the weight of the ends falls by 2.
#guard (removeUselessBranching xaBlocks).map (fun r => (r.1, mu ρx [0, 1, 2] r.2)) == some (true, (3, 0, 9))
#guard (removeEmptyMiddle 10 xaBlocks).map (·.1) == some false
#guard (bbTopo 10 xaBlocks) == some [0, 2, 1]

/-- **A finding on the measure**: `+alias` reports a change (`folded`) when it
turns a `%brn` whose test register is known to be a loob into a `%brz`, which
keeps the blocks, the two-way ends and the targets.  With every two-way end
of weight `1` the measure stayed `(3, 1, 17)` while the loop of `+optimize`
went on; with a `%brn` of weight `2` (`twoW`) it falls from `(3, 2, 17)` to
`(3, 1, 17)`.  The real compiler does the same (`xbcheck.hoon` in the
report of 2026-11-27): `+alias` returns `folded=%.y` with the `%brz`, and
`+optimize` returns after two rounds. -/
def xbBlocks : LM Blob :=
  ⟨[(0, ⟨[], [Pole.lob 1], Termin.brn 1 ⟨[], 1⟩ ⟨[], 2⟩⟩), (1, ⟨[], [], Termin.don 1⟩),
    (2, ⟨[], [], Termin.don 0⟩)]⟩

#guard (mu ρx [0, 1, 2] xbBlocks) == (3, 2, 17)
#guard ((aliasM (fun l => l.headD 0) 2 xbBlocks (revCfg xbBlocks [0, 1, 2]) [0, 1, 2]).map
  fun r => (r.1, mu ρx [0, 1, 2] r.2, (HoonMap.get r.2 0).map (·.fin))) ==
  some (true, (3, 1, 17), some (Termin.brz 1 ⟨[], 1⟩ ⟨[], 2⟩))

/-- `LexLt` as a test. -/
def lexLtB : Nat × Nat × Nat → Nat × Nat × Nat → Bool
  | (a', b', c'), (a, b, c) => a' < a || (a' == a && (b' < b || (b' == b && c' < c)))

-- the measure falls on every change of `+alias` on the examples
#guard ((aliasM (fun l => l.headD 0) 2 xbBlocks (revCfg xbBlocks [0, 1, 2]) [0, 1, 2]).map
  fun r => lexLtB (mu ρx [0, 1, 2] r.2) (mu ρx [0, 1, 2] xbBlocks)) == some true
#guard ((aliasM (fun l => l.headD 0) 1 xaBlocks (revCfg xaBlocks [0, 1, 2]) [0, 1, 2]).map
  fun r => lexLtB (mu ρx [0, 1, 2] r.2) (mu ρx [0, 1, 2] xaBlocks)) == some true
-- a second `+alias` on the result of the first reports no change
#guard ((aliasM (fun l => l.headD 0) 2 xbBlocks (revCfg xbBlocks [0, 1, 2]) [0, 1, 2]).bind
  fun r => (aliasM (fun l => l.headD 0) 2 r.2 (revCfg r.2 [0, 1, 2]) [0, 1, 2]).map (·.1)) == some false

-- `+trim-trace-hints` returns on the examples and keeps the measure
#guard (trimTraceHints xaBlocks [0, 2, 1] (revCfg xaBlocks [0, 2, 1])).map (mu ρx [0, 1, 2]) == some (3, 2, 17)
#guard (trimTraceHints xbBlocks [0, 2, 1] (revCfg xbBlocks [0, 2, 1])).map (mu ρx [0, 1, 2]) == some (3, 2, 17)
-- `+alias` returns on the examples (`AliasRet`), with the `topo` of `+bb-topo`
#guard (bbTopo 10 xbBlocks) == some [0, 2, 1]
#guard (aliasM (fun l => l.headD 0) 2 xbBlocks (revCfg xbBlocks [0, 2, 1]) [0, 2, 1]).isSome
#guard (aliasM (fun l => l.headD 0) 1 xaBlocks (revCfg xaBlocks [0, 2, 1]) [0, 2, 1]).isSome
#guard (aliasM (fun l => l.headD 0) 1 xhBlocks (revCfg xhBlocks [0, 1]) [0, 1]).isSome
-- `+switch-chains` returns on the examples (`SwitchRet`)
#guard (switchChains 10 xaBlocks).isSome && (switchChains 10 xbBlocks).isSome && (switchChains 10 xhBlocks).isSome
-- `+optimize` returns on `xbBlocks` after two rounds, as on the real compiler
#guard ((optLoop 10 ⟨aliasM (fun l => l.headD 0), trimTraceHints, switchChains 10⟩ 2
  ⟨NeedOrd.none, 2, xbBlocks⟩).map fun s => (HoonMap.get s.blocks 0).map (·.fin)) ==
  some (some (Termin.brz 1 ⟨[], 1⟩ ⟨[], 2⟩))

end AuditOptTotal
