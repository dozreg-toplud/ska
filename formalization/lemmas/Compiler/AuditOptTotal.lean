import lemmas.Compiler.OptLinkTotalAlias
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


/-! ## The walk invariant of `+alias`, checked at every step on the examples

`walkStates` lists the state before each block of `topo`; `walkInvB` checks,
for registers below `R`: (W0) every `p ∈ g.rev o` of the next block `o` is
walked; (W1) every walked `p ∈ g.rev o` of an unwalked `o` has `g.new p`, `g.info p`, `g.imms p` set and an end that jumps to
`o`, and a one-predecessor `%brn` / `%clq` / `%brz` has a fact for its test
register; (W2) the facts of a walked block refer only to registers with a
fact; (W3) a walked block that was kept has a fact for `g.old r` for every
`r` below `n` or defined on every path from `0` to it (`DefFirst`). -/

def walkStates (pick : List Nat → Nat) (n : Nat) (bl : LM Blob) : List Nat → AGen LM → List (List Nat × AGen LM)
  | [], g => [([], g)]
  | o :: t, g => (o :: t, g) :: match aliasBlock pick n bl g o with
    | some g' => walkStates pick n bl t g'
    | none => []

def refsB (f : InfoReg) : List Nat := f.hedOf ++ f.telOf ++ f.hasHed.toList ++ f.hasTel.toList ++ f.decOf.toList

/-- The paths of blocks from `0` to `p` (the last block first), with fuel. -/
def pathsTo (bl : LM Blob) : Nat → Nat → List (List Nat)
  | 0, _ => []
  | k + 1, p => if p = 0 then [[0]] else
    (bl.l.map Prod.fst).flatMap fun q => match HoonMap.get bl q with
      | some b => if (getJmps b.fin).any (·.there = p) then (pathsTo bl k q).map (p :: ·) else []
      | none => []

def defOnAll (bl : LM Blob) (p r : Nat) : Bool :=
  (pathsTo bl 6 p).all fun path => path.any fun q => ((HoonMap.get bl q).map fun b => (blockDefs b).contains r).getD false

def testReg : Termin → Option Nat
  | Termin.clq s _ _ => some s
  | Termin.brn s _ _ => some s
  | Termin.brz s _ _ => some s
  | _ => none

def walkInvB (R n : Nat) (bl : LM Blob) (topo : List Nat) : List Nat × AGen LM → Bool
  | (rest, g) =>
    let walked := topo.filter (· ∉ rest)
    (match rest with
      | o :: _ => (g.rev o).all (· ∈ walked)
      | [] => true) &&
    (rest.all fun o => (g.rev o).all fun p => p ∉ walked ||
      match HoonMap.get g.new p, g.info p, g.imms p with
      | some pb, some ip, some _ => (getJmps pb.fin).any (·.there = o) &&
          (g.rev o != [p] || (testReg pb.fin).all fun s => (ip s).isSome)
      | _, _, _ => false) &&
    (walked.all fun p => match g.info p with
      | some ip => (List.range R).all fun k => match ip k with
        | some f => (refsB f).all fun x => (ip x).isSome
        | none => true
      | none => true) &&
    (walked.all fun p => match g.info p with
      | some ip => (List.range R).all fun r => !(decide (r < n) || defOnAll bl p r) || (ip (g.old r)).isSome
      | none => true)

#guard (walkStates (fun l => l.headD 0) 1 xaBlocks [0, 2, 1] (aliasInit (revCfg xaBlocks [0, 2, 1]))).all
  (walkInvB 8 1 xaBlocks [0, 2, 1])
#guard (walkStates (fun l => l.headD 0) 2 xbBlocks [0, 2, 1] (aliasInit (revCfg xbBlocks [0, 2, 1]))).all
  (walkInvB 8 2 xbBlocks [0, 2, 1])
#guard (walkStates (fun l => l.headD 0) 1 xhBlocks [0, 1] (aliasInit (revCfg xhBlocks [0, 1]))).all
  (walkInvB 8 1 xhBlocks [0, 1])
-- the walks are complete (one state per block, and the last)
#guard (walkStates (fun l => l.headD 0) 2 xbBlocks [0, 2, 1] (aliasInit (revCfg xbBlocks [0, 2, 1]))).length == 4
-- the witness of `not_aliasRet`: `wBl` reads register `1`, which `n = 1` does not give
#guard (aliasM (fun l => l.headD 0) 1 AliasWit.wBl (revCfg AliasWit.wBl [0]) [0]).isNone
#guard (aliasM (fun l => l.headD 0) 2 AliasWit.wBl (revCfg AliasWit.wBl [0]) [0]).isSome
-- a `pick` that does not pick a member makes the model crash
def wPick : LM Blob := ⟨[(0, ⟨[], [Pole.imm (Nock.A 5) 1, Pole.imm (Nock.A 5) 2, Pole.inc 2 3], Termin.bom none⟩)]⟩
#guard (aliasM (fun _ => 7) 0 wPick (revCfg wPick [0]) [0]).isNone
#guard (aliasM (fun l => l.headD 0) 0 wPick (revCfg wPick [0]) [0]).isSome

end AuditOptTotal
#print axioms switchRet_of
#print axioms switchChains_some
#print axioms stree_some
#print axioms chainOf_some
#print axioms plainsOf_some
#print axioms not_aliasRet
#print axioms aliasOp_some
#print axioms aliasFin_some
