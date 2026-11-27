import lemmas.Compiler.AuditOptTotal
import lemmas.Compiler.OptLinkTotalFinal

/-!
# Check: every pass of the driver keeps `ReadsIn nargs` (track H, Gaps 13)

`readsB n bl`, the decidable `ReadsIn n bl` (on the blocks reachable from
`0`, `reachB` of `AuditOptTotal.lean`).  `rounds` runs up to eight rounds of
`+optimize-once` with the model passes (`pick` the head of its list) and
records `(pass, readsB)` after every pass: `1`..`3` the structural passes
inside the structural loop (each turn), `4` `+alias`, `5`
`+trim-trace-hints`, `6` `+remove-dead-code`, `7`..`9` the structural
passes after it, `10` `+switch-chains` at the end.  It holds after every
pass on the three examples and on all 4,080 raw outputs of `enumX`
(57,042 checks).  Then the axioms of the theorems of `OptLinkTotalN.lean`,
`OptLinkTotalReads.lean`, `OptLinkTotalFinal.lean`.
-/

namespace Formalization
namespace Compiler
namespace ReadsCheck

open SkaModel Opt AuditOptTotal

def readsB (n : Nat) (bl : LM Blob) : Bool :=
  bl.l.all fun (o, b) => !reachB bl o ||
    ((List.range (b.body.length + 1)).all fun i =>
      ((((b.body.drop i).head?.map aliasReads).getD []) ++ (if i = b.body.length then finRegs b.fin else [])).all
        fun r => (allDefsB bl).contains r || decide (r < n))

/-- the structural loop with a check after every pass; returns the final state and the list of (pass id, ok) -/
def sloop (fuel n N : Nat) (bl : LM Blob) (topo : List Nat) (rev : LM (List Nat)) (acc : List (Nat × Bool)) :
    Option (List Nat × LM (List Nat) × LM Blob) × List (Nat × Bool) :=
  match n with
  | 0 => (none, acc)
  | n + 1 =>
    match removeHops fuel bl rev topo with
    | none => (none, acc)
    | some r1 =>
      let acc := (1, readsB N r1.2) :: acc
      match removeUselessBranching r1.2 with
      | none => (none, acc)
      | some r2 =>
        let acc := (2, readsB N r2.2) :: acc
        match removeEmptyMiddle fuel r2.2 with
        | none => (none, acc)
        | some r3 =>
          let acc := (3, readsB N r3.2) :: acc
          if !(r1.1 || r2.1 || r3.1) then (some (topo, rev, r3.2), acc) else
          match bbTopo fuel r3.2 with
          | none => (none, acc)
          | some topo' => sloop fuel n N r3.2 topo' (revCfg r3.2 topo') acc

def P0 : Passes LM := ⟨aliasM (fun l => l.headD 0), trimTraceHints, switchChains 30⟩

def once (fuel : Nat) (s : Straight LM) (acc : List (Nat × Bool)) : Option (Bool × Straight LM) × List (Nat × Bool) :=
  match bbTopo fuel s.blocks with
  | none => (none, acc)
  | some topo0 =>
    match sloop fuel fuel s.nargs s.blocks topo0 (revCfg s.blocks topo0) acc with
    | (none, acc) => (none, acc)
    | (some r, acc) =>
      match P0.alias s.nargs r.2.2 r.2.1 r.1 with
      | none => (none, (4, false) :: acc)
      | some ra =>
        let acc := (4, readsB s.nargs ra.2) :: acc
        let topo := r.1.filter fun o => (HoonMap.get ra.2 o).isSome
        let rev := revCfg ra.2 topo
        match P0.trim ra.2 topo rev with
        | none => (none, acc)
        | some bt =>
          let acc := (5, readsB s.nargs bt) :: acc
          match removeDeadCode bt topo.reverse with
          | none => (none, acc)
          | some bd =>
            let acc := (6, readsB s.nargs bd) :: acc
            match removeHops fuel bd rev topo with
            | none => (none, acc)
            | some r1 =>
              let acc := (7, readsB s.nargs r1.2) :: acc
              match removeUselessBranching r1.2 with
              | none => (none, acc)
              | some r2 =>
                let acc := (8, readsB s.nargs r2.2) :: acc
                match removeEmptyMiddle fuel r2.2 with
                | none => (none, acc)
                | some r3 =>
                  let acc := (9, readsB s.nargs r3.2) :: acc
                  (some (ra.1 || r1.1 || r2.1 || r3.1, withBlocks s r3.2), acc)

def rounds : Nat → Straight LM → List (Nat × Bool) → List (Nat × Bool)
  | 0, _, acc => acc
  | k + 1, s, acc =>
    match once 30 s acc with
    | (some (ch, s'), acc) => if ch then rounds k s' acc else
        match P0.switch s'.blocks with
        | some b => (10, readsB s'.nargs b) :: acc
        | none => (10, false) :: acc
    | (none, acc) => (0, false) :: acc

def raws : List (Straight LM) := (Raw.enumX.filterMap Raw.naryX).map fun s => (⟨s.need, s.nargs, ⟨Raw.blocksOf s.blocks⟩⟩ : Straight LM)
def exs : List (Straight LM) := match raws with | s :: _ => [⟨s.need, 1, xaBlocks⟩, ⟨s.need, 2, xbBlocks⟩, ⟨s.need, 1, xhBlocks⟩] | [] => []

def allOk (s : Straight LM) : Bool := (rounds 8 s []).all (·.2)

#guard exs.length == 3 && exs.all allOk
#guard raws.length == 4080
#guard raws.all allOk
-- the number of checks: every pass of every round on every output
#guard (raws.foldl (fun n s => n + (rounds 8 s []).length) 0) == 57042

#print axioms optimizeOnce_totalN
#print axioms optLoop_totalN
#print axioms optimizeF_totalN
#print axioms passTotalN_of
#print axioms opt_gate_totalN_of
#print axioms rub_reads
#print axioms mid_reads
#print axioms trim_reads
#print axioms hops_reads
#print axioms dead_reads
#print axioms readsKeep_of
#print axioms gateTotalN_of
#print axioms opt_total_finishLFX'
#print axioms opt_total_finishLUX'

end ReadsCheck
end Compiler
end Formalization
