import lemmas.Compiler.OptLinkTotalReadsCheck

/-!
# Check: the availability invariant of `+alias` at `UN N` (track H, Gaps 13)

`UN bl N y := y ∈ allDefs bl ∨ y < N`, decided by `uB`.  `walkOk` runs the
walk of `+alias` (`aliasBlock`, op by op through `aliasOp`) and checks, at the
start of every block walked and after every op of its body, the decidable
form of `TAv st (UN bl N) (UN bl N)` (`OptAliasAvail.lean`), over the finite
universe of registers the blocks mention and those below `N`, and the
immediates of their `%imm` ops: every immediate's register (`imml`) and every
register a fact names (`loc`) is in `UN`, and `old` maps every register of
`UN` into `UN`.  At the start of a block this also checks `TInvU` (the facts
`info`/`imms` of the walked predecessors, met by `aliasStart`, name only
registers of `UN`, and so do the entry facts `entryInfo nargs`, which name
none).  `roundsA` is `rounds` of `OptLinkTotalReadsCheck.lean` with the check
(pass id `11`) run on the input of every `+alias`.  It holds on the three
examples and on all 4,080 raw outputs of `enumX`: 4 + 4,474 walks of
`+alias` checked.
-/

namespace Formalization
namespace Compiler
namespace AvailCheck

open Nock SkaModel Opt AuditOptTotal ReadsCheck

def namesL (i : InfoReg) : List Nat := i.hasHed.toList ++ i.hasTel.toList ++ i.hedOf ++ i.telOf ++ i.decOf.toList

def regsU (N : Nat) (bl : LM Blob) : List Nat :=
  List.range N ++ bl.l.flatMap fun (_, b) =>
    b.par ++ b.body.flatMap (fun op => aliasReads op ++ (aliasDst op).toList) ++ finRegs b.fin

def immsU (bl : LM Blob) : List Noun :=
  bl.l.flatMap fun (_, b) => b.body.filterMap fun op => match op with | Pole.imm n _ => some n | _ => none

def uB (N : Nat) (bl : LM Blob) (y : Nat) : Bool := (allDefsB bl).contains y || decide (y < N)

/-- The decidable `TAv st (UN bl N) (UN bl N)` on the universe. -/
def stOk (N : Nat) (bl : LM Blob) (R : List Nat) (I : List Noun) (st : ABody) : Bool :=
  (I.all fun n => (st.imml n).all (uB N bl)) &&
  (R.all fun r => match st.loc r with | some i => (namesL i).all (uB N bl) | none => true) &&
  (R.all fun d => !uB N bl d || uB N bl (st.old d))

def bodyOk (pick : List Nat → Nat) (N : Nat) (bl : LM Blob) (R : List Nat) (I : List Noun) :
    List Pole → ABody → Bool
  | [], st => stOk N bl R I st
  | op :: l, st => stOk N bl R I st &&
    match aliasOp pick st op with
    | some (_, st') => bodyOk pick N bl R I l st'
    | none => false

/-- One block: the check, then the state after (`aliasBlock`). -/
def blockOk (pick : List Nat → Nat) (nargs : Nat) (bl : LM Blob) (g : AGen LM) (o : Nat) : Bool :=
  let R := regsU nargs bl
  let I := immsU bl
  let pre := g.rev o
  if pre = [] ∧ o ≠ 0 then true else
  match (if pre = [] then some (entryInfo nargs) else aliasStart g o pre), aliasStartImms g pre,
    HoonMap.get bl o, aliasEdges g o pre with
  | some info, some imms, some b, some edges =>
    match aliasPars g b.par edges info with
    | some loc0 => bodyOk pick nargs bl R I b.body { old := g.old, loc := loc0, imml := imms }
    | none => false
  | _, _, _, _ => false

def walkOk (pick : List Nat → Nat) (nargs : Nat) (bl : LM Blob) : List Nat → AGen LM → Bool
  | [], _ => true
  | o :: t, g => blockOk pick nargs bl g o &&
    match aliasBlock pick nargs bl g o with
    | some g' => walkOk pick nargs bl t g'
    | none => false

def chkAlias (nargs : Nat) (bl : LM Blob) (rev : LM (List Nat)) (topo : List Nat) : Bool :=
  walkOk (fun l => l.headD 0) nargs bl topo
    { new := HoonMap.empty, old := id, info := fun _ => none, imms := fun _ => none,
      rev := fun o => dedupN ((HoonMap.get rev o).getD []), folded := false }

def onceA (fuel : Nat) (s : Straight LM) (acc : List (Nat × Bool)) : Option (Bool × Straight LM) × List (Nat × Bool) :=
  match bbTopo fuel s.blocks with
  | none => (none, acc)
  | some topo0 =>
    match sloop fuel fuel s.nargs s.blocks topo0 (revCfg s.blocks topo0) acc with
    | (none, acc) => (none, acc)
    | (some r, acc) =>
      let acc := (11, chkAlias s.nargs r.2.2 r.2.1 r.1) :: acc
      match P0.alias s.nargs r.2.2 r.2.1 r.1 with
      | none => (none, (4, false) :: acc)
      | some ra =>
        let acc := (4, readsB s.nargs ra.2) :: acc
        let topo := r.1.filter fun o => (HoonMap.get ra.2 o).isSome
        let rev := revCfg ra.2 topo
        match P0.trim ra.2 topo rev with
        | none => (none, acc)
        | some bt =>
          match removeDeadCode bt topo.reverse with
          | none => (none, acc)
          | some bd =>
            match removeHops fuel bd rev topo with
            | none => (none, acc)
            | some r1 =>
              match removeUselessBranching r1.2 with
              | none => (none, acc)
              | some r2 =>
                match removeEmptyMiddle fuel r2.2 with
                | none => (none, acc)
                | some r3 => (some (ra.1 || r1.1 || r2.1 || r3.1, withBlocks s r3.2), acc)

def roundsA : Nat → Straight LM → List (Nat × Bool) → List (Nat × Bool)
  | 0, _, acc => acc
  | k + 1, s, acc =>
    match onceA 30 s acc with
    | (some (ch, s'), acc) => if ch then roundsA k s' acc else acc
    | (none, acc) => (0, false) :: acc

def allOkA (s : Straight LM) : Bool := (roundsA 8 s []).all (·.2)
def nA (s : Straight LM) : Nat := ((roundsA 8 s []).filter (·.1 == 11)).length

#guard exs.length == 3 && exs.all allOkA
#guard raws.all allOkA
-- the number of walks of `+alias` checked
#guard (exs.foldl (fun n s => n + nA s) 0, raws.foldl (fun n s => n + nA s) 0) == (4, 4474)

end AvailCheck
end Compiler
end Formalization
