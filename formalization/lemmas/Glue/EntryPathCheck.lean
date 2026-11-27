import lemmas.Glue.EntryCheck
import lemmas.Ska.CompDirectMCheck
import lemmas.Ska.OptAliasWitness

/-!
# The path guard `CelGuardP`: executable checks (track G, eighth pass)

LEDGER 2.c.  `celGuardPB` is `Glue.CelGuardP` (`Glue/EntryPath.lean`) with
reachability by `reachF`: every split of `s` in a reachable block is
guarded by a `%cel s` of its body, or the block is not `0`, every
reachable block with an edge into it ends with `%clq s _ w` where `w` goes
elsewhere, `s` is not a parameter, and no earlier op writes `s`.

Checked on:
* the seven direct calls of `Ska/CompDirectMCheck.lean` (`finishLUCM envD`,
  `#guard`ed there equal to the real compiler): `dmCases`;
* `enumDX`: the 3,960 nomms of `enumCX` with every indirect call made a
  direct call, once to `bellR` keeping the formula part, once to `bellR2`
  with the formula part `[1 R2]` (7,920 nomms, `finishLUCM envD` and the
  n-ary `finishLFC envD`);
* the indirect calls of `enumCX` (`finishLUC envR`);
* the OPTIMIZED code of all of them (`Opt.optimizeF 30` with `+alias`,
  `+trim-trace-hints`, `+switch-chains`, the passes of
  `Compiler/OptLinkTotalAvailCheck.lean`).

And `EntryOK` along the interpreter's path (`EntryCheck.statsN`, 45
subjects, four oracles) on the raw and optimized code of `dmCases` and of
`enumDX`.
-/

namespace Formalization
namespace SkaModel
namespace Glue
namespace EntryPathCheck

open Nock Opt Comp Raw Path EntryCheck

/-- `EntryCell` with the reachable labels `R`. -/
def entryCellB (bl : FM Blob) (R : List Nat) (o s : Nat) : Bool :=
  o != 0 && (Raw.blocksOf bl).all fun (k, b) => !R.contains k || (getJmps b.fin).all fun j =>
    j.there != o || match b.fin with
      | Termin.clq s' _ w => s' == s && w.there != o
      | _ => false

/-- The guard of one reachable block. -/
def celGuardPBlobB (bl : FM Blob) (R : List Nat) (o : Nat) (b : Blob) : Bool :=
  (List.range b.body.length).all fun i => match (b.body[i]?).bind EntryCheck.splitReg with
    | Option.none => true
    | some s =>
      ((List.range i).any fun j => b.body[j]? == some (Pole.cel s) &&
        ((List.range i).all fun l => !(j < l) || (b.body[l]?.bind aliasDst) != some s)) ||
      (entryCellB bl R o s && !b.par.contains s &&
        (List.range i).all fun l => (b.body[l]?.bind aliasDst) != some s)

/-- **`CelGuardP`.** -/
def celGuardPB (bl : FM Blob) : Bool :=
  let R := reachF bl ((Raw.blocksOf bl).length + 1) 0
  (Raw.blocksOf bl).all fun (o, b) => !R.contains o || celGuardPBlobB bl R o b

/-- The old `CelGuard` on reachable blocks only. -/
def celGuardRB (bl : FM Blob) : Bool :=
  let R := reachF bl ((Raw.blocksOf bl).length + 1) 0
  (Raw.blocksOf bl).all fun (o, b) => !R.contains o || celGuardBlobB b

def noPoisonBl (bl : FM Blob) : Bool := noPoisonB ⟨NeedOrd.this, 0, bl⟩

/-- Some reachable block has a split guarded only by the path. -/
def pathOnlyB (bl : FM Blob) : Bool :=
  let R := reachF bl ((Raw.blocksOf bl).length + 1) 0
  (Raw.blocksOf bl).any fun (o, b) => R.contains o && !celGuardBlobB b

def toLM (bl : FM Blob) : Opt.LM Blob :=
  (Raw.blocksOf bl).foldl (fun m (k, b) => HoonMap.put m k b) HoonMap.empty

def ofLM (bl : Opt.LM Blob) : FM Blob :=
  (MapKeys.keys bl).foldl (fun m k => match HoonMap.get bl k with
    | some b => HoonMap.put m k b
    | Option.none => m) HoonMap.empty

/-- The optimizer of `Compiler/OptLinkTotalAvailCheck.lean` (on `Opt.LM`,
which has `MapKeys`). -/
def optF (c : Straight FM) : Option (Straight FM) :=
  (Opt.optimizeF 30 ⟨Opt.aliasM (fun l => l.headD 0), Opt.trimTraceHints, Opt.switchChains 30⟩
    (⟨c.need, c.nargs, toLM c.blocks⟩ : Straight Opt.LM)).map fun s => ⟨s.need, s.nargs, ofLM s.blocks⟩

/-- `0`: no code; `1`: raw passes both, optimized code passes both; `2`:
raw fails; `3`: the optimizer failed; `4`: optimized fails. -/
def tally (o : Option (Straight FM)) : Nat := match o with
  | Option.none => 0
  | some c =>
    if !(noPoisonBl c.blocks && celGuardPB c.blocks) then 2 else
    match optF c with
    | Option.none => 3
    | some c' => if noPoisonBl c'.blocks && celGuardPB c'.blocks then 1 else 4

def tallyL (l : List (Option (Straight FM))) : List Nat :=
  let t := l.map tally
  [0, 1, 2, 3, 4].map fun k => (t.filter (· == k)).length

/-! ## The seven direct calls of `CompDirectMCheck.lean` -/

def dmNomms : List Nomm :=
  [dtNomm, Nomm.n4 dtNomm, Nomm.cons dtNomm (Nomm.n0 1), Nomm.cons (Nomm.n0 1) dtNomm,
   Nomm.n6 dtNomm (Nomm.n1 (A 0)) (Nomm.n1 (A 1)), etNomm, Nomm.n4 etNomm]

def dmCases : List (Option (Straight FM)) := dmNomms.map (finishLUCM (S := LS) (Map := FM) envD)

/- The old guard FAILS on every one (the split block has no `%cel`), the
path guard holds, raw and optimized. -/
#guard dmCases.all fun o => match o with | some c => !celGuardRB c.blocks | Option.none => false
#guard tallyL dmCases == [0, 7, 0, 0, 0]
/- `EntryOK` along the path, raw and optimized, four oracles. -/
#guard (List.range 4).all fun k => allEnd (statsN (oraE k) dmCases)
#guard (List.range 4).all fun k => allEnd (statsN (oraE k) (dmCases.map fun o => o.bind optF))

/-! ## `enumDX`: the calls of `enumCX` made direct -/

/-- Every indirect call made a direct call to `b`, the formula part kept or
replaced by `q0`. -/
def toDirect (b : Bell) (q0 : Option Nomm) : Nomm → Nomm
  | Nomm.n2 p q Option.none => Nomm.n2 (toDirect b q0 p) (q0.getD (toDirect b q0 q)) (some (b, Option.none))
  | Nomm.n2 p q i => Nomm.n2 (toDirect b q0 p) (toDirect b q0 q) i
  | Nomm.n3 p => Nomm.n3 (toDirect b q0 p)
  | Nomm.n4 p => Nomm.n4 (toDirect b q0 p)
  | Nomm.n5 p q => Nomm.n5 (toDirect b q0 p) (toDirect b q0 q)
  | Nomm.cons p q => Nomm.cons (toDirect b q0 p) (toDirect b q0 q)
  | Nomm.n6 p q r => Nomm.n6 (toDirect b q0 p) (toDirect b q0 q) (toDirect b q0 r)
  | Nomm.n7 p q => Nomm.n7 (toDirect b q0 p) (toDirect b q0 q)
  | Nomm.n10 a v q => Nomm.n10 a (toDirect b q0 v) (toDirect b q0 q)
  | nm => nm

def enumDX : List Nomm :=
  enumCX.map (toDirect bellR Option.none) ++ enumCX.map (toDirect bellR2 (some (Nomm.n1 nounR2)))

def dxMono : List (Option (Straight FM)) := enumDX.map (finishLUCM (S := LS) (Map := FM) envD)

def dxNary : List (Option (Straight FM)) :=
  enumDX.map fun nm => finishLFC (S := LS) (Map := FM) envD nm NeedOrd.this Cape.no (fun ned => (ned, []))

#guard enumDX.length == 7920
/-! ## The annotation `CelAnn` (`Glue/EntryPathD.lean`): the greatest one -/

/-- The registers split anywhere in the blocks. -/
def splitRegs (bl : FM Blob) : List Nat :=
  ((Raw.blocksOf bl).flatMap fun (_, b) => b.body.filterMap EntryCheck.splitReg).eraseDups

def kGet (K : List (Nat × List Nat)) (o : Nat) : List Nat := ((K.find? (·.1 == o)).map (·.2)).getD []

/-- `CellOut`. -/
def cellOutB (K : List (Nat × List Nat)) (o : Nat) (b : Blob) (s : Nat) : Bool :=
  ((kGet K o).contains s && b.body.all fun q => aliasDst q != some s) ||
  (List.range b.body.length).any fun j => b.body[j]? == some (Pole.cel s) &&
    (List.range b.body.length).all fun l => !(j < l) || (b.body[l]?.bind aliasDst) != some s

/-- Every reachable edge into `o'` justifies `s`. -/
def edgeOKB (bl : FM Blob) (R : List Nat) (K : List (Nat × List Nat)) (o' s : Nat) : Bool :=
  (Raw.blocksOf bl).all fun (k, b) => !R.contains k || (getJmps b.fin).all fun j => j.there != o' ||
    (match b.fin with | Termin.clq s' _ w => s' == s && w.there != o' | _ => false) || cellOutB K k b s

def kStep (bl : FM Blob) (R : List Nat) (K : List (Nat × List Nat)) : List (Nat × List Nat) :=
  K.map fun (o, l) => (o, l.filter fun s => edgeOKB bl R K o s)

def kIter (bl : FM Blob) (R : List Nat) : Nat → List (Nat × List Nat) → List (Nat × List Nat)
  | 0, K => K
  | f + 1, K => let K' := kStep bl R K; if K' == K then K else kIter bl R f K'

/-- The greatest annotation: from every split register that is no parameter,
at every reachable label but `0`, down to the fixed point. -/
def kMax (bl : FM Blob) : List Nat × List (Nat × List Nat) :=
  let R := reachF bl ((Raw.blocksOf bl).length + 1) 0
  let U := splitRegs bl
  let K0 := (Raw.blocksOf bl).filterMap fun (o, b) =>
    if o != 0 && R.contains o then some (o, U.filter fun s => !b.par.contains s) else Option.none
  (R, kIter bl R ((Raw.blocksOf bl).length * (U.length + 1) + 1) K0)

/-- **`CelAnn` with the greatest annotation**: it is a fixed point (so
`par`, `zero`, `edge` hold) and every reachable split is guarded. -/
def celAnnB (bl : FM Blob) : Bool :=
  let (R, K) := kMax bl
  kStep bl R K == K && (Raw.blocksOf bl).all fun (o, b) => !R.contains o ||
    (List.range b.body.length).all fun i => match (b.body[i]?).bind EntryCheck.splitReg with
      | Option.none => true
      | some s =>
        ((List.range i).any fun j => b.body[j]? == some (Pole.cel s) &&
          ((List.range i).all fun l => !(j < l) || (b.body[l]?.bind aliasDst) != some s)) ||
        ((kGet K o).contains s && (List.range i).all fun l => (b.body[l]?.bind aliasDst) != some s)

/-- As `tally`, with `CelAnn`: `5` when the optimized code meets
`CelAnn` but not `CelGuardP`. -/
def tallyK (o : Option (Straight FM)) : Nat := match o with
  | Option.none => 0
  | some c =>
    if !(noPoisonBl c.blocks && celGuardPB c.blocks && celAnnB c.blocks) then 2 else
    match optF c with
    | Option.none => 3
    | some c' =>
      if !(noPoisonBl c'.blocks && celAnnB c'.blocks) then 4 else
      if celGuardPB c'.blocks then 1 else 5

def tallyKL (l : List (Option (Straight FM))) : List Nat :=
  let t := l.map tallyK
  [0, 1, 2, 3, 4, 5].map fun k => (t.filter (· == k)).length

def cxMono : List (Option (Straight FM)) := enumCX.map (finishLUC (S := LS) (Map := FM) envR)

/-! ## The tallies (`tallyKL`: no code, both pass, raw fails, the optimizer
fails, optimized fails `CelAnn`, optimized meets `CelAnn` but not
`CelGuardP`) -/

/- The seven calls: `CelGuardP` raw and optimized. -/
#guard tallyKL dmCases == [0, 7, 0, 0, 0, 0]
/- `enumDX`, whole subject: 0 raw failures; every raw code has a split
guarded only by the path; 77 codes where `optimizeF 30` returns `none`;
2,037 optimized codes fail `CelGuardP` and meet `CelAnn`. -/
#guard tallyKL dxMono == [0, 5806, 0, 77, 0, 2037]
#guard countB (fun c => pathOnlyB c.blocks) dxMono == 7920
/- `enumDX`, n-ary (`finishLFC envD`: `%cal` / `%jmp`, no `+mono-try-call`):
the old `CelGuard` holds on every reachable block. -/
#guard tallyKL dxNary == [0, 5921, 0, 0, 0, 1999]
#guard countB (fun c => pathOnlyB c.blocks) dxNary == 0
/- `enumCX` (indirect calls only). -/
#guard tallyKL cxMono == [0, 3011, 0, 0, 0, 949]
#guard tallyKL (enumCX.map naryC) == [0, 3011, 0, 0, 0, 949]

/-! ## The optimizer's witness: a `%tal` moved away from its `%cel`

`[2 [6 [0 2] [0 3] [0 1]] [0 1]]` (no direct call): optimized, block 0 is
`[cel 0, hed 0 10] brn 10 7 8` and block 7 `[tal 0 13] hop 6`. -/
def witO : Nomm := Raw.ic (Nomm.n6 (Nomm.n0 2) (Nomm.n0 3) (Nomm.n0 1)) (Nomm.n0 1)

#guard match (finishLUC (S := LS) (Map := FM) envR witO).bind optF with
  | some c => noPoisonBl c.blocks && !celGuardPB c.blocks && !celGuardRB c.blocks && celAnnB c.blocks &&
      c.blocks.f 7 == some ⟨[], [Pole.tal 0 13], Termin.hop ⟨[some 13], 6⟩⟩ &&
      c.blocks.f 0 == some ⟨[], [Pole.cel 0, Pole.hed 0 10], Termin.brn 10 (jmp0 7) (jmp0 8)⟩
  | Option.none => false
/- Its raw code meets the old guard. -/
#guard match finishLUC (S := LS) (Map := FM) envR witO with
  | some c => celGuardRB c.blocks
  | Option.none => false
/- `EntryOK` along the path on its optimized code, four oracles. -/
#guard (List.range 4).all fun k => allEnd (statsN (oraE k) [(finishLUC (S := LS) (Map := FM) envR witO).bind optF])

/-! ## The 77 codes `optimizeF 30` does not finish: fuel

The first of them (48 blocks) is optimized at fuel 100, and the result meets
`NoPoison` and `CelAnn`. -/
def optFF (k : Nat) (c : Straight FM) : Option (Straight FM) :=
  (Opt.optimizeF k ⟨Opt.aliasM (fun l => l.headD 0), Opt.trimTraceHints, Opt.switchChains k⟩
    (⟨c.need, c.nargs, toLM c.blocks⟩ : Straight Opt.LM)).map fun s => ⟨s.need, s.nargs, ofLM s.blocks⟩

def firstNoOpt : Option Nomm := enumDX.find? fun nm => match finishLUCM (S := LS) (Map := FM) envD nm with
  | some c => (optF c).isNone
  | Option.none => false

#guard (firstNoOpt.map fun nm => (finishLUCM (S := LS) (Map := FM) envD nm).map fun c =>
  ((Raw.blocksOf c.blocks).length, (optFF 100 c).isSome,
    ((optFF 100 c).map fun c' => celAnnB c'.blocks && noPoisonBl c'.blocks))) == some (some (48, true, some true))

end EntryPathCheck
end Glue
end SkaModel
end Formalization
