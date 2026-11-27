import lemmas.Ska.RawInvCheckCX
import lemmas.Ska.Opt

/-!
# `EntryOK` of raw `+comp` output: executable checks

LEDGER 2.c, the leaf `rawEntry`.  The three parts of `Opt.EntryOK` are
checked along the path of the model's interpreter from the entry (`stepF`
is `Path.Step`, `okAt` the three parts at one configuration), on the raw
output of both final passes, entered with the split of each of 45 subjects
(`subjects`: the 38 nouns of depth at most 2 over `0` and `1`, the atoms `2`
and `5`, five deeper cells), so on subjects where Nock crashes (atoms where a
cell is wanted, non-loobean tests) as well as where it does not:

* `enumX` (4,080 nomms of `FragX`): `finishLU` and `finishLF` at
  `NeedOrd.this` (183,600 runs each), and `finishLF` at four more input needs
  and two capes on the first 1,000 nomms;
* `enumCX` (3,960 nomms with indirect calls): `finishLUC envR` and the
  n-ary `naryC` (178,200 runs each) under four oracles (a call returns `0`,
  its first argument, a cell, or crashes).

Every run ends by `endOf` (a product, a boom or a call), none is stuck,
and no configuration fails a part of `EntryOK`.  So `EntryOK` as stated
holds of raw output on every subject, not only those that fit the bell.

What guards each `%hed` / `%tal`: the `%cel` that `+kern-need` puts in the
same op list (`kernBoth`: `mov r d, cel d, hed d rh, .., tal d rt, ..`);
between the `%cel` and a `%tal` lie the head's ops, which write fresh
registers only.  `celGuardB` is that property (`Glue.CelGuard`); `noPoisonB`
says no reachable jump passes `~` (`Glue.NoPoison`).  Both hold on all
outputs above; 8,064 of the 8,160 outputs of `enumX` have a `%hed` or
`%tal`, 1,824 one that is not right after its `%cel`, and 3,360 n-ary
outputs a jump with arguments. -/

namespace Formalization
namespace SkaModel
namespace Glue
namespace EntryCheck

open Nock Opt Comp Raw Path

def libE : Lib := ⟨fun _ _ => Option.none, fun _ => Option.none, fun _ _ => Option.none, fun _ => A 0⟩

/-- An oracle whose calls return a value (`k` picks it). -/
def oraE (k : Nat) : Oracle Unit :=
  ⟨fun _ _ _ vs _ _ => match k with
      | 0 => some (Tone.zero (A 0), ())
      | 1 => some (Tone.zero (vs.headD (A 3)), ())
      | 2 => some (Tone.zero (C (A 0) (A 1)), ())
      | _ => some (Tone.two [], ()),
   fun _ u _ _ => match k with
      | 0 => some (Tone.zero (A 0), ())
      | 1 => some (Tone.zero u, ())
      | 2 => some (Tone.zero (C (A 0) (A 1)), ())
      | _ => some (Tone.two [], ())⟩

/-- One step of `Path.Step`, when there is one. -/
def stepF (O : Oracle Unit) (c : Straight FM) (gul : Noun) (x : Cfg Unit FM) : Option (Cfg Unit FM) :=
  if x.params ≠ [] ∨ x.b.par ≠ [] then
    (evalPass x.params x.b.par x.regs).map fun R => { x with b := { x.b with par := [] }, params := [], regs := R }
  else match x.b.body with
  | p :: rest => match execPole libE O gul x.st p x.regs x.t with
      | some (Tone.zero _, R, t', st') => some { x with b := { x.b with body := rest }, regs := R, t := t', st := st' }
      | _ => Option.none
  | [] => (taken x.regs x.b.fin).bind fun j =>
      (HoonMap.get c.blocks j.there).map fun b' => ⟨j.there, b', j.args, x.regs, x.t, x.st⟩

/-- The three parts of `EntryOK` at one configuration: `0` fine, `1` a real
read of a missing or poisoned register, `2` a pending argument missing, `3`
an op of `safeAssign` that crashes. -/
def okAt (O : Oracle Unit) (gul : Noun) (x : Cfg Unit FM) : Nat :=
  let quiet := x.params.isEmpty && x.b.par.isEmpty
  let rs := if quiet then (match x.b.body with | p :: _ => poleReads gul p | [] => finReads x.b.fin) else []
  if !(rs.all fun k => (read k x.regs).isSome) then 1 else
  if !(x.params.all fun a => match a with | some k => (HoonMap.get x.regs k).isSome | none => true) then 2 else
  if quiet then match x.b.body with
    | p :: _ => if (safeAssign p).isSome && !(execPole libE O gul x.st p x.regs x.t).isSome then 3 else 0
    | [] => 0
  else 0

/-- Walk the path from a configuration: the first failure with the label, or
`0` and how it ended (`10` an end of `endOf`, `11` stuck, `12` out of fuel). -/
def walk (O : Oracle Unit) (c : Straight FM) (gul : Noun) : Nat → Cfg Unit FM → Nat × Nat
  | 0, x => (12, x.lab)
  | f + 1, x =>
    let k := okAt O gul x
    if k ≠ 0 then (k, x.lab) else
    match stepF O c gul x with
    | some y => walk O c gul f y
    | Option.none => (if (endOf libE O gul x).isSome then 10 else 11, x.lab)

def entryRun (O : Oracle Unit) (c : Straight FM) (vals : List Noun) : Nat × Nat :=
  match c.blocks.f 0 with
  | some b0 => walk O c (A 0) 2000 ⟨0, b0, [], regsOf vals, [], ()⟩
  | Option.none => (13, 0)

/-! ## Subjects -/

def ns1 : List Noun := [A 0, A 1]
def ns2 : List Noun := ns1 ++ ns1.flatMap fun a => ns1.map fun b => C a b
def ns3 : List Noun := ns1 ++ ns2.flatMap fun a => ns2.map fun b => C a b
/-- 38 nouns of depth at most 2 over `0`, `1`, two more atoms and some deeper cells. -/
def subjects : List Noun :=
  ns3 ++ [A 2, A 5, C (C (C (A 0) (A 1)) (C (A 1) (A 0))) (C (C (A 0) (A 0)) (C (A 1) (A 1))),
    C (C (A 5) (C (A 0) (A 1))) (C (C (A 1) (A 0)) (A 7)), C (A 0) (C (C (A 1) (A 0)) (C (A 0) (A 0))),
    C (C (A 0) (C (A 1) (A 1))) (C (C (A 0) (A 1)) (A 0)), C (C (A 1) (C (A 0) (C (A 1) (A 0)))) (A 1)]

/-! ## The static predicates -/

/-- No reachable jump passes `~`. -/
def noPoisonB (c : Straight FM) : Bool :=
  let R := reachF c.blocks ((blocksOf c.blocks).length + 1) 0
  (blocksOf c.blocks).all fun (k, b) => !R.contains k || (getJmps b.fin).all fun j => j.args.all Option.isSome

/-- The register a `%hed` or `%tal` takes apart. -/
def splitReg : Pole → Option Nat
  | Pole.hed s _ => some s
  | Pole.tal s _ => some s
  | _ => Option.none

/-- **The `%cel` guard of a block**: every `%hed s` / `%tal s` of its body
comes after a `%cel s` of the same body, with no op between them that
writes `s`. -/
def celGuardBlobB (b : Blob) : Bool :=
  (List.range b.body.length).all fun i => match (b.body[i]?).bind splitReg with
    | Option.none => true
    | some s => (List.range i).any fun j => b.body[j]? == some (Pole.cel s) &&
        ((List.range i).all fun l => !(j < l) || (b.body[l]?.bind aliasDst) != some s)

def celGuardB (c : Straight FM) : Bool := (blocksOf c.blocks).all fun (_, b) => celGuardBlobB b

def badRuns (O : Oracle Unit) (c : Straight FM) (vals : List (List Noun)) : List (List Noun × Nat × Nat) :=
  (vals.map fun v => (v, entryRun O c v)).filter fun (_, r) => r.1 < 10 && r.1 ≠ 0

def statsN (O : Oracle Unit) (cs : List (Option (Straight FM))) : List Nat :=
  let rs := cs.flatMap fun o => match o with
    | some c => subjects.filterMap fun x => (SkaModel.split c.need x).map fun a => (entryRun O c a).1
    | Option.none => []
  rs.length :: [10, 11, 12, 13, 1, 2, 3].map fun k => (rs.filter (· == k)).length

def naryO (ord : NeedOrd) (cape : Cape) (nm : Nomm) : Option (Straight FM) :=
  finishLF (S := LS) (Map := FM) nm ord cape (fun ned => (ned, []))

def ords : List NeedOrd :=
  [NeedOrd.this, NeedOrd.pair NeedOrd.this NeedOrd.this, NeedOrd.both NeedOrd.this NeedOrd.this,
   NeedOrd.both NeedOrd.none (NeedOrd.pair NeedOrd.this NeedOrd.none),
   NeedOrd.pair (NeedOrd.both NeedOrd.this NeedOrd.this) NeedOrd.this]

def hasSplitB (c : Straight FM) : Bool :=
  (blocksOf c.blocks).any fun (_, b) => b.body.any fun p => (splitReg p).isSome

/-- A `%hed`/`%tal` not right after its `%cel`. -/
def gapB (c : Straight FM) : Bool :=
  (blocksOf c.blocks).any fun (_, b) => (List.range b.body.length).any fun i =>
    match (b.body[i]?).bind splitReg with
    | some s => i == 0 || b.body[i - 1]? != some (Pole.cel s)
    | Option.none => false

def staticB (o : Option (Straight FM)) : Bool := match o with
  | some c => noPoisonB c && celGuardB c
  | Option.none => true

/-- Every run returned an `endOf`: no failure of `EntryOK`, nothing stuck. -/
def allEnd (l : List Nat) : Bool := l.getD 0 0 == l.getD 1 0

#guard statsN (oraE 0) (enumX.map mono) == [183600, 183600, 0, 0, 0, 0, 0, 0]
#guard statsN (oraE 0) (enumX.map naryX) == [183600, 183600, 0, 0, 0, 0, 0, 0]
#guard ords.all fun o => allEnd (statsN (oraE 0) ((enumX.take 1000).map (naryO o Cape.no)))
#guard ords.all fun o => allEnd (statsN (oraE 0) ((enumX.take 1000).map (naryO o (Cape.cell Cape.no Cape.no))))
#guard (List.range 4).all fun k => statsN (oraE k) (enumCX.map (finishLUC (S := LS) (Map := FM) envR)) ==
  [178200, 178200, 0, 0, 0, 0, 0, 0]
#guard (List.range 4).all fun k => statsN (oraE k) (enumCX.map naryC) == [178200, 178200, 0, 0, 0, 0, 0, 0]

/-! The two static facts, on both final passes, the raw run blocks of
`enumX`, and `enumCX`; not vacuous. -/
#guard (enumX.map mono ++ enumX.map naryX).all staticB
#guard enumX.all fun nm => ((runX nm).map fun (_, g) => celGuardB ⟨NeedOrd.this, 0, g.blocks⟩) == some true
#guard (enumCX.map (finishLUC (S := LS) (Map := FM) envR) ++ enumCX.map naryC).all staticB
def countB (P : Straight FM → Bool) (l : List (Option (Straight FM))) : Nat :=
  (l.filter fun o => match o with | some c => P c | Option.none => false).length

def argsB' (c : Straight FM) : Bool :=
  (blocksOf c.blocks).any fun (_, b) => (getJmps b.fin).any fun j => !j.args.isEmpty

#guard countB hasSplitB (enumX.map mono ++ enumX.map naryX) == 8064
#guard countB gapB (enumX.map mono ++ enumX.map naryX) == 1824
#guard countB argsB' (enumX.map naryX) == 3360

end EntryCheck
end Glue
end SkaModel
end Formalization
