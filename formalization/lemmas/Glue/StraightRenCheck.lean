import lemmas.Glue.GuardCallsCheckD

/-!
# The proxy facts of the final pass: executable checks (track G, eleventh pass)

LEDGER 2.c, `StraightA`.  The final pass `+to-straight` renames every
register by `renReg sub 1 ∘ unproxy` (a proxy key of `cond` is read as its
source).  `Glue/StraightRen.lean` proves that it keeps the cell annotation
from three facts of the state the top `+kerf` leaves, none of which names
the annotation (`ProxOK`):

1. `wr`: no register a block writes, and no parameter, is a key of `cond`;
2. `cel`: every split of a key of `cond` comes after a `%cel` of it in the
   same body;
3. `src`: a block that splits a key of `cond` or tests it with `%cel` does
   not write its source and does not take it as a parameter.

`proxB` is their Boolean form at the state after the top `+kerf`.  `renOldB`
is the old `RenOK` route's fact (no written register is the source of a
key): it FAILS on the direct calls, which is why the route changed.

Tally `[no code, all hold, wr fails, cel fails, src fails, cond has keys,
the old fact fails]`: 7 of 7 direct calls and 7,920 of 7,920 `enumDX`
nomms meet all three; the old fact fails on 640 of them.
-/

namespace Formalization
namespace SkaModel
namespace Glue
namespace StraightRenCheck

open Nock Opt Comp Raw Path EntryCheck EntryPathCheck GuardCallsCheck GuardCallsCheckD

def isKey (cond : FM (Nat × List Nat)) (x : Nat) : Bool := (HoonMap.get cond x).isSome

def writesB (b : Blob) : List Nat := b.body.filterMap aliasDst ++ b.par

def celReg : Pole → Option Nat
  | Pole.cel p => some p
  | _ => Option.none

def wrB (g : Comp.Gen FM) : Bool :=
  (Raw.blocksOf g.blocks).all fun (_, b) => (writesB b).all fun x => !isKey g.cond x

def celB (g : Comp.Gen FM) : Bool :=
  (Raw.blocksOf g.blocks).all fun (_, b) =>
    (List.range b.body.length).all fun i => match (b.body[i]?).bind EntryCheck.splitReg with
      | Option.none => true
      | some s => !isKey g.cond s || (List.range i).any fun j => b.body[j]? == some (Pole.cel s)

def srcB (g : Comp.Gen FM) : Bool :=
  (Raw.blocksOf g.blocks).all fun (_, b) =>
    (b.body.filterMap EntryCheck.splitReg ++ b.body.filterMap celReg).all fun s =>
      match HoonMap.get g.cond s with
      | Option.none => true
      | some (src, _) => !(writesB b).contains src

/-- The old route's fact: no written register is the source of a key. -/
def renOldB (g : Comp.Gen FM) : Bool :=
  (Raw.blocksOf g.blocks).all fun (_, b) => (writesB b).all fun x =>
    (HoonMapKeys.keys g.cond).all fun k => match HoonMap.get g.cond k with
      | some (src, _) => src != x
      | Option.none => true

/-- The state after the top `+kerf` of `finishLUCM envD`. -/
def kerfState (nm : Nomm) : Option (Comp.Gen FM) :=
  (runLCM (S := LS) (Map := FM) envD true Option.none nm CGoalL.done [] gen0).bind fun (nex, g1) =>
    (kerf nex g1).map fun (_, g2) => g2

def tallyP (l : List Nomm) : List Nat :=
  let rs := l.map fun nm => (kerfState nm).map fun g => (wrB g, celB g, srcB g, !(HoonMapKeys.keys g.cond).isEmpty, renOldB g)
  [rs.countP (·.isNone),
   rs.countP fun r => match r with | some (true, true, true, _, _) => true | _ => false,
   rs.countP fun r => match r with | some (false, _, _, _, _) => true | _ => false,
   rs.countP fun r => match r with | some (_, false, _, _, _) => true | _ => false,
   rs.countP fun r => match r with | some (_, _, false, _, _) => true | _ => false,
   rs.countP fun r => match r with | some (_, _, _, true, _) => true | _ => false,
   rs.countP fun r => match r with | some (_, _, _, _, false) => true | _ => false]

/- The seven direct calls: all three facts hold, two have proxies, the old
fact holds. -/
#guard tallyP dmNomms == [0, 7, 0, 0, 0, 2, 0]
/- All of `enumDX` (7,920 nomms, a few seconds): all three facts hold; 5,351
states have proxies, and on 640 of them the old route's fact fails. -/
#guard tallyP enumDX == [0, 7920, 0, 0, 0, 5351, 640]

end StraightRenCheck
end Glue
end SkaModel
end Formalization
