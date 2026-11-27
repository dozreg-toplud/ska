import lemmas.Glue.StraightRenCheck
import lemmas.Ska.RawInvCLCheck

/-!
# The proxy facts on `PlainN`: executable checks (track G, twelfth pass)

LEDGER 2.c.  `Glue/ProxPlain.lean` proves `StraightA` on `PlainN` from
`ProxOKN` (`wr`, and no split op splits a key: `nsk`), and `ProxOKN` from
track D's `IL.cond` and `SDBody` of every block (every split register is
defined by an earlier op of its body).  At the state after the top `+kerf`
(`kerfState`, `envD`), tally
`[nomms, no code, a key split, a key tested by %cel, a key read in a block
that writes its source, a body without SDBody, ProxOK holds, cond has keys]`:

* `plainCX` (the 2,856 `PlainN` nomms of `enumCX`): no key is split or
  tested, `SDBody` everywhere, 1,927 states with proxies;
* `hand` (28 nomms where an atom feeds a call whose formula need is parked
  behind a bond): every state tests a key with `%cel` (`+crash-need` of the
  bond's need through a proxy), none splits one, `SDBody` everywhere;
* the 7 direct calls and the 7,920 `enumDX` nomms: no key is split, but
  `SDBody` FAILS on every state (the split block `[hed r rh, tal r rt]` of
  `+mono-try-call`), and on 64 `enumDX` states a split register has no
  definition at all (`tallyD`), so `nsk` there needs its own argument
  (`Glue/ProxCalls.lean`, `NskEndC`).
-/

namespace Formalization
namespace SkaModel
namespace Glue
namespace ProxPlainCheck

open Nock Opt Comp Raw Path EntryCheck EntryPathCheck GuardCallsCheck GuardCallsCheckD StraightRenCheck

def plainCX : List Nomm := enumCX.filter Raw.isPlain

def keySplitB (g : Comp.Gen FM) : Bool :=
  (Raw.blocksOf g.blocks).any fun (_, b) => (b.body.filterMap EntryCheck.splitReg).any (isKey g.cond)

def keyCelB (g : Comp.Gen FM) : Bool :=
  (Raw.blocksOf g.blocks).any fun (_, b) => (b.body.filterMap celReg).any (isKey g.cond)

def readsK (q : Pole) : List Nat := match q with
  | Pole.mov a _ => [a]
  | Pole.cel a => [a]
  | Pole.hed a _ => [a]
  | Pole.tal a _ => [a]
  | _ => []

/-- No block reads a key and writes its source. -/
def srcDefB (g : Comp.Gen FM) : Bool :=
  (HoonMapKeys.keys g.cond).all fun k => match HoonMap.get g.cond k with
    | some (src, _) => (Raw.blocksOf g.blocks).all fun (_, b) =>
        !(writesB b).contains src || !(b.body.any fun q => (readsK q).contains k)
    | Option.none => true

/-- `SDBody` of every block. -/
def splitDefB (g : Comp.Gen FM) : Bool :=
  (Raw.blocksOf g.blocks).all fun (_, b) =>
    (List.range b.body.length).all fun i => match (b.body[i]?).bind EntryCheck.splitReg with
      | Option.none => true
      | some s => (List.range i).any fun j => (b.body[j]?.bind aliasDst) == some s

def tallyQ (l : List Nomm) : List Nat :=
  let rs := l.map fun nm => (kerfState nm).map fun g =>
    (keySplitB g, keyCelB g, srcDefB g, splitDefB g, wrB g && celB g && srcB g, !(HoonMapKeys.keys g.cond).isEmpty)
  [l.length, rs.countP (·.isNone),
   rs.countP fun r => match r with | some (true, _, _, _, _, _) => true | _ => false,
   rs.countP fun r => match r with | some (_, true, _, _, _, _) => true | _ => false,
   rs.countP fun r => match r with | some (_, _, false, _, _, _) => true | _ => false,
   rs.countP fun r => match r with | some (_, _, _, false, _, _) => true | _ => false,
   rs.countP fun r => match r with | some (_, _, _, _, true, _) => true | _ => false,
   rs.countP fun r => match r with | some (_, _, _, _, _, true) => true | _ => false]

/-- A call whose subject part is a call: its formula need is parked behind a bond. -/
def icc : Nomm := Raw.ic (Raw.ic (Nomm.n0 1) (Nomm.n0 2)) (Nomm.n0 3)

def atomers : List Nomm :=
  [Nomm.n4 (Nomm.n0 1), Nomm.n3 (Nomm.n0 1), Nomm.n5 (Nomm.n0 2) (Nomm.n0 3), Nomm.n4 (Raw.ic (Nomm.n0 2) (Nomm.n0 3))]

def hand : List Nomm := atomers.flatMap fun a =>
  [Nomm.n7 a icc, Nomm.n7 a (Raw.ic icc (Nomm.n0 1)), Nomm.n7 a (Nomm.cons icc icc), Nomm.n7 a (Nomm.n4 icc),
   Nomm.n7 a (Nomm.n7 icc (Nomm.n0 3)), Raw.ic (Nomm.n7 a icc) (Nomm.n0 2), Nomm.n7 (Nomm.n7 a icc) icc]

#guard tallyQ plainCX == [2856, 0, 0, 0, 0, 0, 2856, 1927]
#guard hand.all Raw.isPlain
#guard tallyQ hand == [28, 0, 0, 28, 0, 0, 28, 28]
#guard tallyQ dmNomms == [7, 0, 0, 0, 0, 7, 7, 2]
#guard tallyQ enumDX == [7920, 0, 0, 0, 0, 7920, 7920, 5351]

/-- `r` has a definition somewhere. -/
def defdB (g : Comp.Gen FM) (x : Nat) : Bool := (Raw.blocksOf g.blocks).any fun (_, b) => (writesB b).contains x

/-- Every split register has a definition somewhere. -/
def splitDefdB (g : Comp.Gen FM) : Bool :=
  (Raw.blocksOf g.blocks).all fun (_, b) => (b.body.filterMap EntryCheck.splitReg).all (defdB g)

/-- `[nomms, no code, a split register defined nowhere, a key split, wr fails]`. -/
def tallyD (l : List Nomm) : List Nat :=
  let rs := l.map fun nm => (kerfState nm).map fun g => (splitDefdB g, keySplitB g, wrB g)
  [l.length, rs.countP (·.isNone),
   rs.countP fun r => match r with | some (false, _, _) => true | _ => false,
   rs.countP fun r => match r with | some (_, true, _) => true | _ => false,
   rs.countP fun r => match r with | some (_, _, false) => true | _ => false]

/- With direct calls, 64 `enumDX` states split a register that has no
definition at all (so `nsk` is not `IL.cond` plus a definition there); no
state splits a key, and `wr` holds everywhere. -/
#guard tallyD dmNomms == [7, 0, 0, 0, 0]
#guard tallyD enumDX == [7920, 0, 64, 0, 0]
#guard tallyD plainCX == [2856, 0, 0, 0, 0]

end ProxPlainCheck
end Glue
end SkaModel
end Formalization
