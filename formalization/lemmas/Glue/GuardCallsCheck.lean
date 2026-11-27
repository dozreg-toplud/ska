import lemmas.Glue.EntryPathCheck

/-!
# `InvA` at every stage of the direct-call runs: executable checks (track G, ninth pass)

LEDGER 2.c, step 4 of the `GuardMonoC` plan: before proving that the final
passes keep the annotation, check it.  `blocksOKAB bl` is `BlocksOKA bl K`
(`Glue/GuardCalls.lean`) for the greatest `K` over ALL blocks (not only the
reachable ones): no block passes `~`, the greatest fixed point of the edge
condition from every split register that is no parameter at every label but
`0`, and every split guarded by a `%cel` of its body or by `K`.  For each
nomm, at the three stages of `finishLUCM`:

1. the end of the run (`runLCM envD true` under `%done`), the state that
   `InvA` describes;
2. after `+kerf`;
3. the finished code (`+to-straight`: unproxying, renaming, `+chase`).

Tally `[no code, all three hold, 1 fails, only 2 fails, only 3 fails]`, on the
seven calls (7 of 7) and on one nomm in 8 of `enumDX` (`enumDX8`, 990 of 990):
every stage meets `BlocksOKA`; a sample of 198 (one in 40) gave the same.
-/

namespace Formalization
namespace SkaModel
namespace Glue
namespace GuardCallsCheck

open Nock Opt Comp Raw Path EntryCheck EntryPathCheck

/-- **`BlocksOKA` with the greatest annotation, on all blocks.** -/
def blocksOKAB (bl : FM Blob) : Bool :=
  let R := (Raw.blocksOf bl).map (·.1)
  let U := splitRegs bl
  let K0 := (Raw.blocksOf bl).filterMap fun (o, b) =>
    if o != 0 then some (o, U.filter fun s => !b.par.contains s) else Option.none
  let K := kIter bl R ((Raw.blocksOf bl).length * (U.length + 1) + 1) K0
  noPoisonBl bl && kStep bl R K == K && (Raw.blocksOf bl).all fun (o, b) =>
    (List.range b.body.length).all fun i => match (b.body[i]?).bind EntryCheck.splitReg with
      | Option.none => true
      | some s =>
        ((List.range i).any fun j => b.body[j]? == some (Pole.cel s) &&
          ((List.range i).all fun l => !(j < l) || (b.body[l]?.bind aliasDst) != some s)) ||
        ((kGet K o).contains s && (List.range i).all fun l => (b.body[l]?.bind aliasDst) != some s)

/-- The blocks at the end of the run, after `+kerf`, and of the finished code. -/
def stages (nm : Nomm) : Option (FM Blob × FM Blob × FM Blob) :=
  (runLCM (S := LS) (Map := FM) envD true Option.none nm CGoalL.done [] gen0).bind fun (nex, g1) =>
    (kerf nex g1).bind fun ((o, sub), g2) =>
      (toStraightF g2.cond g2.blocks (Need.this sub) o).map fun c => (g1.blocks, g2.blocks, c.blocks)

def tallyS (l : List Nomm) : List Nat :=
  let rs := l.map fun nm => (stages nm).map fun (a, b, c) => (blocksOKAB a, blocksOKAB b, blocksOKAB c)
  [rs.countP (·.isNone),
   rs.countP (· == some (true, true, true)),
   rs.countP fun r => match r with | some (false, _, _) => true | _ => false,
   rs.countP fun r => match r with | some (true, false, _) => true | _ => false,
   rs.countP fun r => match r with | some (true, true, false) => true | _ => false]

/-- One nomm in 8 of `enumDX` (990 nomms): the whole list (7,920) does not
finish within the 900 s cap. -/
def enumDX8 : List Nomm := (enumDX.zipIdx.filter fun (_, i) => i % 8 == 0).map (·.1)

#guard tallyS dmNomms == [0, 7, 0, 0, 0]
#guard enumDX8.length == 990
#guard tallyS enumDX8 == [0, 990, 0, 0, 0]

end GuardCallsCheck
end Glue
end SkaModel
end Formalization
