import lemmas.Ska.CompSixLSCheck
import lemmas.Ska.CompSixNxRunU

/-!
# `[6 c a b]` under `%next`: the checks of `RunOKLT` before any proof

README Gaps 12.36.  Every clause of `RunOKLT` and `LOKT`
(`CompSixNxRel.lean`) in a decidable form, on the runs of
`CompSixLSCheck.lean`: the 245 `%6` nomms (calling tests and branches)
under the 30 flat lazy goals, 2 jumps and 2 states with tagged entry blocks
(29,400 runs, all four phases S, K, F, L), with `nexU := unwrapL nex`:

* the shape: `Tree1` of `nexU`, `AskNodup` of the real need, `nodup` of
  `nexU`'s labels, and `WalkEq` read as "`+kerf` of the real result and of
  `nexU` give the same state and product";
* every field of `RunOKLB` that is not semantic, on `nexU`: `re`, `bo`,
  `drop`, `keep`, `GrowU` (`keep`, and `new` up to `JumpsU`), `CondFresh`,
  `lo`, `hi`, `ent`, `regs`, `dist`, `eregs`, `labs`, `ncond`, `econd`;
* the conclusions of `LOKT.run`: the jump at no entry of the real need, the
  goal's jump or a new block, the entries clean.

In phases S and K every clause holds on every run.  In F (and L into F)
`GrowU` fails: `+fork` of the goal re-points the goal entries' blocks, so
`RunOKLS` as it stands (`grow`, `front`) is false there, a finding for F.
The candidates with the real need in place of `nexU` fail (`tallyReal`).

`tagTally`: the tag clause `TagLS` (`CompSixNxS.lean`) that phase S asks of
its branches holds on the 7 branches and the 5,145 nomms of `all6` under
the goals with no entry (123,648 runs, 27,168 of them make proxies).

The semantic clause, through the interpreter: `semU all6`, the whole-subject
code made when every parent reads the UNWRAPPED need of a `%6` under
`%next` (`finishLUCU`, `CompSixNxRunU.lean`), agrees with `+mink` on all
123,480 runs of `CompSixLSCheck.lean`.
-/

namespace Formalization
namespace SkaModel
namespace Comp
namespace SixNxCheck

open Nock Lazy SixCheck

def regsOf := LSXCheck.regsOf

def cleanB : Need → Bool
  | Need.none => true
  | Need.this _ => true
  | Need.pair p q => !(p == Need.none && q == Need.none) && cleanB p && cleanB q
  | Need.both _ p q => cleanB p && cleanB q

def flatL (l : Lazy LS) : Bool := l.fork.isEmpty && l.bond.all fun e => e.2.fork.isEmpty && e.2.bond.isEmpty

/-- `Tree1`. -/
def tree1B (u : Lazy LS) : Bool :=
  u.fork.all (fun e => flatL e.1.2 && flatL e.2.2) && u.bond.all fun e => e.2.fork.isEmpty && e.2.bond.isEmpty

/-- `AskNodup`. -/
def askNodupB (l : Lazy LS) : Bool :=
  (((entries l).filter fun e => !noneEquivalent e.2.sure).map Prod.fst).Nodup

def labels (l : Lazy LS) : List Nat := (entries l).map Prod.fst

/-- The state `+kerf` leaves, as data. -/
def kerfOut (nex : NextL LS) (g : Gen FM) : Option ((Nat × Nat) × Nat × Nat × List (Nat × Option Blob) ×
    List (Option (Nat × List Nat))) :=
  (kerf nex g).map fun (p, g') => (p, g'.re, g'.bo, blocksIn g' 0 g'.bo, (List.range g'.re).map g'.cond.f)

def clauses : List String :=
  ["tree1", "askNodup", "nodupU", "walk", "re", "bo", "drop", "keep", "growKeep", "growNew", "cfr", "lo", "hi",
   "ent", "regs", "dist", "eregs", "labs", "ncond", "econd", "jumpNoEnt", "jumpGoalNew", "clean"]

/-- One run: the phase, and the clauses that FAIL (`none`: the model failed). -/
def oneT (nm : Nomm) (L : Lazy LS) (th : Jmp) (g0 : Gen FM) : String × Option (List String) :=
  let ph := match nm with | Nomm.n6 _ q r => phase L q r | _ => "?"
  match runLC envR Option.none nm (CGoalL.next L th) [] g0 with
  | Option.none => (ph, Option.none)
  | some (nex, g1) =>
    let u : NextL LS := ⟨unwrapL nex.laz, nex.th⟩
    let eu := entries u.laz
    let gl := labels L
    let fresh := fun r => decide (g0.re ≤ r) && decide (r < g1.re)
    let blk := fun (g : Gen FM) k => HoonMap.get g.blocks k
    let cs : List Bool :=
      [ tree1B u.laz, askNodupB nex.laz, (labels u.laz).Nodup, kerfOut nex g1 == kerfOut u g1,
        decide (g0.re ≤ g1.re), decide (g0.bo ≤ g1.bo), g1.drop == g0.drop,
        (List.range g0.bo).all (fun o => gl.contains o || blk g1 o == blk g0 o),
        (List.range g0.bo).all (fun k => match blk g0 k with
          | some b => match blk g1 k with | some b' => b'.par == b.par && b'.fin == b.fin | _ => false
          | Option.none => true),
        (HoonMapKeys.keys g1.blocks).all (fun k => match blk g1 k with
          | some b' => (match blk g0 k with | some b => b'.par == b.par && b'.fin == b.fin | _ => false) ||
              (decide (g0.bo ≤ k) && decide (k < g1.bo))
          | Option.none => true),
        (HoonMapKeys.keys g1.cond ++ HoonMapKeys.keys g0.cond).all (fun k =>
          HoonMap.get g1.cond k == HoonMap.get g0.cond k || fresh k),
        decide (1 ≤ u.th.there), decide (u.th.there < g1.bo),
        (match blk g1 u.th.there with | some b => b.par.isEmpty && u.th.args.isEmpty | _ => false) || u.th == th,
        (regsOf u.laz.sure.ned).all (fun r => (regsOf L.sure.ned).contains r || fresh r),
        (regsOf u.laz.sure.ned).Nodup,
        eu.all (fun e => (regsOf e.2.sure.ned).Nodup && (regsOf e.2.sure.ned).all fun r =>
          ((entries L).any fun e0 => (regsOf e0.2.sure.ned).contains r) || (regsOf L.sure.ned).contains r || fresh r),
        eu.all (fun e => (gl.contains e.1 || (decide (g0.bo ≤ e.1) && decide (e.1 < g1.bo))) &&
          match blk g1 e.1 with | some ⟨[], _, Termin.hop _⟩ => true | _ => false),
        (regsOf u.laz.sure.ned).all (fun r => HoonMap.get g1.cond r == Option.none),
        eu.all (fun e => (regsOf e.2.sure.ned).all fun r => HoonMap.get g1.cond r == Option.none),
        !(labels nex.laz).contains nex.th.there,
        nex.th == th || decide (g0.bo ≤ nex.th.there),
        (entries nex.laz).all fun e => cleanB e.2.sure.ned ]
    (ph, some ((clauses.zip cs).filterMap fun (n, b) => if b then Option.none else some n))

/-- Per phase: `(runs, model fails, failures of each clause that fails)`. -/
def tallyT (nms : List Nomm) : List (String × Nat × Nat × List (String × Nat)) :=
  let rs := nms.flatMap fun nm => LSXCheck.lazies.flatMap fun L => LSXCheck.jumps.flatMap fun th =>
    statesH.map fun g => oneT nm L th g
  ["S", "K", "F", "L"].map fun ph =>
    let xs := rs.filter (·.1 == ph)
    let fails := xs.flatMap fun x => x.2.getD []
    (ph, xs.length, (xs.filter (·.2.isNone)).length,
      (clauses.map fun c => (c, (fails.filter (· == c)).length)).filter (·.2 != 0))

-- 29,400 runs, every phase met.  In S and K no clause fails.  In F (and in
-- L, on the 440 runs whose rest goes to F) `GrowU` fails on every run: `+fork`
-- of the goal points each goal entry's block `[hop th']` to a fork block it
-- made (label 1: `hop 0` becomes `hop 11`), so the `fin` of a goal entry's
-- block changes, and so would `front` of `RunOKLB` (same `fin`, ops in front).
#guard tallyT sixes == [("S", 5880, 0, []), ("K", 5840, 0, []),
  ("F", 15640, 0, [("growKeep", 15640), ("growNew", 15640)]), ("L", 2040, 0, [("growKeep", 440), ("growNew", 440)])]

/-! ## Candidates that fail -/

/-- The real need in place of `nexU`, `(runs, Tree1 fails, nodup fails)`:
`nodup` fails on the 3/5 of the runs whose test calls (17,640), and `Tree1`
on 11,112 of them (a wrapper is `Flat` exactly when the need it wraps has
no bond). -/
def oneReal (nm : Nomm) (L : Lazy LS) (th : Jmp) (g0 : Gen FM) : Option (Bool × Bool) :=
  (runLC envR Option.none nm (CGoalL.next L th) [] g0).map fun (nex, _) =>
    (tree1B nex.laz, (labels nex.laz).Nodup)

def tallyReal (nms : List Nomm) : Nat × Nat × Nat :=
  let rs := nms.flatMap fun nm => LSXCheck.lazies.flatMap fun L => LSXCheck.jumps.flatMap fun th =>
    statesH.filterMap fun g => oneReal nm L th g
  (rs.length, (rs.filter fun x => !x.1).length, (rs.filter fun x => !x.2).length)

#guard tallyReal sixes == (29400, 11112, 17640)

/-! ## The semantic clause through the interpreter -/

/-- `sem` of `CompSixLSCheck.lean` with `finishLUCU`. -/
def semU (nms : List Nomm) : Nat × Nat × Nat × Nat :=
  nms.foldl (fun (a, b, c, d) nm =>
    match (finishLUCU (S := LS) envR nm : Option (Straight FM)) with
    | some cd =>
      let ok := (subjects.filter fun s =>
        (execEntry libT oracleR () cd [s] [] (A 0)).map Prod.fst == minkF libT (A 0) 500 [] s (fol nm)).length
      (a + 1, b + 1, c + subjects.length, d + ok)
    | Option.none => (a + 1, b, c, d)) (0, 0, 0, 0)

#guard semU all6 == (5145, 5145, 123480, 123480)

/-! ## The tag clause of the branches (`TagLS`, `CompSixNxS.lean`) -/

/-- Under a goal with no entry, in region `[7]`: every key the run adds to
`cond` has a tag with the region as a suffix (`CondTag`). -/
def tagOne (nm : Nomm) (s : Sure LS) (th : Jmp) (g0 : Gen FM) : Option Bool :=
  (runLC envR Option.none nm (CGoalL.next (ofSure s) th) [7] g0).map fun (_, g1) =>
    (HoonMapKeys.keys g1.cond).all fun k => match HoonMap.get g1.cond k with
      | some (_, t) => (match HoonMap.get g0.cond k with | some (_, t') => t' == t | _ => false) || [7].isSuffixOf t
      | Option.none => true

/-- `(runs, model fails, CondTag fails, runs whose cond grew)`. -/
def tagTally (nms : List Nomm) : Nat × Nat × Nat × Nat :=
  let rs := nms.flatMap fun nm => LSXCheck.sures.flatMap fun s => LSXCheck.jumps.flatMap fun th =>
    statesH.map fun g => (tagOne nm s th g,
      (runLC envR Option.none nm (CGoalL.next (ofSure s) th) [7] g).map fun (_, g1) =>
        (HoonMapKeys.keys g1.cond).length)
  (rs.length, (rs.filter (·.1.isNone)).length, (rs.filter (·.1 == some false)).length,
    (rs.filter fun x => x.2.getD 0 != 0).length)

-- The 7 branches and the 5,145 nomms of `all6` under the 6 goals with no
-- entry, 2 jumps, 2 states: 123,648 runs, `cond` grows on 27,168 of them,
-- and no key is outside the region.
#guard tagTally (brs ++ all6) == (123648, 0, 0, 27168)

end SixNxCheck
end Comp
end SkaModel
end Formalization
