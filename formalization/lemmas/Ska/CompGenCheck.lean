import lemmas.Ska.CompSixNxCheck
import lemmas.Ska.CompHintNest

/-!
# `RunOKG`: the clauses of the general relation, checked before any proof

README Gaps 12.39.  `RunOKG` (`CompGen.lean`) is the relation of a run at an
ARBITRARY lazy goal with an ARBITRARY lazy result: forks and bonds nested to
any depth, labels possibly repeated, in the goal and in the result.  Every
clause that is not semantic is evaluated here in a decidable form (`oneG`),
on the real result (no unwrapping), on four families of runs:

* `famA`: the 245 `%6` nomms of `CompSixLSCheck.lean` under the 30 flat lazy
  goals, 2 jumps, 2 states (29,400 runs, all four phases S, K, F, L);
* `famB`: the 5,145 nomms of `all6` (a `%6` in every position: both parts of
  a cons, `p` and `q` of `%7`, the operands of `%4`, `%3`, `%5`, both parts of
  an indirect call, the test and a branch of a `%6`, nested two deep) under
  the 30 flat goals, one jump, one state (154,350 runs);
* `famC`: goals that are RESULTS of other runs (`goalsP`: forked, bonded,
  with entries; 10 generators under the 30 flat goals), and the 245 `%6`
  and the 7 branches under each (75,600 runs): the `p` of `[7 p q]`;
* `famH`: track J's 22 nested hint shapes (`HintNest.shapes`) and 49 `%6`
  with a calling test, under goals that are the results of the 22 shapes
  (`goalsH`: nested bonds, repeated labels), with the hint runner `runLCH`.

The semantic clause is checked through the interpreter at the top: the code
of `[7 p q]` (so `p` runs under `q`'s result as goal) agrees with `+mink`
(`semG`, `semGH`).
-/

namespace Formalization
namespace SkaModel
namespace Comp
namespace GenCheck

open Nock Lazy SixCheck

abbrev Runner := Nomm → CGoalL LS → Gen FM → Option (NextL LS × Gen FM)

def runP : Runner := fun nm g g0 => runLC envR Option.none nm g [] g0
def runH : Runner := fun nm g g0 => runLCH (S := LS) (Map := FM) envH sndH true Option.none nm g [] g0

def regsOf := LSXCheck.regsOf
def labels (l : Lazy LS) : List Nat := (entries l).map Prod.fst
def blk (g : Gen FM) (k : Nat) : Option Blob := HoonMap.get g.blocks k
def suffixB (b x : List Pole) : Bool := decide (b.length ≤ x.length) && x.drop (x.length - b.length) == b

/-- Every bond and fork side of `l` is itself flat (no tree below the top). -/
def tree1 (l : Lazy LS) : Bool := SixNxCheck.tree1B l

/-- A goal entry's block got ops in front, the same `par` and `fin`. -/
def frontA (g0 g1 : Gen FM) (o : Nat) : Bool :=
  match blk g0 o, blk g1 o with
  | some b, some b' => b'.par == b.par && b'.fin == b.fin && suffixB b.body b'.body
  | _, _ => false

/-- A goal entry's block re-pointed (`+fork`'s `insertHop`): ops `F`, then a
hop without arguments to a fresh block; the old body (ops in front of it
allowed) and `fin` at another fresh block, with no parameters. -/
def frontR (g0 g1 : Gen FM) (o : Nat) : Bool :=
  match blk g0 o, blk g1 o with
  | some b, some b' => b'.par == b.par &&
      (match b'.fin with
       | Termin.hop j => j.args.isEmpty && decide (g0.bo ≤ j.there) && decide (j.there < g1.bo)
       | _ => false) &&
      ((List.range g1.bo).filter (g0.bo ≤ ·)).any fun o2 => match blk g1 o2 with
        | some b2 => b2.par.isEmpty && b2.fin == b.fin && suffixB b.body b2.body
        | Option.none => false
  | _, _ => false

/-- The registers of the entries at one label are pairwise apart. -/
def labDisj (l : Lazy LS) : Bool :=
  let es := entries l
  (labels l).eraseDups.all fun o => ((es.filter (·.1 == o)).flatMap fun e => regsOf e.2.sure.ned).Nodup

/-- Candidate: the entries at one label have one need. -/
def labEq (l : Lazy LS) : Bool :=
  let es := entries l
  (labels l).eraseDups.all fun o => match es.filter (·.1 == o) with
    | [] => true
    | e :: rest => rest.all fun e' => e'.2.sure.ned == e.2.sure.ned

/-- The goal-side premises a run's conclusions must give its parent's next
part (`GoalG`): every goal entry's block is `[[] B [hop _]]` below `bo`, its
registers below `re`, distinct, apart within a label, and the goal's sure
registers distinct and below `re`. -/
def goalOK (L : Lazy LS) (g0 : Gen FM) : Bool :=
  (entries L).all (fun e => decide (1 ≤ e.1) && decide (e.1 < g0.bo) &&
      (match blk g0 e.1 with | some ⟨[], _, Termin.hop _⟩ => true | _ => false) &&
      (regsOf e.2.sure.ned).Nodup && (regsOf e.2.sure.ned).all (· < g0.re)) &&
  labDisj L && (regsOf L.sure.ned).Nodup && (regsOf L.sure.ned).all (· < g0.re)

def clauses : List String :=
  ["re", "bo", "drop", "keep", "growPar", "growFin", "growNew", "cfr", "lo", "hi", "ent", "regs", "dist", "eregs",
   "labs", "labDisj", "ncond", "econd", "frontG", "jumpNoEnt", "jumpGoalNew", "clean", "goalOut"]

def cands : List String :=
  ["c:nodup", "c:askNodup", "c:labEq", "c:growU", "c:frontA", "c:flat", "c:tree1", "c:eregsTop"]

/-- One run: the clauses that fail and the candidates that fail (`none`:
the model failed), and whether the result's labels repeat. -/
def oneG (run : Runner) (nm : Nomm) (L : Lazy LS) (th : Jmp) (g0 : Gen FM) :
    Option (List String × List String × Bool) :=
  match run nm (CGoalL.next L th) g0 with
  | Option.none => Option.none
  | some (nex, g1) =>
    let es := entries nex.laz
    let gl := labels L
    let fresh := fun r => decide (g0.re ≤ r) && decide (r < g1.re)
    let freshB := fun k => decide (g0.bo ≤ k) && decide (k < g1.bo)
    let cs : List Bool :=
      [ decide (g0.re ≤ g1.re), decide (g0.bo ≤ g1.bo), g1.drop == g0.drop,
        (List.range g0.bo).all (fun o => gl.contains o || blk g1 o == blk g0 o),
        (List.range g0.bo).all (fun k => match blk g0 k with
          | some b => match blk g1 k with | some b' => b'.par == b.par | _ => false
          | Option.none => true),
        (List.range g0.bo).all (fun k => match blk g0 k with
          | some b => match blk g1 k with
            | some b' => b'.fin == b.fin || (gl.contains k && frontR g0 g1 k)
            | _ => false
          | Option.none => true),
        (HoonMapKeys.keys g1.blocks).all (fun k => match blk g1 k with
          | some b' => (match blk g0 k with | some b => b'.par == b.par | _ => false) || freshB k
          | Option.none => true),
        (HoonMapKeys.keys g1.cond ++ HoonMapKeys.keys g0.cond).all (fun k =>
          HoonMap.get g1.cond k == HoonMap.get g0.cond k || fresh k),
        decide (1 ≤ nex.th.there), decide (nex.th.there < g1.bo),
        (match blk g1 nex.th.there with | some b => b.par.isEmpty && nex.th.args.isEmpty | _ => false) || nex.th == th,
        (regsOf nex.laz.sure.ned).all (fun r => (regsOf L.sure.ned).contains r || fresh r),
        (regsOf nex.laz.sure.ned).Nodup,
        es.all (fun e => (regsOf e.2.sure.ned).Nodup && (regsOf e.2.sure.ned).all fun r =>
          ((entries L).any fun e0 => (regsOf e0.2.sure.ned).contains r) || (regsOf L.sure.ned).contains r || fresh r),
        es.all (fun e => (gl.contains e.1 || freshB e.1) &&
          match blk g1 e.1 with | some ⟨[], _, Termin.hop _⟩ => true | _ => false),
        labDisj nex.laz,
        (regsOf nex.laz.sure.ned).all (fun r => HoonMap.get g1.cond r == Option.none),
        es.all (fun e => (regsOf e.2.sure.ned).all fun r => HoonMap.get g1.cond r == Option.none),
        (entries L).all (fun e => frontA g0 g1 e.1 || frontR g0 g1 e.1),
        !(labels nex.laz).contains nex.th.there,
        nex.th == th || freshB nex.th.there,
        es.all (fun e => SixNxCheck.cleanB e.2.sure.ned),
        goalOK nex.laz g1 ]
    let ks : List Bool :=
      [ (labels nex.laz).Nodup, SixNxCheck.askNodupB nex.laz, labEq nex.laz,
        (List.range g0.bo).all (fun k => match blk g0 k with
          | some b => match blk g1 k with | some b' => b'.par == b.par && b'.fin == b.fin | _ => false
          | Option.none => true),
        (entries L).all (fun e => frontA g0 g1 e.1), SixCheck.flatB nex.laz, tree1 nex.laz,
        -- the registers of an entry are those of a goal entry AT ITS LABEL, the goal's sure ones, or fresh
        es.all (fun e => (regsOf e.2.sure.ned).all fun r =>
          ((entries L).any fun e0 => e0.1 == e.1 && (regsOf e0.2.sure.ned).contains r) ||
          (regsOf L.sure.ned).contains r || fresh r) ]
    some ((clauses.zip cs).filterMap (fun (n, b) => if b then Option.none else some n),
      (cands.zip ks).filterMap (fun (n, b) => if b then Option.none else some n),
      !(labels nex.laz).Nodup)

/-- A goal: the lazy need, the jump, the state. -/
abbrev Goal := Lazy LS × Jmp × Gen FM

/-- `(runs, model fails, runs with repeated result labels, failures of each
clause, failures of each candidate)`. -/
def tallyG (run : Runner) (nms : List Nomm) (gs : List Goal) :
    Nat × Nat × Nat × List (String × Nat) × List (String × Nat) :=
  let rs := nms.flatMap fun nm => gs.map fun (L, th, g) => oneG run nm L th g
  let ok := rs.filterMap id
  let f := ok.flatMap (·.1)
  let k := ok.flatMap (·.2.1)
  (rs.length, (rs.filter (·.isNone)).length, (ok.filter (·.2.2)).length,
    (clauses.map fun c => (c, (f.filter (· == c)).length)).filter (·.2 != 0),
    (cands.map fun c => (c, (k.filter (· == c)).length)).filter (·.2 != 0))

def flatGoals (js : List Jmp) (ss : List (Gen FM)) : List Goal :=
  LSXCheck.lazies.flatMap fun L => js.flatMap fun th => ss.map fun g => (L, th, g)

/-- The goals that runs of `qs` leave under the flat goals. -/
def goalsOf (run : Runner) (qs : List Nomm) : List Goal :=
  qs.flatMap fun q => (flatGoals [jmp0 1] [genAtH 4 4]).filterMap fun (L, th, g) =>
    (run q (CGoalL.next L th) g).map fun (nx, g1) => (nx.laz, nx.th, g1)

/-- Generators of goals: `%6` results (forked, wrapped), a nested `%6`,
conses with a calling part (bonds at fresh labels). -/
def gensP : List Nomm :=
  [Nomm.n6 ind ind (Nomm.n0 3), Nomm.n6 (Nomm.n3 (Nomm.n0 3)) ind (Nomm.cons ind (Nomm.n0 2)),
   Nomm.n6 ind (Nomm.n4 ind) (Nomm.n1 (A 7)), Nomm.n6 (Nomm.n3 ind) (Nomm.cons (Nomm.n0 3) (Nomm.n0 2)) ind,
   Nomm.n6 ind (Nomm.n6 ind (Nomm.n0 2) ind) (Nomm.n0 3), Nomm.cons ind (Nomm.n0 2), LSXCheck.parkC,
   Nomm.cons (Nomm.n0 3) ind, Nomm.cons (Nomm.n6 ind ind (Nomm.n0 2)) ind, Nomm.n4 (Nomm.n6 ind (Nomm.n0 2) ind)]

def goalsP : List Goal := goalsOf runP gensP

/-- The kind of a goal: `(flat, forked somewhere, a tree below the top,
repeated labels)`. -/
def kind (L : Lazy LS) : Bool × Bool × Bool × Bool :=
  (SixCheck.flatB L, (entries L).any (fun e => !e.2.fork.isEmpty) || !L.fork.isEmpty, !tree1 L, !(labels L).Nodup)

def kinds (gs : List Goal) : Nat × Nat × Nat × Nat × Nat :=
  let ks := gs.map fun (L, _, _) => kind L
  (gs.length, (ks.filter (·.1)).length, (ks.filter (·.2.1)).length, (ks.filter (·.2.2.1)).length,
    (ks.filter (·.2.2.2)).length)

/-- The formula of a nomm with static and dynamic hints. -/
def folH : Nomm → Noun
  | Nomm.cons p q => C (folH p) (folH q)
  | Nomm.n0 a => C (A 0) (A a)
  | Nomm.n1 k => C (A 1) k
  | Nomm.n2 p q _ => C (A 2) (C (folH p) (folH q))
  | Nomm.n3 p => C (A 3) (folH p)
  | Nomm.n4 p => C (A 4) (folH p)
  | Nomm.n5 p q => C (A 5) (C (folH p) (folH q))
  | Nomm.n6 c a b => C (A 6) (C (folH c) (C (folH a) (folH b)))
  | Nomm.n7 p q => C (A 7) (C (folH p) (folH q))
  | Nomm.n11s t q _ => C (A 11) (C (A t) (folH q))
  | Nomm.n11d t h q _ => C (A 11) (C (C (A t) (folH h)) (folH q))
  | _ => A 0

/-- The code of `[7 p q]` against `+mink`: `(nomms compiled, runs, agree)`. -/
def semG (ps qs : List Nomm) : Nat × Nat × Nat :=
  (ps.flatMap fun p => qs.map fun q => Nomm.n7 p q).foldl (fun (a, c, d) nm =>
    match (finishLUC (S := LS) envR nm : Option (Straight FM)) with
    | some cd =>
      let ok := (SixCheck.subjects.filter fun s =>
        (execEntry libT oracleR () cd [s] [] (A 0)).map Prod.fst == minkF libT (A 0) 500 [] s (fol nm)).length
      (a + 1, c + SixCheck.subjects.length, d + ok)
    | Option.none => (a, c, d)) (0, 0, 0)

/-- The same with hints (`finishLUCH`, traces compared by `toneOK`). -/
def semGH (ps qs : List Nomm) : Nat × Nat × Nat :=
  (ps.flatMap fun p => qs.map fun q => Nomm.n7 p q).foldl (fun (a, c, d) nm =>
    match (finishLUCH (S := LS) (Map := FM) envH sndH nm : Option (Straight FM)) with
    | some cd =>
      let ok := (SixCheck.subjects.filter fun s =>
        toneOK ((execEntry libT oracleD () cd [s] [] (A 0)).map Prod.fst) (minkF libT (A 0) 500 [] s (folH nm))).length
      (a + 1, c + SixCheck.subjects.length, d + ok)
    | Option.none => (a, c, d)) (0, 0, 0)

def goalsH : List Goal := goalsOf runH HintNest.shapes

/-- The 49 `%6` whose test is the indirect call. -/
def sixesT : List Nomm := brs.flatMap fun a => brs.map fun b => Nomm.n6 ind a b

/-- The first run where a candidate fails: the nomm, the goal's labels, the
result's labels. -/
def witness (run : Runner) (nms : List Nomm) (gs : List Goal) (cand : String) :
    Option (Nomm × List Nat × List Nat) :=
  (nms.flatMap fun nm => gs.map fun g => (nm, g)).findSome? fun (nm, L, th, g) =>
    match oneG run nm L th g with
    | some (_, ks, _) => if ks.contains cand then
        (run nm (CGoalL.next L th) g).map fun (nex, _) => (nm, labels L, labels nex.laz) else Option.none
    | Option.none => Option.none

/-! ## The checks -/

-- The goals made by runs: `(goals, flat, forked, a tree below the top, repeated labels)`.
#guard kinds goalsP == (300, 90, 210, 79, 180)
#guard kinds goalsH == (660, 159, 0, 501, 254)

-- famA: no clause fails; every candidate below fails somewhere.  `c:growU`
-- and `c:frontA` fail exactly on the F runs and the L runs into F (16,080):
-- `+fork` re-points the goal entries' blocks.
#guard tallyG runP sixes (flatGoals LSXCheck.jumps statesH) == (29400, 0, 17640, [],
  [("c:nodup", 17640), ("c:labEq", 16548), ("c:growU", 16080), ("c:frontA", 16080), ("c:flat", 29400),
   ("c:tree1", 11112)])

-- famH: the hint shapes under the flat goals, and the shapes and 49 `%6`
-- under the goals the shapes leave (nested bonds, repeated labels).
#guard tallyG runH HintNest.shapes (flatGoals LSXCheck.jumps statesH) == (2640, 0, 1016, [],
  [("c:nodup", 1016), ("c:askNodup", 1016), ("c:labEq", 1016), ("c:flat", 2004), ("c:tree1", 2004)])
#guard tallyG runH (HintNest.shapes ++ sixesT) goalsH == (46860, 0, 37858, [],
  [("c:nodup", 37858), ("c:askNodup", 6390), ("c:labEq", 27256), ("c:growU", 22758), ("c:frontA", 22758),
   ("c:flat", 43469), ("c:tree1", 36254)])

-- The semantic clause at the top: `[7 p q]`, so `p` runs under `q`'s result.
#guard semG (sixes ++ brs) gensP == (2520, 60480, 60480)
#guard semGH (HintNest.shapes ++ sixesT) HintNest.shapes == (1562, 37488, 37488)
#guard semGH sixesT gensP == (490, 11760, 11760)

/-! ## Witnesses of the candidates that fail -/

def wit (x : Option (Nomm × List Nat × List Nat)) : Option (Noun × List Nat × List Nat) :=
  x.map fun (nm, a, b) => (nm.toNoun, a, b)

-- `AskNodup` (the relaxed `nodup` of Gaps 12.34): track J's witness under the
-- goal with one entry at label 1; labels 5 and 1 repeat with entries that ask.
#guard wit (witness runH HintNest.shapes (flatGoals LSXCheck.jumps statesH) "c:askNodup") ==
  some ((Nomm.n7 (HintNest.c (HintNest.bo (HintNest.z 2)) (HintNest.z 3)) (HintNest.bo (HintNest.z 1))).toNoun,
    [1], [10, 5, 1, 8, 5, 1])
-- ... and without hints: a `%6` result through the `+split` of a cons.
#guard wit (witness runP all6 (flatGoals [jmp0 1] [genAtH 4 4]) "c:askNodup") ==
  some ((Nomm.n7 (Nomm.cons (Nomm.n0 2) (Nomm.n0 3)) (Nomm.n6 ind (Nomm.n0 2) (Nomm.n0 2))).toNoun, [], [7, 7, 8, 8])
-- One need per label: the wrapper of `+past-fork` (`bunt` and the need at 7).
#guard wit (witness runP sixes (flatGoals LSXCheck.jumps statesH) "c:labEq") ==
  some ((Nomm.n6 ind (Nomm.n0 2) (Nomm.n0 2)).toNoun, [], [7, 7, 8, 8])

end GenCheck
end Comp
end SkaModel
end Formalization
