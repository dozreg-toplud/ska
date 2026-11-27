import lemmas.Ska.CompGenCheck
import lemmas.Ska.CompGen

/-!
# The entry semantics of a re-pointed goal entry (phase F), checked

README Gaps 12.39, item 4.  `+fork` (phase F of a `%6`, and L into F)
re-points a goal entry's block `a`: `a: F, hop o1`, `o1: [brz p k0 k1]`, the
kid `k_b` (a result entry, so a fill in front) hops with the forked need's
registers to the join, and the join to the old body at `o2`.  The candidate
clause is the precondition of the witness (`Wit`): at a jump into a goal
entry, the registers the run allocated hold what they held when the run
reached its goal's jump `th` (`FrameG.dreg`: a witness lives there), and
from ANY registers where that holds, a jump into `a` reaches the old body
with the needs of the goal's entries at `a` holding the product.

The check runs the interpreter (`execPole`, the `Termin` cases of
`execBlob`) on the code of the run: `g1`'s blocks unproxied, with `imm`
fills of the subject at the result's entries (a `bom` block where the
subject does not fit), every goal entry's block replaced BEFORE the run by
`[[] [] [hop 5000+a]]` (so reaching label `5000+a` is reaching the start of
its old body).  Phase 1: from the run's jump with the subject in the
result's sure registers to `th`: the goal's sure registers hold `+mink`'s
product (`sem`).  Phase 2: from the registers at `th` restricted to the
fresh ones (`K1`; `K2` adds the goal's sure registers, `x = true`), a jump
into each goal entry `a` reaches `5000+a` with the needs at `a` holding the
product, or crashes where the product does not fit them.
-/

namespace Formalization
namespace SkaModel
namespace Comp
namespace GenFCheck

open Nock Lazy SixCheck GenCheck

/-- The registers of a need holding `n`. -/
def putN : Need → Noun → Option (List (Nat × Noun))
  | Need.none, _ => some []
  | Need.this r, n => some [(r, n)]
  | Need.pair p q, Noun.cell h t => do let a ← putN p h; let b ← putN q t; pure (a ++ b)
  | Need.both r p q, Noun.cell h t => do let a ← putN p h; let b ← putN q t; pure ((r, C h t) :: a ++ b)
  | _, _ => Option.none

def looksB (lok : LS) (n : Noun) : Bool := (HoonSet.toList lok).all fun a => (slot? a n).isSome

def putS (s : Sure LS) (n : Noun) : Option (List (Nat × Noun)) :=
  if looksB s.lok n then putN s.ned n else Option.none

def holdsB : Need → FM (Option Noun) → Noun → Bool
  | Need.none, _, _ => true
  | Need.this r, R, n => read r R == some n
  | Need.pair p q, R, Noun.cell h t => holdsB p R h && holdsB q R t
  | Need.both r p q, R, Noun.cell h t => read r R == some (C h t) && holdsB p R h && holdsB q R t
  | _, _, _ => false

def holdsSB (s : Sure LS) (R : FM (Option Noun)) (n : Noun) : Bool := holdsB s.ned R n && looksB s.lok n

def regsL (ps : List (Nat × Noun)) : FM (Option Noun) :=
  ps.foldl (fun m (r, n) => HoonMap.put m r (some n)) HoonMap.empty

def restrict (R : FM (Option Noun)) (keep : Nat → Bool) : FM (Option Noun) :=
  R.ks.eraseDups.foldl (fun m k => if keep k then match R.f k with
    | some v => HoonMap.put m k v | Option.none => m else m) HoonMap.empty

/-- How a walk ends. -/
inductive WEnd where
  | reach (R : FM (Option Noun))
  | crash
  | other
  | fail

def WEnd.isCrash : WEnd → Bool | WEnd.crash => true | _ => false

/-- Run ops and ends until a jump to `stop` (the registers then, the
arguments passed when `stop`'s block exists). -/
def walk (bl : Nat → Option Blob) (stop : Nat) : Nat → FM (Option Noun) → List Pole → Termin → WEnd
  | 0, _, _, _ => WEnd.fail
  | n + 1, R, p :: ps, fin =>
    match execPole libT oracleR (A 0) () p R [] with
    | some (Tone.zero _, R', _, _) => walk bl stop n R' ps fin
    | some (Tone.two _, _, _, _) => WEnd.crash
    | some _ => WEnd.other
    | Option.none => WEnd.fail
  | n + 1, R, [], fin =>
    let go : Jmp → WEnd := fun j =>
      if j.there = stop then
        (if j.args.isEmpty then WEnd.reach R else
          match bl stop with
          | some b => match evalPass j.args b.par R with | some R' => WEnd.reach R' | Option.none => WEnd.fail
          | Option.none => WEnd.fail)
      else match bl j.there with
        | some b => match evalPass j.args b.par R with
          | some R' => walk bl stop n R' b.body b.fin
          | Option.none => WEnd.fail
        | Option.none => WEnd.fail
    match fin with
    | Termin.hop j => go j
    | Termin.brz r z o => match read r R with
      | some v => go (if v = A 0 then z else o) | Option.none => WEnd.fail
    | Termin.brn r z o => match read r R with
      | some v => if v = A 0 then go z else if v = A 1 then go o else WEnd.crash
      | Option.none => WEnd.fail
    | Termin.clq r z o => match read r R with
      | some (Noun.cell _ _) => go z | some _ => go o | Option.none => WEnd.fail
    | Termin.eqq l r z o => match read l R, read r R with
      | some x, some y => go (if x = y then z else o) | _, _ => WEnd.fail
    | Termin.lti k r z o => match read r R with
      | some v => go (if (match v with | Noun.atom a => decide (a < k) | _ => false) then z else o)
      | Option.none => WEnd.fail
    | Termin.bom _ => WEnd.crash
    | _ => WEnd.other

def stopOf (a : Nat) : Nat := 5000 + a

/-- The goal state with every goal entry's block `[[] [] [hop 5000+a]]`. -/
def markGoal (L : Lazy LS) (g : Gen FM) : Gen FM :=
  (labels L).eraseDups.foldl (fun g a =>
    { g with blocks := HoonMap.put g.blocks a ⟨[], [], Termin.hop (jmp0 (stopOf a))⟩ }) g

/-- The code of the run for the subject `s`: `g1` unproxied, the subject
filled at the result's entries. -/
def codeOf (g1 : Gen FM) (nex : NextL LS) (s : Noun) : Nat → Option Blob := fun k =>
  (HoonMap.get g1.blocks k).map fun b =>
    let b := unproxyBlob g1.cond b
    if (labels nex.laz).contains k then
      match (suresAt nex.laz k).mapM (putS · s) with
      | some ps => { b with body := ps.flatten.map (fun (r, n) => Pole.imm n r) ++ b.body }
      | Option.none => ⟨b.par, [], Termin.bom Option.none⟩
    else b

/-- Counts: `(pairs, phase-1 failures, entries checked, re-pointed ones,
phase-2 failures under K1, under K2, under no register at all)`. -/
abbrev Cnt := Nat × Nat × Nat × Nat × Nat × Nat × Nat

def add (a b : Cnt) : Cnt := (a.1 + b.1, a.2.1 + b.2.1, a.2.2.1 + b.2.2.1, a.2.2.2.1 + b.2.2.2.1,
  a.2.2.2.2.1 + b.2.2.2.2.1, a.2.2.2.2.2.1 + b.2.2.2.2.2.1, a.2.2.2.2.2.2 + b.2.2.2.2.2.2)

def zero : Cnt := (0, 0, 0, 0, 0, 0, 0)

/-- Phase 2 at one goal label: true when it behaves. -/
def entryOK (bl : Nat → Option Blob) (L : Lazy LS) (a : Nat) (R : FM (Option Noun)) (v : Noun) : Bool :=
  let Ls := suresAt L a
  match bl a with
  | Option.none => false
  | some b =>
    match walk bl (stopOf a) 4000 R b.body b.fin with
    | WEnd.reach R' => (Ls.all fun l => (putS l v).isSome) && (Ls.all fun l => holdsSB l R' v) &&
        -- the registers of the precondition outside the needs are kept
        R.ks.all fun x => (Ls.any fun l => (GenCheck.regsOf l.ned).contains x) || read x R' == read x R
    | WEnd.crash => Ls.any fun l => (putS l v).isNone
    | _ => false

/-- One run of `nm` at the goal `(L, th, g)` on the subjects with their
`+mink` products `vs`; `only`: count only runs that re-point an entry. -/
def oneF (run : GenCheck.Runner) (nm : Nomm) (vs : List (Noun × Option Tone)) (L : Lazy LS) (th : Jmp) (g : Gen FM)
    (only : Bool) : Cnt :=
  let g0 := markGoal L g
  match run nm (CGoalL.next L th) g0 with
  | Option.none => zero
  | some (nex, g1) =>
    let las := (labels L).eraseDups
    let rep := las.filter fun a => frontR g0 g1 a
    if only && rep.isEmpty then zero else
    vs.foldl (fun acc (s, v?) =>
      match putS nex.laz.sure s, v? with
      | some ps, some (Tone.zero v) =>
        let bl := codeOf g1 nex s
        let w := match bl nex.th.there with
          | some b => match evalPass nex.th.args b.par (regsL ps) with
            | some R0 => walk bl th.there 4000 R0 b.body b.fin
            | Option.none => WEnd.fail
          | Option.none => WEnd.fail
        if (putS L.sure v).isNone then add acc (1, if w.isCrash then 0 else 1, 0, 0, 0, 0, 0) else
        match w with
        | WEnd.reach Rth =>
          if !holdsSB L.sure Rth v then add acc (1, 1, 0, 0, 0, 0, 0) else
          let fresh := fun x => decide (g0.re ≤ x) && decide (x < g1.re)
          let R1 := restrict Rth fresh
          let R2 := restrict Rth fun x => fresh x || (GenCheck.regsOf L.sure.ned).contains x
          let f1 := (las.filter fun a => !entryOK bl L a R1 v).length
          let f2 := (las.filter fun a => !entryOK bl L a R2 v).length
          let f0 := (las.filter fun a => !entryOK bl L a HoonMap.empty v).length
          add acc (1, 0, las.length, rep.length, f1, f2, f0)
        | _ => add acc (1, 1, 0, 0, 0, 0, 0)
      | _, _ => acc) zero

/-- The goals whose jump is to a block of the goal (below `bo`): the jump
`3` at the state `genAtH 10 3` lands in the run's own first block. -/
def wellFormed (gs : List GenCheck.Goal) : List GenCheck.Goal := gs.filter fun (_, th, g) => decide (th.there < g.bo)

def tallyF (run : GenCheck.Runner) (nms : List Nomm) (gs : List GenCheck.Goal) (subs : List Noun) (only : Bool) : Cnt :=
  nms.foldl (fun acc nm =>
    let vs := subs.map fun s => (s, minkF libT (A 0) 500 [] s (fol nm))
    (wellFormed gs).foldl (fun acc (L, th, g) => add acc (oneF run nm vs L th g only)) acc) zero

/-- The number of runs where a re-pointed goal entry is also a result entry
(L into F: `+copy-all` puts back at its label the part `+leap` took off). -/
def repResRuns (run : GenCheck.Runner) (nms : List Nomm) (gs : List GenCheck.Goal) : Nat :=
  (nms.flatMap fun nm => (wellFormed gs).filter fun (L, th, g) =>
    match run nm (CGoalL.next L th) (markGoal L g) with
    | some (nex, g1) => (labels L).eraseDups.any fun a => frontR (markGoal L g) g1 a && (labels nex.laz).contains a
    | Option.none => false).length

/-- The number of runs that re-point a goal entry. -/
def repRuns (run : GenCheck.Runner) (nms : List Nomm) (gs : List GenCheck.Goal) : Nat :=
  (nms.flatMap fun nm => (wellFormed gs).filter fun (L, th, g) =>
    match run nm (CGoalL.next L th) (markGoal L g) with
    | some (_, g1) => (labels L).eraseDups.any fun a => frontR (markGoal L g) g1 a
    | Option.none => false).length

/-- Every third subject (famB). -/
def subs8 : List Noun := (List.range 8).filterMap fun i => SixCheck.subjects[3 * i]?

/-! ## The checks

famA: the 245 `%6` under the 30 flat goals, the 3 well-formed (jump, state)
pairs (22,050 runs, of which 12,060 re-point a goal entry), all 24
subjects.  Phase 1 (`sem`) never fails; phase 2 never fails under K1 (the
run's fresh registers) nor K2 (and the goal's sure registers), the kept
registers unchanged; with NO register the jump fails at every re-pointed
entry (209,100 of 209,100) and at 54,708 fronted ones: the witness
registers are needed.  On 270 runs a re-pointed label is also a result
entry (so `FrontRG`'s premise is `EntA` of the result's needs at `a`, not
the block unproxied). -/
#guard repRuns GenCheck.runP sixes (flatGoals LSXCheck.jumps statesH) == 12060
#guard repResRuns GenCheck.runP sixes (flatGoals LSXCheck.jumps statesH) == 270
#guard tallyF GenCheck.runP sixes (flatGoals LSXCheck.jumps statesH) SixCheck.subjects false ==
  (472500, 0, 288540, 209100, 0, 0, 263808)

/-! famB: `all6` (a `%6` in every position) under the 30 flat goals, one jump,
one state: the 41,330 runs that re-point an entry, 8 subjects.  K2 never
fails; K1 fails on 2,526 of the 167,816 re-pointed entries, so a phase-F
run may read its goal's sure registers in a re-pointed entry's path
(`x = true`; first witness `[[6 [2 [0 3] [0 2]] [0 2] [0 3]] [4 [2 [0 3] [0 2]]]]`
under the goal `[[v0 ~] v1]` with a bond at `1`). -/
#guard repRuns GenCheck.runP all6 (flatGoals [jmp0 1] [genAtH 4 4]) == 41330
#guard tallyF GenCheck.runP all6 (flatGoals [jmp0 1] [genAtH 4 4]) subs8 true == (204094, 0, 168408, 167816, 2526, 0, 167816)

end GenFCheck
end Comp
end SkaModel
end Formalization
