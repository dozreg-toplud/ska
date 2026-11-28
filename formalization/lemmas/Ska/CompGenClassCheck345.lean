import lemmas.Ska.CompGenClassCheck

/-!
# The `%3`/`%4`/`%5` check of `NextGCS`'s fronts (README Gaps 12.39, item 12 (e))

A scratch copy of `CompGenClassCheck.lean`'s `chk` restricted to the fronts:
`frontChk` reads every goal label's front ops (`readOld`: a register below the
run's start outside the result's needs at the label; `readSure`: the goal's
sure register).  The finding it found: `[3 p]`, `[4 p]`, `[5 p q]` read the
goal's sure register under a goal with an entry (`x = true`), so they are not
in `NextGCS` (`E = none`); witness `[4 [0 2]]` under the sure need `[0]` with
the entry `(1, [2])`, front `[mov 0 2]`.  The `#guard` below: the `%4`s under
`%7` on the flat goals (1,440 runs, 96 read the goal's sure register).
-/


namespace Formalization
namespace SkaModel
namespace Comp
namespace GenCheck
namespace C345

open Nock Lazy SixCheck

def rdW : Pole → List Nat × List Nat
  | Pole.imm _ d => ([], [d])
  | Pole.mov s d => ([s], [d])
  | Pole.inc s d => ([s], [d])
  | Pole.con h t d => ([h, t], [d])
  | Pole.hed s d => ([s], [d])
  | Pole.tal s d => ([s], [d])
  | Pole.cel p => ([p], [])
  | Pole.lob p => ([p], [])
  | Pole.equ l r => ([l, r], [])
  | _ => ([999999], [])

/-- registers read before written -/
def freeReads (F : List Pole) : List Nat :=
  (F.foldl (fun (acc : List Nat × List Nat) p =>
    let (r, w) := rdW p
    (acc.1 ++ r.filter (fun x => !acc.2.contains x), acc.2 ++ w)) ([], [])).1

def suresAtB (l : Lazy LS) (a : Nat) : List Nat :=
  ((entries l).filter (·.1 == a)).flatMap fun e => regsOf e.2.sure.ned

/-- per run: tags of failures: "nofront" (not frontA at a goal label), "readOld" (a front reads an old
register outside the result's needs at the label), "readSure" (that register is a goal sure one),
"growU" -/
def frontChk (nm : Nomm) (L : Lazy LS) (th : Jmp) (g0 : Gen FM) : List String :=
  match runP nm (CGoalL.next L th) g0 with
  | Option.none => ["model"]
  | some (nex, g1) =>
    let gl := (labels L).eraseDups
    let gu := (List.range g0.bo).all (fun k => match blk g0 k with
          | some b => match blk g1 k with | some b' => b'.par == b.par && b'.fin == b.fin | _ => false
          | Option.none => true)
    (if gu then [] else ["growU"]) ++
    gl.flatMap fun a =>
      if frontA g0 g1 a then
        match blk g0 a, blk g1 a with
        | some b, some b' =>
          let F := b'.body.take (b'.body.length - b.body.length)
          let bad := (freeReads F).filter fun r => decide (r < g0.re) && !(suresAtB nex.laz a).contains r
          (if bad.isEmpty then [] else ["readOld"]) ++
          (if bad.any (fun r => (regsOf L.sure.ned).contains r) then ["readSure"] else [])
        | _, _ => ["nofront"]
      else ["nofront"]

def tallyF (nms : List Nomm) (gs : List Goal) : Nat × List (String × Nat) :=
  let gs' := gs.filter fun (L, th, g) => premB L th g
  let fs := nms.flatMap fun nm => gs'.flatMap fun (L, th, g) => (frontChk nm L th g).eraseDups
  (nms.length * gs'.length, (["model", "growU", "nofront", "readOld", "readSure"].map fun t =>
    (t, (fs.filter (· == t)).length)).filter (·.2 != 0))

def witF (nms : List Nomm) (gs : List Goal) (t : String) : Option (Nomm × Need × List (Nat × Need) × Jmp) :=
  let gs' := gs.filter fun (L, th, g) => premB L th g
  (nms.flatMap fun nm => gs'.map fun (L, th, g) => (nm, L, th, g)).findSome? fun (nm, L, th, g) =>
    if (frontChk nm L th g).contains t then some (nm, L.sure.ned, (entries L).map (fun e => (e.1, e.2.sure.ned)), th)
    else Option.none

def ops1 : List Nomm := brsP
def fam345 : List Nomm :=
  ops1.map Nomm.n4 ++ ops1.map Nomm.n3 ++ ops1.flatMap (fun a => ops1.map fun b => Nomm.n5 a b) ++
  ops1.flatMap (fun a => ops1.map fun b => Nomm.n4 (Nomm.cons a b)) ++
  ops1.flatMap (fun a => ops1.map fun b => Nomm.n3 (Nomm.n7 a b))
def famLeaf : List Nomm := ops1 ++ ops1.flatMap (fun a => ops1.map fun b => Nomm.cons a b) ++
  ops1.flatMap (fun a => ops1.map fun b => Nomm.n7 a b)

def witS (nms : List Nomm) (gs : List Goal) (t : String) : Option String :=
  let gs' := gs.filter fun (L, th, g) => premB L th g
  (nms.flatMap fun nm => gs'.map fun (L, th, g) => (nm, L, th, g)).findSome? fun (nm, L, th, g) =>
    if (frontChk nm L th g).contains t then
      let fr := match runP nm (CGoalL.next L th) g with
        | some (nex, g1) => (labels L).eraseDups.map fun a =>
            match blk g a, blk g1 a with
            | some b, some b' => (a, reprStr (b'.body.take (b'.body.length - b.body.length)),
                suresAtB nex.laz a, regsOf nex.laz.sure.ned)
            | _, _ => (a, "", [], [])
        | Option.none => []
      some (reprStr (folH nm) ++ " | sure " ++ reprStr (regsOf L.sure.ned) ++ " | ents " ++
        reprStr ((entries L).map (fun e => (e.1, regsOf e.2.sure.ned))) ++ " | th " ++ reprStr th.there ++
        " | re " ++ reprStr g.re ++ " | fronts " ++ reprStr fr)
    else Option.none

def flatG := flatGoals LSXCheck.jumps statesH
def fours : List Nomm := ops1.map Nomm.n4

end C345
end GenCheck
end Comp
end SkaModel
end Formalization
