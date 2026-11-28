import lemmas.Ska.CompGenClassCheck

namespace Formalization
namespace SkaModel
namespace Comp
namespace GenCheck
namespace CX

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
  | _ => ([999999], [999999])

def freeReads (F : List Pole) : List Nat :=
  (F.foldl (fun (acc : List Nat × List Nat) p =>
    let (r, w) := rdW p
    (acc.1 ++ r.filter (fun x => !acc.2.contains x), acc.2 ++ w)) ([], [])).1

def writesOf (F : List Pole) : List Nat := F.flatMap fun p => (rdW p).2

def suresAtB (l : Lazy LS) (a : Nat) : List Nat :=
  ((entries l).filter (·.1 == a)).flatMap fun e => regsOf e.2.sure.ned

/-- The front ops at a goal label (`frontA`). -/
def frontOps (g0 g1 : Gen FM) (a : Nat) : Option (List Pole) :=
  match blk g0 a, blk g1 a with
  | some b, some b' => if frontA g0 g1 a then some (b'.body.take (b'.body.length - b.body.length)) else Option.none
  | _, _ => Option.none

/-- The registers of the goal's sure need that the fronts of a run read
(outside the result's needs at the label and the fresh ones): nonempty iff
the run needs `x = true`. -/
def xReads (L : Lazy LS) (g0 g1 : Gen FM) (nex : NextL LS) : List Nat :=
  let fresh := fun r => decide (g0.re ≤ r) && decide (r < g1.re)
  (labels L).eraseDups.flatMap fun a => match frontOps g0 g1 a with
    | some F => (freeReads F).filter fun r => !(suresAtB nex.laz a).contains r && !fresh r &&
        (regsOf L.sure.ned).contains r
    | Option.none => []

/-- The label the block at `u` hops up to, if it does (`UpAt`). -/
def upTo (g : Gen FM) (u : Nat) : Option Nat :=
  match blk g u with
  | some b => match b.fin with
    | Termin.hop j => if u < j.there then some j.there else Option.none
    | _ => Option.none
  | Option.none => Option.none

/-- `UpBelow`: every block that hops up hops below `bo`. -/
def upBelowB (g : Gen FM) : Bool :=
  (List.range (g.bo + 4)).all fun u => match upTo g u with | some t => decide (t < g.bo) | Option.none => true

def isHopB : Termin → Bool
  | Termin.hop _ => true
  | _ => false

/-- `JumpsU g.blocks g.bo k fin`. -/
def jumpsUB (g : Gen FM) (k : Nat) (fin : Termin) : Bool :=
  (finJumps fin).all fun j => decide (1 ≤ j.there) &&
    ((decide (j.there < k) && (match upTo g j.there with | some t => decide (t < k) | Option.none => true)) ||
     (isHopB fin && decide (k < j.there) && decide (j.there < g.bo) && (upTo g j.there).isNone))

/-- `GrowU.new`'s hops-up half: every block new in `g1` meets `JumpsU`. -/
def jnewB (g0 g1 : Gen FM) : Bool :=
  (List.range (g1.bo + 4)).all fun k => match blk g0 k, blk g1 k with
    | Option.none, some b => jumpsUB g1 k b.fin
    | _, _ => true

/-- The run-level clauses of the widened class at one run: the frame
(`oneG`'s 23 clauses: `GrowG`, fronts or re-pointing, ...), `ResG`, and per
goal label: `loc` (an old result register at the label is a goal entry's
there; `locE`: it is a goal sure one), `rd` (the front reads only the
result's needs at the label, fresh registers and the goal's sure ones),
`wr` (it writes only the goal's needs at the label and fresh registers),
`eApart` (with `x`, the goal's sure registers are apart from the result's
needs at every goal label), `nofront`.  Info: needs `x`, re-points. -/
def oneX (nm : Nomm) (L : Lazy LS) (th : Jmp) (g0 : Gen FM) : List String :=
  match runP nm (CGoalL.next L th) g0 with
  | Option.none => []
  | some (nex, g1) =>
    let frame := match oneG runP nm L th g0 with
      | some (fs, _, _) => fs.map ("frame:" ++ ·)
      | Option.none => ["model"]
    let res := (if resB nex.laz && goalOK nex.laz g1 then [] else ["res"]) ++
      (if eregsAtB L g0 g1 nex.laz then [] else ["eregsAt"])
    let fresh := fun r => decide (g0.re ≤ r) && decide (r < g1.re)
    let sureL := regsOf L.sure.ned
    let xs := xReads L g0 g1 nex
    let gl := (labels L).eraseDups
    let per := gl.flatMap fun a =>
      let resA := suresAtB nex.laz a
      let goalA := suresAtB L a
      let loc := (resA.filter fun r => decide (r < g0.re)).filter fun r => !goalA.contains r
      let locT := if loc.isEmpty then [] else if loc.all sureL.contains then ["locE"] else ["loc"]
      let eap := if !xs.isEmpty && sureL.any resA.contains then ["eApart"] else []
      match frontOps g0 g1 a with
      | some F =>
        let rd := (freeReads F).filter fun r => !resA.contains r && !fresh r && !sureL.contains r
        let wr := (writesOf F).filter fun r => !goalA.contains r && !fresh r
        locT ++ eap ++ (if rd.isEmpty then [] else ["rd"]) ++ (if wr.isEmpty then [] else ["wr"])
      | Option.none => locT ++ eap ++ (if frontR g0 g1 a then ["i:rep"] else ["nofront"])
    let xk := match nm with
      | Nomm.n6 _ _ _ => "i:x6" | Nomm.n3 _ => "i:x3" | Nomm.n4 _ => "i:x4" | Nomm.n5 _ _ => "i:x5"
      | Nomm.n7 _ _ => "i:x7" | Nomm.cons _ _ => "i:xc" | _ => "i:xo"
    let up := (if upBelowB g0 && !upBelowB g1 then ["upEnd"] else []) ++
      (if jnewB g0 g1 then [] else ["jnew"]) ++ (if upBelowB g0 then [] else ["i:upStart"])
    frame ++ res ++ up ++ per.eraseDups ++ (if xs.isEmpty then [] else ["i:x", xk])

def getG : CM FM (Gen FM) := fun g => some (g, g)

/-- The parts of `[5 p q]` under `%next L th`, as `runLC` makes them. -/
def fiveParts (p q : Nomm) (L : Lazy LS) (th : Jmp) (g0 : Gen FM) :
    Option ((Lazy LS × Jmp × Gen FM) × (Lazy LS × Jmp × Gen FM) × (NextL LS × Gen FM) × Lazy LS) :=
  ((do
    let rp ← (re : CM FM Nat)
    let rq ← (re : CM FM Nat)
    let o ← (do
        let a ← collapseLazyAtomL (S := LS) (Map := FM) ⟨L, th⟩
        match a with
        | Option.none =>
            if th.args = [] then emit (Map := FM) ⟨[], [Pole.equ rp rq], Termin.hop (jmp0 th.there)⟩
            else fun _ => Option.none
        | some (r, o) => do
            let (z, o') ← forl (Map := FM) r o
            emit (Map := FM) ⟨[], [], Termin.eqq rp rq (jmp0 z) (jmp0 o')⟩ : CM FM Nat)
    let gq ← getG
    let nexq ← runLC (S := LS) (Map := FM) envR Option.none q (CGoalL.next (ofSure (lazyReg rq)) (jmp0 o)) []
    let nexq ← pastL (Map := FM) envR.cod nexq p []
    let gp ← getG
    let nexp ← runLC (S := LS) (Map := FM) envR Option.none p (CGoalL.next (ofSure (lazyReg rp)) nexq.th) []
    let g3 ← getG
    pure (((ofSure (lazyReg rq) : Lazy LS), jmp0 o, gq), ((ofSure (lazyReg rp) : Lazy LS), nexq.th, gp),
      (nexp, g3), nexq.laz) : CM FM _) g0).map (·.1)

/-- The part's goal of `[4 p]` under `%next L th`. -/
def fourPart (L : Lazy LS) (th : Jmp) (g0 : Gen FM) : Option (Lazy LS × Jmp × Gen FM) :=
  ((do
    let a ← collapseLazyAtomL (S := LS) (Map := FM) ⟨L, th⟩
    let (pro, th') ← (match a with
      | some x => pure x
      | Option.none => do
          let r ← (re : CM FM Nat)
          if th.args = [] then pure (r, th.there) else fun _ => Option.none : CM FM (Nat × Nat))
    let arg ← (re : CM FM Nat)
    let o ← emit (Map := FM) ⟨[], [Pole.inc arg pro], Termin.hop (jmp0 th')⟩
    let g ← getG
    pure (((ofSure (lazyReg arg)) : Lazy LS), jmp0 o, g) : CM FM _) g0).map (·.1)

/-- The part's goal of `[3 p]` under `%next L th`. -/
def threePart (L : Lazy LS) (th : Jmp) (g0 : Gen FM) : Option (Lazy LS × Jmp × Gen FM) :=
  if noneEquivalentL L then some (L, th, g0) else
  ((do
    let a ← collapseLazyAtomL (S := LS) (Map := FM) ⟨L, th⟩
    match a with
    | Option.none => fun _ => Option.none
    | some (r, o) => do
        let (z, o') ← forl (Map := FM) r o
        let r' ← (re : CM FM Nat)
        let oc ← emit (Map := FM) ⟨[], [], Termin.clq r' (jmp0 z) (jmp0 o')⟩
        let g ← getG
        pure (((ofSure (lazyReg r')) : Lazy LS), jmp0 oc, g) : CM FM _) g0).map (·.1)

def key (r : Option (NextL LS × Gen FM)) := r.map fun (nx, g) => (lzKey nx.laz, nx.th, g.bo, g.re)

/-- Every clause at every sub-run through the cons, `%7`, `%5`, `%4`, `%3`,
with the parts' premises, the copies' `CopyPreAt`, the reassembly, and the
composition of `x` (info: a part needs `x`, the registers it reads are
fresh in the run before it, `i:7pxF`, `i:cpxF`, `i:cqxF`). -/
def chkX : Nomm → Lazy LS → Jmp → Gen FM → List String
  | Nomm.cons p q, L, th, g0 =>
    oneX (Nomm.cons p q) L th g0 ++
    (match consParts p q L th g0 with
     | some ((tel, thq, gq), (hed, thp, gp), (nex1, g3), lz2) =>
       (if premB tel thq gq then [] else ["prem:q"]) ++ chkX q tel thq gq ++
       (if premB hed thp gp then [] else ["prem:p"]) ++ chkX p hed thp gp ++
       (if copyPreB g3 nex1.laz lz2 then [] else ["copy"]) ++
       (if key (copyL (Map := FM) nex1 lz2 g3) == key (runP (Nomm.cons p q) (CGoalL.next L th) g0) then []
        else ["recon"]) ++
       (match runP q (CGoalL.next tel thq) gq with
        | some (nq, g2) => if (xReads tel gq g2 nq).any (fun r => !(regsOf L.sure.ned).contains r) then ["i:cqxF"]
            else []
        | Option.none => []) ++
       (match runP p (CGoalL.next hed thp) gp with
        | some (np, g3') => if (xReads hed gp g3' np).any (fun r => !(regsOf L.sure.ned).contains r) then ["i:cpxF"]
            else []
        | Option.none => [])
     | Option.none => [])
  | Nomm.n7 p q, L, th, g0 =>
    oneX (Nomm.n7 p q) L th g0 ++ chkX q L th g0 ++
    (match runP q (CGoalL.next L th) g0 with
     | some (nx, g1) => (if premB nx.laz nx.th g1 then [] else ["prem:7"]) ++ chkX p nx.laz nx.th g1 ++
        (match runP p (CGoalL.next nx.laz nx.th) g1 with
         | some (np, g2) => if (xReads nx.laz g1 g2 np).any (fun r => !(regsOf L.sure.ned).contains r)
             then ["i:7pxF"] else []
         | Option.none => [])
     | Option.none => [])
  | Nomm.n5 p q, L, th, g0 =>
    oneX (Nomm.n5 p q) L th g0 ++
    (match fiveParts p q L th g0 with
     | some ((lq, thq, gq), (lp, thp, gp), (nexp, g3), lz2) =>
       (if premB lq thq gq then [] else ["prem:5q"]) ++ chkX q lq thq gq ++
       (if premB lp thp gp then [] else ["prem:5p"]) ++ chkX p lp thp gp ++
       (if copyPreB g3 nexp.laz lz2 then [] else ["copy5"]) ++
       (if key (copyL (Map := FM) nexp lz2 g3) == key (runP (Nomm.n5 p q) (CGoalL.next L th) g0) then []
        else ["recon5"])
     | Option.none => [])
  | Nomm.n4 p, L, th, g0 =>
    oneX (Nomm.n4 p) L th g0 ++
    (match fourPart L th g0 with
     | some (l, j, g) => (if premB l j g then [] else ["prem:4"]) ++ chkX p l j g ++
        (if key (runP p (CGoalL.next l j) g) == key (runP (Nomm.n4 p) (CGoalL.next L th) g0) then [] else ["recon4"])
     | Option.none => [])
  | Nomm.n3 p, L, th, g0 =>
    oneX (Nomm.n3 p) L th g0 ++
    (match threePart L th g0 with
     | some (l, j, g) => (if premB l j g then [] else ["prem:3"]) ++ chkX p l j g ++
        (if key (runP p (CGoalL.next l j) g) == key (runP (Nomm.n3 p) (CGoalL.next L th) g0) then [] else ["recon3"])
     | Option.none => [])
  | nm, L, th, g0 => oneX nm L th g0

def tagsX : List String :=
  ["model", "res", "eregsAt", "loc", "locE", "rd", "wr", "eApart", "nofront", "prem:q", "prem:p", "prem:7",
   "prem:5q", "prem:5p", "prem:4", "prem:3", "copy", "copy5", "recon", "recon5", "recon4", "recon3",
   "i:x", "i:x6", "i:x3", "i:x4", "i:x5", "i:x7", "i:xc", "i:xo", "i:rep", "i:cqxF", "i:cpxF", "i:7pxF", "upEnd", "jnew", "i:upStart"] ++ clauses.map ("frame:" ++ ·)

/-- `(top runs, runs failing (or flagged) with each tag)`, call-free nomms
and the others apart; only goals that meet `premB`. -/
def tallyX (nms : List Nomm) (gs : List Goal) : Nat × List (String × Nat) × List (String × Nat) :=
  let gs' := gs.filter fun (L, th, g) => premB L th g
  let fs := nms.flatMap fun nm => gs'.map fun (L, th, g) => ((chkX nm L th g).eraseDups, nm.pure)
  let cnt := fun (pu : Bool) => (tagsX.map fun t => (t, (fs.filter fun (ts, b) => b == pu && ts.contains t).length)).filter
    (·.2 != 0)
  (nms.length * gs'.length, cnt true, cnt false)

def witX (nms : List Nomm) (gs : List Goal) (t : String) : Option String :=
  let gs' := gs.filter fun (L, th, g) => premB L th g
  (nms.flatMap fun nm => gs'.map fun (L, th, g) => (nm, L, th, g)).findSome? fun (nm, L, th, g) =>
    if nm.pure && (chkX nm L th g).contains t then
      some (reprStr (folH nm) ++ " | sure " ++ reprStr (regsOf L.sure.ned) ++ " | ents " ++
        reprStr ((entries L).map (fun e => (e.1, regsOf e.2.sure.ned))) ++ " | th " ++ reprStr th.there ++
        " | re " ++ reprStr g.re ++ " | bo " ++ reprStr g.bo)
    else Option.none

def ops1 : List Nomm := brsP
def fam345 : List Nomm :=
  ops1.map Nomm.n4 ++ ops1.map Nomm.n3 ++ ops1.flatMap (fun a => ops1.map fun b => Nomm.n5 a b) ++
  ops1.flatMap (fun a => ops1.map fun b => Nomm.n4 (Nomm.cons a b)) ++
  ops1.flatMap (fun a => ops1.map fun b => Nomm.n3 (Nomm.n7 a b))
def fours : List Nomm := ops1.map Nomm.n4
/-- composites with a `%3`/`%4`/`%5` part -/
def famX : List Nomm :=
  ops1.flatMap fun a => (fours ++ (ops1.map Nomm.n3) ++ [Nomm.n5 a a]).flatMap fun b =>
    [Nomm.n7 a b, Nomm.n7 b a, Nomm.cons a b, Nomm.cons b a, Nomm.n5 b a, Nomm.n4 (Nomm.n7 a b)]
def flatG := flatGoals LSXCheck.jumps statesH

end CX
end GenCheck
end Comp
end SkaModel
end Formalization
