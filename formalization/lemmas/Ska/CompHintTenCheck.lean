import lemmas.Ska.CompHintSevenCheck

/-!
# `[10 [a v] q]` with a kept value, checked on the model (README Gaps 24.20)

The run of `[10 [a v] q]` (`runLCH`, the case `n10`) under `%next (ofSure
sur) th`, step by step:
1. `+simple-next`: `⟨ofSure sur, th⟩`;
2. `+into` at `a` (`intoL`): the block `o` (the `%con`s that build the
   goal's registers from the donor's and the recipient's, then `hop th`),
   the donor lazy `don` and the recipient lazy `rec`, both `ofSure`;
3. `+past` of `⟨rec, jmp0 o⟩` over `v` (`pastL`): when `v` is hinted and
   `rec` asks something, a block `o' = hop o` with `rec` parked in a bond
   at `o'` (the shape of `+lazy-bound` of `⟨rec, jmp0 o⟩`), else nothing;
4. `v` under `%next don (jmp0 o')` (or `jmp0 o`): the result `nexDon`;
5. `+past` of `nexDon` over `q` (nothing when `q` is pure);
6. `q` under `%next nexR.laz nexDon.th`: for `q = [0 1]` the goal itself;
7. `+copy` of `q`'s result and `nexDon.laz`.

The checks (`tenSteps`, `#guard`), under `%next (lazy-from-reg r)` (the
goal the `%10` of `spotArm`'s `S3` meets: the direct call's result is
`lazy-from-reg` of the subject register, `#guard` below) and under the
bond-free goals of `HintKeep.goals`:
* `don` is `lazy-from-reg d` for a fresh `d` (so `v` needs `RegGBT`
  only, not `SurGBT`) when the goal is `lazy-from-reg`;
* `rec` and `don` have no entries;
* the past parks `rec` exactly as `+lazy-bound` would (`pastRec`);
* with `q = [0 1]` the result's entries are `rec`'s bond then `nexDon`'s
  (in that order), the result's sure need asks nothing, the result is flat
  with no fork (`RegFT`'s shape).
On `spotArm`'s `[10 6 [spot [0 13]] [0 1]]`, on `d20`
(`[10 2 [spot [4 [0 3]]] [0 1]]`, the only `%10` of the 39), and on shapes
(kept spots and `%bout`s over `[0 a]`, `[4 ..]`, a cons, at axes 2, 3, 6,
7, 13).
-/

set_option maxRecDepth 4000

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

namespace HintTen
open HintNest HintKeep HintSpot HintSeven

/-- The `%10`s inside a nomm. -/
def tensOf : Nomm → List Nomm
  | Nomm.n10 a v q => Nomm.n10 a v q :: (tensOf v ++ tensOf q)
  | Nomm.cons p q => tensOf p ++ tensOf q
  | Nomm.n5 p q => tensOf p ++ tensOf q
  | Nomm.n7 p q => tensOf p ++ tensOf q
  | Nomm.n6 p q r => tensOf p ++ tensOf q ++ tensOf r
  | Nomm.n3 p => tensOf p
  | Nomm.n4 p => tensOf p
  | Nomm.n2 p q _ => tensOf p ++ tensOf q
  | Nomm.n11s _ q _ => tensOf q
  | Nomm.n11d _ h q _ => tensOf h ++ tensOf q
  | Nomm.n12 p q => tensOf p ++ tensOf q
  | _ => []

-- `d20` is the only one of the 39 with a `%10`; it is that `%10`
#guard (nm39.filter fun (_, nm) => !(tensOf nm).isEmpty).map Prod.fst == ["d20"]
#guard (tensOf (nmOf "d20")).map Nomm.toNoun == [(nmOf "d20").toNoun]
#guard (nmOf "d20").toNoun == (Nomm.n10 2 (Nomm.n11d tagSpot (Nomm.n1 (A 0)) (Nomm.n4 (z 3)) (C (A 4) (C (A 0) (A 3)))) (z 1)).toNoun

/-- The labels and sure needs of the entries, each with its own entry count
and whether it has a fork. -/
def entK (l : Lazy LS) : List (Nat × Need × Nat × Bool) :=
  (entries l).map fun e => (e.1, e.2.sure.ned, (entries e.2).length, e.2.fork.isEmpty)

/-- The steps of the run of `[10 [a v] q]` under `%next L th` from `g`, as
`runLCH` takes them; `(donReg, recFree, pastRec, sameRun, entOrder, flat)`:
* `donReg`: `don` is `ofSure (lazyReg d)` with `d` fresh (at least `g.re`);
* `recFree`: `don` and `rec` have no entries and no fork;
* `pastRec`: the past of `⟨rec, jmp0 o⟩` over `v` is `+lazy-bound` of it
  (same result, same state) when `v` is hinted and `rec` asks something
  (its need, or its lock: `+into` puts the axis in the recipient's lock, so
  under a goal that asks nothing the lock `{a}` is not small and `rec` is
  parked too), and `⟨rec, jmp0 o⟩` itself otherwise;
* `sameRun`: the steps give the run of `runLCH` (result and state);
* `entOrder`: the result's entries are those of `q`'s result, then those of
  `nexDon` (the copy's order);
* `flat`: the result has no fork, its entries no entry and no fork, its sure
  need `none` when `v` is hinted. -/
def tenSteps (a : Nat) (v q : Nomm) (L : Lazy LS) (th : Jmp) (g : Gen FM) :
    Option (Bool × Bool × Bool × Bool × Bool × Bool) := do
  let (nex, g1) ← simpleNextL (Map := FM) (CGoalL.next L th) g
  let ((don, rec, o), g2) ← intoL (Map := FM) nex a g1
  let donReg := match don.sure.ned with
    | Need.this d => decide (g.re ≤ d) && (HoonSet.toList don.sure.lok).isEmpty && don.fork.isEmpty && don.bond.isEmpty
    | _ => false
  let recFree := (entries don).isEmpty && (entries rec).isEmpty && don.fork.isEmpty && rec.fork.isEmpty
  let (nexR, g3) ← pastL (Map := FM) envH.cod ⟨rec, jmp0 o⟩ v [] g2
  let pastRec := match lazyBound (Map := FM) ⟨rec, jmp0 o⟩ [] g2 with
    | some (nb, gb) =>
        if hinted envH.cod v != some true ||
            (rec.sure.ned == Need.none && HoonSet.small rec.sure.lok && rec.fork.isEmpty) then
          entK nexR.laz == entK rec && nexR.laz.sure.ned == rec.sure.ned && nexR.th == jmp0 o && g3.bo == g2.bo
        else entK nexR.laz == entK nb.laz && nexR.th == nb.th && gb.bo == g3.bo && gb.re == g3.re
    | Option.none => false
  let (nexDon, g4) ← runLCH (S := LS) (Map := FM) envH sndH true Option.none v (CGoalL.next don nexR.th) [] g3
  let (nexDon, g5) ← pastL (Map := FM) envH.cod nexDon q [] g4
  let (nexRec, g6) ← runLCH (S := LS) (Map := FM) envH sndH true Option.none q (CGoalL.next nexR.laz nexDon.th) [] g5
  let (res, g7) ← copyL (Map := FM) nexRec nexDon.laz g6
  let sameRun := match runLCH (S := LS) (Map := FM) envH sndH true Option.none (Nomm.n10 a v q) (CGoalL.next L th) [] g with
    | some (r, gr) => entK r.laz == entK res.laz && r.th == res.th && gr.re == g7.re && gr.bo == g7.bo
    | Option.none => false
  let entOrder := (entK res.laz).map (·.1) == (entK nexRec.laz).map (·.1) ++ (entK nexDon.laz).map (·.1)
  let flat := res.laz.fork.isEmpty && (entK res.laz).all (fun e => e.2.2.1 == 0 && e.2.2.2) &&
    (hinted envH.cod v != some true || res.laz.sure.ned == Need.none)
  pure (donReg, recFree, pastRec, sameRun, entOrder, flat)

def allT (r : Option (Bool × Bool × Bool × Bool × Bool × Bool)) : Bool := r == some (true, true, true, true, true, true)

/-- The register goal `%next (lazy-from-reg 0) (jmp0 1)` from `gS`. -/
def tenReg (nm : Nomm) : Option (Bool × Bool × Bool × Bool × Bool × Bool) :=
  match nm with
  | Nomm.n10 a v q => tenSteps a v q (ofSure (lazyReg 0)) (jmp0 1) gS
  | _ => Option.none

-- the goal of `S3`'s `%10`: the direct call's result is `lazy-from-reg` of a register, no entry
#guard (runLCH (S := LS) (Map := FM) envH sndH true Option.none call22 gReg [] gS).map
  (fun (nex, _) => (nex.laz.sure.ned matches Need.this _) && (entries nex.laz).isEmpty && nex.laz.fork.isEmpty) == some true

-- `spotArm`'s `%10` and `d20`
#guard allT (tenReg tenS3)
#guard allT (tenReg (nmOf "d20"))

/-- Shapes: kept spots and `%bout`s over `[0 a]`, `[4 ..]`, a cons, and the
unhinted values, at axes 2, 3, 6, 7, 13, the recipient `[0 1]`. -/
def vals : List Nomm :=
  let ks : List Nomm := [z 13, z 3, z 2, Nomm.n4 (z 3), Nomm.cons (z 2) (z 3), Nomm.n1 (A 5)]
  ks.flatMap fun k => [sp k, bo k, k]
def shapes10 : List Nomm :=
  [2, 3, 6, 7, 13].flatMap fun a => vals.map fun v => Nomm.n10 a v (z 1)

#guard shapes10.length == 90
#guard shapes10.all fun nm => allT (tenReg nm)

/-- The same under the bond-free goals of `HintKeep.goals` that are `%next`:
everything but `donReg` (the donor need is the goal's need at the axis). -/
def tenGoals (nm : Nomm) : List (Option (Bool × Bool × Bool × Bool × Bool × Bool)) :=
  match nm with
  | Nomm.n10 a v q => goals.filterMap fun g => match g with
      | CGoalL.next L th => some (tenSteps a v q L th gS)
      | _ => Option.none
  | _ => []

def restT (r : Option (Bool × Bool × Bool × Bool × Bool × Bool)) : Bool :=
  match r with
  | some (_, true, true, true, true, true) => true
  | Option.none => true
  | _ => false

#guard (tenGoals tenS3).length > 0
#guard (tenS3 :: nmOf "d20" :: shapes10).all fun nm => (tenGoals nm).all restT

end HintTen

end Comp
end SkaModel
end Formalization
