import lemmas.Ska.SccLoopData
import lemmas.Ska.ShapeCol

/-! # The model of the loop of `+compile-scc-in` against the real compiler

The dumps of `SccLoopData.lean` (`tools/hoon/sccloop.py`: 18 formulas, 23 SCCs that go
through the loop: self-recursive bells (a decrement, a list walk, a tree walk, a loop that swaps
fields, a loop that grows one field, Ackermann), SCCs of two and three bells (even/odd, a cycle
of three, members that read different parts of a cell, a member that calls itself and another, four members reading shifted parts of a pair, a ring
rotating a triple).
The member compile is the dump itself (`look`: the record of the same bell, mode and views of
the kids), `+msg-need-ord` is `msgOrd` of `ShapeCol.lean` with the member's cape.  Checked:
* `traceOk`: the model's compiles are the compiler's, in the same order, with the same `keep`,
  `need-new`, `sur` (after `keep`), previous entry and `need-pessimized`; the sweeps set the same
  `any`; the entries of the final pass have the needs of the compiler's final map.  So the
  schedule (`dirty`, the ticks, `keep` after `4 * |scc|` compiles), `moved`, `chg` and
  `+msg-need-ord` agree, and every compile the model asks for is one the compiler made.
* `bOk`: property (b) on the real compiler: on `%done` `need-new` is that of the member's last
  `%must` compile and `need-pessimized` is the entry found (it never differs).
* `detOk`: the hypotheses `kidsOnly` and `shape` of `Hyp` on the dumps: two compiles of a bell on
  the same views of its kids give the same `need-new` and `sur`, `%must` and `%done` alike. -/

namespace Formalization.SkaModel.SccLoop
open Formalization.SkaModel

def Dump.kidsOf (d : Dump) (b : Nat) : List Nat := (d.kids.lookup b).getD []

def Dump.capeOf (d : Dump) (b : Nat) : Cape := (d.capes.lookup b).getD Cape.no

/-- The member compile of a dump: the record with the same bell, mode and views. -/
def look (d : Dump) (b : Nat) (m : Mode) (vn vs : Nat → NeedOrd) : Out NeedOrd :=
  let vw := (d.kidsOf b).map (fun k => (k, vn k, vs k))
  match d.comps.find? (fun r => decide (r.b = b) && decide (r.mode = m) && decide (r.views = vw)) with
  | some r => ⟨r.nn, r.surRaw⟩
  | none => ⟨NeedOrd.both NeedOrd.none NeedOrd.none, NeedOrd.both NeedOrd.none NeedOrd.none⟩

def cfgOf (d : Dump) : Cfg Nat NeedOrd where
  scc := d.mem
  order := d.order
  kids := d.kidsOf
  none := NeedOrd.none
  msg := fun b n p => Comp.msgOrd n p (d.capeOf b)
  comp := look d

structure Key where
  b : Nat
  mode : Mode
  keep : Bool
  nn : NeedOrd
  sur : NeedOrd
  prev : Option NeedOrd
  np : NeedOrd
  deriving DecidableEq

def Rec.key (r : Rec) : Key := ⟨r.b, r.mode, r.keep, r.nn, r.sur, r.prev, r.np⟩

def Ev.key (e : Ev Nat NeedOrd) : Key := ⟨e.b, e.mode, e.keep, e.nn, e.sur, e.prev, e.np⟩

def run (d : Dump) : Option (St Nat NeedOrd) := compileSccIn (cfgOf d) false 10 St.empty

def traceOk (d : Dump) : Bool :=
  match run d with
  | none => false
  | some s =>
    decide ((s.tr.map Ev.key : List Key) = (d.comps.map Rec.key : List Key)) &&
      decide (s.sw = d.sweeps) &&
      d.fin.all (fun (b, n) => decide (s.ml b = some n)) && decide (d.fin.length = d.mem.length)

def bOk (d : Dump) : Bool :=
  d.comps.all fun r =>
    r.mode != Mode.done ||
      (decide (r.prev = some r.np) &&
        match (d.comps.filter (fun q => decide (q.b = r.b) && decide (q.mode = Mode.must))).getLast? with
        | some q => decide (q.nn = r.nn)
        | none => false)

def detOk (d : Dump) : Bool :=
  d.comps.all fun r => d.comps.all fun q =>
    !(decide (r.b = q.b) && decide (r.views = q.views) && r.mode != Mode.may && q.mode != Mode.may) ||
      (decide (r.nn = q.nn) && decide (r.surRaw = q.surRaw))

#guard dumps.length = 23
#guard dumps.all traceOk
#guard dumps.all bOk
#guard dumps.all detOk
-- Every SCC took three sweeps (the last compiles nothing).
#guard dumps.all (fun d => d.sweeps = [true, true, false])
-- Compiles per SCC in the loop (`%must`): at most twice the members.
#guard dumps.all (fun d => (d.comps.filter (fun r => decide (r.mode = Mode.must))).length ≤ 2 * d.mem.length)
-- A need changed in the second sweep in three SCCs (`%deep`, `%deep4`, `%deep2` or `%rot3`):
-- `need-pessimized` there is not the previous need.
#guard (dumps.filter (fun d => d.comps.any (fun r => r.mode == Mode.must &&
    match r.prev with | some p => decide (p ≠ r.np) | none => false))).length = 3

end Formalization.SkaModel.SccLoop
