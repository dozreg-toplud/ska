import lemmas.Ska.CompDirect
import lemmas.Ska.CompPairLSXCheck

/-!
# `[6 c a b]` with parts that call: the checks before any proof

README Gaps 12.34.  Run on the executable model (`runLC`, `finishLUC` with
`envR`) and the interpreter model (`execEntry` with `oracleR`, which answers
an indirect call by `+mink`), against `+mink` on the formula (`minkF`).

* `sem all6`: 5,145 nomms, each a `[6 c a b]` (`c` one of 5 tests, three of
  them calling, `a` and `b` each one of 7 branches, four of them calling:
  245 nomms) put into one of 21 contexts: alone (`%done`), head or tail of a
  cons (with a pure part, with a calling part, with `[4 call]`, the head of
  a cons inside a cons with a calling tail), `p` of `[7 p q]` (`q` the
  identity, `[3 [0 1]]`, and two cons with a calling tail, so that `p`'s goal
  has entries), `q` of `[7 p q]` (three `p`), the operand of `%4` and `%3`,
  `p` of `%5`, the subject and the formula of an indirect call, the test and
  a branch of a `%6`.  Each on 24 subjects `[F D]`, where the indirect call
  `[2 [0 3] [0 2]]` runs `F` on `D`.  The whole-subject code exists for every
  nomm, and the code and `+mink` agree on all 123,480 runs.
* `tally`: the 245 nomms alone under the 30 flat lazy goals of
  `CompPairLSXCheck.lean`, 2 jumps and 2 states whose entry blocks are
  tagged `[hop]` blocks (`genAtH`; with the untagged `genAt`, `+kerf` and
  `+fork` fail at `+proxy`).  Per phase of `sixNextLC` (S: `+fork-sure`, K:
  `+kerf`, F: `+fork`, L: `+leap` first): runs, model fails, result NOT flat,
  entry labels NOT `Nodup`, jump at an entry.  Every phase is met; the
  result is never flat; the labels repeat exactly when the test calls
  (`+past-fork` binds each branch's need in a bond at the fork's own label);
  the jump is never at an entry.
* `doneTally`: the same under `%done` from `gen0`.
* `phasesUnder`: the phases the `%6` meets inside the contexts with entries
  (head of a cons with a calling tail, `p` of `[7 p q]` with such a `q`), so
  the semantic check covers K, F and L, not only S.
-/

namespace Formalization
namespace SkaModel
namespace Comp
namespace SixCheck

open Nock Lazy

/-- The Nock formula of a nomm without hints (indirect calls only). -/
def fol : Nomm → Noun
  | Nomm.cons p q => C (fol p) (fol q)
  | Nomm.n0 a => C (A 0) (A a)
  | Nomm.n1 k => C (A 1) k
  | Nomm.n2 p q _ => C (A 2) (C (fol p) (fol q))
  | Nomm.n3 p => C (A 3) (fol p)
  | Nomm.n4 p => C (A 4) (fol p)
  | Nomm.n5 p q => C (A 5) (C (fol p) (fol q))
  | Nomm.n6 c a b => C (A 6) (C (fol c) (C (fol a) (fol b)))
  | Nomm.n7 p q => C (A 7) (C (fol p) (fol q))
  | _ => A 0

def ind : Nomm := Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none

/-- Formulas `F` for the indirect call: `0`, `1`, the data itself, its cell
test, its test against `4`, its increment. -/
def fs : List Noun := [C (A 1) (A 0), C (A 1) (A 1), C (A 0) (A 1), C (A 3) (C (A 0) (A 1)),
  C (A 5) (C (C (A 0) (A 1)) (C (A 1) (A 4))), C (A 4) (C (A 0) (A 1))]
def ds : List Noun := [A 0, A 4, C (A 1) (A 2), C (C (A 0) (A 1)) (A 3)]
def subjects : List Noun := fs.flatMap fun f => ds.map fun d => C f d

def tests : List Nomm :=
  [ind, Nomm.n3 ind, Nomm.n5 ind (Nomm.n1 (A 0)), Nomm.n3 (Nomm.n0 3), Nomm.n5 (Nomm.n0 3) (Nomm.n1 (A 4))]
def brs : List Nomm := [Nomm.n0 2, Nomm.n0 3, ind, Nomm.n4 ind, Nomm.cons ind (Nomm.n0 2),
  Nomm.cons (Nomm.n0 3) (Nomm.n0 2), Nomm.n1 (A 7)]
def sixes : List Nomm := tests.flatMap fun c => brs.flatMap fun a => brs.map fun b => Nomm.n6 c a b
def pureSixes : List Nomm := sixes.filter fun nm => match nm with | Nomm.n6 c _ _ => c.pure | _ => false

def ctxs : List (Nomm → Nomm) :=
  [id, (Nomm.cons · (Nomm.n0 3)), (Nomm.cons (Nomm.n0 2) ·), (Nomm.cons · ind), (Nomm.cons ind ·),
   (Nomm.n7 · (Nomm.n0 1)), (Nomm.n7 · (Nomm.n3 (Nomm.n0 1))), (Nomm.n7 (Nomm.n0 1) ·),
   (Nomm.n7 (Nomm.cons (Nomm.n0 2) (Nomm.n0 3)) ·), (Nomm.n7 (Nomm.cons ind (Nomm.n0 3)) ·),
   (Nomm.n4 ·), (Nomm.n3 ·), (Nomm.n5 · (Nomm.n0 3)), (Nomm.n2 · (Nomm.n0 2) Option.none),
   (Nomm.n2 (Nomm.n0 1) · Option.none), (Nomm.n6 · (Nomm.n0 2) (Nomm.n0 3)), (Nomm.n6 ind · (Nomm.n0 3)),
   (fun x => Nomm.cons (Nomm.cons x (Nomm.n0 2)) ind), (Nomm.n7 · (Nomm.cons (Nomm.cons (Nomm.n0 2) (Nomm.n0 3)) ind)),
   (Nomm.n7 · (Nomm.cons (Nomm.n0 2) ind)), (Nomm.cons · (Nomm.n4 ind))]

def all6 : List Nomm := ctxs.flatMap fun k => sixes.map k

/-- `(nomms, of them compiled, runs, runs where the code and Nock agree)`. -/
def sem (nms : List Nomm) : Nat × Nat × Nat × Nat :=
  nms.foldl (fun (a, b, c, d) nm =>
    match (finishLUC (S := LS) envR nm : Option (Straight FM)) with
    | some cd =>
      let ok := (subjects.filter fun s =>
        (execEntry libT oracleR () cd [s] [] (A 0)).map Prod.fst == minkF libT (A 0) 500 [] s (fol nm)).length
      (a + 1, b + 1, c + subjects.length, d + ok)
    | Option.none => (a + 1, b, c, d)) (0, 0, 0, 0)

-- The code of every nomm agrees with `+mink` on every subject.
#guard sem all6 == (5145, 5145, 123480, 123480)

/-! ## The shape of the result under flat lazy goals -/

def flatB (l : Lazy LS) : Bool := l.fork.isEmpty && l.bond.all fun e => e.2.fork.isEmpty && e.2.bond.isEmpty

/-- The phase of `sixNextLC` (fuel 3) a goal sends the `%6` to. -/
def phase (L : Lazy LS) (q r : Nomm) : String :=
  match leap L q r with
  | Option.none => "leapcrash"
  | some (some _) => "L"
  | some Option.none =>
    if !(noneEquivalentL (Lazy.mk Sure.bunt L.fork L.bond)) then
      if (whole q && whole r) || thisOnly L || lazyBig (softLess noSoft L) || softFork noSoft (fun _ => false) L
      then "K" else "F"
    else "S"

/-- A state with registers from `re` and labels from `bo`, the labels below
`bo` holding tagged `[hop]` blocks, as the entries of a goal are. -/
def genAtH (re bo : Nat) : Gen FM :=
  ⟨re, bo, 0, false,
   ⟨fun k => if 1 ≤ k ∧ k < bo then some ⟨[], [], Termin.hop (jmp0 0)⟩ else Option.none,
    (List.range bo).filter (1 ≤ ·), fun k => by
      by_cases h : 1 ≤ k ∧ k < bo
      · simp [h, List.mem_filter, List.mem_range]
      · simp only [h, if_false, Option.isSome_none, List.mem_filter, List.mem_range, decide_eq_true_eq]
        constructor
        · intro ⟨a, b⟩; exact absurd ⟨b, a⟩ h
        · intro e; cases e⟩,
   ⟨fun k => if 1 ≤ k ∧ k < bo then some [] else Option.none,
    (List.range bo).filter (1 ≤ ·), fun k => by
      by_cases h : 1 ≤ k ∧ k < bo
      · simp [h, List.mem_filter, List.mem_range]
      · simp only [h, if_false, Option.isSome_none, List.mem_filter, List.mem_range, decide_eq_true_eq]
        constructor
        · intro ⟨a, b⟩; exact absurd ⟨b, a⟩ h
        · intro e; cases e⟩, ⟨fun _ => Option.none, [], fun k => by simp⟩⟩

def statesH : List (Gen FM) := [genAtH 4 4, genAtH 10 3]

/-- One run: the phase, and `(flat, Nodup of the entry labels, jump at no entry)`. -/
def one6 (nm : Nomm) (L : Lazy LS) (th : Jmp) (g : Gen FM) : String × Option (Bool × Bool × Bool) :=
  let ph := match nm with | Nomm.n6 _ q r => phase L q r | _ => "?"
  match runLC envR Option.none nm (CGoalL.next L th) [] g with
  | some (nex, _) =>
    let es := (entries nex.laz).map Prod.fst
    (ph, some (flatB nex.laz, es.Nodup, !(es.contains nex.th.there)))
  | Option.none => (ph, Option.none)

/-- Per phase: `(runs, model fails, not flat, labels not Nodup, jump at an entry)`. -/
def tally (nms : List Nomm) : List (String × Nat × Nat × Nat × Nat × Nat) :=
  let rs := nms.flatMap fun nm => LSXCheck.lazies.flatMap fun L => LSXCheck.jumps.flatMap fun th =>
    statesH.map fun g => one6 nm L th g
  ["S", "K", "F", "L"].map fun ph =>
    let xs := rs.filter (·.1 == ph)
    (ph, xs.length, (xs.filter (·.2.isNone)).length,
      (xs.filter fun x => match x.2 with | some (f, _, _) => !f | _ => false).length,
      (xs.filter fun x => match x.2 with | some (_, n, _) => !n | _ => false).length,
      (xs.filter fun x => match x.2 with | some (_, _, j) => !j | _ => false).length)

-- 29,400 runs: the result is never flat; the labels repeat on the 3/5 of
-- the runs whose test calls; never with a call-free test.
#guard tally sixes == [("S", 5880, 0, 5880, 3528, 0), ("K", 5840, 0, 5840, 3504, 0),
  ("F", 15640, 0, 15640, 9384, 0), ("L", 2040, 0, 2040, 1224, 0)]
#guard tally pureSixes == [("S", 2352, 0, 2352, 0, 0), ("K", 2336, 0, 2336, 0, 0),
  ("F", 6256, 0, 6256, 0, 0), ("L", 816, 0, 816, 0, 0)]

/-- Under `%done` from `gen0`: `(runs, model fails, not flat, labels not Nodup)`. -/
def doneTally (nms : List Nomm) : Nat × Nat × Nat × Nat :=
  nms.foldl (fun (a, b, c, d) nm =>
    match runLC envR Option.none nm (CGoalL.done : CGoalL LS) [] (gen0 : Gen FM) with
    | some (nex, _) => (a + 1, b, if flatB nex.laz then c else c + 1,
        if ((entries nex.laz).map Prod.fst).Nodup then d else d + 1)
    | Option.none => (a + 1, b + 1, c, d)) (0, 0, 0, 0)

#guard doneTally sixes == (245, 0, 245, 147)
#guard doneTally pureSixes == (98, 0, 98, 0)

/-! ## The phases met inside the contexts with entries -/

/-- The goal of the head of `[X q]` under `%done`. -/
def headGoal (q : Nomm) : Option (Lazy LS) :=
  let g := (gen0 : Gen FM)
  let g := ({ g with re := g.re + 1 }.emitted ⟨[], [], Termin.don g.re⟩)
  match (do
    let (hed, tel, o) ← splitL ⟨ofSure (lazyReg 0), jmp0 0⟩
    let nexh ← pastL envR.cod ⟨hed, jmp0 o⟩ q []
    let _ ← runLC envR Option.none q (CGoalL.next tel nexh.th) []
    pure nexh.laz : CM FM (Lazy LS)) g with
  | some (l, _) => some l
  | Option.none => Option.none

/-- The goal of `p` in `[7 p q]` under `%done`: `q`'s result. -/
def qGoal (q : Nomm) : Option (Lazy LS) :=
  (runLC envR Option.none q (CGoalL.done : CGoalL LS) [] (gen0 : Gen FM)).map fun x => x.1.laz

def phasesUnder (l : Option (Lazy LS)) : List (String × Nat) :=
  let xs := match l with
    | some L => sixes.map fun nm => match nm with | Nomm.n6 _ q r => phase L q r | _ => "?"
    | Option.none => ["none"]
  ["S", "K", "F", "L"].map fun p => (p, (xs.filter (· == p)).length)

#guard phasesUnder (headGoal ind) == [("S", 0), ("K", 235), ("F", 0), ("L", 10)]
#guard phasesUnder (headGoal (Nomm.n4 ind)) == [("S", 0), ("K", 235), ("F", 0), ("L", 10)]
#guard phasesUnder (qGoal (Nomm.cons (Nomm.cons (Nomm.n0 2) (Nomm.n0 3)) ind)) ==
  [("S", 0), ("K", 45), ("F", 170), ("L", 30)]
#guard phasesUnder (qGoal (Nomm.cons (Nomm.n0 2) ind)) == [("S", 0), ("K", 45), ("F", 185), ("L", 15)]
#guard phasesUnder (qGoal (Nomm.n0 1)) == [("S", 245), ("K", 0), ("F", 0), ("L", 0)]

end SixCheck
end Comp
end SkaModel
end Formalization
