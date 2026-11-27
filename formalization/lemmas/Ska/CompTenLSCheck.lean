import lemmas.Ska.CompSixLSCheck

/-!
# `[10 [a v] q]` with parts that call: the checks before any proof

README Gaps 12.35.  Run on the executable model (`runLC`, `finishLUC` with
`envR`) and the interpreter model (`execEntry` with `oracleR`, which answers
an indirect call by `+mink`), against `+mink` on the formula (`minkF`), as in
`CompSixLSCheck.lean`.

* `sem all10`: the edits `[10 [a v] q]` for `a` in `1, 2, 3, 6, 7` and `v`,
  `q` each one of 6 parts (three call-free: `[0 3]`, `[0 7]`, `[1 7]`; three
  calling: the indirect call `[2 [0 3] [0 2]]`, `[4 call]`, `[call [0 2]]`):
  180 nomms, put into 8 contexts (alone under `%done`, head and tail of a
  cons with a calling part, `p` of `[7 p q]` with `q` the identity and with
  `q` a cons with a calling tail, so that `p`'s goal has entries, `q` of
  `[7 p q]`, the operand of `%4`, a branch of a `%6`), on the 24 subjects of
  `SixCheck`: the whole-subject code exists for every nomm and agrees with
  `+mink` on every run.
* `tally`: the 180 nomms alone under the 30 flat lazy goals of
  `CompPairLSXCheck.lean`, 2 jumps and the 2 states `SixCheck.statesH`,
  split by the parts' calls: runs, model fails, result NOT flat, entry labels
  NOT `Nodup`, jump at an entry, jump neither the goal's nor a new block.
  These are the conclusions of `LOKS.run`.
* `doneTally`: the same under `%done` from `gen0`.
-/

namespace Formalization
namespace SkaModel
namespace Comp
namespace TenCheck

open Nock Lazy SixCheck

/-- The Nock formula of a nomm without hints, with `%10`. -/
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
  | Nomm.n10 a v q => C (A 10) (C (C (A a) (fol v)) (fol q))
  | _ => A 0

def parts : List Nomm := [Nomm.n0 3, Nomm.n0 7, Nomm.n1 (A 7), ind, Nomm.n4 ind, Nomm.cons ind (Nomm.n0 2)]
def axes : List Nat := [1, 2, 3, 6, 7]
def tens : List Nomm := axes.flatMap fun a => parts.flatMap fun v => parts.map fun q => Nomm.n10 a v q
def pureTens : List Nomm := tens.filter Nomm.pure
def callTens : List Nomm := tens.filter fun nm => !nm.pure

def ctxs : List (Nomm → Nomm) :=
  [id, (Nomm.cons · ind), (Nomm.cons ind ·), (Nomm.n7 · (Nomm.n0 1)),
   (Nomm.n7 · (Nomm.cons (Nomm.cons (Nomm.n0 2) (Nomm.n0 3)) ind)), (Nomm.n7 (Nomm.n0 1) ·),
   (Nomm.n4 ·), (Nomm.n6 (Nomm.n3 (Nomm.n0 3)) · (Nomm.n0 2))]

def all10 : List Nomm := ctxs.flatMap fun k => tens.map k

/-- `(nomms, of them compiled, runs, runs where the code and Nock agree)`. -/
def sem (nms : List Nomm) : Nat × Nat × Nat × Nat :=
  nms.foldl (fun (a, b, c, d) nm =>
    match (finishLUC (S := LS) envR nm : Option (Straight FM)) with
    | some cd =>
      let ok := (subjects.filter fun s =>
        (execEntry libT oracleR () cd [s] [] (A 0)).map Prod.fst == minkF libT (A 0) 500 [] s (fol nm)).length
      (a + 1, b + 1, c + subjects.length, d + ok)
    | Option.none => (a + 1, b, c, d)) (0, 0, 0, 0)

/-- One run under `%next L th`: `(flat, Nodup of the entry labels, jump at no
entry, jump the goal's or a new block)`. -/
def one10 (nm : Nomm) (L : Lazy LS) (th : Jmp) (g : Gen FM) : Option (Bool × Bool × Bool × Bool) :=
  match runLC envR Option.none nm (CGoalL.next L th) [] g with
  | some (nex, _) =>
    let es := (entries nex.laz).map Prod.fst
    some (flatB nex.laz, es.Nodup, !(es.contains nex.th.there), nex.th == th || decide (g.bo ≤ nex.th.there))
  | Option.none => Option.none

/-- `(runs, model fails, not flat, labels not Nodup, jump at an entry, jump
neither the goal's nor new)`. -/
def tally (nms : List Nomm) : Nat × Nat × Nat × Nat × Nat × Nat :=
  let rs := nms.flatMap fun nm => LSXCheck.lazies.flatMap fun L => LSXCheck.jumps.flatMap fun th =>
    statesH.map fun g => one10 nm L th g
  (rs.length, (rs.filter (·.isNone)).length,
    (rs.filter fun x => match x with | some (f, _, _, _) => !f | _ => false).length,
    (rs.filter fun x => match x with | some (_, n, _, _) => !n | _ => false).length,
    (rs.filter fun x => match x with | some (_, _, j, _) => !j | _ => false).length,
    (rs.filter fun x => match x with | some (_, _, _, k) => !k | _ => false).length)

/-- Under `%done` from `gen0`: `(runs, model fails, not flat, labels not Nodup)`. -/
def doneTally (nms : List Nomm) : Nat × Nat × Nat × Nat :=
  nms.foldl (fun (a, b, c, d) nm =>
    match runLC envR Option.none nm (CGoalL.done : CGoalL LS) [] (gen0 : Gen FM) with
    | some (nex, _) => (a + 1, b, if flatB nex.laz then c else c + 1,
        if ((entries nex.laz).map Prod.fst).Nodup then d else d + 1)
    | Option.none => (a + 1, b + 1, c, d)) (0, 0, 0, 0)

-- The code of every nomm agrees with `+mink` on every subject.
#guard sem all10 == (1440, 1440, 34560, 34560)

-- Under the 30 flat lazy goals: the model never fails, the result is always
-- flat, its entry labels are distinct, its jump is at no entry and is the
-- goal's or a new block: every conclusion of `LOKS.run` that is not
-- semantic, for call-free parts (45 nomms) and calling parts (135 nomms).
#guard (tens.length, pureTens.length) == (180, 45)
#guard tally pureTens == (5400, 0, 0, 0, 0, 0)
#guard tally callTens == (16200, 0, 0, 0, 0, 0)
#guard doneTally tens == (180, 0, 0, 0)

end TenCheck
end Comp
end SkaModel
end Formalization
