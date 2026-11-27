import lemmas.Ska.CompDirectMEq
import lemmas.Ska.CompDirect

/-!
# `finishLUCM` against the real compiler

README Gaps 18 (track J, 2026-11-27).  The `#guard` lines below compare the
whole-subject code `finishLUCM` makes (after `+to-straight`, with its
renaming of registers and its chasing of hop-only blocks) with the raw blocks
of `+compiled-mono` that `tools/hoon/directdump2.hoon` prints, for seven
direct calls: all EQUAL, registers and labels as the Hoon's.

The callees: `R = [6 [3 [0 3]] [9 2 [10 [3 [0 7]] [0 1]]] [0 3]]` (need
`[~ this]`, `CompCall.lean`) and `R2 = [6 [3 [0 6]] [9 2 [10 [6 [0 13]] [0
1]]] [0 7]]`, whose need `[~ [this this]]` splits two levels deep (the dump
prints `need=[p=[%none ~] q=[p=[%this ~] q=[%this ~]]]`); both recur, so
`+inlined` keeps the call.  The cases, each `[8 [1 X] [9 2 [0 1]]]` with
`X = R` (`%dt`) or `R2` (`%et`), whose nomm is `[7 [[1 X] [0 1]] [7 [0 1]
[2 [0 1] [1 X] [X-bell ~]]]]`, placed:

* `%dt`, `%et`: a tail call (the optimistic `jmp`, the pessimistic `jsp`);
* `%dn`, `%en`: under `%4` (`cal`/`csl` hopping with their product to the
  merge block with a parameter);
* `%dc`, `%dk`: in the head and in the tail of a cons;
* `%dp`: as the test of a `%6` (the goal `%pick`).

The `dmRun` checks run that code with the interpreter model against an
oracle that answers the n-ary call by `+mink` on the subject rebuilt from
the arguments and the call by subject by `+mink` on the subject, and compare
with `+mink` on the formula; with `R2` and an atom sample the pessimistic
`jsp` runs (the subject does not split by `[~ [this this]]`).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

/-- `R2 = [6 [3 [0 6]] [9 2 [10 [6 [0 13]] [0 1]]] [0 7]]`. -/
def nounR2 : Noun :=
  C (A 6) (C (C (A 3) (C (A 0) (A 6)))
    (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 13))) (C (A 0) (A 1)))))) (C (A 0) (A 7))))

/-- The bell of `R2` in the dump: `[[[& |] [R2 0]] R2]`. -/
def bellR2 : Bell := ⟨Sock.mk (Cape.cell Cape.yes Cape.no) (C nounR2 (A 0)), nounR2⟩

/-- The environment of the dump: `R` needs `[~ this]`, `R2` needs `[~ [this
this]]`, both impure, no jet. -/
def envD : CallEnv :=
  ⟨fun b => if b = bellR then some (NeedOrd.pair NeedOrd.none NeedOrd.this)
     else if b = bellR2 then some (NeedOrd.pair NeedOrd.none (NeedOrd.pair NeedOrd.this NeedOrd.this))
     else Option.none,
   fun _ => NeedOrd.none, fun _ => false, fun _ => Option.none, fun _ => some false,
   fun _ _ _ _ _ => false⟩

/-- `[2 [0 1] [1 R2] [R2-bell ~]]`. -/
def callR2 : Nomm := Nomm.n2 (Nomm.n0 1) (Nomm.n1 nounR2) (some (bellR2, Option.none))

/-- The nomm of `[8 [1 R2] [9 2 [0 1]]]`. -/
def etNomm : Nomm :=
  Nomm.n7 (Nomm.cons (Nomm.n1 nounR2) (Nomm.n0 1)) (Nomm.n7 (Nomm.n0 1) callR2)

/-- The need, the argument count and the blocks `0 ..< n` of the
whole-subject code `finishLUCM` makes. -/
def monoOutM (nm : Nomm) (n : Nat) : Option (NeedOrd × Nat × List (Nat × Option Blob)) :=
  (finishLUCM (S := LS) (Map := FM) envD nm).map fun c => (c.need, c.nargs, blocksOf c n)

/-- A block with parameters. -/
abbrev bkp (par : List Nat) (body : List Pole) (fin : Termin) : Option Blob := some ⟨par, body, fin⟩

/-- A hop with one argument. -/
abbrev hpa (r o : Nat) : Termin := Termin.hop ⟨[some r], o⟩

/- `%dt`, `[8 [1 R] [9 2 [0 1]]]`: the tail call. -/
#guard monoOutM dtNomm 10 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 6] (hp 8)), (1, bk [] (Termin.jmp bellR [1])),
    (2, bk [] (Termin.jsp bellR 2)), (3, bk [Pole.mov 3 1] (hp 1)),
    (4, bk [Pole.hed 2 4, Pole.tal 2 3] (hp 3)), (5, bk [] (Termin.clq 2 (jmp0 4) (jmp0 2))),
    (6, none), (7, bk [Pole.con 5 6 2] (hp 5)), (8, bk [Pole.imm nounR 5] (hp 7)), (9, none)])

/- `%dn`, `[4 [8 [1 R] [9 2 [0 1]]]]`: the call under `%4`. -/
#guard monoOutM (Nomm.n4 dtNomm) 13 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 12] (hp 11)), (1, bk [Pole.inc 2 1] (Termin.don 1)),
    (2, bk [Pole.mov 4 2] (hp 1)), (3, bkp [5] [Pole.mov 5 4] (hp 2)),
    (4, bk [Pole.cal bellR [3] 7] (hpa 7 3)), (5, bk [Pole.csl bellR 6 8] (hpa 8 3)),
    (6, bk [Pole.mov 9 3] (hp 4)), (7, bk [Pole.hed 6 10, Pole.tal 6 9] (hp 6)),
    (8, bk [] (Termin.clq 6 (jmp0 7) (jmp0 5))), (9, none), (10, bk [Pole.con 11 12 6] (hp 8)),
    (11, bk [Pole.imm nounR 11] (hp 10)), (12, none)])

/- `%dc`, `[[8 [1 R] [9 2 [0 1]]] [0 1]]`: the call in the head of a cons. -/
#guard monoOutM (Nomm.cons dtNomm (Nomm.n0 1)) 15 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 13] (hp 13)), (1, bk [] (Termin.don 1)),
    (2, bk [Pole.con 2 3 1] (hp 1)), (3, bk [Pole.mov 0 3] (hp 2)), (4, bk [Pole.mov 5 2] (hp 3)),
    (5, bkp [6] [Pole.mov 6 5] (hp 4)), (6, bk [Pole.cal bellR [4] 8] (hpa 8 5)),
    (7, bk [Pole.csl bellR 7 9] (hpa 9 5)), (8, bk [Pole.mov 10 4] (hp 6)),
    (9, bk [Pole.hed 7 11, Pole.tal 7 10] (hp 8)), (10, bk [] (Termin.clq 7 (jmp0 9) (jmp0 7))),
    (11, none), (12, bk [Pole.con 12 13 7] (hp 10)), (13, bk [Pole.imm nounR 12] (hp 12)), (14, none)])

/- `%dk`, `[[0 1] [8 [1 R] [9 2 [0 1]]]]`: the call in the tail of a cons. -/
#guard monoOutM (Nomm.cons (Nomm.n0 1) dtNomm) 15 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 13] (hp 13)), (1, bk [] (Termin.don 1)),
    (2, bk [Pole.con 2 3 1] (hp 1)), (3, bk [Pole.mov 0 2] (hp 2)), (4, bk [Pole.mov 5 3] (hp 3)),
    (5, bkp [6] [Pole.mov 6 5] (hp 4)), (6, bk [Pole.cal bellR [4] 8] (hpa 8 5)),
    (7, bk [Pole.csl bellR 7 9] (hpa 9 5)), (8, bk [Pole.mov 10 4] (hp 6)),
    (9, bk [Pole.hed 7 11, Pole.tal 7 10] (hp 8)), (10, bk [] (Termin.clq 7 (jmp0 9) (jmp0 7))),
    (11, none), (12, bk [Pole.con 12 13 7] (hp 10)), (13, bk [Pole.imm nounR 12] (hp 12)), (14, none)])

/- `%dp`, `[6 [8 [1 R] [9 2 [0 1]]] [1 0] [1 1]]`: the call for `%pick`. -/
#guard monoOutM (Nomm.n6 dtNomm (Nomm.n1 (A 0)) (Nomm.n1 (A 1))) 17 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 13] (hp 15)), (1, bk [Pole.imm (A 1) 1] (Termin.don 1)),
    (2, bk [Pole.imm (A 0) 2] (Termin.don 2)), (3, none), (4, none),
    (5, bk [] (Termin.brn 4 (jmp0 2) (jmp0 1))), (6, bk [Pole.mov 5 4] (hp 5)),
    (7, bkp [6] [Pole.mov 6 5] (hp 6)), (8, bk [Pole.cal bellR [3] 8] (hpa 8 7)),
    (9, bk [Pole.csl bellR 7 9] (hpa 9 7)), (10, bk [Pole.mov 10 3] (hp 8)),
    (11, bk [Pole.hed 7 11, Pole.tal 7 10] (hp 10)), (12, bk [] (Termin.clq 7 (jmp0 11) (jmp0 9))),
    (13, none), (14, bk [Pole.con 12 13 7] (hp 12)), (15, bk [Pole.imm nounR 12] (hp 14)), (16, none)])

/- `%et`, `[8 [1 R2] [9 2 [0 1]]]`: the tail call, the need split two levels deep. -/
#guard monoOutM etNomm 13 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 9] (hp 11)), (1, bk [] (Termin.jmp bellR2 [1, 2])),
    (2, bk [] (Termin.jsp bellR2 3)), (3, bk [Pole.mov 6 2] (hp 1)), (4, bk [Pole.mov 7 1] (hp 3)),
    (5, bk [Pole.hed 4 7, Pole.tal 4 6] (hp 4)), (6, bk [] (Termin.clq 4 (jmp0 5) (jmp0 2))),
    (7, bk [Pole.hed 3 5, Pole.tal 3 4] (hp 6)), (8, bk [] (Termin.clq 3 (jmp0 7) (jmp0 2))),
    (9, none), (10, bk [Pole.con 8 9 3] (hp 8)), (11, bk [Pole.imm nounR2 8] (hp 10)), (12, none)])

/- `%en`, `[4 [8 [1 R2] [9 2 [0 1]]]]`: under `%4`, the need split two levels deep. -/
#guard monoOutM (Nomm.n4 etNomm) 16 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 15] (hp 14)), (1, bk [Pole.inc 2 1] (Termin.don 1)),
    (2, bk [Pole.mov 5 2] (hp 1)), (3, bkp [6] [Pole.mov 6 5] (hp 2)),
    (4, bk [Pole.cal bellR2 [3, 4] 8] (hpa 8 3)), (5, bk [Pole.csl bellR2 7 9] (hpa 9 3)),
    (6, bk [Pole.mov 12 4] (hp 4)), (7, bk [Pole.mov 13 3] (hp 6)),
    (8, bk [Pole.hed 10 13, Pole.tal 10 12] (hp 7)), (9, bk [] (Termin.clq 10 (jmp0 8) (jmp0 5))),
    (10, bk [Pole.hed 7 11, Pole.tal 7 10] (hp 9)), (11, bk [] (Termin.clq 7 (jmp0 10) (jmp0 5))),
    (12, none), (13, bk [Pole.con 14 15 7] (hp 11)), (14, bk [Pole.imm nounR2 14] (hp 13)), (15, none)])

/-! ## The code run by the interpreter model -/

/-- An oracle for `R` and `R2`: the n-ary call by `+mink` on the subject
rebuilt from the arguments (`[R v]`, `[R2 [a c]]`), the call by subject by
`+mink` on the subject, an indirect call by `+mink`. -/
def oracleD : Oracle Unit :=
  ⟨fun st b m vals t gul =>
    let run := fun (s : Noun) => (minkF libT gul 500 t s b.fol).map fun r => (r, st)
    if b = bellR then
      (match m, vals with
       | false, [v] => run (C nounR v)
       | true, [s] => run s
       | _, _ => Option.none)
    else if b = bellR2 then
      (match m, vals with
       | false, [a, c] => run (C nounR2 (C a c))
       | true, [s] => run s
       | _, _ => Option.none)
    else Option.none,
   fun st u f gul => (minkF libT gul 500 [] u f).map fun r => (r, st)⟩

/-- The interpreter model on `finishLUCM`'s code of `nm`, against `+mink`
on the formula `f`. -/
def dmRun (nm : Nomm) (f s : Noun) : Bool :=
  match (finishLUCM (S := LS) envD nm : Option (Straight FM)) with
  | some c => (execEntry libT oracleD () c [s] [] (A 0)).map Prod.fst == minkF libT (A 0) 500 [] s f
  | Option.none => false

/-- `[8 [1 R2] [9 2 [0 1]]]`. -/
def etFol : Noun := C (A 8) (C (C (A 1) nounR2) (C (A 9) (C (A 2) (C (A 0) (A 1)))))

#guard dmRun dtNomm dtFol (C (A 1) (C (A 2) (A 3)))
#guard dmRun dtNomm dtFol (A 7)
#guard dmRun (Nomm.n4 dtNomm) (C (A 4) dtFol) (C (A 0) (A 0))
#guard dmRun (Nomm.cons dtNomm (Nomm.n0 1)) (C dtFol (C (A 0) (A 1))) (C (A 1) (C (A 2) (A 3)))
#guard dmRun etNomm etFol (C (C (A 1) (A 2)) (A 3))
#guard dmRun etNomm etFol (A 7)
#guard dmRun etNomm etFol (C (A 7) (A 3))
#guard dmRun (Nomm.n4 etNomm) (C (A 4) etFol) (C (C (A 1) (A 2)) (A 3))
#guard dmRun (Nomm.n4 etNomm) (C (A 4) etFol) (A 7)
#guard minkF libT (A 0) 500 [] (C (C (A 1) (A 2)) (A 3)) etFol == some (Tone.zero (A 3))

end Comp
end SkaModel
end Formalization
