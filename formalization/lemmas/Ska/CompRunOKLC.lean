import lemmas.Ska.CompConsT

/-!
# One relation for runs that call, under any lazy goal: `RunOKLC`

README Gaps 12.20.  `RunOKL` (`CompLazyGoal.lean`) is the relation of a
call-free run under a goal `%next L th` with entries; `RunOKGC`
(`CompUOKC.lean`) is the relation of a run that may call, under a goal
without entries.  `RunOKLC` is both at once.

## The raw blocks

`tools/hoon/calldump2.hoon` (whole-subject version, subject unknown, before
`+optimize`; `vN` registers, `N` labels), checked against `finishLUC` by the
`#guard`s below.

`[[2 [0 3] [0 2]] [2 [0 3] [0 2]]]` (`%cc2`, calls in both halves, subject
`[[4 0 1] 5]`, product `[6 6]`): `0: v0 -> cel, hed -> va, tal -> v9,
hop 9`; `9: nok v9 va -> v7, hop 7` (the head's call, its `+kerf` block a
bare hop under the bond goal, chased); `7: v0 -> cel, hed -> v6, tal -> v5,
hop 5` (the `+past` of the tail's need behind the head's call, filled from
the subject by the final pass); `5: nok v5 v6 -> v4, hop 4` (the tail's
call); `4: mov v4 v3, hop 3`; `3: mov v7 v2, hop 2` (the bond block of the
head's need behind the tail's call: the head's `+kern` put `mov v7 v2`
there, `v7` the head call's product, kept across the tail's call); `2: con
v2 v3 -> v1`; `1: don v1`.  So the head is the indirect call under the bond
goal `mk bunt [] [(3, this v2)]`, its `D` is `this v7` (`+kern`'s register)
and its `W` the call's product, a value of the oracle: `W` is no function of
the subject, and the relation takes a witness relation `Q s v d w` in place
of `D`, `W`.

`[7 [2 [0 3] [0 2]] [4 [0 1]]]` (`%s7a`, product `7`): `0: v0 -> v5, v4,
hop 3`; `3: nok v4 v5 -> v3, hop 2`; `2: mov v3 v2, hop 1`; `1: inc v2 v1,
don v1`.  The call runs under `q`'s result goal `%next (this v2)`, no entries.

`[7 [[0 1] [0 1]] [2 [0 3] [0 2]]]` (`%s7b`, subject `[0 1]`, product
`[0 1]`): `0: mov v0 v4, hop 6`; `6: mov v4 v3, hop 3` (the copy of the
cons's halves, both the subject); `3: nok v3 v4 -> v2, hop 2`; `2`, `1`.

`[[7 [0 3] [4 [0 1]]] [2 [0 3] [0 2]]]` (`%s7c`, product `[6 6]`): `0: v0
-> v6, v9, hop 8`; `8: mov v9 v5, hop 7`; `7: inc v9 v7, hop 5` (the head:
`[4 [0 1]]` consumes the bond entry, `D = this v7`, then `[0 3]` under a
goal without entries); `5: nok v5 v6 -> v4`; `4: mov v4 v3`; `3: mov v7 v2`
(bond); `2: con`; `1: don`.

`[[4 [2 [0 3] [0 2]]] [2 [0 3] [0 2]]]` (`%h4c`) and `[[7 [2 [0 3] [0 2]]
[4 [0 1]]] [2 [0 3] [0 2]]]` (`%h7c`, the same nomm after the analysis
folds nothing; identical blocks): `10: nok v11 v12 -> v10`; `9: mov v10 v9`;
`8: inc v9 v7` (the head's increment after its call); `7: v0 -> v6, v5`
(past of the tail behind the head); `5: nok v5 v6 -> v4`; `4`; `3: mov v7
v2` (bond, `v7` written before the tail's call); `2: con`.

`[2 [2 [0 3] [0 2]] [0 2]]` (`%isc`, an indirect call whose subject part
calls, product `7`): `6: nok v6 v7 -> v5`; `5: mov v5 v3`; `4: v0 -> cel,
hed -> v4, hop 3` (past of the formula part `[0 2]` behind the subject part's
call); `3: nok v3 v4 -> v2`.  `[2 [0 3] [2 [0 1] [0 2]]]` (`%ifc`, subject
`[[0 3] [0 1]]`, product `[0 1]`): `0: v0 -> v8, hed -> v7, tal -> v3,
hop 6`; `6: mov v8 v6` (copy); `5: nok v6 v7 -> v5` (the formula part's
call); `4: mov v5 v4`; `3: nok v3 v4 -> v2` (`v3`, the subject part's
register, kept across the formula part's call).

`[[0 1] [[2 [0 3] [0 2]] [0 1]]]` (`%cct`): `0: v0 -> v8, v7, hop 7`;
`7: nok v7 v8 -> v6`; `6: mov v6 v4`; `5: mov v0 v5` (past of the inner
tail behind the call); `4: con v4 v5 -> v3`; `3: mov v0 v2` (bond of the
outer head `[0 1]` behind the inner cons, kept by `[0 1]` and filled by the
final pass); `2: con`; `1: don`.

`[7 [[2 [0 3] [0 2]] [0 1]] [2 [0 3] [0 2]]]` (`%s7d`) and `[7 [[2 [0 3]
[0 2]] [0 3]] [[0 2] [0 3]]]` (`%s7e`): `q` runs under `%done`, then the cons
whose head calls under `q`'s result goal, a `pair` of registers, so
`+split` puts no `con` and the tail's `+past` block (`6: mov v0 v3`,
`5: v0 -> cel, tal -> v3`) fills the tail's half from the subject.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

/-! ## The raw blocks -/

-- `%cc2`
#guard monoOutC envR (Nomm.cons (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) 11 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 11, Pole.cel 11, Pole.hed 11 13, Pole.mov 13 10, Pole.tal 11 12, Pole.mov 12 9] (hp 9)),
    (1, bk [] (Termin.don 1)),
    (2, bk [Pole.con 2 3 1] (hp 1)),
    (3, bk [Pole.mov 7 2] (hp 2)),
    (4, bk [Pole.mov 4 3] (hp 3)),
    (5, bk [Pole.nok 5 6 4] (hp 4)),
    (6, none),
    (7, bk [Pole.mov 0 15, Pole.cel 15, Pole.hed 15 17, Pole.mov 17 6, Pole.tal 15 16, Pole.mov 16 5] (hp 5)),
    (8, none),
    (9, bk [Pole.nok 9 10 7] (hp 7)),
    (10, none)])

-- `%s7a`
#guard monoOutC envR (Nomm.n7 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n4 (Nomm.n0 1))) 5 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 6, Pole.cel 6, Pole.hed 6 8, Pole.mov 8 5, Pole.tal 6 7, Pole.mov 7 4] (hp 3)),
    (1, bk [Pole.inc 2 1] (Termin.don 1)),
    (2, bk [Pole.mov 3 2] (hp 1)),
    (3, bk [Pole.nok 4 5 3] (hp 2)),
    (4, none)])

-- `%s7b`
#guard monoOutC envR (Nomm.n7 (Nomm.cons (Nomm.n0 1) (Nomm.n0 1)) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) 8 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 4] (hp 6)),
    (1, bk [] (Termin.don 1)),
    (2, bk [Pole.mov 2 1] (hp 1)),
    (3, bk [Pole.nok 3 4 2] (hp 2)),
    (4, none),
    (5, none),
    (6, bk [Pole.mov 4 3] (hp 3)),
    (7, none)])

-- `%s7c`
#guard monoOutC envR (Nomm.cons (Nomm.n7 (Nomm.n0 3) (Nomm.n4 (Nomm.n0 1))) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) 10 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 10, Pole.cel 10, Pole.hed 10 12, Pole.mov 12 6, Pole.tal 10 11, Pole.mov 11 9] (hp 8)),
    (1, bk [] (Termin.don 1)),
    (2, bk [Pole.con 2 3 1] (hp 1)),
    (3, bk [Pole.mov 7 2] (hp 2)),
    (4, bk [Pole.mov 4 3] (hp 3)),
    (5, bk [Pole.nok 5 6 4] (hp 4)),
    (6, none),
    (7, bk [Pole.inc 9 7] (hp 5)),
    (8, bk [Pole.mov 9 5] (hp 7)),
    (9, none)])

-- `%h4c`
#guard monoOutC envR (Nomm.cons (Nomm.n4 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) 12 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 13, Pole.cel 13, Pole.hed 13 15, Pole.mov 15 12, Pole.tal 13 14, Pole.mov 14 11] (hp 10)),
    (1, bk [] (Termin.don 1)),
    (2, bk [Pole.con 2 3 1] (hp 1)),
    (3, bk [Pole.mov 7 2] (hp 2)),
    (4, bk [Pole.mov 4 3] (hp 3)),
    (5, bk [Pole.nok 5 6 4] (hp 4)),
    (6, none),
    (7, bk [Pole.mov 0 17, Pole.cel 17, Pole.hed 17 19, Pole.mov 19 6, Pole.tal 17 18, Pole.mov 18 5] (hp 5)),
    (8, bk [Pole.inc 9 7] (hp 7)),
    (9, bk [Pole.mov 10 9] (hp 8)),
    (10, bk [Pole.nok 11 12 10] (hp 9)),
    (11, none)])

-- `%h7c`
#guard monoOutC envR (Nomm.cons (Nomm.n7 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n4 (Nomm.n0 1))) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) 12 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 13, Pole.cel 13, Pole.hed 13 15, Pole.mov 15 12, Pole.tal 13 14, Pole.mov 14 11] (hp 10)),
    (1, bk [] (Termin.don 1)),
    (2, bk [Pole.con 2 3 1] (hp 1)),
    (3, bk [Pole.mov 7 2] (hp 2)),
    (4, bk [Pole.mov 4 3] (hp 3)),
    (5, bk [Pole.nok 5 6 4] (hp 4)),
    (6, none),
    (7, bk [Pole.mov 0 17, Pole.cel 17, Pole.hed 17 19, Pole.mov 19 6, Pole.tal 17 18, Pole.mov 18 5] (hp 5)),
    (8, bk [Pole.inc 9 7] (hp 7)),
    (9, bk [Pole.mov 10 9] (hp 8)),
    (10, bk [Pole.nok 11 12 10] (hp 9)),
    (11, none)])

-- `%cct`
#guard monoOutC envR (Nomm.cons (Nomm.n0 1) (Nomm.cons (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 1))) 9 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 9, Pole.cel 9, Pole.hed 9 11, Pole.mov 11 8, Pole.tal 9 10, Pole.mov 10 7] (hp 7)),
    (1, bk [] (Termin.don 1)),
    (2, bk [Pole.con 2 3 1] (hp 1)),
    (3, bk [Pole.mov 0 2] (hp 2)),
    (4, bk [Pole.con 4 5 3] (hp 3)),
    (5, bk [Pole.mov 0 5] (hp 4)),
    (6, bk [Pole.mov 6 4] (hp 5)),
    (7, bk [Pole.nok 7 8 6] (hp 6)),
    (8, none)])

-- `%isc`
#guard monoOutC envR (Nomm.n2 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 2) Option.none) 8 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 8, Pole.cel 8, Pole.hed 8 10, Pole.mov 10 7, Pole.tal 8 9, Pole.mov 9 6] (hp 6)),
    (1, bk [] (Termin.don 1)),
    (2, bk [Pole.mov 2 1] (hp 1)),
    (3, bk [Pole.nok 3 4 2] (hp 2)),
    (4, bk [Pole.mov 0 12, Pole.cel 12, Pole.hed 12 14, Pole.mov 14 4] (hp 3)),
    (5, bk [Pole.mov 5 3] (hp 4)),
    (6, bk [Pole.nok 6 7 5] (hp 5)),
    (7, none)])

-- `%ifc`
#guard monoOutC envR (Nomm.n2 (Nomm.n0 3) (Nomm.n2 (Nomm.n0 1) (Nomm.n0 2) Option.none) Option.none) 8 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 8, Pole.cel 8, Pole.hed 8 10, Pole.mov 10 7, Pole.tal 8 9, Pole.mov 9 3] (hp 6)),
    (1, bk [] (Termin.don 1)),
    (2, bk [Pole.mov 2 1] (hp 1)),
    (3, bk [Pole.nok 3 4 2] (hp 2)),
    (4, bk [Pole.mov 5 4] (hp 3)),
    (5, bk [Pole.nok 6 7 5] (hp 4)),
    (6, bk [Pole.mov 8 6] (hp 5)),
    (7, none)])

-- `%s7d`
#guard monoOutC envR (Nomm.n7 (Nomm.cons (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 1)) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) 10 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 8, Pole.cel 8, Pole.hed 8 10, Pole.mov 10 7, Pole.tal 8 9, Pole.mov 9 6] (hp 8)),
    (1, bk [] (Termin.don 1)),
    (2, bk [Pole.mov 2 1] (hp 1)),
    (3, bk [Pole.nok 3 4 2] (hp 2)),
    (4, none),
    (5, none),
    (6, bk [Pole.mov 0 3] (hp 3)),
    (7, bk [Pole.mov 5 4] (hp 6)),
    (8, bk [Pole.nok 6 7 5] (hp 7)),
    (9, none)])

-- `%s7e`
#guard monoOutC envR (Nomm.n7 (Nomm.cons (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 3)) (Nomm.cons (Nomm.n0 2) (Nomm.n0 3))) 9 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 7, Pole.cel 7, Pole.hed 7 9, Pole.mov 9 6, Pole.tal 7 8, Pole.mov 8 5] (hp 7)),
    (1, bk [] (Termin.don 1)),
    (2, bk [Pole.con 2 3 1] (hp 1)),
    (3, none),
    (4, none),
    (5, bk [Pole.mov 0 11, Pole.cel 11, Pole.tal 11 12, Pole.mov 12 3] (hp 2)),
    (6, bk [Pole.mov 4 2] (hp 5)),
    (7, bk [Pole.nok 5 6 4] (hp 6)),
    (8, none)])

end Comp
end SkaModel
end Formalization
