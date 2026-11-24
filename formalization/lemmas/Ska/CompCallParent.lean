import lemmas.Ska.CompIndirectOut
import lemmas.Ska.CompWhole

/-!
# Calls under a parent: the raw blocks

README Gaps 12.13 (seventeenth session).  The whole-subject blocks of an
indirect call inside a cons and inside a `%7` (`tools/hoon/wholedump.hoon`
with the cases below, subject `[[4 0 1] 5]`, a sock that knows nothing), and
`finishLUC` against them.

* `[[2 [0 3] [0 2]] [0 1]]` (`%conh`, product `[6 [4 0 1] 5]`): `0w0 mov v0
  v7, cel v7, hed v7 v9, mov v9 v6, tal v7 v8, mov v8 v5, hop 5`; `0w1 don
  v1`; `0w2 con v2 v3 v1, hop 1`; `0w3 mov v0 v3, hop 2` (the tail `[0 1]`
  reads the subject register `v0` after the call); `0w4 mov v4 v2, hop 3`
  (the `+kerf` block of the call under the head's `%next`); `0w5 nok v5 v6
  v4, hop 4`.
* `[[0 1] [2 [0 3] [0 2]]]` (`%cont`): the same with `0w3 mov v0 v2, hop 2`
  and `0w4 mov v4 v3, hop 3` (the head runs after the call in the tail).
* `[7 [2 [0 3] [0 2]] [0 1]]` and `[7 [0 1] [2 [0 3] [0 2]]]`: the nomm of
  the first is `[7 [2 [0 3] [0 2]] [0 1]]`, of the second the call itself
  after the analysis; both have the blocks of the call alone.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

#guard monoOutC envR (Nomm.cons (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 1)) 7 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 7, Pole.cel 7, Pole.hed 7 9, Pole.mov 9 6, Pole.tal 7 8,
      Pole.mov 8 5] (hp 5)),
    (1, bk [] (Termin.don 1)), (2, bk [Pole.con 2 3 1] (hp 1)), (3, bk [Pole.mov 0 3] (hp 2)),
    (4, bk [Pole.mov 4 2] (hp 3)), (5, bk [Pole.nok 5 6 4] (hp 4)), (6, none)])

#guard monoOutC envR (Nomm.cons (Nomm.n0 1) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) 7 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 7, Pole.cel 7, Pole.hed 7 9, Pole.mov 9 6, Pole.tal 7 8,
      Pole.mov 8 5] (hp 5)),
    (1, bk [] (Termin.don 1)), (2, bk [Pole.con 2 3 1] (hp 1)), (3, bk [Pole.mov 0 2] (hp 2)),
    (4, bk [Pole.mov 4 3] (hp 3)), (5, bk [Pole.nok 5 6 4] (hp 4)), (6, none)])

#guard monoOutC envR (Nomm.n7 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 1)) 5 ==
  some (NeedOrd.this, 1, [(0, bk [Pole.mov 0 5, Pole.cel 5, Pole.hed 5 7, Pole.mov 7 4, Pole.tal 5 6,
      Pole.mov 6 3] (hp 3)),
    (1, bk [] (Termin.don 1)), (2, bk [Pole.mov 2 1] (hp 1)), (3, bk [Pole.nok 3 4 2] (hp 2)), (4, none)])

end Comp
end SkaModel
end Formalization
