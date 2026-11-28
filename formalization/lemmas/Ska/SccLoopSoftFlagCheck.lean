import lemmas.Ska.SccLoopSoftTryCheck
import lemmas.Ska.SccLoopFlagData

/-! # `finishLFCS2` on both sides of `+soft-free` (README Gaps 21.22)

The `%done` compiles of the 29 cases of `FLAG` in `tools/hoon/sccreal.py --flag` (the instrumented
library prints `[%sf o free tries]` at `+soft-free` in `+soft-emit`): soft calls whose tries take
the `&` side of `+soft-free` (tries last) and five (`q5`, `q8`, `q9`, `q10`, `q11`) whose bond
block reads a register that the try defines (the callee's part passed twice: `+.y +.y`), the `|`
side (`softFlag`, the tries first and the flag tested at the bond's last block). -/

namespace Formalization.SkaModel.SccLoop.SoftFlagCheck

open Nock Formalization.SkaModel Formalization.SkaModel.Comp Formalization.SkaModel.SccLoop.RealData
open Formalization.SkaModel.SccLoop.SoftTryCheck

-- All 87 compiles: `finishLFCS2` gives the straight of `(finish ~)` block by block, and the soft
-- map after `+coerce-lazy`.
#guard FlagData.recs.length == 87
#guard FlagData.recs.all fun r => finOk2 r == 0
#guard FlagData.recs.all csoftOk2
-- The compiles with tries, `(tries, side)` per soft call (`1` `&`, `0` `|`), in the order of the
-- instrumented compiler's `[%sf o free tries]` prints (`free` `0` is `&`, `1` is `|`): 24 compiles
-- on the `&` side (27 tries), 5 on the `|` side.
#guard ((FlagData.recs.filter fun r => (tryInfo r).any (·.1 > 0)).map fun r => (r.cs, tryInfo r)) =
  [("f6", [(1, 1)]), ("f8", [(1, 1)]), ("f19", [(1, 1)]), ("h1", [(1, 1)]), ("h2", [(1, 1)]),
   ("h3", [(1, 1)]), ("h4", [(1, 1)]), ("h6", [(1, 1)]), ("h7", [(1, 1)]), ("p1", [(1, 1)]),
   ("p3", [(1, 1)]), ("p5", [(1, 1)]), ("p6", [(1, 1)]), ("q1", [(1, 1)]), ("q3", [(1, 1)]),
   ("q6", [(2, 1)]), ("g1", [(1, 1)]), ("g2", [(1, 1)]), ("g3", [(1, 1)]), ("g5", [(1, 1)]),
   ("p2", [(1, 1)]), ("p7", [(1, 1)]), ("p8", [(1, 1)]), ("q5", [(1, 0)]), ("q7", [(2, 1)]),
   ("q8", [(1, 0)]), ("q9", [(1, 0)]), ("q10", [(1, 0)]), ("q11", [(1, 0)])]

end Formalization.SkaModel.SccLoop.SoftFlagCheck
