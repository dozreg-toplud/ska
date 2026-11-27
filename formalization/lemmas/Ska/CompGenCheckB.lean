import lemmas.Ska.CompGenCheck

/-!
# `RunOKG`: the larger families of the check

README Gaps 12.39.  `famB` (`all6`, a `%6` in every position, under the 30
flat goals: 154,350 runs) and `famC` (the 245 `%6` and the 7 branches under
the 300 goals that runs of `gensP` leave: forked, wrapped, with entries,
repeated labels: 75,600 runs).  No clause of `oneG` fails.
-/

namespace Formalization
namespace SkaModel
namespace Comp
namespace GenCheck

open Nock Lazy SixCheck

#guard tallyG runP all6 (flatGoals [jmp0 1] [genAtH 4 4]) == (154350, 0, 96906, [],
  [("c:nodup", 96906), ("c:askNodup", 8196), ("c:labEq", 92412), ("c:growU", 41330), ("c:frontA", 41330),
   ("c:flat", 153310), ("c:tree1", 57675)])

#guard tallyG runP (sixes ++ brs) goalsP == (75600, 0, 46980, [],
  [("c:nodup", 46980), ("c:askNodup", 720), ("c:labEq", 46080), ("c:growU", 53750), ("c:frontA", 53750),
   ("c:flat", 74340), ("c:tree1", 49666)])

end GenCheck
end Comp
end SkaModel
end Formalization
