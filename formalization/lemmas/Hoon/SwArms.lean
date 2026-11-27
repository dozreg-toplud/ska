module

public import lemmas.Hoon.ListsSort
public import lemmas.Hoon.ListsMore
public import lemmas.Pill.Arm.Rear
public import lemmas.Pill.Arm.Snip
import all lemmas.Pill.Arm.Sort
import all lemmas.Pill.Arm.Rear
import all lemmas.Pill.Arm.Snip

/-!
The arms `+sort`, `+rear` and `+snip` build their gates: the facts the link of
`+switch-chains` (`Compiler/OptLinkSw*.lean`) needs to run them from the
pill's second layer, where `sort_gate`, `rear_gate`, `snip_gate` take over.
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

@[nock_exec] theorem sort_arm (c : Noun) :
    nock c sort.arm = some (C sort.battery (C (C (A 0) (C (C (A 0) (A 15)) (C (C (A 0) (A 0)) (C (C (A 0) (A 0)) (A 0))))) c)) := by
  nock_open sort.arm; simp only [nock_exec]

@[nock_exec] theorem rear_arm (c : Noun) :
    nock c rear.arm = some (C rear.battery (C (A 0) c)) := by
  nock_open rear.arm; simp only [nock_exec]

@[nock_exec] theorem snip_arm (c : Noun) :
    nock c snip.arm = some (C snip.battery (C (A 0) c)) := by
  nock_open snip.arm; simp only [nock_exec]

end Hoon
end Formalization

end
