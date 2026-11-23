module

public import lemmas.Hoon.Basic
public import lemmas.Pill.Arm.Need
public import lemmas.Pill.Arm.Fall
import all lemmas.Pill.Arm.Need
import all lemmas.Pill.Arm.Fall

/-!
`+need` and `+fall` of the pill's `hoon.hoon`, on units: `~` is `A 0` and
`[~ u]` is `C (A 0) u`.

```hoon
++  need                                                ::  demand
  ~/  %need
  |*  a=(unit)
  ?~  a  ~>(%mean.'need' !!)
  u.a
::
++  fall                                                ::  default
  |*  [a=(unit) b=*]
  ?~(a b u.a)
```

Neither gate reads its context.  `+fall` has no `%fast` label; its gate's
battery is the literal `fallBattery`.
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

abbrev NeedIn (c : Noun) : Prop := slot? need.axis c = some need.arm
abbrev FallIn (c : Noun) : Prop := slot? fall.axis c = some fall.arm

@[nock_exec] theorem need_arm (c : Noun) :
    nock c need.arm = some (C need.battery (C (A 0) c)) := by
  nock_open need.arm; simp only [nock_exec]

/-- `(need [h u])` is `u`. -/
@[nock_exec] theorem need_gate (c h u : Noun) :
    nock (C need.battery (C (C h u) c)) need.battery = some u := by
  nock_open need.battery; simp [nock_exec]

/-- `(need ~)` crashes. -/
theorem need_gate_nil (c : Noun) : nock (C need.battery (C (A 0) c)) need.battery = none := by
  nock_open need.battery; simp [nock_exec]

/-- The battery of the gate that the arm `fall` builds. -/
def fallBattery : Noun :=
  C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 12)))) (C (C (A 0) (A 13)) (C (A 0) (A 25))))

@[nock_exec] theorem fall_arm (c : Noun) :
    nock c fall.arm = some (C fallBattery (C (C (A 0) (A 0)) c)) := by
  nock_open fall.arm; simp only [nock_exec]; rfl

/-- `(fall ~ b)` is `b`. -/
@[nock_exec] theorem fall_gate_nil (c b : Noun) :
    nock (C fallBattery (C (C (A 0) b) c)) fallBattery = some b := by
  simp [fallBattery, nock_exec]

/-- `(fall [h u] b)` is `u`. -/
@[nock_exec] theorem fall_gate_some (c h u b : Noun) :
    nock (C fallBattery (C (C (C h u) b) c)) fallBattery = some u := by
  simp [fallBattery, nock_exec]

end Hoon
end Formalization

end
