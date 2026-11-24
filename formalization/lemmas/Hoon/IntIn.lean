module

public import lemmas.Hoon.UniIn
public import lemmas.Hoon.RepBy
import all lemmas.Pill.Arm.In
import all lemmas.Pill.Arm.By

/-!
`+int:in` of the pill's `hoon.hoon` on an empty door set, and `+rep` over a
treap of one node.

```hoon
++  int                                               ::  intersection
  ~/  %int
  |*  b=_a
  |-  ^+  a
  ?~  b
    ~
  ?~  a
    ~
  ?.  (mor n.a n.b)
    $(a b, b a)
  ?:  =(n.b n.a)
    a(l $(a l.a, b l.b), r $(a r.a, b r.b))
  ?:  (gor n.b n.a)
    %-  uni(a $(a l.a, r.b ~))  $(b r.b)
  %-  uni(a $(a r.a, l.b ~))  $(b l.b)
```

`int_in_nil`: with the door's set `a` empty the gate returns `~` whatever
`b` is (by its first test when `b` is `~`, by its second otherwise).  The
other branches are not linked.

`rep_gate_one`: `+rep` over `[x ~ ~]` is the gate on `x` and the first
accumulator, whatever the gate (as `roll_gate_one` for `+roll`).
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

/-- The arm `int` of a door `+in` builds its gate, whose sample bunt is the
door's set. -/
theorem int_in_arm (a ctx : Noun) :
    nock (C in.battery (C a ctx)) in.int.arm = some (C in.int.battery (C a (C in.battery (C a ctx)))) := by
  nock_open in.int.arm
  simp [nock_exec]

theorem int_loop_nil (B ctx : Noun) :
    nock (C in.int.loop (C in.int.battery (C B (C in.battery (C (A 0) ctx))))) in.int.loop = some (A 0) := by
  nock_open in.int.loop
  by_cases h : B = A 0
  · subst h; simp [nock_exec]
  · simp [nock_exec, eqCode, Ne.symm h]

/-- **`+int:in` with the door's set empty** is `~`. -/
theorem int_in_nil (B ctx : Noun) :
    nock (C in.int.battery (C B (C in.battery (C (A 0) ctx)))) in.int.battery = some (A 0) := by
  nock_open in.int.battery
  simp only [nock_exec, int_loop_nil]

theorem rep_loop_nil (B ctx bp e bc acc : Noun) :
    nock (C by.rep.loop (C by.rep.battery (C (C bp (C (C e acc) bc)) (C B (C (A 0) ctx))))) by.rep.loop
      = some acc := by
  nock_open by.rep.loop
  simp [nock_exec]

/-- **`+rep` over a treap of one node** is the gate on that node and the
first accumulator, whatever the gate. -/
theorem rep_gate_one (B ctx bp e acc bc x : Noun) :
    nock (C by.rep.battery (C (C bp (C (C e acc) bc)) (C B (C (C x (C (A 0) (A 0))) ctx)))) by.rep.battery
      = nock (C bp (C (C x acc) bc)) bp := by
  nock_open by.rep.battery
  simp only [nock_exec]
  nock_open by.rep.loop
  cases e1 : nock (C bp (C (C x acc) bc)) bp with
  | none => simp [nock_exec, e1]
  | some r => simp [nock_exec, e1, rep_loop_nil]

end Hoon
end Formalization

end
