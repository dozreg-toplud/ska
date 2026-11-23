import Formalization.Hoon.Order
import Formalization.Hoon.Treap

/-!
`+put:by` of the pill's `hoon.hoon` inserts into a map.

```hoon
++  put
  ~/  %put
  |*  [b=* c=*]
  |-  ^+  a
  ?~  a
    [[b c] ~ ~]
  ?:  =(b p.n.a)
    ?:  =(c q.n.a)
      a
    a(n [b c])
  ?:  (gor b p.n.a)
    =+  d=$(a l.a)
    ?>  ?=(^ d)
    ?:  (mor p.n.a p.n.d)
      a(l d)
    d(r a(l r.d))
  =+  d=$(a r.a)
  ?>  ?=(^ d)
  ?:  (mor p.n.a p.n.d)
    a(r d)
  d(l a(r l.d))
```

Two layers.  `put_loop` runs the pill's Nock and shows that it computes the
Lean model `putF`.  `Treap.lean` shows what `putF` does to a map.  `put_by`
joins them.

The one assumption is `MugSpec mug`: slamming the pill's `+mug` gate on any
noun ends with an atom, and `mug` names that atom.  Nothing else about the
hash is used.
-/

namespace Formalization
namespace Hoon

open Nock Pill

/-- The loop of `+put:by` in the door whose map is `a`, with sample `[b c]`,
computes the model. -/
theorem put_loop {mug : Noun → Nat} (hmug : MugSpec mug) (b c a : Noun) :
    ∀ out, putF mug b c a = some out →
      nock (C put.loop (C put.battery (C (C b c) (C by.battery (C a layer2))))) put.loop
        = some out := by
  fun_induction putF mug b c a
  all_goals intro out h
  all_goals first
    | (simp at h; done)
    | skip
  all_goals
    cases h
    nock_open put.loop
    simp [nock_exec, gor_gate hmug, mor_gate hmug, *]

/-- The gate `put` of the door `by` with map `a`, slammed on `[b c]`. -/
theorem put_gate {mug : Noun → Nat} (hmug : MugSpec mug) (b c a out : Noun)
    (h : putF mug b c a = some out) :
    nock (C put.battery (C (C b c) (C by.battery (C a layer2)))) put.battery = some out := by
  nock_open put.battery
  simp only [nock_exec, put_loop hmug b c a out h]

/-- The arm `by` of layer 2 builds the door, with an empty map. -/
theorem by_arm : nock layer2 by.arm = some (C by.battery (C (A 0) layer2)) := by
  nock_open by.arm
  simp only [nock_exec]

/-- The arm `put` of a `by` door builds the gate, with a bunted sample. -/
theorem put_arm (a : Noun) :
    nock (C by.battery (C a layer2)) put.arm
      = some (C put.battery (C (C (A 0) (A 0)) (C by.battery (C a layer2)))) := by
  nock_open put.arm
  simp only [nock_exec]

/-- `+put:by` on a map noun `a` that satisfies the invariant of `+by` ends,
its product satisfies the invariant, and the product holds the pair `[k v]`
and the pairs of `a` under other keys. -/
theorem put_by {mug : Noun → Nat} (hmug : MugSpec mug) (a k v : Noun) (h : IsMap mug a) :
    ∃ out,
      Eval (C put.battery (C (C k v) (C by.battery (C a layer2)))) put.battery out ∧
      IsMap mug out ∧
      ∀ k' v', Get out k' v' ↔ (k' = k ∧ v' = v) ∨ (k' ≠ k ∧ Get a k' v') := by
  obtain ⟨out, hput, hmap, hget⟩ := putF_spec mug a k v h
  exact ⟨out, eval_of_nock (put_gate hmug k v a out hput), hmap, hget⟩

end Hoon
end Formalization
