import lemmas.Hoon.Order
import lemmas.Hoon.Treap

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

The door `+by` is `[by.battery a c]` with the map `a` and a context `c`.  The
gate reads `+gor` and `+mor` from `c` (`GorIn mug c ∧ MorIn mug c`), and
through them `+mug`: slamming the `+mug` gate of `c` on any noun ends with an
atom, and `mug` names that atom.  Nothing else about the hash is used.
-/

namespace Formalization
namespace Hoon

open Nock Pill

/-- The loop of `+put:by` in the door whose map is `a`, with sample `[b c]`,
computes the model. -/
theorem put_loop {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx)
    (b c a : Noun) :
    ∀ out, putF mug b c a = some out →
      nock (C by.put.loop (C by.put.battery (C (C b c) (C by.battery (C a ctx)))))
        by.put.loop = some out := by
  have hgor := gor_gate (mug := mug) ctx hc.1.2
  have hmor := mor_gate (mug := mug) ctx hc.2.2
  obtain ⟨⟨hg, _⟩, ⟨hm, _⟩⟩ := hc
  fun_induction putF mug b c a
  all_goals intro out h
  all_goals first
    | (simp at h; done)
    | skip
  all_goals
    cases h
    nock_open by.put.loop
    simp [nock_exec, gor_arm, mor_arm, *]

/-- The gate `put` of the door `by` with map `a`, slammed on `[b c]`. -/
theorem put_gate {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx)
    (b c a out : Noun) (h : putF mug b c a = some out) :
    nock (C by.put.battery (C (C b c) (C by.battery (C a ctx)))) by.put.battery = some out := by
  nock_open by.put.battery
  simp only [nock_exec, put_loop ctx hc b c a out h]

/-- The arm `by` builds the door, with an empty map. -/
@[nock_exec] theorem by_arm (c : Noun) : nock c by.arm = some (C by.battery (C (A 0) c)) := by
  nock_open by.arm
  simp only [nock_exec]

/-- The arm `put` of a door builds the gate, with a bunted sample. -/
@[nock_exec] theorem put_arm (d : Noun) :
    nock d by.put.arm = some (C by.put.battery (C (C (A 0) (A 0)) d)) := by
  nock_open by.put.arm
  simp only [nock_exec]

/-- `+put:by` on a map noun `a` that satisfies the invariant of `+by` ends,
its product satisfies the invariant, and the product holds the pair `[k v]`
and the pairs of `a` under other keys. -/
theorem put_by {mug : Noun → Nat} (ctx : Noun) (hc : GorIn mug ctx ∧ MorIn mug ctx)
    (a k v : Noun) (h : IsMap mug a) :
    ∃ out,
      Eval (C by.put.battery (C (C k v) (C by.battery (C a ctx)))) by.put.battery out ∧
      IsMap mug out ∧
      ∀ k' v', Get out k' v' ↔ (k' = k ∧ v' = v) ∨ (k' ≠ k ∧ Get a k' v') := by
  obtain ⟨out, hput, hmap, hget⟩ := putF_spec mug a k v h
  exact ⟨out, eval_of_nock (put_gate ctx hc k v a out hput), hmap, hget⟩

/-- The same in the pill's second layer, given `+mug`. -/
theorem put_by_layer2 {mug : Noun → Nat} (hmug : MugSpec mug layer2)
    (a k v : Noun) (h : IsMap mug a) :
    ∃ out,
      Eval (C by.put.battery (C (C k v) (C by.battery (C a layer2)))) by.put.battery out ∧
      IsMap mug out ∧
      ∀ k' v', Get out k' v' ↔ (k' = k ∧ v' = v) ∨ (k' ≠ k ∧ Get a k' v') :=
  put_by layer2 (gorIn_layer2 hmug) a k v h

end Hoon
end Formalization
