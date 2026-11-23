module

public import lemmas.Hoon.TapBy
import all lemmas.Pill.Arm.By

/-!
`+rep:by` and `+rep:in` of the pill's `hoon.hoon` (the two arms are the same
noun): fold a gate over the nodes of a treap.

```hoon
++  rep                                               ::  reduce to product
  ~/  %rep
  |*  b=_=>(~ |=([* *] +<+))
  |-
  ?~  a  +<+.b
  $(a r.a, +<+.b $(a l.a, +<+.b (b n.a +<+.b)))
```

**The order.**  At a node the gate first takes the node and the
accumulator, then the fold goes through the left subtree, then through the
right subtree: the nodes in pre-order (`preorder`).  That is not the order of
the keys; it is the order of the treap's shape, which `+mor` (the mug of the
mug of the keys) decides.  For a map the nodes are the pairs `[k v]`, for a set
the keys.

The gate `b = [bp [e acc] bc]` is slammed as `+rep` does it; the theorems
assume that slamming it on `[x acc]` gives `f x acc` for every `x` and `acc`.
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

/-- `+rep` with the gate `f` and the accumulator `acc`, as the Nock computes
it. -/
def repF (f : Noun → Noun → Noun) : Noun → Noun → Option Noun
  | Noun.atom 0, acc => some acc
  | Noun.cell n (Noun.cell l r), acc => (repF f l (f n acc)).bind (repF f r)
  | _, _ => none

@[nock_exec] theorem rep_arm (d : Noun) :
    nock d by.rep.arm
      = some (C by.rep.battery (C (C (C (A 0) (A 13)) (C (C (A 0) (A 0)) (A 0))) d)) := by
  nock_open by.rep.arm; simp only [nock_exec]

theorem rep_loop (B ctx bp e bc : Noun) (f : Noun → Noun → Noun)
    (hf : ∀ x acc, nock (C bp (C (C x acc) bc)) bp = some (f x acc)) : ∀ (a acc : Noun),
    nock (C by.rep.loop (C by.rep.battery (C (C bp (C (C e acc) bc)) (C B (C a ctx)))))
      by.rep.loop = repF f a acc
  | Noun.atom 0, acc => by
    nock_open by.rep.loop; simp [nock_exec, repF]
  | Noun.atom (k + 1), acc => by
    nock_open by.rep.loop; simp [nock_exec, repF]
  | Noun.cell n (Noun.atom k), acc => by
    nock_open by.rep.loop; simp [nock_exec, repF, hf]
  | Noun.cell n (Noun.cell l r), acc => by
    have hl := rep_loop B ctx bp e bc f hf l (f n acc)
    have hr := fun x => rep_loop B ctx bp e bc f hf r x
    nock_open by.rep.loop
    simp [nock_exec, repF, hf, hl, hr, tap_bind_bind]

/-- Slamming the gate `rep` of a door `[B a ctx]` on the gate `[bp [e acc] bc]`. -/
theorem rep_gate (B ctx bp e acc bc : Noun) (f : Noun → Noun → Noun)
    (hf : ∀ x acc, nock (C bp (C (C x acc) bc)) bp = some (f x acc)) (a : Noun) :
    nock (C by.rep.battery (C (C bp (C (C e acc) bc)) (C B (C a ctx)))) by.rep.battery
      = repF f a acc := by
  nock_open by.rep.battery
  simp only [nock_exec, rep_loop B ctx bp e bc f hf a acc]

/-- The nodes of a tree in pre-order: the root, the left subtree, the right
subtree. -/
def preorder : Noun → List Noun
  | Noun.cell n (Noun.cell l r) => n :: (preorder l ++ preorder r)
  | _ => []

theorem repF_tree (f : Noun → Noun → Noun) {a : Noun} (h : Tree a) :
    ∀ acc, repF f a acc = some ((preorder a).foldl (fun acc x => f x acc) acc) := by
  induction h with
  | nil => intro acc; rfl
  | @node n l r _ _ ihl ihr =>
    intro acc
    simp [repF, preorder, ihl, ihr, List.foldl_append]

/-- `+rep` on a tree (a map or a set) folds the gate over its nodes in
pre-order. -/
theorem rep_tree (B ctx bp e acc bc : Noun) (f : Noun → Noun → Noun)
    (hf : ∀ x acc, nock (C bp (C (C x acc) bc)) bp = some (f x acc)) (a : Noun) (h : Tree a) :
    Eval (C by.rep.battery (C (C bp (C (C e acc) bc)) (C B (C a ctx)))) by.rep.battery
      ((preorder a).foldl (fun acc x => f x acc) acc) :=
  eval_of_nock (by rw [rep_gate B ctx bp e acc bc f hf a, repF_tree f h])

/-- The nodes of a tree in pre-order are those that `+tap` lists. -/
theorem mem_preorder_tapList : ∀ (a x : Noun), x ∈ preorder a ↔ x ∈ tapList a
  | Noun.atom _, x => by simp [preorder, tapList]
  | Noun.cell n (Noun.atom _), x => by simp [preorder, tapList]
  | Noun.cell n (Noun.cell l r), x => by
    have hl := mem_preorder_tapList l x
    have hr := mem_preorder_tapList r x
    simp only [preorder, tapList, List.mem_cons, List.mem_append, hl, hr]
    constructor
    · rintro (h | h | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
    · rintro (h | h | h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)

end Hoon
end Formalization

end
