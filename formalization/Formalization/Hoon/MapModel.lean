import Formalization.Nock

/-!
Lean models of the `hoon.hoon` arms behind `+put:by`, as functions on nouns.

They are models, not specifications: `Hoon/Order.lean` and `Hoon/PutBy.lean`
prove that the Nock of the pill computes them, and `Hoon/Treap.lean` proves
what they do to a map.

`mug` is a parameter.  The proofs need a hash that is a function of the noun
and nothing else about it.
-/

namespace Formalization
namespace Hoon

open Nock

/-- `+dor`: atoms before cells, atoms by size, cells by head and then tail. -/
def dorF : Noun → Noun → Bool
  | Noun.atom a, Noun.atom b => decide (a ≤ b)
  | Noun.atom _, Noun.cell _ _ => true
  | Noun.cell _ _, Noun.atom _ => false
  | Noun.cell h t, Noun.cell h' t' => if h = h' then dorF t t' else dorF h h'

/-- `+gor`: by `mug`, and by `+dor` when the mugs collide. -/
def gorF (mug : Noun → Nat) (a b : Noun) : Bool :=
  if mug a = mug b then dorF a b else decide (mug a < mug b)

/-- `+mor`: by the `mug` of the `mug`, and by `+dor` when those collide. -/
def morF (mug : Noun → Nat) (a b : Noun) : Bool :=
  if mug (A (mug a)) = mug (A (mug b)) then dorF a b
  else decide (mug (A (mug a)) < mug (A (mug b)))

/-- `+put:by`: insert the pair `[b c]` into the treap `a`.

A map is `~` or `[n=[p q] l r]`.  The result is `none` where the Nock crashes
or where this model does not follow it (a subtree that is not a map). -/
def putF (mug : Noun → Nat) (b c : Noun) : Noun → Option Noun
  | Noun.atom 0 => some (C (C b c) (C (A 0) (A 0)))
  | Noun.cell (Noun.cell p q) (Noun.cell l r) =>
    if b = p then
      if c = q then some (C (C p q) (C l r)) else some (C (C b c) (C l r))
    else if gorF mug b p then
      match putF mug b c l with
      | some (Noun.cell (Noun.cell dp dq) (Noun.cell dl dr)) =>
        if morF mug p dp then some (C (C p q) (C (C (C dp dq) (C dl dr)) r))
        else some (C (C dp dq) (C dl (C (C p q) (C dr r))))
      | _ => none
    else
      match putF mug b c r with
      | some (Noun.cell (Noun.cell dp dq) (Noun.cell dl dr)) =>
        if morF mug p dp then some (C (C p q) (C l (C (C dp dq) (C dl dr))))
        else some (C (C dp dq) (C (C (C p q) (C l dl)) dr))
      | _ => none
  | _ => none

/-- `Get a k v`: the map noun `a` has a node with key `k` and value `v`. -/
inductive Get : Noun → Noun → Noun → Prop where
  | here {k v l r} : Get (C (C k v) (C l r)) k v
  | left {p q l r k v} : Get l k v → Get (C (C p q) (C l r)) k v
  | right {p q l r k v} : Get r k v → Get (C (C p q) (C l r)) k v

/-- The invariant of `+by` maps, as `+apt:by` checks it: a search tree in
`+gor` order on the keys and a heap in `+mor` order, with distinct keys.
The conditions are stated for every key of a subtree, which is what the checks
of `+apt` against the nearest ancestors amount to when the orders are
transitive. -/
inductive IsMap (mug : Noun → Nat) : Noun → Prop where
  | nil : IsMap mug (A 0)
  | node {p q l r} :
      IsMap mug l → IsMap mug r →
      (∀ k v, Get l k v → k ≠ p ∧ gorF mug k p = true ∧ morF mug p k = true) →
      (∀ k v, Get r k v → k ≠ p ∧ gorF mug p k = true ∧ morF mug p k = true) →
      IsMap mug (C (C p q) (C l r))

end Hoon
end Formalization
