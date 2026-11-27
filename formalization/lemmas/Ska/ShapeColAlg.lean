import lemmas.Ska.ShapeCol

/-!
# Is `+uni-need-ord` a semilattice join? (the fuel of `fixLoop`)

The loop of `+inter2-collapse` (`fixLoop`) stops if the rounds form an
ascending chain in a finite poset: each round is inflationary at every node
for the order `a ≤ b ↔ uniOrd a b = b` (the new sure is a fold of `uniOrd`
from `uniOrd parent s`), no arm deepens a shape, and the fork skeleton is
fixed.  That needs `uniOrd` to be a semilattice join (idempotent by its
first test, commutative, associative) on the shapes the arms produce.

Checked here by enumeration (`shapesUpTo k`: every shape of depth at most
`k + 1`):

* commutativity holds on every shape of depth at most `3` (202 shapes);
* associativity FAILS on shapes with `[%pair [%none ~] [%none ~]]`
  (`assocWitness`: `(this ∪ pair none none) ∪ both none none` is
  `both none none`, `this ∪ (pair none none ∪ both none none)` is `this`);
* on `normal` shapes (no `pair none none` anywhere, what `+cons-need`
  makes), associativity holds on every triple of depth at most `2` here;
  a scratch run (2026-11-27) checked every triple of depth at most `3`
  (163 shapes, 4,330,747 triples, no failure) and 300,000 random triples of
  depth at most `4`, with commutativity, closure of `normal` shapes under
  `uniOrd`, `msgOrd` and `msgFix`, and that none of them deepens a shape.

So the missing algebraic fact is: `uniOrd` is associative and commutative on
`normal` shapes, and every sure of the trees of `+inter2-collapse` is
`normal` (true of `consOrd`, `sureLook`, `msgOrd`, `msgFix` by the checks; for
the sures of `l2i` it needs the `Need`s of the final pass to have no
`[%pair [%none ~] [%none ~]]`, which `needToOrd` maps to a non-normal shape).
-/

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Compiler

/-- No `[%pair [%none ~] [%none ~]]` anywhere. -/
def ordNormal : NeedOrd → Bool
  | NeedOrd.pair NeedOrd.none NeedOrd.none => false
  | NeedOrd.pair p q => ordNormal p && ordNormal q
  | NeedOrd.both h t => ordNormal h && ordNormal t
  | _ => true

/-- The depth of a shape. -/
def ordDepth : NeedOrd → Nat
  | NeedOrd.pair p q => max (ordDepth p) (ordDepth q) + 1
  | NeedOrd.both h t => max (ordDepth h) (ordDepth t) + 1
  | _ => 0

/-- Every shape of depth at most `k + 1`. -/
def shapesUpTo : Nat → List NeedOrd
  | 0 => [NeedOrd.none, NeedOrd.this]
  | k + 1 =>
    let s := shapesUpTo k
    [NeedOrd.none, NeedOrd.this] ++ (s.flatMap fun a => s.flatMap fun b => [NeedOrd.both a b, NeedOrd.pair a b])

#guard (shapesUpTo 2).length = 202

/- Commutativity on every shape of depth at most `3`. -/
#guard (shapesUpTo 2).all fun a => (shapesUpTo 2).all fun b => uniOrd a b = uniOrd b a

/-- **The witness**: associativity fails on a non-normal shape. -/
def assocWitness : NeedOrd × NeedOrd × NeedOrd :=
  (NeedOrd.this, NeedOrd.pair NeedOrd.none NeedOrd.none, NeedOrd.both NeedOrd.none NeedOrd.none)

#guard uniOrd (uniOrd assocWitness.1 assocWitness.2.1) assocWitness.2.2 = NeedOrd.both NeedOrd.none NeedOrd.none
#guard uniOrd assocWitness.1 (uniOrd assocWitness.2.1 assocWitness.2.2) = NeedOrd.this

/- Associativity on every normal triple of depth at most `2`. -/
#guard let s := (shapesUpTo 1).filter ordNormal
  s.all fun a => s.all fun b => s.all fun c => uniOrd (uniOrd a b) c = uniOrd a (uniOrd b c)

/- `uniOrd` keeps normal shapes normal and does not deepen them (depth at
most `3`). -/
#guard let s := (shapesUpTo 2).filter ordNormal
  s.all fun a => s.all fun b => ordNormal (uniOrd a b) && ordDepth (uniOrd a b) ≤ max (ordDepth a) (ordDepth b)

/- So does `msgOrd`, on every cape of depth at most `2` here (depth at most
`2` shapes). -/
#guard let s := (shapesUpTo 1).filter ordNormal
  let capes := [Cape.no, Cape.yes, Cape.cell Cape.yes Cape.no, Cape.cell Cape.no Cape.yes]
  s.all fun a => s.all fun b => capes.all fun l =>
    ordNormal (msgOrd a b l) && ordDepth (msgOrd a b l) ≤ max (ordDepth a) (ordDepth b)

end Comp
end SkaModel
end Formalization
