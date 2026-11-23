import lemmas.Hoon.Mug
import lemmas.Hoon.Sets

/-!
The theorems about the orders, maps and sets, in the pill's second layer and
with no assumption: the predicates on the context hold for `layer2`, and the
hash is `mugF`, which the pill's `+mug` computes (`mug_layer2`).
-/

namespace Formalization
namespace Hoon

open Nock Pill

theorem gorIn_morIn_layer2 : GorIn mugF layer2 ∧ MorIn mugF layer2 := gorIn_layer2 mug_layer2

/-- The pill's `+gor` computes `gorF mugF`. -/
theorem gor_pill (a b : Noun) :
    nock (C gor.battery (C (C a b) layer2)) gor.battery = some (loob (gorF mugF a b)) :=
  gor_gate layer2 gorIn_morIn_layer2.1.2 a b

/-- The pill's `+mor` computes `morF mugF`. -/
theorem mor_pill (a b : Noun) :
    nock (C mor.battery (C (C a b) layer2)) mor.battery = some (loob (morF mugF a b)) :=
  mor_gate layer2 gorIn_morIn_layer2.2.2 a b

/-- The pill's `+put:by` inserts into a map. -/
theorem put_by_pill (a k v : Noun) (h : IsMap mugF a) :
    ∃ out,
      Eval (C by.put.battery (C (C k v) (C by.battery (C a layer2)))) by.put.battery out ∧
      IsMap mugF out ∧
      ∀ k' v', Get out k' v' ↔ (k' = k ∧ v' = v) ∨ (k' ≠ k ∧ Get a k' v') :=
  put_by layer2 gorIn_morIn_layer2 a k v h

/-- The pill's `+get:by` looks a key up in a map. -/
theorem get_by_pill (a k : Noun) (h : IsMap mugF a) :
    (∀ v, Get a k v →
      Eval (C by.get.battery (C k (C by.battery (C a layer2)))) by.get.battery (C (A 0) v)) ∧
    ((∀ v, ¬ Get a k v) →
      Eval (C by.get.battery (C k (C by.battery (C a layer2)))) by.get.battery (A 0)) :=
  get_by layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ a k h

/-- The pill's `+has:by` tells whether a map holds a key. -/
theorem has_by_pill (a k : Noun) (h : IsMap mugF a) :
    ∃ f : Bool,
      Eval (C by.has.battery (C k (C by.battery (C a layer2)))) by.has.battery (loob f) ∧
      (f = true ↔ ∃ v, Get a k v) :=
  has_by layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ a k h

/-- The pill's `+put:in` inserts into a set. -/
theorem put_in_pill (a k : Noun) (h : IsSet mugF a) :
    ∃ out,
      Eval (C in.put.battery (C k (C in.battery (C a layer2)))) in.put.battery out ∧
      IsSet mugF out ∧ ∀ k', Has out k' ↔ k' = k ∨ Has a k' :=
  put_in layer2 gorIn_morIn_layer2 a k h

/-- The pill's `+has:in` tells whether a set holds a key. -/
theorem has_in_pill (a k : Noun) (h : IsSet mugF a) :
    ∃ t : Bool,
      Eval (C in.has.battery (C k (C in.battery (C a layer2)))) in.has.battery (loob t) ∧
      (t = true ↔ Has a k) :=
  has_in layer2 gorIn_morIn_layer2.1 a k h

end Hoon
end Formalization
