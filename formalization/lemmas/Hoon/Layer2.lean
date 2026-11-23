module

public import lemmas.Hoon.Layer1
public import lemmas.Hoon.Mug
public import lemmas.Hoon.Sets
public import lemmas.Hoon.Lists
/-!
The pill's second layer satisfies the predicates of its arms, and the
theorems about the orders, maps and sets hold there with no assumption: the
hash is `mugF`, which the pill's `+mug` computes (`mug_layer2`).
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

theorem homoIn_layer2 : HomoIn layer2 := homo.arm_at

theorem decIn_below_layer2 : Below DecIn layer2 := decIn_layer1

/-- The pill's second layer holds `+some`. -/
theorem someIn_layer2 : SomeIn layer2 := some.arm_at

theorem dorIn_layer2 : DorIn layer2 := ⟨dor.arm_at, arith_layer1.2.2.2.1⟩

/-- `layer2` holds `+gor` and `+mor` with what they read, given `+mug`. -/
theorem gorIn_layer2 {mug : Noun → Nat} (hmug : MugSpec mug layer2) :
    GorIn mug layer2 ∧ MorIn mug layer2 :=
  ⟨⟨gor.arm_at, ⟨Pill.mug.arm_at, hmug⟩, dorIn_layer2⟩,
    ⟨mor.arm_at, ⟨Pill.mug.arm_at, hmug⟩, dorIn_layer2⟩⟩

/-- `layer2` holds `+mug` and everything it reads. -/
theorem mugNeeds_layer2 : MugNeeds layer2 := by
  obtain ⟨ha, hs, hm, _, _, _, _, _, _, _, hdv, hmd⟩ := arith_layer1
  have hbex : BexIn layer2 := ⟨bex.arm_at, hm⟩
  have hrsh : RshIn layer2 := ⟨rsh.arm_at, hbex, hdv⟩
  have hlsh : LshIn layer2 := ⟨lsh.arm_at, hbex⟩
  have hend : EndIn layer2 := ⟨end.arm_at, hbex, hmd⟩
  have hlog : LogicNeeds layer2 := ⟨hrsh, hlsh, hend, ha⟩
  have hmet : MetIn layer2 := ⟨met.arm_at, hrsh⟩
  exact ⟨muk.arm_at, ⟨fe.arm_at, ⟨⟨con.arm_at, hlog⟩, hs, hmd⟩, ⟨cut.arm_at, hend, hrsh⟩,
    ⟨mix.arm_at, hlog⟩, ⟨dis.arm_at, hlog⟩, hdv, hm⟩, hmet, ⟨cat.arm_at, hlsh, hmet, ha⟩⟩

/-- The pill's `+mug` gate computes `mugF`. -/
theorem mug_layer2 : MugSpec mugF layer2 := mug_spec layer2 mugNeeds_layer2

/-- The same in the pill's second layer, given `+mug`. -/
theorem put_by_layer2 {mug : Noun → Nat} (hmug : MugSpec mug layer2)
    (a k v : Noun) (h : IsMap mug a) :
    ∃ out,
      Eval (C by.put.battery (C (C k v) (C by.battery (C a layer2)))) by.put.battery out ∧
      IsMap mug out ∧
      ∀ k' v', Get out k' v' ↔ (k' = k ∧ v' = v) ∨ (k' ≠ k ∧ Get a k' v') :=
  put_by layer2 (gorIn_layer2 hmug) a k v h

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

end
