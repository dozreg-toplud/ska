module

public import lemmas.Hoon.Treap
public import lemmas.Hoon.Basic
public import lemmas.Pill.Arm.By
import all lemmas.Pill.Arm.By

/-!
`+tap:by` of the pill's `hoon.hoon`: the list of the pairs of a map.

```hoon
++  tap                                               ::  listify pairs
  =<  $
  ~/  %tap
  =+  b=`(list _?>(?=(^ a) n.a))`~
  |.  ^+  b
  ?~  a
    b
  $(a r.a, b [n.a $(a l.a)])
```

The arm is a trap whose state is the accumulator `b`.  It reads nothing from
the context, and its Nock is that of `+tap:in` too.  `tap_loop` shows that the
Nock computes `tapF` exactly, crashes included; `tapF_list` and `tap_by` say
what it computes on a map: the nodes in reverse order of the keys.
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

/-- `+tap` with accumulator `b`, as the Nock computes it. -/
def tapF : Noun → Noun → Option Noun
  | Noun.atom 0, b => some b
  | Noun.cell n (Noun.cell l r), b => (tapF l b).bind fun x => tapF r (C n x)
  | _, _ => none

theorem tap_bind_bind {α β γ : Type} (x : Option α) (f : α → Option β) (g : β → Option γ) :
    (x.bind f).bind g = x.bind fun a => (f a).bind g := by
  cases x <;> rfl

theorem tap_loop (B ctx : Noun) : ∀ (a b : Noun),
    nock (C by.tap.battery (C b (C B (C a ctx)))) by.tap.battery = tapF a b
  | Noun.atom 0, b => by
    nock_open by.tap.battery; simp [nock_exec, tapF]
  | Noun.atom (k + 1), b => by
    nock_open by.tap.battery; simp [nock_exec, tapF]
  | Noun.cell n (Noun.atom k), b => by
    nock_open by.tap.battery; simp [nock_exec, tapF]
  | Noun.cell n (Noun.cell l r), b => by
    have hl := tap_loop B ctx l b
    have hr := fun x => tap_loop B ctx r (C n x)
    nock_open by.tap.battery
    simp [nock_exec, tapF, hl, hr, tap_bind_bind]

theorem tap_arm (d : Noun) :
    nock d by.tap.arm = nock (C by.tap.battery (C (A 0) d)) by.tap.battery := by
  nock_open by.tap.arm
  simp only [nock_exec]

/-- The nodes of a tree in reverse order. -/
def tapList : Noun → List Noun
  | Noun.cell n (Noun.cell l r) => tapList r ++ n :: tapList l
  | _ => []

/-- A tree: `~` or `[n l r]` with trees `l` and `r`. -/
inductive Tree : Noun → Prop where
  | nil : Tree (A 0)
  | node {n l r : Noun} : Tree l → Tree r → Tree (C n (C l r))

theorem Tree.of_isMap {mug : Noun → Nat} {a : Noun} (h : IsMap mug a) : Tree a := by
  induction h with
  | nil => exact Tree.nil
  | node _ _ _ _ ihl ihr => exact Tree.node ihl ihr

theorem tapF_list {a : Noun} (h : Tree a) :
    ∀ acc, tapF a (listN acc) = some (listN (tapList a ++ acc)) := by
  induction h with
  | nil => intro acc; rfl
  | @node n l r _ _ ihl ihr =>
    intro acc
    simp only [tapF, tapList, ihl acc, Option.bind_some]
    rw [show C n (listN (tapList l ++ acc)) = listN (n :: (tapList l ++ acc)) from rfl, ihr]
    simp

theorem mem_tapList {mug : Noun → Nat} {a : Noun} (h : IsMap mug a) (x : Noun) :
    x ∈ tapList a ↔ ∃ k v, x = C k v ∧ Get a k v := by
  induction h with
  | nil => simp [tapList, Get_atom]
  | @node p q l r _ _ _ _ ihl ihr =>
    simp only [tapList, List.mem_append, List.mem_cons, ihl, ihr]
    constructor
    · rintro (⟨k, v, rfl, hg⟩ | rfl | ⟨k, v, rfl, hg⟩)
      · exact ⟨k, v, rfl, Get.right hg⟩
      · exact ⟨p, q, rfl, Get.here⟩
      · exact ⟨k, v, rfl, Get.left hg⟩
    · rintro ⟨k, v, rfl, hg⟩
      rw [Get_node] at hg
      rcases hg with ⟨rfl, rfl⟩ | hg | hg
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨k, v, rfl, hg⟩)
      · exact Or.inl ⟨k, v, rfl, hg⟩

/-- `~(tap by a)` on a map: a list whose elements are exactly the pairs
`[k v]` of the map. -/
theorem tap_by {mug : Noun → Nat} (ctx : Noun) (a : Noun) (h : IsMap mug a) :
    Eval (C by.battery (C a ctx)) by.tap.arm (listN (tapList a)) ∧
      ∀ x, x ∈ tapList a ↔ ∃ k v, x = C k v ∧ Get a k v := by
  refine ⟨eval_of_nock ?_, mem_tapList h⟩
  rw [tap_arm, tap_loop, show A 0 = listN [] from rfl, tapF_list (Tree.of_isMap h),
    List.append_nil]

end Hoon
end Formalization

end
