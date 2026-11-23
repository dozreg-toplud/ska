module

public import lemmas.Hoon.TapBy
public import lemmas.Hoon.Sets

/-!
`+tap:in` of the pill's `hoon.hoon`.  Its arm is the noun `by.tap.arm` itself
(the battery of `+in` holds it), so `tap_loop` covers it; on a set the list
holds exactly the keys.
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

theorem Tree.of_isSet {mug : Noun → Nat} : ∀ {a : Noun}, IsSet mug a → Tree a
  | Noun.atom 0, _ => Tree.nil
  | Noun.atom (_ + 1), h => by unfold IsSet at h; simp at h; cases h
  | Noun.cell _ (Noun.atom _), h => by unfold IsSet at h; simp at h; cases h
  | Noun.cell _ (Noun.cell l r), h => by
    unfold IsSet at h
    simp only [toMap_node] at h
    cases h with
    | node hl hr _ _ => exact Tree.node (Tree.of_isSet hl) (Tree.of_isSet hr)

theorem tapList_toMap : ∀ (a : Noun), tapList (toMap a) = (tapList a).map (fun n => C n (A 0))
  | Noun.atom k => by simp [tapList]
  | Noun.cell n (Noun.atom k) => by simp [tapList]
  | Noun.cell n (Noun.cell l r) => by
    simp [tapList, tapList_toMap l, tapList_toMap r]

theorem mem_tapList_set {mug : Noun → Nat} {a : Noun} (h : IsSet mug a) (x : Noun) :
    x ∈ tapList a ↔ Has a x := by
  have hm := mem_tapList h (C x (A 0))
  rw [tapList_toMap] at hm
  simp only [List.mem_map, Noun.cell.injEq, and_true, exists_eq_right] at hm
  unfold Has
  rw [hm]
  constructor
  · rintro ⟨k, v, ⟨rfl, rfl⟩, hg⟩; exact hg
  · intro hg; exact ⟨x, A 0, ⟨rfl, rfl⟩, hg⟩

/-- `~(tap in a)` on a set: a list whose elements are exactly the keys of the
set. -/
theorem tap_in {mug : Noun → Nat} (ctx : Noun) (a : Noun) (h : IsSet mug a) :
    Eval (C in.battery (C a ctx)) by.tap.arm (listN (tapList a)) ∧
      ∀ x, x ∈ tapList a ↔ Has a x := by
  refine ⟨eval_of_nock ?_, mem_tapList_set h⟩
  rw [tap_arm, tap_loop, show A 0 = listN [] from rfl, tapF_list (Tree.of_isSet h),
    List.append_nil]

end Hoon
end Formalization

end
