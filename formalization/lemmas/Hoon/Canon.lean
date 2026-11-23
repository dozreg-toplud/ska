module

public import lemmas.Hoon.RepBy
public import lemmas.Hoon.TapIn
/-!
Treaps are canonical: a map noun that satisfies `IsMap mug` is determined by
its pairs, and a set noun that satisfies `IsSet mug` by its keys.  This is why
Hoon can compare maps and sets with `=`.

The root of a treap is the key that is greatest in `+mor`, the left subtree
holds the keys below it in `+gor` and the right subtree those above, so two
treaps with the same pairs have the same root, the same value there and, by
induction, the same subtrees (`isMap_ext`).  A set is the map of its keys to
`~` (`toMap`), and `toMap` is injective (`toMap_inj`), which gives `isSet_ext`.

The listings follow.  `+tap:by` lists the pairs of a map in decreasing `+gor`
order of the keys (`tapList_pairwise`), and a list that is strictly ordered by
an asymmetric relation is determined by its members (`pairwise_ext`), so the
list of `+tap:by` is a function of the pairs alone, whatever the treap was
built from (`tapList_ext`).  `+rep` folds in the pre-order of the treap
(`rep_tree`), which by `isMap_ext` is a function of the pairs too
(`preorder_ext`).
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock

/-! ## The root and the subtrees -/

/-- The root of a map is greatest in `+mor` among its keys. -/
theorem morF_root_all {mug : Noun → Nat} {p q l r : Noun}
    (h : IsMap mug (Noun.cell (Noun.cell p q) (Noun.cell l r))) :
    ∀ k v, Get (Noun.cell (Noun.cell p q) (Noun.cell l r)) k v → morF mug p k = true := by
  obtain ⟨_, _, hL, hR⟩ := IsMap_node h
  intro k v hg
  rw [Get_node] at hg
  rcases hg with ⟨rfl, _⟩ | hg | hg
  · exact morF_refl mug _
  · exact (hL _ _ hg).2.2
  · exact (hR _ _ hg).2.2

/-- A pair of a map whose key is below the root in `+gor` is in the left
subtree. -/
theorem Get_left_of {mug : Noun → Nat} {p q l r k v : Noun}
    (h : IsMap mug (Noun.cell (Noun.cell p q) (Noun.cell l r)))
    (hk : k ≠ p) (hg : gorF mug k p = true)
    (hget : Get (Noun.cell (Noun.cell p q) (Noun.cell l r)) k v) : Get l k v := by
  obtain ⟨_, _, _, hR⟩ := IsMap_node h
  rw [Get_node] at hget
  rcases hget with ⟨e, _⟩ | hget | hget
  · exact absurd e hk
  · exact hget
  · exact absurd (gorF_antisymm mug hg (hR _ _ hget).2.1) hk

/-- A pair of a map whose key is above the root in `+gor` is in the right
subtree. -/
theorem Get_right_of {mug : Noun → Nat} {p q l r k v : Noun}
    (h : IsMap mug (Noun.cell (Noun.cell p q) (Noun.cell l r)))
    (hk : k ≠ p) (hg : gorF mug p k = true)
    (hget : Get (Noun.cell (Noun.cell p q) (Noun.cell l r)) k v) : Get r k v := by
  obtain ⟨_, _, hL, _⟩ := IsMap_node h
  rw [Get_node] at hget
  rcases hget with ⟨e, _⟩ | hget | hget
  · exact absurd e hk
  · exact absurd (gorF_antisymm mug (hL _ _ hget).2.1 hg) hk
  · exact hget

/-! ## Canonical maps and sets -/

/-- Two maps with the same pairs are the same noun. -/
theorem isMap_ext {mug : Noun → Nat} {a b : Noun} (ha : IsMap mug a) (hb : IsMap mug b)
    (h : ∀ k v, Get a k v ↔ Get b k v) : a = b := by
  induction ha generalizing b with
  | nil =>
    cases hb with
    | nil => rfl
    | node _ _ _ _ => exact absurd ((h _ _).2 Get.here) Get_atom
  | @node p q l r hl hr hL hR ihl ihr =>
    cases hb with
    | nil => exact absurd ((h _ _).1 Get.here) Get_atom
    | @node p' q' l' r' hl' hr' hL' hR' =>
      have ha' : IsMap mug (Noun.cell (Noun.cell p q) (Noun.cell l r)) := IsMap.node hl hr hL hR
      have hb' : IsMap mug (Noun.cell (Noun.cell p' q') (Noun.cell l' r')) :=
        IsMap.node hl' hr' hL' hR'
      have e1 : morF mug p' p = true := morF_root_all hb' _ _ ((h _ _).1 Get.here)
      have e2 : morF mug p p' = true := morF_root_all ha' _ _ ((h _ _).2 Get.here)
      obtain rfl : p = p' := morF_antisymm mug e2 e1
      obtain rfl : q = q' := Get.unique hb' ((h _ _).1 Get.here) Get.here
      have el : l = l' := ihl hl' fun k v => by
        constructor
        · intro hg
          obtain ⟨ne, g, _⟩ := hL k v hg
          exact Get_left_of hb' ne g ((h k v).1 (Get.left hg))
        · intro hg
          obtain ⟨ne, g, _⟩ := hL' k v hg
          exact Get_left_of ha' ne g ((h k v).2 (Get.left hg))
      have er : r = r' := ihr hr' fun k v => by
        constructor
        · intro hg
          obtain ⟨ne, g, _⟩ := hR k v hg
          exact Get_right_of hb' ne g ((h k v).1 (Get.right hg))
        · intro hg
          obtain ⟨ne, g, _⟩ := hR' k v hg
          exact Get_right_of ha' ne g ((h k v).2 (Get.right hg))
      rw [el, er]

/-- `toMap` is injective. -/
theorem toMap_inj : ∀ (a b : Noun), toMap a = toMap b → a = b
  | Noun.atom m, b, h => by
    cases b with
    | atom m' => simpa using h
    | cell n t =>
      cases t with
      | atom _ => simp at h
      | cell _ _ => simp at h
  | Noun.cell n (Noun.atom k), b, h => by
    cases b with
    | atom _ => simp at h
    | cell n' t =>
      cases t with
      | atom _ => simpa using h
      | cell _ _ => simp at h
  | Noun.cell n (Noun.cell l r), b, h => by
    cases b with
    | atom _ => simp at h
    | cell n' t =>
      cases t with
      | atom _ => simp at h
      | cell l' r' =>
        simp only [toMap_node, Noun.cell.injEq, and_true] at h
        obtain ⟨rfl, h1, h2⟩ := h
        rw [toMap_inj l l' h1, toMap_inj r r' h2]

/-- Two sets with the same keys are the same noun. -/
theorem isSet_ext {mug : Noun → Nat} {a b : Noun} (ha : IsSet mug a) (hb : IsSet mug b)
    (h : ∀ k, Has a k ↔ Has b k) : a = b := by
  apply toMap_inj
  apply isMap_ext ha hb
  intro k v
  constructor
  · intro hg
    obtain rfl := Get_toMap hg
    exact (h k).1 hg
  · intro hg
    obtain rfl := Get_toMap hg
    exact (h k).2 hg

/-! ## The order of `+tap:by` -/

/-- `x` comes before `y` in `~(tap by a)`: their keys differ and the key of
`y` is below that of `x` in `+gor`. -/
def TapBefore (mug : Noun → Nat) (x y : Noun) : Prop :=
  ∃ kx vx ky vy, x = C kx vx ∧ y = C ky vy ∧ kx ≠ ky ∧ gorF mug ky kx = true

theorem TapBefore.asymm {mug : Noun → Nat} {x y : Noun} (h1 : TapBefore mug x y)
    (h2 : TapBefore mug y x) : False := by
  obtain ⟨kx, vx, ky, vy, rfl, rfl, ne, g⟩ := h1
  obtain ⟨_, _, _, _, e1, e2, _, g'⟩ := h2
  simp only [Noun.cell.injEq] at e1 e2
  obtain ⟨rfl, rfl⟩ := e1
  obtain ⟨rfl, rfl⟩ := e2
  exact ne (gorF_antisymm mug g' g)

/-- `~(tap by a)` lists the pairs of a map in strictly decreasing `+gor` order
of the keys. -/
theorem tapList_pairwise {mug : Noun → Nat} {a : Noun} (h : IsMap mug a) :
    (tapList a).Pairwise (TapBefore mug) := by
  induction h with
  | nil => simp [tapList]
  | @node p q l r hl hr hL hR ihl ihr =>
    simp only [tapList]
    rw [List.pairwise_append, List.pairwise_cons]
    refine ⟨ihr, ⟨?_, ihl⟩, ?_⟩
    · intro y hy
      obtain ⟨k, v, rfl, hg⟩ := (mem_tapList hl y).1 hy
      obtain ⟨ne, g, _⟩ := hL k v hg
      exact ⟨p, q, k, v, rfl, rfl, Ne.symm ne, g⟩
    · intro x hx y hy
      obtain ⟨k, v, rfl, hg⟩ := (mem_tapList hr x).1 hx
      obtain ⟨ne, g, _⟩ := hR k v hg
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ⟨k, v, p, q, rfl, rfl, ne, g⟩
      · obtain ⟨k', v', rfl, hg'⟩ := (mem_tapList hl y).1 hy
        obtain ⟨ne', g', _⟩ := hL k' v' hg'
        refine ⟨k, v, k', v', rfl, rfl, ?_, gorF_trans mug g' g⟩
        intro e
        subst e
        exact ne (gorF_antisymm mug g' g)

/-- Two lists ordered strictly by an asymmetric relation, with the same
members, are equal. -/
theorem pairwise_ext {α : Type} {R : α → α → Prop} (hR : ∀ x y, R x y → R y x → False) :
    ∀ {l1 l2 : List α}, l1.Pairwise R → l2.Pairwise R → (∀ x, x ∈ l1 ↔ x ∈ l2) → l1 = l2
  | [], [], _, _, _ => rfl
  | [], y :: _, _, _, h => absurd ((h y).2 List.mem_cons_self) List.not_mem_nil
  | x :: _, [], _, _, h => absurd ((h x).1 List.mem_cons_self) List.not_mem_nil
  | x :: xs, y :: ys, h1, h2, h => by
    rw [List.pairwise_cons] at h1 h2
    have irr : ∀ z, R z z → False := fun z hz => hR z z hz hz
    by_cases e : x = y
    · subst e
      rw [pairwise_ext hR h1.2 h2.2 fun z => ?_]
      constructor
      · intro hz
        have ne : z ≠ x := fun ez => irr x (ez ▸ h1.1 z hz)
        rcases List.mem_cons.1 ((h z).1 (List.mem_cons_of_mem _ hz)) with ez | hz'
        · exact absurd ez ne
        · exact hz'
      · intro hz
        have ne : z ≠ x := fun ez => irr x (ez ▸ h2.1 z hz)
        rcases List.mem_cons.1 ((h z).2 (List.mem_cons_of_mem _ hz)) with ez | hz'
        · exact absurd ez ne
        · exact hz'
    · have hx : x ∈ ys := by
        rcases List.mem_cons.1 ((h x).1 List.mem_cons_self) with ex | hx
        · exact absurd ex e
        · exact hx
      have hy : y ∈ xs := by
        rcases List.mem_cons.1 ((h y).2 List.mem_cons_self) with ey | hy
        · exact absurd ey.symm e
        · exact hy
      exact absurd (h2.1 x hx) fun h' => hR _ _ (h1.1 y hy) h'

/-- The list of `~(tap by a)` is the only list of the pairs of `a` in
strictly decreasing `+gor` order of the keys. -/
theorem tapList_unique {mug : Noun → Nat} {a : Noun} (h : IsMap mug a) {l : List Noun}
    (hl : l.Pairwise (TapBefore mug)) (hm : ∀ x, x ∈ l ↔ ∃ k v, x = C k v ∧ Get a k v) :
    l = tapList a :=
  pairwise_ext (fun _ _ => TapBefore.asymm) hl (tapList_pairwise h)
    fun x => (hm x).trans (mem_tapList h x).symm

/-- Two maps with the same pairs have the same `~(tap by ...)`. -/
theorem tapList_ext {mug : Noun → Nat} {a b : Noun} (ha : IsMap mug a) (hb : IsMap mug b)
    (h : ∀ k v, Get a k v ↔ Get b k v) : tapList a = tapList b := by
  rw [isMap_ext ha hb h]

/-- Two maps with the same pairs are folded by `+rep` in the same order. -/
theorem preorder_ext {mug : Noun → Nat} {a b : Noun} (ha : IsMap mug a) (hb : IsMap mug b)
    (h : ∀ k v, Get a k v ↔ Get b k v) : preorder a = preorder b := by
  rw [isMap_ext ha hb h]

/-- The members of the pre-order of a map are its pairs. -/
theorem mem_preorder {mug : Noun → Nat} {a : Noun} (h : IsMap mug a) (x : Noun) :
    x ∈ preorder a ↔ ∃ k v, x = C k v ∧ Get a k v :=
  (mem_preorder_tapList a x).trans (mem_tapList h x)

/-- The pre-order of a map node: its root, then the pairs below the root in
`+gor`, then those above. -/
theorem preorder_node (p q l r : Noun) :
    preorder (C (C p q) (C l r)) = C p q :: (preorder l ++ preorder r) := rfl

/-! ## Sets -/

/-- The keys of a set in the order of `~(tap in a)`. -/
theorem tapList_set_pairwise {mug : Noun → Nat} {a : Noun} (h : IsSet mug a) :
    ((tapList a).map fun n => C n (A 0)).Pairwise (TapBefore mug) := by
  rw [← tapList_toMap]
  exact tapList_pairwise h

/-- Two sets with the same keys have the same `~(tap in ...)`. -/
theorem tapList_set_ext {mug : Noun → Nat} {a b : Noun} (ha : IsSet mug a) (hb : IsSet mug b)
    (h : ∀ k, Has a k ↔ Has b k) : tapList a = tapList b := by
  rw [isSet_ext ha hb h]

end Hoon
end Formalization

end
