import lemmas.Compiler.TreapMap
import lemmas.Hoon.Canon
import lemmas.Ska.CompTop

/-!
# Equality and listings of the treaps of `TreapMap`

The laws that the analysis model's `Treap` class (`lemmas/Ska/Analysis.lean`)
asks of a map beyond `get_put` and `get_del`, on the treaps of
`TreapMap.lean`:

* `TreapMap.ext`: two treaps with the same lookups are equal.  It comes from
  `isMap_ext` (`Hoon/Canon.lean`) under every layout of the values, and
  `Tr.toNoun_inj`: a treap is determined by its nouns under all layouts.
* `TreapMap.tap` and `TreapMap.rap`: the pairs in the order of
  `~(tap by ...)` and in the order in which `~(rep by ...)` visits them.  Their
  nouns are the lists that `tap_by` and `rep_tree` speak of (`tapList_toNoun`,
  `preorder_toNoun`), and their members are the pairs of the map (`mem_tap`,
  `mem_rap`).  `tap` is strictly decreasing in `+gor` of the key nouns
  (`tap_pairwise`), which determines it.
* The instance of `HoonMapKeys` (`lemmas/Ska/CompTop.lean`), whose keys are
  those of `tap`.
-/

namespace Formalization
namespace Compiler

open Nock Hoon SkaModel

namespace Tr

variable {ν : Type}

/-- The pairs in the order of `~(tap by ...)`: right subtree, root, left
subtree. -/
def tapL : Tr ν → List (Nat × ν)
  | nil => []
  | node k v l r => tapL r ++ (k, v) :: tapL l

/-- The pairs in the order in which `~(rep by ...)` visits them: root, left
subtree, right subtree. -/
def pre : Tr ν → List (Nat × ν)
  | nil => []
  | node k v l r => (k, v) :: (pre l ++ pre r)

/-- The noun of a pair. -/
def pairNoun (f : ν → Noun) (x : Nat × ν) : Noun := C (A x.1) (f x.2)

theorem tapList_toNoun (f : ν → Noun) :
    ∀ t : Tr ν, tapList (t.toNoun f) = (t.tapL).map (pairNoun f)
  | nil => rfl
  | node k v l r => by
    simp [toNoun, tapList, tapL, tapList_toNoun f l, tapList_toNoun f r, pairNoun]

theorem preorder_toNoun (f : ν → Noun) :
    ∀ t : Tr ν, preorder (t.toNoun f) = (t.pre).map (pairNoun f)
  | nil => rfl
  | node k v l r => by
    simp [toNoun, preorder, pre, preorder_toNoun f l, preorder_toNoun f r, pairNoun]

/-- The keys of the noun of a treap are atoms. -/
theorem Get_toNoun_atom (f : ν → Noun) :
    ∀ (t : Tr ν) {x w : Noun}, Get (t.toNoun f) x w → ∃ k, x = A k
  | nil, _, _, h => absurd h Get_atom
  | node k v l r, x, w, h => by
    simp only [toNoun] at h
    rw [Get_node] at h
    rcases h with ⟨rfl, _⟩ | h | h
    · exact ⟨k, rfl⟩
    · exact Get_toNoun_atom f l h
    · exact Get_toNoun_atom f r h

/-- A key whose lookup on a map is a unit is in the map. -/
theorem Get_of_getF {mug : Noun → Nat} {a k w : Noun} (h : IsMap mug a)
    (hg : getF mug k a = some (C (A 0) w)) : Get a k w := by
  by_cases hv : ∃ w', Get a k w'
  · obtain ⟨w', hw'⟩ := hv
    rw [getF_some h hw'] at hg
    simp only [Option.some.injEq, Noun.cell.injEq, true_and] at hg
    exact hg ▸ hw'
  · rw [getF_none h fun w' hw' => hv ⟨w', hw'⟩] at hg
    simp at hg

/-- The pairs of the noun of a treap that is a map are its lookups. -/
theorem Get_toNoun_iff {mug : Noun → Nat} (f : ν → Noun) (t : Tr ν) (h : IsMap mug (t.toNoun f))
    (x w : Noun) :
    Get (t.toNoun f) x w ↔ ∃ k v, x = A k ∧ t.get mug k = some v ∧ w = f v := by
  constructor
  · intro hg
    obtain ⟨k, rfl⟩ := Get_toNoun_atom f t hg
    have e := getF_some h hg
    rw [getF_toNoun] at e
    cases hk : t.get mug k with
    | none => rw [hk] at e; simp [unitNoun] at e
    | some v =>
      rw [hk] at e
      simp only [unitNoun, Option.some.injEq, Noun.cell.injEq, true_and] at e
      exact ⟨k, v, rfl, hk, e.symm⟩
  · rintro ⟨k, v, rfl, hk, rfl⟩
    apply Get_of_getF h
    rw [getF_toNoun, hk]
    rfl

/-- A treap is determined by its nouns under every layout of the values. -/
theorem toNoun_inj : ∀ {a b : Tr ν}, (∀ f : ν → Noun, a.toNoun f = b.toNoun f) → a = b
  | nil, nil, _ => rfl
  | nil, node _ _ _ _, h => by have := h (fun _ => A 0); simp [toNoun] at this
  | node _ _ _ _, nil, h => by have := h (fun _ => A 0); simp [toNoun] at this
  | node k v l r, node k' v' l' r', h => by
    classical
    have h0 := h (fun _ => A 0)
    simp only [toNoun, Noun.cell.injEq, Noun.atom.injEq] at h0
    obtain ⟨⟨rfl, -⟩, -, -⟩ := h0
    have hv := h (fun x => if x = v then A 0 else A 1)
    simp only [toNoun, Noun.cell.injEq] at hv
    have ev : v' = v := by
      by_cases e : v' = v
      · exact e
      · rw [if_neg e] at hv; simp at hv
    subst ev
    have hl : ∀ f : ν → Noun, l.toNoun f = l'.toNoun f := fun f => by
      have := h f; simp only [toNoun, Noun.cell.injEq] at this; exact this.2.1
    have hr : ∀ f : ν → Noun, r.toNoun f = r'.toNoun f := fun f => by
      have := h f; simp only [toNoun, Noun.cell.injEq] at this; exact this.2.2
    rw [toNoun_inj hl, toNoun_inj hr]

/-- A pair `(k, v)` is in a list of pairs whose nouns under every layout are
the pairs of the noun of `t` exactly when `t` looks `k` up to `v`. -/
theorem mem_of_nouns {mug : Noun → Nat} (t : Tr ν) (h : ∀ f : ν → Noun, IsMap mug (t.toNoun f))
    (L : List (Nat × ν)) (hL : ∀ f x, x ∈ L.map (pairNoun f) ↔ ∃ k w, x = C k w ∧ Get (t.toNoun f) k w)
    (k : Nat) (v : ν) : (k, v) ∈ L ↔ t.get mug k = some v := by
  classical
  let f : ν → Noun := fun x => if x = v then A 0 else A 1
  have sep : ∀ x, f x = f v → x = v := fun x e => by
    by_cases ex : x = v
    · exact ex
    · simp [f, ex] at e
  constructor
  · intro hm
    obtain ⟨k', w, e, hg⟩ := (hL f _).1 (List.mem_map_of_mem (f := pairNoun f) hm)
    obtain ⟨k'', v', rfl, hk, rfl⟩ := (Get_toNoun_iff f t (h f) _ _).1 hg
    simp only [pairNoun, Noun.cell.injEq, Noun.atom.injEq] at e
    obtain ⟨rfl, e⟩ := e
    rw [hk, sep v' e.symm]
  · intro hk
    obtain ⟨y, hy, e⟩ := List.mem_map.1 ((hL f _).2 ⟨A k, f v, rfl,
      (Get_toNoun_iff f t (h f) _ _).2 ⟨k, v, rfl, hk, rfl⟩⟩)
    obtain ⟨k', v'⟩ := y
    simp only [pairNoun, Noun.cell.injEq, Noun.atom.injEq] at e
    obtain ⟨rfl, e⟩ := e
    rw [← sep v' e]
    exact hy

end Tr

namespace TreapMap

variable {mug : Noun → Nat} {ν : Type}

/-- Two treaps with the same lookups are equal. -/
theorem ext (a b : TreapMap mug ν) (h : ∀ k, get a k = get b k) : a = b := by
  apply Subtype.ext
  apply Tr.toNoun_inj
  intro f
  apply isMap_ext (a.2 f) (b.2 f)
  intro x w
  rw [Tr.Get_toNoun_iff f a.1 (a.2 f), Tr.Get_toNoun_iff f b.1 (b.2 f)]
  simp only [get] at h
  simp only [h]

/-- The pairs in the order of `~(tap by ...)`. -/
def tap (m : TreapMap mug ν) : List (Nat × ν) := m.1.tapL

/-- The pairs in the order in which `~(rep by ...)` visits them. -/
def rap (m : TreapMap mug ν) : List (Nat × ν) := m.1.pre

/-- The noun list of `~(tap by ...)` on the noun of a treap. -/
theorem tapList_toNoun (f : ν → Noun) (m : TreapMap mug ν) :
    tapList (toNoun f m) = (tap m).map (Tr.pairNoun f) :=
  Tr.tapList_toNoun f m.1

/-- The noun list that `~(rep by ...)` folds over, on the noun of a treap. -/
theorem preorder_toNoun (f : ν → Noun) (m : TreapMap mug ν) :
    preorder (toNoun f m) = (rap m).map (Tr.pairNoun f) :=
  Tr.preorder_toNoun f m.1

theorem mem_tap (m : TreapMap mug ν) (k : Nat) (v : ν) : (k, v) ∈ tap m ↔ get m k = some v :=
  Tr.mem_of_nouns m.1 m.2 m.1.tapL (fun f x => by
    rw [← Tr.tapList_toNoun]; exact mem_tapList (m.2 f) x) k v

theorem mem_rap (m : TreapMap mug ν) (k : Nat) (v : ν) : (k, v) ∈ rap m ↔ get m k = some v :=
  Tr.mem_of_nouns m.1 m.2 m.1.pre (fun f x => by
    rw [← Tr.preorder_toNoun]; exact mem_preorder (m.2 f) x) k v

/-- `tap` lists the keys in strictly decreasing `+gor` order of their nouns. -/
theorem tap_pairwise (m : TreapMap mug ν) :
    (tap m).Pairwise (fun x y => x.1 ≠ y.1 ∧ gorF mug (A y.1) (A x.1) = true) := by
  have hp := tapList_pairwise (m.2 fun _ => A 0)
  rw [Tr.tapList_toNoun, List.pairwise_map] at hp
  refine hp.imp fun {x y} hxy => ?_
  obtain ⟨kx, vx, ky, vy, ex, ey, ne, g⟩ := hxy
  simp only [Tr.pairNoun, Noun.cell.injEq] at ex ey
  obtain ⟨rfl, -⟩ := ex
  obtain ⟨rfl, -⟩ := ey
  exact ⟨fun e => ne (by rw [e]), g⟩

end TreapMap

/-- The keys of a treap, in the order of `~(tap by ...)`. -/
instance : Comp.HoonMapKeys (TreapMap mugF) where
  keys m := (TreapMap.tap m).map Prod.fst
  mem_keys m k := by
    constructor
    · intro hk
      obtain ⟨⟨k', v⟩, hm, rfl⟩ := List.mem_map.1 hk
      show (TreapMap.get m k').isSome = true
      rw [(TreapMap.mem_tap m k' v).1 hm]
      rfl
    · intro hk
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hk
      exact List.mem_map.2 ⟨(k, v), (TreapMap.mem_tap m k v).2 hv, rfl⟩

end Compiler
end Formalization
