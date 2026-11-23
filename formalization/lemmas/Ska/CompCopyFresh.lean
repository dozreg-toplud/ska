import lemmas.Ska.CompLazyArms

/-!
# `+copy-lazy` on lazy needs whose blocks are apart

`+copy-lazy` merges the forks of its two needs by the label of the yes
block, and the bonds by their label.  When no label of the first need is a
label of the second, nothing is merged: the forks of the first come first,
then all those of the second, and the same for the bonds
(`copyLazyL_apart`).  This is the case of a Nock 6 used as a test, or of a
Nock 6 under `%pick`, whose lazy blocks are fresh: `index` finds nothing
(`get_index_none`), `mergeForks` and `mergeBonds` return their list
(`mergeForks_fresh`, `mergeBonds_fresh`), and the filter by `seen` keeps
everything (`seen_false`).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

theorem get_foldl_put_none {α : Type} (key : α → Nat) (k : Nat) :
    ∀ (l : List α) (m : Map α), (∀ e ∈ l, key e ≠ k) →
      HoonMap.get (l.foldl (fun m e => HoonMap.put m (key e) e) m) k = HoonMap.get m k
  | [], _, _ => rfl
  | e :: l, m, h => by
    simp only [List.foldl_cons]
    rw [get_foldl_put_none key k l _ (fun e' he' => h e' (List.mem_cons_of_mem _ he')), HoonMap.get_put]
    have := h e List.mem_cons_self
    simp [Ne.symm this]

/-- **`index` finds nothing under a key no entry has.** -/
theorem get_index_none {α : Type} (key : α → Nat) {l : List α} {k : Nat} (h : ∀ e ∈ l, key e ≠ k) :
    HoonMap.get (index (Map := Map) key l) k = Option.none := by
  unfold index
  rw [get_foldl_put_none key k l _ h, HoonMap.get_empty]

theorem mem_foldl_put : ∀ (xs : List Nat) (s : S) (y : Nat),
    y ∈ HoonSet.toList (xs.foldl HoonSet.put s) ↔ y ∈ xs ∨ y ∈ HoonSet.toList s
  | [], s, y => by simp
  | x :: xs, s, y => by
    simp only [List.foldl_cons]
    rw [mem_foldl_put xs (HoonSet.put s x) y, HoonSet.mem_put]
    simp only [List.mem_cons]
    constructor
    · rintro (h | h | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rintro ((h | h) | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

/-- **`seen` says no to a key no entry has.** -/
theorem seen_false {α : Type} (key : α → Nat) {l : List α} {k : Nat} (h : ∀ e ∈ l, key e ≠ k) :
    seen (S := S) key l k = false := by
  unfold seen
  rw [decide_eq_false_iff_not, mem_foldl_put]
  rintro (hk | hk)
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
    exact h e he rfl
  · exact HoonSet.mem_empty k hk

/-- **`mergeForks` returns its list when the index has none of its yes
labels.** -/
theorem mergeForks_fresh (idx : Map (ForkE S)) :
    ∀ (l : List (ForkE S)), (∀ e ∈ l, HoonMap.get idx e.1.1 = Option.none) →
      (mergeForks idx l : CM Map (List (ForkE S))) = pure l
  | [], _ => by rw [mergeForks]
  | ((oy, y), (on, n)) :: rest, h => by
    rw [mergeForks]
    have h0 : HoonMap.get idx oy = Option.none := h _ List.mem_cons_self
    have ih := mergeForks_fresh idx rest (fun e he => h e (List.mem_cons_of_mem _ he))
    simp only [h0, ih, pure_bind]

/-- **`mergeBonds` returns its list when the index has none of its
labels.** -/
theorem mergeBonds_fresh (idx : Map (Nat × Lazy S)) :
    ∀ (l : List (Nat × Lazy S)), (∀ e ∈ l, HoonMap.get idx e.1 = Option.none) →
      (mergeBonds idx l : CM Map (List (Nat × Lazy S))) = pure l
  | [], _ => by rw [mergeBonds]
  | (ob, l) :: rest, h => by
    rw [mergeBonds]
    have h0 : HoonMap.get idx ob = Option.none := h _ List.mem_cons_self
    have ih := mergeBonds_fresh idx rest (fun e he => h e (List.mem_cons_of_mem _ he))
    simp only [h0, ih, pure_bind]

/-- The forks of `+copy-lazy` when the yes labels are apart. -/
theorem copyForks_apart {f1 f2 : List (ForkE S)} (h : ∀ e ∈ f1, ∀ e' ∈ f2, e.1.1 ≠ e'.1.1) :
    (if f2.isEmpty then pure f1 else if f1.isEmpty then pure f2 else do
      let merged ← mergeForks (index (Map := Map) (fun e : ForkE S => e.1.1) f2) f1
      pure (merged ++ f2.filter fun e => !(seen (S := S) (fun e : ForkE S => e.1.1) f1 e.1.1)) :
        CM Map (List (ForkE S))) = pure (f1 ++ f2) := by
  by_cases e2 : f2.isEmpty = true
  · rw [if_pos e2, List.isEmpty_iff.mp e2, List.append_nil]
  rw [if_neg e2]
  by_cases e1 : f1.isEmpty = true
  · rw [if_pos e1, List.isEmpty_iff.mp e1, List.nil_append]
  rw [if_neg e1, mergeForks_fresh _ f1 (fun e he => get_index_none _ (fun e' he' => (h e he e' he').symm)),
    pure_bind]
  congr 2
  exact List.filter_eq_self.mpr fun e' he' => by
    rw [seen_false _ (fun e he => h e he e' he')]; rfl

/-- The bonds of `+copy-lazy` when the labels are apart. -/
theorem copyBonds_apart {b1 b2 : List (Nat × Lazy S)} (h : ∀ e ∈ b1, ∀ e' ∈ b2, e.1 ≠ e'.1) :
    (if b2.isEmpty then pure b1 else if b1.isEmpty then pure b2 else do
      let merged ← mergeBonds (index (Map := Map) (fun e : Nat × Lazy S => e.1) b2) b1
      pure (merged ++ b2.filter fun e => !(seen (S := S) (fun e : Nat × Lazy S => e.1) b1 e.1)) :
        CM Map (List (Nat × Lazy S))) = pure (b1 ++ b2) := by
  by_cases e2 : b2.isEmpty = true
  · rw [if_pos e2, List.isEmpty_iff.mp e2, List.append_nil]
  rw [if_neg e2]
  by_cases e1 : b1.isEmpty = true
  · rw [if_pos e1, List.isEmpty_iff.mp e1, List.nil_append]
  rw [if_neg e1, mergeBonds_fresh _ b1 (fun e he => get_index_none _ (fun e' he' => (h e he e' he').symm)),
    pure_bind]
  congr 2
  exact List.filter_eq_self.mpr fun e' he' => by
    rw [seen_false _ (fun e he => h e he e' he')]; rfl

/-- **`+copy-lazy` of two lazy needs whose blocks are apart** merges the
sure needs and puts the forks and bonds side by side. -/
theorem copyLazyL_apart (o : Nat) (s1 : Sure S) (f1 : List (ForkE S)) (b1 : List (Nat × Lazy S))
    (second : Lazy S) (hf : ∀ e ∈ f1, ∀ e' ∈ second.fork, e.1.1 ≠ e'.1.1)
    (hb : ∀ e ∈ b1, ∀ e' ∈ second.bond, e.1 ≠ e'.1) :
    (copyLazyL o (mk s1 f1 b1) second : CM Map (Lazy S)) = (do
      let (ned, ops) ← copyNeed s1.ned second.sure.ned []
      addOps o ops
      pure (mk ⟨ned, HoonSet.uni s1.lok second.sure.lok⟩ (f1 ++ second.fork) (b1 ++ second.bond))) := by
  rw [copyLazyL]
  simp only [copyForks_apart hf, copyBonds_apart hb, pure_bind]

end Comp
end SkaModel
end Formalization
