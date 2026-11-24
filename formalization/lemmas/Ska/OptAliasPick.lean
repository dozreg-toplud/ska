import lemmas.Ska.AnaInv

/-!
# The choice of `+alias`: the root of the treap of a `+silt`

`+alias` picks a member of a set of registers with `n` of the set's treap
(`n.res` for `%imm`, `n.intersect` for `%con`), and the model of the pass
takes the choice as a parameter `pick : List Nat → Nat` with the hypothesis
`hpick : ∀ l, l ≠ [] → pick l ∈ l` (`OptAliasModel.lean`).  `pick` is not
instantiated in the model track.  Here it is, for any treap of the analysis
(`Ana.Treap`), as the first key of `rap` of the `+silt` of the list: `rap`
lists a treap in the order in which `~(rep by ...)` visits it, which visits
`n` first, so on the treaps of the Hoon this is the root.  **`pickR_mem`**:
it meets `hpick`.  What the pill link must still supply is that the Hoon's
`n` of the set is this key, which is the pre-order of `+rep`
(`Hoon/RepBy.lean`) on the concrete treap.
-/

namespace Formalization
namespace SkaModel
namespace Ana
open Nock

/-- Registers as treap keys: atoms. -/
abbrev tkeyNat : TKey Nat := ⟨fun n => Noun.atom n, fun _ _ h => Noun.atom.inj h⟩

attribute [local instance] tkeyNat

variable {M : Type → Type → Type} [Treap M]

/-- **The choice**: the first key of `rap` of the `+silt` of the list. -/
def pickR (M : Type → Type → Type) [Treap M] (l : List Nat) : Nat :=
  match Treap.rap (Treap.silt l : M Nat Unit) with
  | (k, _) :: _ => k
  | [] => 0

theorem get_silt_fold (k : Nat) : ∀ (l : List Nat) (acc : M Nat Unit),
    Treap.get (l.foldl Treap.ins acc) k = some () ↔ Treap.get acc k = some () ∨ k ∈ l
  | [], acc => by simp
  | x :: l, acc => by
    simp only [List.foldl_cons]
    rw [get_silt_fold k l (Treap.ins acc x), Treap.get_ins]
    by_cases e : k = x
    · subst e; simp
    · simp [e]

theorem get_silt (l : List Nat) (k : Nat) : Treap.get (Treap.silt l : M Nat Unit) k = some () ↔ k ∈ l := by
  unfold Treap.silt
  rw [get_silt_fold k l Treap.empty, Treap.get_empty]
  simp

/-- **The choice picks a member** of a non-empty list (`hpick`). -/
theorem pickR_mem (l : List Nat) (hl : l ≠ []) : pickR M l ∈ l := by
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil l hl
  have hin : (x, ()) ∈ Treap.rap (Treap.silt l : M Nat Unit) :=
    (Treap.mem_rap _ _ _).mpr ((get_silt l x).mpr hx)
  unfold pickR
  split
  · rename_i k u tl e
    have hk : (k, u) ∈ Treap.rap (Treap.silt l : M Nat Unit) := by rw [e]; exact List.mem_cons_self
    exact (get_silt l k).mp ((Treap.mem_rap _ _ _).mp hk)
  · rename_i e
    rw [e] at hin; cases hin

end Ana
end SkaModel
end Formalization
