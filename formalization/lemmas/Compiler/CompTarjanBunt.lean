import lemmas.Compiler.CompSccOfMissBunt
import lemmas.Hoon.Ju

/-!
# `TarjanLinkAt` on every nonempty jug noun (track Q)

The three hypotheses of fork C's `tarjanLinkAt_of`, on a jug noun `G` (a
map whose values are sets, `TjJug`) that is not `~`:

* `tjSamB_run`: the bunt of the outer gate's sample (`tjSamB`, the molds
  `_p.n.-.g`, `(set vertex)` and `gen`) is `[[k ~] [0 ~ ~ ~ ~]]`, `k` the
  key of the root node, by the kernel (`evalFuel`; the molds test only
  whether `k` is a cell, so one case per shape of `k`);
* `tjGraphAt_jug`: the `+get:ju` of `G` on every key is a tree whose
  pre-order is `kidsOf (tjGraph G)` (a map has one pair per key);
* **`tarjanLinkAt_jug`**: `TarjanLinkAt G`;
* `scoSub_jug`: the `sub` the loop of `+scc-of` builds from `~[b]` is a
  nonempty jug; so **`sccG_missJ`**: the miss of `+scc-of` is `scoMiss`
  with no hypothesis on `+tarjan`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel Tarjan

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- **The bunt of the sample of `+tarjan`'s outer gate** on a nonempty
graph. -/
theorem tjSamB_run (k v l r : Noun) :
    nock (C tjBat (C (C (C k v) (C l r)) ana)) tjSamB
      = some (C (C k (A 0)) (tjAccN (A 0) (A 0) (A 0) (A 0) (A 0))) := by
  cases k with
  | atom n => exact nock_of_evalFuel (fuel := 3000) (by kernel_rfl)
  | cell a b => exact nock_of_evalFuel (fuel := 3000) (by kernel_rfl)

/-- A jug noun: a map whose values are sets. -/
def TjJug (G : Noun) : Prop := IsMap mugF G ∧ ∀ k v, Get G k v → IsSet mugF v

/-- The doors of `+ju` in the hoon core. -/
theorem scoJuIn : JuIn mugF layer2 :=
  ⟨by.arm_at, in.arm_at, someIn_layer2, gorIn_morIn_layer2.1, gorIn_morIn_layer2.2⟩

/-- A key's value in a map is unique. -/
theorem tj_get_uniq {G k v v' : Noun} (hG : IsMap mugF G) (h : Get G k v) (h' : Get G k v') : v = v' := by
  have a := getF_some hG h
  rw [getF_some hG h'] at a
  simp at a
  exact a.symm

/-- `kidsOf` of the model graph of a map is the pre-order of the value. -/
theorem tj_kidsOf {G : Noun} (hG : IsMap mugF G) (k : Noun) :
    kidsOf (tjGraph G) k = match getF mugF k G with
      | some (Noun.cell _ v) => preorder v
      | _ => [] := by
  unfold kidsOf tjGraph
  rw [List.find?_map]
  by_cases h : ∃ v, Get G k v
  · obtain ⟨v, hv⟩ := h
    rw [getF_some hG hv]
    cases e : (preorder G).find? ((fun p => decide (p.1 = k)) ∘ tjEntry) with
    | none =>
      have hm : C k v ∈ preorder G := (mem_preorder hG _).2 ⟨k, v, rfl, hv⟩
      have := List.find?_eq_none.1 e _ hm
      simp [tjEntry] at this
    | some x =>
      have hx := List.find?_some e
      have hm := List.mem_of_find?_eq_some e
      obtain ⟨k', v', rfl, hg⟩ := (mem_preorder hG _).1 hm
      simp only [Function.comp, tjEntry] at hx
      have hx' : k' = k := of_decide_eq_true hx
      subst hx'
      simp [tjEntry, tj_get_uniq hG hg hv]
  · rw [getF_none hG (fun v hv => h ⟨v, hv⟩)]
    cases e : (preorder G).find? ((fun p => decide (p.1 = k)) ∘ tjEntry) with
    | none => rfl
    | some x =>
      have hx := List.find?_some e
      have hm := List.mem_of_find?_eq_some e
      obtain ⟨k', v', rfl, hg⟩ := (mem_preorder hG _).1 hm
      simp only [Function.comp, tjEntry] at hx
      have hx' : k' = k := of_decide_eq_true hx
      subst hx'
      exact absurd ⟨v', hg⟩ h

/-- **`TjGraphAt` on a nonempty jug noun.** -/
theorem tjGraphAt_jug {k v l r : Noun} (hG : TjJug (C (C k v) (C l r))) :
    TjGraphAt (C tjBat (C (C (C k v) (C l r)) ana)) (tjGraph (C (C k v) (C l r))) := by
  refine ⟨C (C k v) (C l r), k, by simp [nock_exec], by simp [nock_exec], fun x => ?_⟩
  have hk := tj_kidsOf hG.1 x
  by_cases h : ∃ w, Get (C (C k v) (C l r)) x w
  · obtain ⟨w, hw⟩ := h
    have hg := getF_some hG.1 hw
    rw [hg] at hk
    refine ⟨w, ?_, Tree.of_isSet (hG.2 x w hw), hk.symm⟩
    have := ju_get_gate layer2 scoJuIn ju.battery x _ _ hg
    simpa [unUnit] using this
  · have hg := getF_none hG.1 (fun w hw => h ⟨w, hw⟩)
    rw [hg] at hk
    refine ⟨A 0, ?_, Tree.nil, by simpa [preorder] using hk.symm⟩
    have := ju_get_gate layer2 scoJuIn ju.battery x _ _ hg
    simpa [unUnit] using this

/-- **`TarjanLinkAt` on every nonempty jug noun.** -/
theorem tarjanLinkAt_jug {G : Noun} (hG : TjJug G) (hne : G ≠ A 0) : TarjanLinkAt G := by
  have hm := hG.1
  cases hm with
  | nil => exact absurd rfl hne
  | @node k v l r _ _ _ _ =>
    refine tarjanLinkAt_of (Tree.of_isMap hG.1) (fun x hx => ?_) (tjGraphAt_jug hG) (tjSamB_run k v l r)
    obtain ⟨k', v', rfl, hg⟩ := (mem_preorder hG.1 _).1 hx
    exact ⟨k', v', rfl, Tree.of_isSet (hG.2 k' v' hg)⟩

end Compiler
end Formalization
