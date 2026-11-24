module

public import lemmas.Hoon.MapFolds
import all lemmas.Pill.Arm.By

/-!
`+run:by` with a gate that is known only on the values of the map.

`run_by` (`Hoon/MapFolds.lean`) takes a gate that maps every noun; the gate of
`+run:by` in `+trim-trace-hints` maps a block, and is known only on the
nouns of blocks.  `run_by_P`: on a map whose values meet `P`, with a gate
that maps each noun with `P` to `f` of it, the whole call (the arm, the
gate slammed) returns a map with the same keys and the values mapped.
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

/-- The arm `+run:by`: the wet gate with its bunt. -/
@[nock_exec] theorem by_run_arm (d : Noun) :
    nock d by.run.arm = some (C by.run.battery (C (C (C (A 0) (A 15)) (C (A 0) (C (A 0) (A 0)))) d)) := by
  nock_open by.run.arm; simp only [nock_exec]

theorem run_loop_P (B ctx fp fs fc : Noun) (P : Noun → Prop) (f : Noun → Noun)
    (hf : ∀ x, P x → nock (C fp (C x fc)) fp = some (f x)) {mug : Noun → Nat} {a : Noun} (h : IsMap mug a) :
    (∀ k v, Get a k v → P v) →
    ∃ out, nock (C by.run.loop (C by.run.battery (C (C fp (C fs fc)) (C B (C a ctx))))) by.run.loop = some out ∧
      IsMap mug out ∧ ∀ k w, Get out k w ↔ ∃ v, Get a k v ∧ w = f v := by
  induction h with
  | nil =>
    intro _
    refine ⟨A 0, ?_, IsMap.nil, fun k w => by simp [Get_atom]⟩
    nock_open by.run.loop
    simp [nock_exec]
  | @node p q l r hl hr hL hR ihl ihr =>
    intro hp
    obtain ⟨l', hl1, hml, hgl⟩ := ihl (fun k v h => hp k v (Get.left h))
    obtain ⟨r', hr1, hmr, hgr⟩ := ihr (fun k v h => hp k v (Get.right h))
    have hq := hf q (hp p q Get.here)
    refine ⟨C (C p (f q)) (C l' r'), ?_, ?_, fun k w => ?_⟩
    · nock_open by.run.loop
      simp [nock_exec, hq, hl1, hr1]
    · refine IsMap.node hml hmr (fun k w hk => ?_) (fun k w hk => ?_)
      · obtain ⟨v, hv, _⟩ := (hgl k w).1 hk; exact hL k v hv
      · obtain ⟨v, hv, _⟩ := (hgr k w).1 hk; exact hR k v hv
    · rw [Get_node, hgl, hgr]
      constructor
      · rintro (⟨rfl, rfl⟩ | ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
        · exact ⟨q, Get.here, rfl⟩
        · exact ⟨v, Get.left hv, rfl⟩
        · exact ⟨v, Get.right hv, rfl⟩
      · rintro ⟨v, hv, rfl⟩
        rw [Get_node] at hv
        rcases hv with ⟨rfl, rfl⟩ | hv | hv
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr (Or.inl ⟨v, hv, rfl⟩)
        · exact Or.inr (Or.inr ⟨v, hv, rfl⟩)

/-- **`+run:by` with a gate known on the values**: the gate of `+run:by`
slammed on the gate `[fp [fs fc]]` returns a map with the keys of `a` and
the values mapped by `f`. -/
theorem run_by_P (ctx fp fs fc : Noun) (P : Noun → Prop) (f : Noun → Noun)
    (hf : ∀ x, P x → nock (C fp (C x fc)) fp = some (f x)) {mug : Noun → Nat} {a : Noun} (h : IsMap mug a)
    (hp : ∀ k v, Get a k v → P v) :
    ∃ out, nock (C by.run.battery (C (C fp (C fs fc)) (C by.battery (C a ctx)))) by.run.battery = some out ∧
      IsMap mug out ∧ ∀ k w, Get out k w ↔ ∃ v, Get a k v ∧ w = f v := by
  obtain ⟨out, ho, hm, hg⟩ := run_loop_P by.battery ctx fp fs fc P f hf h hp
  refine ⟨out, ?_, hm, hg⟩
  nock_open by.run.battery
  simp [nock_exec, ho]

end Hoon
end Formalization

end
