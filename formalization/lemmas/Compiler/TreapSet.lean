import lemmas.Compiler.TreapKey

/-!
# Sets of the `FinMap` instance

`FinMap.setNoun m` is the noun of the map of `m` with the value `~` under each
key, with the values dropped (`unMap`).  `toMap` puts them back
(`toMap_setNoun`), so the noun is an `IsSet mugF` whose members are the
encoded keys of `m` (`isSet_setNoun`, `has_setNoun`), and by `isSet_ext` the
model of `+put:in` on it gives the noun of `FinMap.put m k ()`
(`putInF_setNoun`).  For example the callee set of `fol-loop`: `+put:in` of
`[seat id-there]` into the noun of `callees` is the noun of
`Treap.ins callees ⟨seat, id-there⟩` (`calleePutIs` of
`Compiler/FolLoopStep.lean`).
-/

namespace Formalization
namespace Compiler

open Nock Hoon SkaModel SkaModel.Ana

namespace FinMap

variable {κ : Type}

/-- `toMap` undoes `unMap` on a map whose values are all `~`. -/
theorem toMap_unMap {a : Noun} (h : IsMap mugF a) (hv : ∀ k v, Get a k v → v = A 0) :
    toMap (unMap a) = a := by
  induction h with
  | nil => rfl
  | @node p q l r hl hr _ _ ihl ihr =>
    have hq : q = A 0 := hv p q Get.here
    subst hq
    show toMap (C p (C (unMap l) (unMap r))) = _
    rw [toMap_node, ihl (fun k v g => hv k v (Get.left g)),
      ihr (fun k v g => hv k v (Get.right g))]

variable [TKey κ]

theorem toMap_setNoun (m : FinMap κ Unit) : toMap m.setNoun = m.toNoun fun _ => A 0 :=
  toMap_unMap (isMap_toNoun _ m) fun k v g => by
    obtain ⟨_, _, _, _, rfl⟩ := (get_toNoun _ m k v).1 g
    rfl

theorem isSet_setNoun (m : FinMap κ Unit) : IsSet mugF m.setNoun := by
  unfold IsSet
  rw [toMap_setNoun]
  exact isMap_toNoun _ m

/-- The members of the noun of a set are the encoded keys. -/
theorem has_setNoun (m : FinMap κ Unit) (kn : Noun) :
    Has m.setNoun kn ↔ ∃ k, m.1 k = some () ∧ kn = TKey.enc k := by
  unfold Has
  rw [toMap_setNoun, get_toNoun]
  constructor
  · rintro ⟨k, v, h1, h2, -⟩
    exact ⟨k, h1, h2⟩
  · rintro ⟨k, h1, h2⟩
    exact ⟨k, (), h1, h2, rfl⟩

variable [DecidableEq κ]

/-- `+put:in` on the noun of a set is the noun of the set with the key. -/
theorem putInF_setNoun (m : FinMap κ Unit) (k : κ) :
    putInF mugF (TKey.enc k) m.setNoun = some (m.put k ()).setNoun := by
  obtain ⟨out, hp, hs, hh⟩ := putInF_spec mugF m.setNoun (TKey.enc k) (isSet_setNoun m)
  rw [hp, isSet_ext hs (isSet_setNoun (m.put k ()))]
  intro kn
  rw [hh, has_setNoun, has_setNoun]
  constructor
  · rintro (rfl | ⟨k', h1, rfl⟩)
    · exact ⟨k, by simp [put], rfl⟩
    · by_cases e : k' = k
      · subst e
        exact ⟨k', by simp [put], rfl⟩
      · exact ⟨k', by simp [put, e, h1], rfl⟩
  · rintro ⟨k', h1, rfl⟩
    by_cases e : k' = k
    · subst e
      exact Or.inl rfl
    · simp only [put, e, if_false] at h1
      exact Or.inr ⟨k', h1, rfl⟩

end FinMap

end Compiler
end Formalization
