import lemmas.Compiler.TreapList
import lemmas.Hoon.DifBy
import lemmas.Ska.CompLazyRun

/-!
# `+dif:by` on the treaps of `TreapMap` is `difM`

`difM a b` (`Ska/CompLazyRun.lean`, the model of `~(dif by a) b` that
`sectThread` reads) deletes the keys of `b` from `a` one by one.  On the
treaps of the pill's `+by` its lookups are those of `a` off the keys of `b`
(`get_difM`), and its noun is what `+dif:by` makes of the nouns of `a` and
`b` (`difByF_hoonMap`, from `difByF_spec` and `isMap_ext`), so the arm
gives it (`dif_by_hoonMap`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

variable {ν : Type}

theorem get_foldl_del (a : TreapMap mugF ν) : ∀ (ks : List Nat) (k : Nat),
    HoonMap.get (ks.foldl HoonMap.del a) k = if k ∈ ks then none else HoonMap.get a k
  | [], k => by simp
  | x :: xs, k => by
    simp only [List.foldl_cons]
    rw [get_foldl_del (HoonMap.del a x) xs k, HoonMap.get_del]
    by_cases h1 : k ∈ xs <;> by_cases h2 : k = x <;> simp [h1, h2]

/-- The lookups of `difM`: those of `a` off the keys of `b`. -/
theorem get_difM (a b : TreapMap mugF ν) (k : Nat) :
    HoonMap.get (difM a b) k = if (HoonMap.get b k).isSome then none else HoonMap.get a k := by
  unfold difM
  rw [get_foldl_del]
  simp only [HoonMapKeys.mem_keys]

/-- `+dif:by`'s model on the nouns of two treaps is the noun of `difM`. -/
theorem difByF_hoonMap (f : ν → Noun) (a b : TreapMap mugF ν) :
    difByF mugF (HoonMap.toNoun f a) (HoonMap.toNoun f b) = some (HoonMap.toNoun f (difM a b)) := by
  obtain ⟨out, h, hm, hk⟩ := difByF_spec (isMap_hoonMap f b) _ (isMap_hoonMap f a)
  rw [h]
  congr 1
  apply isMap_ext hm (isMap_hoonMap f _)
  intro x w
  rw [hk]
  simp only [hoonMap_toNoun]
  rw [Tr.Get_toNoun_iff f _ (a.2 f), Tr.Get_toNoun_iff f _ ((difM a b).2 f)]
  constructor
  · rintro ⟨⟨k, v, rfl, ha, rfl⟩, hn⟩
    refine ⟨k, v, rfl, ?_, rfl⟩
    have hb : (HoonMap.get b k).isSome = false := by
      cases e : HoonMap.get b k with
      | none => rfl
      | some u =>
        exact absurd ((Tr.Get_toNoun_iff f _ (b.2 f) _ _).2 ⟨k, u, rfl, e, rfl⟩) (hn (f u))
    rw [← hoonMap_get, get_difM, hb]
    exact ha
  · rintro ⟨k, v, rfl, hd, rfl⟩
    rw [← hoonMap_get, get_difM] at hd
    split at hd
    · cases hd
    · rename_i hb
      refine ⟨⟨k, v, rfl, hd, rfl⟩, fun w' hw => ?_⟩
      obtain ⟨k', v', hk', hb', rfl⟩ := (Tr.Get_toNoun_iff f _ (b.2 f) _ _).1 hw
      cases hk'
      rw [← hoonMap_get] at hb'
      simp [hb'] at hb

/-- `+dif:by` on the nouns of two treaps gives the noun of `difM`. -/
theorem dif_by_hoonMap (ctx : Noun) (hc : GorIn mugF ctx ∧ MorIn mugF ctx) (f : ν → Noun)
    (a b : TreapMap mugF ν) :
    nock (C by.dif.battery (C (HoonMap.toNoun f b) (C by.battery (C (HoonMap.toNoun f a) ctx))))
      by.dif.battery = some (HoonMap.toNoun f (difM a b)) :=
  dif_by_gate ctx hc _ _ _ (difByF_hoonMap f a b)

end Compiler
end Formalization
