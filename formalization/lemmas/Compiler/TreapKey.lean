import lemmas.Hoon.Canon
import lemmas.Hoon.DelBy
import lemmas.Hoon.Maps
import lemmas.Hoon.Sets
import lemmas.Hoon.Mug
import lemmas.Ska.Analysis

/-!
# An instance of `Treap` for the analysis model

`Treap` of `Ska/Analysis.lean` takes the type of its maps, `M κ ν`, before the
encoding of the keys (`TKey κ` is an argument of each operation).  So `M κ ν`
cannot hold a treap ordered by `+gor` of the encoded keys, nor the proof that
its noun is a map: both depend on the encoding.  But a treap is determined by
its pairs (`isMap_ext`), so here `M κ ν` is the finite map itself (`FinMap`,
a lookup function with a finite support), and the treap is made from it when
an encoding is given:

* `FinMap.toNoun f m` is the noun of the map: the pairs of `m`, keys encoded
  by `TKey.enc` and values laid out by `f`, put one by one with `+put:by`
  (`putF`).  It is an `IsMap mugF` (`isMap_toNoun`), with exactly the pairs of
  `m` (`get_toNoun`), so it is the noun of every treap with these pairs.
* `tap` and `rap` read the keys off `~(tap by ...)` and the pre-order of
  `+rep` of that noun and pair them with their values (`mem_tap`, `mem_rap`).
* `get`, `put`, `del` are the lookup and its updates, so the laws of the class
  are immediate, `ext` included (by function extensionality; on nouns it is
  `isMap_ext`).

What the pill's arms do to the nouns: `putF_toNoun`, `delF_toNoun`,
`getF_toNoun`.
-/

namespace Formalization
namespace Compiler

open Nock Hoon SkaModel SkaModel.Ana

/-- A finite map from `κ` to `ν`: a lookup with a finite support. -/
def FinMap (κ ν : Type) : Type := {f : κ → Option ν // ∃ l : List κ, ∀ k, f k ≠ none → k ∈ l}

namespace FinMap

variable {κ ν : Type}

/-- A list of keys that holds every key of `m`. -/
noncomputable def supp (m : FinMap κ ν) : List κ := Classical.choose m.2

theorem mem_supp (m : FinMap κ ν) {k : κ} (h : m.1 k ≠ none) : k ∈ m.supp :=
  Classical.choose_spec m.2 k h

def empty : FinMap κ ν := ⟨fun _ => none, [], fun _ h => absurd rfl h⟩

def get (m : FinMap κ ν) (k : κ) : Option ν := m.1 k

def put [DecidableEq κ] (m : FinMap κ ν) (k : κ) (v : ν) : FinMap κ ν :=
  ⟨fun k' => if k' = k then some v else m.1 k', k :: m.supp, fun k' h => by
    by_cases e : k' = k
    · exact e ▸ List.mem_cons_self
    · simp only [e, if_false] at h
      exact List.mem_cons_of_mem _ (m.mem_supp h)⟩

def del [DecidableEq κ] (m : FinMap κ ν) (k : κ) : FinMap κ ν :=
  ⟨fun k' => if k' = k then none else m.1 k', m.supp, fun k' h => by
    by_cases e : k' = k
    · simp [e] at h
    · simp only [e, if_false] at h
      exact m.mem_supp h⟩

/-! ## The noun -/

variable [TKey κ]

/-- Put the pair of `k`, if `m` has one, into the map noun `a`. -/
noncomputable def step (f : ν → Noun) (m : FinMap κ ν) (a : Noun) (k : κ) : Noun :=
  match m.1 k with
  | some v => (putF mugF (TKey.enc k) (f v) a).getD (A 0)
  | none => a

/-- The noun of `m`, its values laid out by `f`. -/
noncomputable def toNoun (f : ν → Noun) (m : FinMap κ ν) : Noun :=
  m.supp.foldl (step f m) (A 0)

/-- The pairs of the noun made from the keys `L`. -/
def PairsOf (f : ν → Noun) (m : FinMap κ ν) (L : List κ) (kn vn : Noun) : Prop :=
  ∃ k v, k ∈ L ∧ m.1 k = some v ∧ kn = TKey.enc k ∧ vn = f v

theorem foldl_spec (f : ν → Noun) (m : FinMap κ ν) :
    ∀ (L P : List κ) (a : Noun), IsMap mugF a → (∀ kn vn, Get a kn vn ↔ PairsOf f m P kn vn) →
      IsMap mugF (L.foldl (step f m) a) ∧
        ∀ kn vn, Get (L.foldl (step f m) a) kn vn ↔ PairsOf f m (P ++ L) kn vn
  | [], P, a, ha, hg => by simpa using ⟨ha, hg⟩
  | k :: L, P, a, ha, hg => by
    simp only [List.foldl_cons]
    have hstep : IsMap mugF (step f m a k) ∧
        ∀ kn vn, Get (step f m a k) kn vn ↔ PairsOf f m (P ++ [k]) kn vn := by
      unfold step
      cases e : m.1 k with
      | none =>
        refine ⟨ha, fun kn vn => (hg kn vn).trans ?_⟩
        constructor
        · rintro ⟨k', v', hk, h1, h2, h3⟩; exact ⟨k', v', List.mem_append_left _ hk, h1, h2, h3⟩
        · rintro ⟨k', v', hk, h1, h2, h3⟩
          rcases List.mem_append.1 hk with hk | hk
          · exact ⟨k', v', hk, h1, h2, h3⟩
          · simp only [List.mem_singleton] at hk; subst hk; rw [e] at h1; cases h1
      | some v =>
        obtain ⟨out, hp, hm, hgo⟩ := putF_spec mugF a (TKey.enc k) (f v) ha
        dsimp only
        rw [hp, Option.getD_some]
        refine ⟨hm, fun kn vn => (hgo kn vn).trans ?_⟩
        constructor
        · rintro (⟨rfl, rfl⟩ | ⟨hne, hga⟩)
          · exact ⟨k, v, by simp, e, rfl, rfl⟩
          · obtain ⟨k', v', hk, h1, h2, h3⟩ := (hg kn vn).1 hga
            exact ⟨k', v', List.mem_append_left _ hk, h1, h2, h3⟩
        · rintro ⟨k', v', hk, h1, rfl, rfl⟩
          by_cases ek : k' = k
          · subst ek; rw [e, Option.some.injEq] at h1; subst h1; exact Or.inl ⟨rfl, rfl⟩
          · refine Or.inr ⟨fun h => ek (TKey.enc_inj _ _ h), (hg _ _).2 ⟨k', v', ?_, h1, rfl, rfl⟩⟩
            rcases List.mem_append.1 hk with hk | hk
            · exact hk
            · simp only [List.mem_singleton] at hk; exact absurd hk ek
    have := foldl_spec f m L (P ++ [k]) _ hstep.1 hstep.2
    simpa using this

theorem isMap_toNoun (f : ν → Noun) (m : FinMap κ ν) : IsMap mugF (m.toNoun f) :=
  (foldl_spec f m m.supp [] (A 0) IsMap.nil
    (fun kn vn => by simp [Get_atom, PairsOf])).1

/-- The pairs of the noun of `m` are those of `m`, encoded. -/
theorem get_toNoun (f : ν → Noun) (m : FinMap κ ν) (kn vn : Noun) :
    Get (m.toNoun f) kn vn ↔ ∃ k v, m.1 k = some v ∧ kn = TKey.enc k ∧ vn = f v := by
  have h := (foldl_spec f m m.supp [] (A 0) IsMap.nil
    (fun kn vn => by simp [Get_atom, PairsOf])).2 kn vn
  rw [List.nil_append] at h
  unfold toNoun
  rw [h]
  constructor
  · rintro ⟨k, v, -, h1, h2, h3⟩; exact ⟨k, v, h1, h2, h3⟩
  · rintro ⟨k, v, h1, h2, h3⟩
    exact ⟨k, v, m.mem_supp (by rw [h1]; simp), h1, h2, h3⟩

/-- The key of a noun, if it encodes one. -/
noncomputable def decode? (kn : Noun) : Option κ := by
  classical
  exact if h : ∃ k, TKey.enc k = kn then some (Classical.choose h) else none

theorem decode?_enc (k : κ) : decode? (TKey.enc k) = some k := by
  have h : ∃ k', TKey.enc k' = TKey.enc k := ⟨k, rfl⟩
  unfold decode?
  rw [dif_pos h]
  exact congrArg some (TKey.enc_inj _ _ (Classical.choose_spec h))

/-- The entry of `m` named by a pair of its noun. -/
noncomputable def entry (m : FinMap κ ν) : Noun → Option (κ × ν)
  | Noun.cell kn _ => (decode? kn).bind fun k => (m.1 k).map fun v => (k, v)
  | Noun.atom _ => none

theorem mem_filterMap_entry (m : FinMap κ ν) (l : List Noun)
    (hl : ∀ x, x ∈ l ↔ ∃ kn vn, x = C kn vn ∧ Get (m.toNoun fun _ => A 0) kn vn)
    (k : κ) (v : ν) : (k, v) ∈ l.filterMap m.entry ↔ m.1 k = some v := by
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨x, -, hx⟩
    cases x with
    | atom _ => cases hx
    | cell kn vn =>
      simp only [entry, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at hx
      obtain ⟨k', -, v', h1, rfl, rfl⟩ := hx
      exact h1
  · intro h
    refine ⟨C (TKey.enc k) (A 0), (hl _).2 ⟨_, _, rfl, (get_toNoun _ m _ _).2 ⟨k, v, h, rfl, rfl⟩⟩, ?_⟩
    simp [entry, decode?_enc, h]

/-- `~(tap by ...)`: the entries in the order of `+tap:by` on the noun. -/
noncomputable def tap (m : FinMap κ ν) : List (κ × ν) :=
  (tapList (m.toNoun fun _ => A 0)).filterMap m.entry

/-- The entries in the order in which `+rep` visits the noun. -/
noncomputable def rap (m : FinMap κ ν) : List (κ × ν) :=
  (preorder (m.toNoun fun _ => A 0)).filterMap m.entry

theorem mem_tap (m : FinMap κ ν) (k : κ) (v : ν) : (k, v) ∈ m.tap ↔ m.1 k = some v :=
  mem_filterMap_entry m _ (mem_tapList (isMap_toNoun _ m)) k v

theorem mem_rap (m : FinMap κ ν) (k : κ) (v : ν) : (k, v) ∈ m.rap ↔ m.1 k = some v :=
  mem_filterMap_entry m _ (mem_preorder (isMap_toNoun _ m)) k v

/-- A map with values `~` as a set: `[[k ~] l r]` to `[k l r]`. -/
def unMap : Noun → Noun
  | Noun.cell (Noun.cell k _) (Noun.cell l r) => C k (C (unMap l) (unMap r))
  | x => x

/-- The noun of a set. -/
noncomputable def setNoun (m : FinMap κ Unit) : Noun := unMap (m.toNoun fun _ => A 0)

end FinMap

noncomputable instance : Treap FinMap where
  empty := FinMap.empty
  get m k := FinMap.get m k
  put m k v := FinMap.put m k v
  del m k := FinMap.del m k
  tap m := FinMap.tap m
  rap m := FinMap.rap m
  toNoun f m := FinMap.toNoun f m
  setNoun m := FinMap.setNoun m
  get_empty _ := rfl
  get_put m k v k' := rfl
  get_del m k k' := rfl
  mem_tap m k v := FinMap.mem_tap m k v
  mem_rap m k v := FinMap.mem_rap m k v
  ext a b h := Subtype.ext (funext h)

/-! ## What the pill's arms do to the nouns -/

namespace FinMap

variable {κ ν : Type} [DecidableEq κ] [TKey κ]

theorem putF_toNoun (f : ν → Noun) (m : FinMap κ ν) (k : κ) (v : ν) :
    putF mugF (TKey.enc k) (f v) (m.toNoun f) = some ((m.put k v).toNoun f) := by
  obtain ⟨out, hp, hm, hg⟩ := putF_spec mugF _ (TKey.enc k) (f v) (isMap_toNoun f m)
  rw [hp, isMap_ext hm (isMap_toNoun f (m.put k v))]
  intro kn vn
  rw [hg, get_toNoun, get_toNoun]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨hne, k', v', h1, rfl, rfl⟩)
    · exact ⟨k, v, by simp [put], rfl, rfl⟩
    · refine ⟨k', v', ?_, rfl, rfl⟩
      have : k' ≠ k := fun e => hne (e ▸ rfl)
      simp [put, this, h1]
  · rintro ⟨k', v', h1, rfl, rfl⟩
    by_cases e : k' = k
    · subst e; simp only [put, if_true, Option.some.injEq] at h1; subst h1; exact Or.inl ⟨rfl, rfl⟩
    · simp only [put, e, if_false] at h1
      exact Or.inr ⟨fun h => e (TKey.enc_inj _ _ h), k', v', h1, rfl, rfl⟩

theorem delF_toNoun (f : ν → Noun) (m : FinMap κ ν) (k : κ) :
    delF mugF (TKey.enc k) (m.toNoun f) = some ((m.del k).toNoun f) := by
  obtain ⟨out, hp, hm, hg⟩ := delF_spec (TKey.enc k) (isMap_toNoun f m)
  rw [hp, isMap_ext hm (isMap_toNoun f (m.del k))]
  intro kn vn
  rw [hg, get_toNoun, get_toNoun]
  constructor
  · rintro ⟨hne, k', v', h1, rfl, rfl⟩
    have : k' ≠ k := fun e => hne (e ▸ rfl)
    exact ⟨k', v', by simp [del, this, h1], rfl, rfl⟩
  · rintro ⟨k', v', h1, rfl, rfl⟩
    by_cases e : k' = k
    · simp [del, e] at h1
    · simp only [del, e, if_false] at h1
      exact ⟨fun h => e (TKey.enc_inj _ _ h), k', v', h1, rfl, rfl⟩

theorem getF_toNoun (f : ν → Noun) (m : FinMap κ ν) (k : κ) :
    getF mugF (TKey.enc k) (m.toNoun f) = some (unitNoun f (m.get k)) := by
  cases e : m.1 k with
  | some v =>
    rw [getF_some (isMap_toNoun f m) ((get_toNoun f m _ _).2 ⟨k, v, e, rfl, rfl⟩)]
    simp [get, e, unitNoun]
  | none =>
    rw [getF_none (isMap_toNoun f m)]
    · simp [get, e, unitNoun]
    · intro vn hg
      obtain ⟨k', v', h1, h2, -⟩ := (get_toNoun f m _ _).1 hg
      rw [TKey.enc_inj _ _ h2.symm, e] at h1
      cases h1

end FinMap

end Compiler
end Formalization
