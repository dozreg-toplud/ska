module

public import lemmas.Hoon.MapModel
/-!
What the models of `Hoon/MapModel.lean` do to a map.

`+dor` is a total order on nouns, hence `+gor` and `+mor` are total orders
for any `mug`.  `putF` on a map that satisfies `IsMap` returns a map that
satisfies `IsMap`, and its pairs are the old ones with the key `k` rebound
to `v`.
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock

/-! ## `+dor` is a total order -/

theorem dorF_refl (a : Noun) : dorF a a = true := by
  induction a with
  | atom n => simp [dorF]
  | cell h t _ iht => simp [dorF, iht]

theorem dorF_antisymm : ∀ {a b : Noun}, dorF a b = true → dorF b a = true → a = b := by
  intro a
  induction a with
  | atom n =>
    intro b h1 h2
    cases b with
    | atom m =>
      simp only [dorF, decide_eq_true_eq] at h1 h2
      have : n = m := by omega
      rw [this]
    | cell h' t' => simp [dorF] at h2
  | cell h t ihh iht =>
    intro b h1 h2
    cases b with
    | atom m => simp [dorF] at h1
    | cell h' t' =>
      simp only [dorF] at h1 h2
      by_cases e : h = h'
      · subst e
        rw [if_pos rfl] at h1 h2
        rw [iht h1 h2]
      · rw [if_neg e] at h1
        rw [if_neg (Ne.symm e)] at h2
        exact absurd (ihh h1 h2) e

theorem dorF_trans : ∀ {a b c : Noun}, dorF a b = true → dorF b c = true → dorF a c = true := by
  intro a
  induction a with
  | atom n =>
    intro b c h1 h2
    cases b with
    | atom m =>
      cases c with
      | atom o =>
        simp only [dorF, decide_eq_true_eq] at h1 h2 ⊢
        omega
      | cell h'' t'' => simp [dorF]
    | cell h' t' =>
      cases c with
      | atom o => simp [dorF] at h2
      | cell h'' t'' => simp [dorF]
  | cell h t ihh iht =>
    intro b c h1 h2
    cases b with
    | atom m => simp [dorF] at h1
    | cell h' t' =>
      cases c with
      | atom o => simp [dorF] at h2
      | cell h'' t'' =>
        simp only [dorF] at h1 h2 ⊢
        by_cases e1 : h = h'
        · subst e1
          rw [if_pos rfl] at h1
          by_cases e2 : h = h''
          · subst e2
            rw [if_pos rfl] at h2 ⊢
            exact iht h1 h2
          · rw [if_neg e2] at h2 ⊢
            exact h2
        · rw [if_neg e1] at h1
          by_cases e2 : h' = h''
          · subst e2
            rw [if_pos rfl] at h2
            rw [if_neg e1]
            exact h1
          · rw [if_neg e2] at h2
            by_cases e3 : h = h''
            · subst e3
              exact absurd (dorF_antisymm h1 h2) e1
            · rw [if_neg e3]
              exact ihh h1 h2

theorem dorF_total : ∀ (a b : Noun), dorF a b = true ∨ dorF b a = true := by
  intro a
  induction a with
  | atom n =>
    intro b
    cases b with
    | atom m =>
      simp only [dorF, decide_eq_true_eq]
      omega
    | cell h' t' => simp [dorF]
  | cell h t ihh iht =>
    intro b
    cases b with
    | atom m => simp [dorF]
    | cell h' t' =>
      simp only [dorF]
      by_cases e : h = h'
      · subst e
        rw [if_pos rfl, if_pos rfl]
        exact iht t'
      · rw [if_neg e, if_neg (Ne.symm e)]
        exact ihh h'

/-! ## An order by a numeric key, with `+dor` on ties -/

/-- The common shape of `+gor` and `+mor`: by the key `f`, and by `+dor` when
the keys collide. -/
def korF (f : Noun → Nat) (a b : Noun) : Bool :=
  if f a = f b then dorF a b else decide (f a < f b)

theorem gorF_eq_korF (mug : Noun → Nat) : gorF mug = korF mug := rfl

theorem morF_eq_korF (mug : Noun → Nat) :
    morF mug = korF (fun a => mug (A (mug a))) := rfl

theorem korF_refl (f : Noun → Nat) (a : Noun) : korF f a a = true := by
  unfold korF
  rw [if_pos rfl]
  exact dorF_refl a

theorem korF_antisymm (f : Noun → Nat) {a b : Noun}
    (h1 : korF f a b = true) (h2 : korF f b a = true) : a = b := by
  unfold korF at h1 h2
  by_cases e : f a = f b
  · rw [if_pos e] at h1
    rw [if_pos e.symm] at h2
    exact dorF_antisymm h1 h2
  · rw [if_neg e] at h1
    rw [if_neg (Ne.symm e)] at h2
    simp only [decide_eq_true_eq] at h1 h2
    omega

theorem korF_trans (f : Noun → Nat) {a b c : Noun}
    (h1 : korF f a b = true) (h2 : korF f b c = true) : korF f a c = true := by
  unfold korF at h1 h2 ⊢
  by_cases e1 : f a = f b
  · rw [if_pos e1] at h1
    by_cases e2 : f b = f c
    · rw [if_pos e2] at h2
      rw [if_pos (e1.trans e2)]
      exact dorF_trans h1 h2
    · rw [if_neg e2] at h2
      simp only [decide_eq_true_eq] at h2
      have e3 : ¬ f a = f c := by omega
      rw [if_neg e3]
      simp only [decide_eq_true_eq]
      omega
  · rw [if_neg e1] at h1
    simp only [decide_eq_true_eq] at h1
    by_cases e2 : f b = f c
    · have e3 : ¬ f a = f c := by omega
      rw [if_neg e3]
      simp only [decide_eq_true_eq]
      omega
    · rw [if_neg e2] at h2
      simp only [decide_eq_true_eq] at h2
      have e3 : ¬ f a = f c := by omega
      rw [if_neg e3]
      simp only [decide_eq_true_eq]
      omega

theorem korF_total (f : Noun → Nat) (a b : Noun) :
    korF f a b = true ∨ korF f b a = true := by
  unfold korF
  by_cases e : f a = f b
  · rw [if_pos e, if_pos e.symm]
    exact dorF_total a b
  · rw [if_neg e, if_neg (Ne.symm e)]
    simp only [decide_eq_true_eq]
    omega

/-! ## `+gor` and `+mor` are total orders -/

theorem gorF_refl (mug : Noun → Nat) (a : Noun) : gorF mug a a = true :=
  korF_refl mug a

theorem gorF_antisymm (mug : Noun → Nat) {a b : Noun}
    (h1 : gorF mug a b = true) (h2 : gorF mug b a = true) : a = b :=
  korF_antisymm mug h1 h2

theorem gorF_trans (mug : Noun → Nat) {a b c : Noun}
    (h1 : gorF mug a b = true) (h2 : gorF mug b c = true) : gorF mug a c = true :=
  korF_trans mug h1 h2

theorem gorF_total (mug : Noun → Nat) (a b : Noun) :
    gorF mug a b = true ∨ gorF mug b a = true :=
  korF_total mug a b

theorem gorF_of_not (mug : Noun → Nat) {a b : Noun}
    (h : ¬ gorF mug a b = true) : gorF mug b a = true :=
  (gorF_total mug a b).resolve_left h

theorem morF_refl (mug : Noun → Nat) (a : Noun) : morF mug a a = true :=
  korF_refl (fun a => mug (A (mug a))) a

theorem morF_antisymm (mug : Noun → Nat) {a b : Noun}
    (h1 : morF mug a b = true) (h2 : morF mug b a = true) : a = b :=
  korF_antisymm (fun a => mug (A (mug a))) h1 h2

theorem morF_trans (mug : Noun → Nat) {a b c : Noun}
    (h1 : morF mug a b = true) (h2 : morF mug b c = true) : morF mug a c = true :=
  korF_trans (fun a => mug (A (mug a))) h1 h2

theorem morF_total (mug : Noun → Nat) (a b : Noun) :
    morF mug a b = true ∨ morF mug b a = true :=
  korF_total (fun a => mug (A (mug a))) a b

theorem morF_of_not (mug : Noun → Nat) {a b : Noun}
    (h : ¬ morF mug a b = true) : morF mug b a = true :=
  (morF_total mug a b).resolve_left h

/-! ## Inversions -/

theorem Get_atom {n : Nat} {k v : Noun} : ¬ Get (Noun.atom n) k v := by
  intro h
  cases h

theorem Get_node {p q l r k v : Noun} :
    Get (Noun.cell (Noun.cell p q) (Noun.cell l r)) k v ↔
      (k = p ∧ v = q) ∨ Get l k v ∨ Get r k v := by
  constructor
  · intro h
    cases h with
    | here => exact Or.inl ⟨rfl, rfl⟩
    | left h => exact Or.inr (Or.inl h)
    | right h => exact Or.inr (Or.inr h)
  · intro h
    rcases h with ⟨rfl, rfl⟩ | h | h
    · exact Get.here
    · exact Get.left h
    · exact Get.right h

theorem IsMap_node {mug : Noun → Nat} {p q l r : Noun}
    (h : IsMap mug (Noun.cell (Noun.cell p q) (Noun.cell l r))) :
    IsMap mug l ∧ IsMap mug r ∧
      (∀ k v, Get l k v → k ≠ p ∧ gorF mug k p = true ∧ morF mug p k = true) ∧
      (∀ k v, Get r k v → k ≠ p ∧ gorF mug p k = true ∧ morF mug p k = true) := by
  cases h with
  | node hl hr hL hR => exact ⟨hl, hr, hL, hR⟩

/-- A key has one value in a map. -/
theorem Get.unique {mug : Noun → Nat} {a k v v' : Noun} (h : IsMap mug a)
    (h1 : Get a k v) (h2 : Get a k v') : v = v' := by
  induction h with
  | nil => exact absurd h1 Get_atom
  | @node p q l r hl hr hL hR ihl ihr =>
    rw [Get_node] at h1 h2
    rcases h1 with ⟨e1, e1'⟩ | h1 | h1
    · rcases h2 with ⟨_, e2'⟩ | h2 | h2
      · rw [e1', e2']
      · exact absurd e1 (hL _ _ h2).1
      · exact absurd e1 (hR _ _ h2).1
    · rcases h2 with ⟨e2, _⟩ | h2 | h2
      · exact absurd e2 (hL _ _ h1).1
      · exact ihl h1 h2
      · exact absurd (gorF_antisymm mug (hL _ _ h1).2.1 (hR _ _ h2).2.1) (hL _ _ h1).1
    · rcases h2 with ⟨e2, _⟩ | h2 | h2
      · exact absurd e2 (hR _ _ h1).1
      · exact absurd (gorF_antisymm mug (hL _ _ h2).2.1 (hR _ _ h1).2.1) (hL _ _ h2).1
      · exact ihr h1 h2

/-- A key that the root of a map dominates in `+mor` dominates every key of
the map. -/
theorem morF_of_root {mug : Noun → Nat} {x dp dq dl dr : Noun}
    (h : IsMap mug (Noun.cell (Noun.cell dp dq) (Noun.cell dl dr)))
    (m : morF mug x dp = true) :
    ∀ k v, Get (Noun.cell (Noun.cell dp dq) (Noun.cell dl dr)) k v →
      morF mug x k = true := by
  obtain ⟨_, _, hDL, hDR⟩ := IsMap_node h
  intro k v hg
  rw [Get_node] at hg
  rcases hg with ⟨e, _⟩ | hg | hg
  · rw [e]; exact m
  · exact morF_trans mug m (hDL _ _ hg).2.2
  · exact morF_trans mug m (hDR _ _ hg).2.2

/-! ## `putF` on a map -/

/-- `putF` on a map returns a node that is a map and whose pairs are the old
ones with `k` rebound to `v`. -/
theorem putF_node (mug : Noun → Nat) (k v : Noun) {a : Noun} (h : IsMap mug a) :
    ∃ dp dq dl dr,
      putF mug k v a = some (Noun.cell (Noun.cell dp dq) (Noun.cell dl dr)) ∧
      IsMap mug (Noun.cell (Noun.cell dp dq) (Noun.cell dl dr)) ∧
      ∀ k' v', Get (Noun.cell (Noun.cell dp dq) (Noun.cell dl dr)) k' v' ↔
        (k' = k ∧ v' = v) ∨ (k' ≠ k ∧ Get a k' v') := by
  induction h with
  | nil =>
    refine ⟨k, v, A 0, A 0, rfl, ?_, ?_⟩
    · exact IsMap.node IsMap.nil IsMap.nil
        (fun _ _ hg => absurd hg Get_atom) (fun _ _ hg => absurd hg Get_atom)
    · intro k' v'
      rw [Get_node]
      constructor
      · rintro (hg | hg | hg)
        · exact Or.inl hg
        · exact absurd hg Get_atom
        · exact absurd hg Get_atom
      · rintro (hg | ⟨_, hg⟩)
        · exact Or.inl hg
        · exact absurd hg Get_atom
  | @node p q l r hl hr hL hR ihl ihr =>
    by_cases e : k = p
    · -- the key is at the root
      subst e
      by_cases e2 : v = q
      · subst e2
        refine ⟨k, v, l, r, by simp [putF], IsMap.node hl hr hL hR, ?_⟩
        intro k' v'
        simp only [Get_node]
        constructor
        · rintro (hg | hg | hg)
          · exact Or.inl hg
          · exact Or.inr ⟨(hL _ _ hg).1, Or.inr (Or.inl hg)⟩
          · exact Or.inr ⟨(hR _ _ hg).1, Or.inr (Or.inr hg)⟩
        · rintro (hg | ⟨_, hg⟩)
          · exact Or.inl hg
          · exact hg
      · refine ⟨k, v, l, r, by simp [putF, e2], IsMap.node hl hr hL hR, ?_⟩
        intro k' v'
        simp only [Get_node]
        constructor
        · rintro (hg | hg | hg)
          · exact Or.inl hg
          · exact Or.inr ⟨(hL _ _ hg).1, Or.inr (Or.inl hg)⟩
          · exact Or.inr ⟨(hR _ _ hg).1, Or.inr (Or.inr hg)⟩
        · rintro (hg | ⟨ne, ⟨e3, _⟩ | hg | hg⟩)
          · exact Or.inl hg
          · exact absurd e3 ne
          · exact Or.inr (Or.inl hg)
          · exact Or.inr (Or.inr hg)
    · by_cases g : gorF mug k p = true
      · -- into the left subtree
        obtain ⟨dp, dq, dl, dr, hput, hmap, hget⟩ := ihl
        have hRk : ∀ k' v', Get r k' v' → k' ≠ k := by
          intro k' v' hg ek
          subst ek
          exact e (gorF_antisymm mug g (hR _ _ hg).2.1)
        by_cases m : morF mug p dp = true
        · refine ⟨p, q, Noun.cell (Noun.cell dp dq) (Noun.cell dl dr), r,
            by simp [putF, e, g, hput, m], ?_, ?_⟩
          · refine IsMap.node hmap hr ?_ hR
            intro k' v' hg
            refine ⟨?_, ?_, morF_of_root hmap m _ _ hg⟩
            · rcases (hget k' v').1 hg with ⟨ek, _⟩ | ⟨_, hg'⟩
              · rw [ek]; exact e
              · exact (hL _ _ hg').1
            · rcases (hget k' v').1 hg with ⟨ek, _⟩ | ⟨_, hg'⟩
              · rw [ek]; exact g
              · exact (hL _ _ hg').2.1
          · intro k' v'
            rw [Get_node (l := Noun.cell (Noun.cell dp dq) (Noun.cell dl dr)), hget,
              Get_node]
            constructor
            · rintro (⟨e1, e2⟩ | (hg | ⟨ne, hg⟩) | hg)
              · exact Or.inr ⟨fun ek => e (ek.symm.trans e1), Or.inl ⟨e1, e2⟩⟩
              · exact Or.inl hg
              · exact Or.inr ⟨ne, Or.inr (Or.inl hg)⟩
              · exact Or.inr ⟨hRk _ _ hg, Or.inr (Or.inr hg)⟩
            · rintro (hg | ⟨ne, hg | hg | hg⟩)
              · exact Or.inr (Or.inl (Or.inl hg))
              · exact Or.inl hg
              · exact Or.inr (Or.inl (Or.inr ⟨ne, hg⟩))
              · exact Or.inr (Or.inr hg)
        · -- the new key comes up: rotate right
          have hk : dp = k ∧ dq = v := by
            rcases (hget dp dq).1 Get.here with hk | ⟨_, hg⟩
            · exact hk
            · exact absurd (hL _ _ hg).2.2 m
          obtain ⟨rfl, rfl⟩ := hk
          obtain ⟨hdl, hdr, hDL, hDR⟩ := IsMap_node hmap
          have mk : morF mug dp p = true := morF_of_not mug m
          have hdrl : ∀ k' v', Get dr k' v' → Get l k' v' := by
            intro k' v' hg
            rcases (hget k' v').1 (Get.right hg) with ⟨ek, _⟩ | ⟨_, hg'⟩
            · exact absurd ek (hDR _ _ hg).1
            · exact hg'
          refine ⟨dp, dq, dl, Noun.cell (Noun.cell p q) (Noun.cell dr r),
            by simp [putF, e, g, hput, m], ?_, ?_⟩
          · refine IsMap.node hdl (IsMap.node hdr hr ?_ hR) hDL ?_
            · intro k' v' hg
              exact hL _ _ (hdrl _ _ hg)
            · intro k' v' hg
              rw [Get_node] at hg
              rcases hg with ⟨e1, _⟩ | hg | hg
              · rw [e1]; exact ⟨Ne.symm e, g, mk⟩
              · exact hDR _ _ hg
              · exact ⟨hRk _ _ hg, gorF_trans mug g (hR _ _ hg).2.1,
                  morF_trans mug mk (hR _ _ hg).2.2⟩
          · intro k' v'
            have hget' := hget k' v'
            rw [Get_node] at hget'
            rw [Get_node (r := Noun.cell (Noun.cell p q) (Noun.cell dr r)), Get_node,
              Get_node]
            constructor
            · rintro (hg | hg | ⟨e1, e2⟩ | hg | hg)
              · exact Or.inl hg
              · rcases hget'.1 (Or.inr (Or.inl hg)) with hk | ⟨ne, hg'⟩
                · exact Or.inl hk
                · exact Or.inr ⟨ne, Or.inr (Or.inl hg')⟩
              · exact Or.inr ⟨fun ek => e (ek.symm.trans e1), Or.inl ⟨e1, e2⟩⟩
              · rcases hget'.1 (Or.inr (Or.inr hg)) with hk | ⟨ne, hg'⟩
                · exact Or.inl hk
                · exact Or.inr ⟨ne, Or.inr (Or.inl hg')⟩
              · exact Or.inr ⟨hRk _ _ hg, Or.inr (Or.inr hg)⟩
            · rintro (hg | ⟨ne, hg | hg | hg⟩)
              · exact Or.inl hg
              · exact Or.inr (Or.inr (Or.inl hg))
              · rcases hget'.2 (Or.inr ⟨ne, hg⟩) with ⟨ek, _⟩ | hg' | hg'
                · exact absurd ek ne
                · exact Or.inr (Or.inl hg')
                · exact Or.inr (Or.inr (Or.inr (Or.inl hg')))
              · exact Or.inr (Or.inr (Or.inr (Or.inr hg)))
      · -- into the right subtree
        obtain ⟨dp, dq, dl, dr, hput, hmap, hget⟩ := ihr
        have g' : gorF mug p k = true := gorF_of_not mug g
        have hLk : ∀ k' v', Get l k' v' → k' ≠ k := by
          intro k' v' hg ek
          subst ek
          exact g (hL _ _ hg).2.1
        by_cases m : morF mug p dp = true
        · refine ⟨p, q, l, Noun.cell (Noun.cell dp dq) (Noun.cell dl dr),
            by simp [putF, e, g, hput, m], ?_, ?_⟩
          · refine IsMap.node hl hmap hL ?_
            intro k' v' hg
            refine ⟨?_, ?_, morF_of_root hmap m _ _ hg⟩
            · rcases (hget k' v').1 hg with ⟨ek, _⟩ | ⟨_, hg'⟩
              · rw [ek]; exact e
              · exact (hR _ _ hg').1
            · rcases (hget k' v').1 hg with ⟨ek, _⟩ | ⟨_, hg'⟩
              · rw [ek]; exact g'
              · exact (hR _ _ hg').2.1
          · intro k' v'
            rw [Get_node (r := Noun.cell (Noun.cell dp dq) (Noun.cell dl dr)), hget,
              Get_node]
            constructor
            · rintro (⟨e1, e2⟩ | hg | (hg | ⟨ne, hg⟩))
              · exact Or.inr ⟨fun ek => e (ek.symm.trans e1), Or.inl ⟨e1, e2⟩⟩
              · exact Or.inr ⟨hLk _ _ hg, Or.inr (Or.inl hg)⟩
              · exact Or.inl hg
              · exact Or.inr ⟨ne, Or.inr (Or.inr hg)⟩
            · rintro (hg | ⟨ne, hg | hg | hg⟩)
              · exact Or.inr (Or.inr (Or.inl hg))
              · exact Or.inl hg
              · exact Or.inr (Or.inl hg)
              · exact Or.inr (Or.inr (Or.inr ⟨ne, hg⟩))
        · -- the new key comes up: rotate left
          have hk : dp = k ∧ dq = v := by
            rcases (hget dp dq).1 Get.here with hk | ⟨_, hg⟩
            · exact hk
            · exact absurd (hR _ _ hg).2.2 m
          obtain ⟨rfl, rfl⟩ := hk
          obtain ⟨hdl, hdr, hDL, hDR⟩ := IsMap_node hmap
          have mk : morF mug dp p = true := morF_of_not mug m
          have hdlr : ∀ k' v', Get dl k' v' → Get r k' v' := by
            intro k' v' hg
            rcases (hget k' v').1 (Get.left hg) with ⟨ek, _⟩ | ⟨_, hg'⟩
            · exact absurd ek (hDL _ _ hg).1
            · exact hg'
          refine ⟨dp, dq, Noun.cell (Noun.cell p q) (Noun.cell l dl), dr,
            by simp [putF, e, g, hput, m], ?_, ?_⟩
          · refine IsMap.node (IsMap.node hl hdl hL ?_) hdr ?_ hDR
            · intro k' v' hg
              exact hR _ _ (hdlr _ _ hg)
            · intro k' v' hg
              rw [Get_node] at hg
              rcases hg with ⟨e1, _⟩ | hg | hg
              · rw [e1]; exact ⟨Ne.symm e, g', mk⟩
              · exact ⟨hLk _ _ hg, gorF_trans mug (hL _ _ hg).2.1 g',
                  morF_trans mug mk (hL _ _ hg).2.2⟩
              · exact hDL _ _ hg
          · intro k' v'
            have hget' := hget k' v'
            rw [Get_node] at hget'
            rw [Get_node (l := Noun.cell (Noun.cell p q) (Noun.cell l dl)), Get_node,
              Get_node]
            constructor
            · rintro (hg | (⟨e1, e2⟩ | hg | hg) | hg)
              · exact Or.inl hg
              · exact Or.inr ⟨fun ek => e (ek.symm.trans e1), Or.inl ⟨e1, e2⟩⟩
              · exact Or.inr ⟨hLk _ _ hg, Or.inr (Or.inl hg)⟩
              · rcases hget'.1 (Or.inr (Or.inl hg)) with hk | ⟨ne, hg'⟩
                · exact Or.inl hk
                · exact Or.inr ⟨ne, Or.inr (Or.inr hg')⟩
              · rcases hget'.1 (Or.inr (Or.inr hg)) with hk | ⟨ne, hg'⟩
                · exact Or.inl hk
                · exact Or.inr ⟨ne, Or.inr (Or.inr hg')⟩
            · rintro (hg | ⟨ne, hg | hg | hg⟩)
              · exact Or.inl hg
              · exact Or.inr (Or.inl (Or.inl hg))
              · exact Or.inr (Or.inl (Or.inr (Or.inl hg)))
              · rcases hget'.2 (Or.inr ⟨ne, hg⟩) with ⟨ek, _⟩ | hg' | hg'
                · exact absurd ek ne
                · exact Or.inr (Or.inl (Or.inr (Or.inr hg')))
                · exact Or.inr (Or.inr hg')

/-- `putF` on a map succeeds, returns a map, and the pairs of the result are
the old pairs with the key `k` rebound to `v`. -/
theorem putF_spec (mug : Noun → Nat) (a k v : Noun) (h : IsMap mug a) :
    ∃ out, putF mug k v a = some out ∧ IsMap mug out ∧
      ∀ k' v', Get out k' v' ↔ (k' = k ∧ v' = v) ∨ (k' ≠ k ∧ Get a k' v') := by
  obtain ⟨dp, dq, dl, dr, hput, hmap, hget⟩ := putF_node mug k v h
  exact ⟨_, hput, hmap, hget⟩

end Hoon
end Formalization

end
