import lemmas.Ska.OptAliasPick
import lemmas.Ska.OptAliasPerm
import lemmas.Compiler.OptLinkAlJReg

/-!
# The choice of `+alias` is the root of the set, and `InfoEq` is what `InfoRel` reads

Two facts on the noun side of the pill link of `+alias`, about the model.

* **`sawRel_root`**: the Hoon picks `n.res` (`%imm`) and `n.intersect`
  (`%con`), the root of a set noun.  A set noun `S` related to a non-empty list
  `l` by `SawRel` (an `IsSet mugF` treap with the members of `l`) is the noun of
  the `+silt` of `l` (`isSet_ext`: a treap is a function of its members), and
  its root is `pickR FinMap l` (`Ska/OptAliasPick.lean`: the first key of
  `rap`, the pre-order of `+rep`, of the `+silt` of the list), so
  `S = [pickR FinMap l L R]`.  So `P.alias = aliasM (pickR FinMap)` is the
  choice for which the link holds; it meets `hpick` (`pickR_mem`) and depends
  only on the members of the list (`pickR_ext`), which is what keeps it in
  step with the Hoon when two orders of `pre` give lists in other orders
  (`OptAliasPerm.lean`).
* **`infoRel_of_infoEq`**: `InfoRel N x` and `InfoEq x y` give `InfoRel N y`,
  so the results of the phases under a permutation of `pre`
  (`aliasStart_perm` etc., related by `InfoEq` at each register) are related
  to the same Hoon nouns.
-/

namespace Formalization
namespace Compiler

open Nock Hoon SkaModel SkaModel.Opt

attribute [local instance] SkaModel.Ana.tkeyNat

/-- **The choice depends only on the members of the list**, for any treap. -/
theorem pickR_ext {M : Type → Type → Type} [Ana.Treap M] {l l' : List Nat} (h : ∀ x, x ∈ l ↔ x ∈ l') :
    Ana.pickR M l = Ana.pickR M l' := by
  have e : (Ana.Treap.silt l : M Nat Unit) = Ana.Treap.silt l' :=
    Ana.Treap.ext _ _ fun k => by
      cases e1 : Ana.Treap.get (Ana.Treap.silt l : M Nat Unit) k with
      | none =>
        cases e2 : Ana.Treap.get (Ana.Treap.silt l' : M Nat Unit) k with
        | none => rfl
        | some u =>
          cases u
          have := (Ana.get_silt l' k).mp e2
          rw [← h] at this
          rw [(Ana.get_silt l k).mpr this] at e1; cases e1
      | some u =>
        cases u
        have := (h k).mp ((Ana.get_silt l k).mp e1)
        exact ((Ana.get_silt l' k).mpr this).symm
  unfold Ana.pickR
  rw [e]

/-- The members of the noun of the `+silt` of a list. -/
theorem has_silt_setNoun (l : List Nat) (kn : Noun) :
    Has (FinMap.setNoun (Ana.Treap.silt l : FinMap Nat Unit)) kn ↔ ∃ n ∈ l, kn = A n := by
  rw [FinMap.has_setNoun]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, (Ana.get_silt (M := FinMap) l k).mp hk, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, (Ana.get_silt (M := FinMap) l n).mpr hn, rfl⟩

/-- **The root of a set noun related to a non-empty list is `pickR FinMap`
of the list** (`n.res`, `n.intersect` of the Hoon). -/
theorem sawRel_root {S : Noun} {l : List Nat} (h : SawRel S l) (hl : l ≠ []) :
    ∃ L R, S = C (A (Ana.pickR FinMap l)) (C L R) := by
  let m : FinMap Nat Unit := Ana.Treap.silt l
  have eS : S = FinMap.setNoun m :=
    isSet_ext h.1 (FinMap.isSet_setNoun m) fun kn => by rw [h.2, has_silt_setNoun]
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil l hl
  have hget : Get (m.toNoun fun _ => A 0) (A x) (A 0) :=
    (FinMap.get_toNoun _ m _ _).mpr ⟨x, (), (Ana.get_silt (M := FinMap) l x).mpr hx, rfl, rfl⟩
  have hm := FinMap.isMap_toNoun (fun _ => A 0) m
  have hrap : Ana.pickR FinMap l = match FinMap.rap m with | (k, _) :: _ => k | [] => 0 := rfl
  have hrap2 : FinMap.rap m = (preorder (m.toNoun fun _ => A 0)).filterMap m.entry := rfl
  have hset : FinMap.setNoun m = FinMap.unMap (m.toNoun fun _ => A 0) := rfl
  generalize hN : (m.toNoun fun _ => A 0) = N at hget hm hrap2 hset
  cases hm with
  | nil => cases hget
  | @node p q L R _ _ _ _ =>
    have hroot : Get (m.toNoun fun _ => A 0) p q := hN ▸ Get.here
    obtain ⟨k, v, hk, rfl, rfl⟩ := (FinMap.get_toNoun _ m p q).mp hroot
    have he : m.entry (C (Ana.TKey.enc k) (A 0)) = some (k, ()) := by
      simp [FinMap.entry, FinMap.decode?_enc, hk]
    have hpk : Ana.pickR FinMap l = k := by
      rw [hrap, hrap2]
      simp only [preorder, List.filterMap_cons, he]
    refine ⟨FinMap.unMap L, FinMap.unMap R, ?_⟩
    rw [eS, hset, hpk]
    rfl

/-- **`InfoEq` is what `InfoRel` reads**: a noun related to `x` is related to
every `y` with `InfoEq x y`. -/
theorem infoRel_of_infoEq {N : Noun} {x y : InfoReg} (h : InfoRel N x) (e : InfoEq x y) : InfoRel N y := by
  obtain ⟨lb, hs, ts, rfl, h1, h2, h3⟩ := h
  refine ⟨lb, hs, ts, ?_, ⟨h1.1, fun k => ?_⟩, ⟨h2.1, fun k => ?_⟩, ?_⟩
  · unfold infoN
    rw [e.cell, e.hasHed, e.hasTel, e.decOf, e.hasImm]
  · rw [h1.2]
    constructor
    · rintro ⟨n, hn, rfl⟩; exact ⟨n, (e.hed n).mp hn, rfl⟩
    · rintro ⟨n, hn, rfl⟩; exact ⟨n, (e.hed n).mpr hn, rfl⟩
  · rw [h2.2]
    constructor
    · rintro ⟨n, hn, rfl⟩; exact ⟨n, (e.tel n).mp hn, rfl⟩
    · rintro ⟨n, hn, rfl⟩; exact ⟨n, (e.tel n).mpr hn, rfl⟩
  · have hl := e.loob
    unfold InfoReg.loobC at hl
    rw [← hl, ← e.loobImm]; exact h3

/-- **The list of `~(tap in ...)` of a set has no duplicates**, so the Hoon's
`pre` and the model's `g.rev o` (`RevNodup`) with the same members are
permutations (`perm_of_nodup`). -/
theorem tapList_set_nodup {mug : Noun → Nat} {a : Noun} (h : IsSet mug a) : (tapList a).Nodup := by
  have hp := List.pairwise_map.mp (tapList_set_pairwise h)
  exact hp.imp fun {x y} hxy e => by subst e; exact TapBefore.asymm hxy hxy

end Compiler
end Formalization
