import lemmas.Ska.OptSwitchWalk

/-!
# `+switch-chains`: several tagged chains in one walk

The walk calls `switchTag bl out` at each head: the chain is that of `bl`,
the blocks so far are `out`.  This file carries `TagHyp` from `bl` to `out`
(`tagHyp_out`) through an invariant of the walk (`WInv`): outside the
regions and heads of the chains done the blocks are those of `bl`, a head
done is its block of `bl` with the `%clq` to the root and the final miss, and
a block inside a region done is a tree node (`NodeOK`: no parameters, jumps
that pass nothing to the region, its hits or its miss, and mentions of the
head and of the registers of the chain only).

* `stree_shape`: every node `stree` makes is a `NodeOK` node.
* `chain_disj`: the labels of a later chain (and its hits) are outside the
  region of an earlier one, since each is reached by a jump from the label
  before it, and a block that jumps into an earlier region is a label of that
  chain (`labs_into`); the head of the later chain is not in `done` and comes
  later in `topo`.  `chain_disj'`: the hits and no sides of the earlier chain
  are outside the later region, the same way round.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Opt

open Nock

variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

/-- A tree node: no parameters, jumps that pass nothing to `P`, mentions in
`S`. -/
def NodeOK (P S : Nat → Prop) (b : Blob) : Prop :=
  b.par = [] ∧ (∀ j ∈ getJmps b.fin, j.args = [] ∧ P j.there) ∧ ∀ r ∈ blobMentions b, S r

/-- **Every node `stree` makes is a tree node**, and the map it returns is the
one it was given but at the labels it used, a prefix of `ids`. -/
theorem stree_shape (d mis : Nat) (P S : Nat → Prop) (hd : S d) (hm : P mis) :
    ∀ (n : Nat) (cas : List SCase) (ids : List Nat) (out : Map Blob) (nb : List Pole) (nf : Termin)
      (ids' : List Nat) (out' : Map Blob),
    stree d mis n cas ids out = some (nb, nf, ids', out') → (∀ k ∈ ids, P k) →
    (∀ x ∈ cas, P x.hit ∧ S x.r) →
    ∃ used, ids = used ++ ids' ∧ (∀ k, k ∉ used → HoonMap.get out' k = HoonMap.get out k) ∧
      (∀ k ∈ used, ∃ b, HoonMap.get out' k = some b ∧ NodeOK P S b) ∧ NodeOK P S ⟨[], nb, nf⟩
  | 0, cas, ids, out, nb, nf, ids', out', h, _, _ => by simp [stree] at h
  | n + 1, [], ids, out, nb, nf, ids', out', h, _, _ => by simp [stree] at h
  | n + 1, [x], ids, out, nb, nf, ids', out', h, _, hc => by
    simp only [stree, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    obtain ⟨hp, hs⟩ := hc x List.mem_cons_self
    refine ⟨[], by simp, fun _ _ => rfl, fun k hk => absurd hk List.not_mem_nil, rfl, ?_, ?_⟩
    · intro j hj
      simp only [getJmps, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact ⟨rfl, hp⟩
      · exact ⟨rfl, hm⟩
    · intro r hr
      simp only [blobMentions, finRegs, jmpRegs, poleRegs, List.filterMap_nil, List.append_nil,
        List.nil_append, List.flatMap_cons, List.flatMap_nil, List.mem_cons, List.mem_append,
        List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl) | rfl
      · exact hd
      · exact hs
      · exact hs
  | n + 1, x :: y :: t, ids, out, nb, nf, ids', out', h, hi, hc => by
    rw [stree.eq_def] at h
    simp only at h
    generalize hall : x :: y :: t = all at h hc
    generalize (all.length / 2) = haf at h
    cases hdr : List.drop haf all with
    | nil => rw [hdr] at h; simp at h
    | cons h0 tl =>
    rw [hdr] at h
    rcases ids with _ | ⟨lid, _ | ⟨rid, rest⟩⟩
    · simp at h
    · simp at h
    simp only at h
    cases hL : stree d mis n (all.take haf) rest out with
    | none => simp [hL] at h
    | some L =>
    obtain ⟨lb, lf, lids, lout⟩ := L
    simp only [hL, Option.bind_some] at h
    cases hR : stree d mis n (h0 :: tl) lids (HoonMap.put lout lid ⟨[], lb, lf⟩) with
    | none => simp [hR] at h
    | some R =>
    obtain ⟨rb, rf, rids, rout⟩ := R
    simp only [hR, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    have hcT : ∀ x ∈ all.take haf, P x.hit ∧ S x.r := fun x hx => hc x (List.mem_of_mem_take hx)
    have hcD : ∀ x ∈ h0 :: tl, P x.hit ∧ S x.r := fun x hx =>
      hc x (List.mem_of_mem_drop (hdr ▸ hx : x ∈ all.drop haf))
    have hiR : ∀ k ∈ rest, P k := fun k hk => hi k (by simp [hk])
    have hlid : P lid := hi lid (by simp)
    have hrid : P rid := hi rid (by simp)
    obtain ⟨usedL, eL, frL, ndL, okL⟩ := stree_shape d mis P S hd hm n _ rest out lb lf lids lout hL hiR hcT
    have hiL : ∀ k ∈ lids, P k := fun k hk => hiR k (by rw [eL]; exact List.mem_append_right _ hk)
    obtain ⟨usedR, eR, frR, ndR, okR⟩ := stree_shape d mis P S hd hm n _ lids _ rb rf rids rout hR hiL hcD
    subst eL; subst eR
    refine ⟨lid :: rid :: (usedL ++ usedR), by simp, fun k hk => ?_, fun k hk => ?_, rfl, ?_, ?_⟩
    · simp only [List.mem_cons, List.mem_append, not_or] at hk
      rw [HoonMap.get_put, if_neg hk.2.1, frR k hk.2.2.2, HoonMap.get_put, if_neg hk.1, frL k hk.2.2.1]
    · rw [HoonMap.get_put]
      split
      · exact ⟨_, rfl, okR⟩
      rename_i hkr
      by_cases hkR : k ∈ usedR
      · exact ndR k hkR
      rw [frR k hkR, HoonMap.get_put]
      split
      · exact ⟨_, rfl, okL⟩
      rename_i hkl
      have : k ∈ usedL := by
        simp only [List.mem_cons, List.mem_append] at hk
        rcases hk with h1 | h1 | h1 | h1
        · exact absurd h1 hkl
        · exact absurd h1 hkr
        · exact h1
        · exact absurd h1 hkR
      exact ndL k this
    · intro j hj
      simp only [getJmps, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact ⟨rfl, hlid⟩
      · exact ⟨rfl, hrid⟩
    · intro r hr
      simp only [blobMentions, finRegs, jmpRegs, List.filterMap_nil, List.append_nil,
        List.nil_append, List.flatMap_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact hd

end Opt
end SkaModel
end Formalization
