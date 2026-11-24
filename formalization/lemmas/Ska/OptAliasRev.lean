import lemmas.Ska.OptAliasField

/-!
# `+alias` trusts `rev`: the predecessors it lists must be real (`RevSound`)

`+alias` drops a block of `topo` only when `rev` lists no predecessor for it,
and otherwise walks it, so a block that no jump reaches is walked when `rev`
lists a predecessor for it anyway.  Its ops then change the global `old`, and
a later read of a register it writes is renamed even after that register's one
live definition.  `TopoInv` says only that `rev` lists every member of `topo`
that jumps to a block, so it allows that.  Witness on the real pass
(`tools/hoon/aliasrev.hoon`): block `0w0` hops to `0w2`, the unreachable
`0w1` is `[%mov 0v5 0v2]`, `[%bom ~]`, and `0w2` is `[%imm 5 0v2]`,
`[%don 0v2]`; with `topo` `~[0w0 0w1 0w2]` and `rev-cfg` plus `0w0` listed as
a predecessor of `0w1`, `+alias` makes the end of `0w2` `[%don 0v5]`, and
`+eval-blob` with `0v5 = 7` returns `5` before and `7` after.  With `rev-cfg`
alone it drops `0w1` and keeps `[%don 0v2]`.  The blocks have `DInvT`,
`AliasSSAB` (`0w1` is not reachable) and `TopoInv`.

So the field `alias` assumes **`RevSound`**: every block `rev` lists for `o`
is a member of `topo` that jumps to `o`.  `+rev-cfg` gives it
(`revCfg_sound`), and the passes the driver runs between `+rev-cfg` and
`+alias` keep it when they report no change (`rvs_eq`, `rvs_rub`), as do
`+trim-trace-hints` and `+remove-dead-code`, which keep every end
(`rvs_shape`).
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock
variable {Map : Type → Type} [HoonMap Map]

set_option linter.unusedSectionVars false

/-- **Every predecessor `rev` lists is real**: a member of `topo` that jumps
to the block. -/
def RevSound (bl : Map Blob) (topo : List Nat) (rev : Map (List Nat)) : Prop :=
  ∀ o p, p ∈ getJa rev o → p ∈ topo ∧ ∃ b j, HoonMap.get bl p = some b ∧ j ∈ getJmps b.fin ∧ j.there = o

theorem rvs_addJa {acc : Map (List Nat)} {k x o p : Nat} (h : p ∈ getJa (addJa acc k x) o) :
    (o = k ∧ p = x) ∨ p ∈ getJa acc o := by
  unfold addJa getJa at h
  rw [HoonMap.get_put] at h
  by_cases e : o = k
  · subst e
    simp only [if_true, Option.getD_some, List.mem_cons] at h
    rcases h with h | h
    · exact Or.inl ⟨rfl, h⟩
    · exact Or.inr h
  · simp only [e, if_false] at h
    exact Or.inr h

theorem rvs_inner {bl : Map Blob} {topo : List Nat} {x : Nat} {v : Blob} (hx : x ∈ topo)
    (hv : HoonMap.get bl x = some v) : ∀ (js : List Jmp) (acc : Map (List Nat)), (∀ j ∈ js, j ∈ getJmps v.fin) →
    RevSound bl topo acc → RevSound bl topo (js.foldl (fun acc j => addJa acc j.there x) acc)
  | [], _, _, h => h
  | j :: js, acc, hjs, h => by
    simp only [List.foldl_cons]
    refine rvs_inner hx hv js _ (fun j' hj' => hjs j' (List.mem_cons_of_mem _ hj')) fun o p hp => ?_
    rcases rvs_addJa hp with ⟨rfl, rfl⟩ | hp
    · exact ⟨hx, v, j, hv, hjs j List.mem_cons_self, rfl⟩
    · exact h o p hp

theorem rvs_fold {bl : Map Blob} {topo : List Nat} : ∀ (ks : List Nat) (acc : Map (List Nat)),
    RevSound bl topo acc → RevSound bl topo (ks.foldl (revStep bl topo) acc)
  | [], _, h => h
  | k :: ks, acc, h => by
    simp only [List.foldl_cons]
    apply rvs_fold ks
    unfold revStep
    split
    · rename_i v hv
      split
      · rename_i hk
        exact rvs_inner hk hv _ acc (fun _ hj => hj) h
      · exact h
    · exact h

/-- **`+rev-cfg` lists only real predecessors.** -/
theorem revCfg_sound [MapKeys Map] (bl : Map Blob) (topo : List Nat) : RevSound bl topo (revCfg bl topo) :=
  rvs_fold _ _ fun o p hp => by simp [getJa, HoonMap.get_empty] at hp

/-- A pass that leaves every block of `topo` as it was keeps `RevSound`. -/
theorem rvs_eq {bl bl' : Map Blob} {topo : List Nat} {rev : Map (List Nat)} (h : RevSound bl topo rev)
    (he : ∀ k ∈ topo, HoonMap.get bl' k = HoonMap.get bl k) : RevSound bl' topo rev := fun o p hp => by
  obtain ⟨hpt, b, j, hb, hj, ho⟩ := h o p hp
  exact ⟨hpt, b, j, by rw [he p hpt]; exact hb, hj, ho⟩

/-- A pass that keeps the end of every block, and a block at every label of
`topo`, keeps `RevSound`. -/
theorem rvs_shape {bl bl' : Map Blob} {topo : List Nat} {rev : Map (List Nat)} (h : RevSound bl topo rev)
    (hs : SameShape bl bl') (hm : ∀ k ∈ topo, (HoonMap.get bl' k).isSome) : RevSound bl' topo rev :=
  fun o p hp => by
    obtain ⟨hpt, b, j, hb, hj, ho⟩ := h o p hp
    obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.mp (hm p hpt)
    obtain ⟨b0, hb0, -, hf⟩ := hs p b' hb'
    rw [hb] at hb0; cases hb0
    exact ⟨hpt, b', j, hb', by rw [hf]; exact hj, ho⟩

/-- Without a change, `+remove-useless-branching` keeps every end. -/
theorem rvs_rubFold (bl : Map Blob) : ∀ (ks : List Nat) (acc : Option (Bool × Map Blob)) (r : Bool × Map Blob),
    ks.foldl (rubStep bl) acc = some r → r.1 = false →
      (∃ a, acc = some a ∧ a.1 = false) ∧
        ∀ k ∈ ks, ∀ b e, HoonMap.get bl k = some b → rubFin bl b.fin = some e → e.2 = b.fin
  | [], acc, r, h, hf => by
    simp only [List.foldl_nil] at h; subst h
    exact ⟨⟨r, rfl, hf⟩, fun _ hk => absurd hk List.not_mem_nil⟩
  | k0 :: ks, acc, r, h, hf => by
    simp only [List.foldl_cons] at h
    cases hs : rubStep bl acc k0 with
    | none => rw [hs, rubFold_none] at h; cases h
    | some a' =>
      rw [hs] at h
      obtain ⟨⟨a'', ha'', hf''⟩, hin⟩ := rvs_rubFold bl ks _ r h hf
      cases ha''
      unfold rubStep at hs
      obtain ⟨a, ha, hs1⟩ := Option.bind_eq_some_iff.mp hs
      subst ha
      obtain ⟨b0, hb0, hs2⟩ := Option.bind_eq_some_iff.mp hs1
      obtain ⟨e0, he0, hs3⟩ := Option.map_eq_some_iff.mp hs2
      subst hs3
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Decidable.not_not] at hf''
      refine ⟨⟨a, rfl, hf''.1⟩, fun k hk b e hb he => ?_⟩
      rcases List.mem_cons.mp hk with rfl | hk
      · rw [hb0] at hb; cases hb; rw [he0] at he; cases he; exact hf''.2
      · exact hin k hk b e hb he

theorem rvs_rub [MapKeys Map] {bl bl' : Map Blob} {topo : List Nat} {rev : Map (List Nat)}
    (h : RevSound bl topo rev) (hr : removeUselessBranching bl = some (false, bl')) : RevSound bl' topo rev :=
  fun o p hp => by
    obtain ⟨hpt, b, j, hb, hj, ho⟩ := h o p hp
    obtain ⟨e, he, hb'⟩ := ((rub_blocks hr) p).2 b hb
    have hfin := (rvs_rubFold bl _ _ _ hr rfl).2 p ((MapKeys.mem_keys bl p).mpr (by simp [hb])) b e hb he
    exact ⟨hpt, rubBlob b e, j, hb', by simp only [rubBlob]; rw [hfin]; exact hj, ho⟩

end Opt
end SkaModel
end Formalization
