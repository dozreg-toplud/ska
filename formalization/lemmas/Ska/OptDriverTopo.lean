import lemmas.Ska.OptTopoOK
import lemmas.Ska.OptDriverFields

/-!
# `topo` and `rev` through the structural passes

The three structural passes keep `Acyclic` whatever they report
(`rub_acyclic`, `hops_acyclic`, `mid_acyclic`): `+remove-useless-branching`
keeps or drops jumps (`rub_sub`), a block merged by `+remove-hops` ends as the
last block of its chain, which lies down the chain in the rank
(`mtail_rank`), and a jump redirected by `+remove-empty-middle` lands down a
chain of empty blocks (`rewriteJump_rank`, `rewriteHop_rank`).

After a pass that reports no change, the old `topo` and `rev` still meet
`TopoInv` (`topoInv_sub`, for blocks whose jumps go to targets of the old
ones and whose labels on `topo` hold blocks): `+remove-useless-branching`
with any flag, since its new jumps are old ones; `+remove-hops` without a
merge leaves every block of `topo` as it was and drops the others
(`hops_same`); `+remove-empty-middle` without a change leaves every block as
it was (`mid_same`).

With `DInv` (`BlkInv` and `Acyclic`) as the block invariant and `TopoInv` as
the invariant of `topo` and `rev`, the fields `topo`, `hops`, `rub` of
`DriverHyp` hold, and `middle` holds given `PassOK` of the result of the pass
(`DriverRest.hyp`: the fields of `DriverHyp` still assumed, with that one).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Opt

open Nock

variable {Map : Type → Type} [HoonMap Map]

/-! ## Jumps to old targets -/

/-- Every block of `bl'` is at a label of `bl` and jumps only to targets of
the block of `bl` there. -/
def TargetsSub (bl bl' : Map Blob) : Prop :=
  ∀ k b', HoonMap.get bl' k = some b' → ∃ b, HoonMap.get bl k = some b ∧
    ∀ j' ∈ getJmps b'.fin, ∃ j ∈ getJmps b.fin, j.there = j'.there

theorem acyclic_sub {bl bl' : Map Blob} (ha : Acyclic bl) (hs : TargetsSub bl bl') : Acyclic bl' := by
  obtain ⟨ρ, hρ⟩ := ha
  refine ⟨ρ, fun o b' j' hb' hj' => ?_⟩
  obtain ⟨b, hb, hj⟩ := hs o b' hb'
  obtain ⟨j, hj, e⟩ := hj j' hj'
  rw [← e]; exact hρ o b j hb hj

theorem reach_sub {bl bl' : Map Blob} (hs : TargetsSub bl bl') {o : Nat} (h : Reach bl' o) : Reach bl o := by
  induction h with
  | zero => exact Reach.zero
  | @jump o b' j' _ hb' hj' ih =>
    obtain ⟨b, hb, hj⟩ := hs o b' hb'
    obtain ⟨j, hj, e⟩ := hj j' hj'
    rw [← e]; exact Reach.jump ih hb hj

/-- **`TopoInv` carries over** to blocks that jump only to old targets and
hold a block at every label of `topo`. -/
theorem topoInv_sub {bl bl' : Map Blob} {topo : List Nat} {rev : Map (List Nat)} (hi : TopoInv bl topo rev)
    (hs : TargetsSub bl bl') (hm : ∀ o ∈ topo, (HoonMap.get bl' o).isSome) : TopoInv bl' topo rev := by
  obtain ⟨⟨hn, h0, -, hr, hf⟩, hrev⟩ := hi
  refine ⟨⟨hn, h0, hm, fun o h => hr o (reach_sub hs h), fun i o b' j' hi hb' hj' => ?_⟩,
    fun o b' j' ho hb' hj' => ?_⟩
  · obtain ⟨b, hb, hj⟩ := hs o b' hb'
    obtain ⟨j, hj, e⟩ := hj j' hj'
    rw [← e]; exact hf i o b j hi hb hj
  · obtain ⟨b, hb, hj⟩ := hs o b' hb'
    obtain ⟨j, hj, e⟩ := hj j' hj'
    rw [← e]; exact hrev o b j ho hb hj

theorem targetsSub_eq {bl bl' : Map Blob} (h : ∀ k b, HoonMap.get bl' k = some b → HoonMap.get bl k = some b) :
    TargetsSub bl bl' :=
  fun k b' hb' => ⟨b', h k b' hb', fun j' hj' => ⟨j', hj', rfl⟩⟩

/-! ## `+remove-useless-branching` -/

section
variable [MapKeys Map]

theorem rub_sub {bl bl' : Map Blob} {ch : Bool} (h : removeUselessBranching bl = some (ch, bl')) :
    TargetsSub bl bl' := by
  intro k b' hb'
  obtain ⟨b, e, hb, he, rfl⟩ := (rub_blocks h).back hb'
  refine ⟨b, hb, fun j' hj' => ?_⟩
  simp only [rubBlob] at hj'
  rcases rubFin_cases he with rfl | ⟨z, o, nz, -, -, -, -, h2, hf⟩
  · exact ⟨j', hj', rfl⟩
  · rw [h2] at hj'
    simp only [getJmps, List.mem_singleton] at hj'
    subst hj'
    refine ⟨z, ?_, rfl⟩
    rcases hf with ⟨s, hf, -⟩ | ⟨s, hf, -⟩ | ⟨l, r, hf, -⟩ | ⟨s, hf, -⟩ <;> simp [hf, getJmps]

theorem rub_acyclic {bl bl' : Map Blob} {ch : Bool} (h : removeUselessBranching bl = some (ch, bl'))
    (ha : Acyclic bl) : Acyclic bl' := acyclic_sub ha (rub_sub h)

/-- **`TopoInv` after `+remove-useless-branching`**, whatever its flag. -/
theorem rub_topoInv {bl bl' : Map Blob} {ch : Bool} {topo : List Nat} {rev : Map (List Nat)}
    (h : removeUselessBranching bl = some (ch, bl')) (hi : TopoInv bl topo rev) : TopoInv bl' topo rev := by
  refine topoInv_sub hi (rub_sub h) fun o ho => ?_
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hi.1.2.2.1 o ho)
  obtain ⟨e, -, hb'⟩ := (rub_blocks h o).2 b hb
  rw [hb']; rfl

end

/-! ## `+remove-hops` -/

/-- The end of a merged chain lies down the chain. -/
theorem mtail_rank {bl : Map Blob} {rev : Map (List Nat)} {ρ : Nat → Nat}
    (hρ : ∀ o b j, HoonMap.get bl o = some b → j ∈ getJmps b.fin → ρ j.there < ρ o) {o : Nat} {b : Blob}
    {T : List Pole} {F : Termin} (h : MTail bl rev o b T F) (hb : HoonMap.get bl o = some b) :
    ∃ e be, HoonMap.get bl e = some be ∧ F = be.fin ∧ ρ e ≤ ρ o := by
  induction h with
  | stop => exact ⟨_, _, hb, rfl, Nat.le_refl _⟩
  | @link o b t b1 ops T F hf _ hb1 _ _ ih =>
    obtain ⟨e, be, hbe, hF, hle⟩ := ih hb1
    have := hρ o b t hb (by simp [hf, getJmps])
    exact ⟨e, be, hbe, hF, by omega⟩

theorem hops_acyclic {fuel : Nat} {bl : Map Blob} {rev : Map (List Nat)} {topo : List Nat} {ch : Bool}
    {bl' : Map Blob} (hn : topo.Nodup) (h0 : topo.head? = some 0) (h : removeHops fuel bl rev topo = some (ch, bl'))
    (ha : Acyclic bl) : Acyclic bl' := by
  obtain ⟨ρ, hρ⟩ := ha
  refine ⟨ρ, fun o m j hm hj => ?_⟩
  obtain ⟨b, T, F, hb, hmt, rfl⟩ := (hops_blocks hn h0 h).back o m hm
  obtain ⟨e, be, hbe, hF, hle⟩ := mtail_rank hρ hmt hb
  simp only [merge] at hj
  rw [hF] at hj
  have := hρ e be j hbe hj
  omega

/-- A chain that merged nothing returns the block it started from. -/
theorem hopChain_nil (bl : Map Blob) (rev : Map (List Nat)) : ∀ (n o : Nat) (bnew : Blob)
    (segs : List (List Pole)) (saw : List Nat) (bout : Blob),
    hopChain bl rev n o bnew segs saw = some (bout, []) → bout = hopDone bnew segs ∧ saw = []
  | 0, _, _, _, _, _, h => by simp [hopChain] at h
  | n + 1, o, bnew, segs, saw, bout, h => by
    simp only [hopChain] at h
    split at h
    · rename_i t ht
      split at h
      · cases h
      · split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact ⟨h.1.symm, h.2⟩
        · obtain ⟨b1, -, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨seg, -, h⟩ := Option.bind_eq_some_iff.mp h
          have := (hopChain_nil bl rev n t.there _ _ _ _ h).2
          cases this
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨h.1.symm, h.2⟩

theorem hopsFold_same (fuel : Nat) (bl : Map Blob) (rev : Map (List Nat)) :
    ∀ (l : List Nat) (acc r : Map Blob × List Nat), l.Nodup → l.foldlM (hopsStep fuel bl rev) acc = some r →
      r.2 = [] → (∀ k ∈ l, HoonMap.get r.1 k = HoonMap.get bl k) ∧ (∀ k, k ∉ l → HoonMap.get r.1 k = HoonMap.get acc.1 k)
  | [], acc, r, _, h, _ => by
    simp only [List.foldlM_nil] at h
    cases h
    exact ⟨fun _ h => absurd h List.not_mem_nil, fun _ _ => rfl⟩
  | o :: l, acc, r, hn, h, hr => by
    rw [List.foldlM_cons] at h
    obtain ⟨acc1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    have hn' := List.nodup_cons.mp hn
    obtain ⟨i1, i2⟩ := hopsFold_same fuel bl rev l acc1 r hn'.2 h hr
    obtain ⟨-, -, -, i4, -⟩ := hopsFold_spec fuel bl rev l acc1 r hn'.2 h
    have hacc1 : acc1.2 = [] := by
      cases e : acc1.2 with
      | nil => rfl
      | cons x xs => have := i4 x (by rw [e]; exact List.mem_cons_self); rw [hr] at this; cases this
    unfold hopsStep at h1
    split at h1
    · rename_i hsaw
      cases h1
      rw [hacc1] at hsaw; cases hsaw
    · obtain ⟨b, hb, h1⟩ := Option.bind_eq_some_iff.mp h1
      obtain ⟨⟨bout, saw'⟩, hc, h1⟩ := Option.map_eq_some_iff.mp h1
      cases h1
      simp only at hacc1
      subst hacc1
      obtain ⟨hbo, -⟩ := hopChain_nil bl rev fuel o b [] acc.2 bout hc
      subst hbo
      refine ⟨fun k hk => ?_, fun k hk => ?_⟩
      · rcases List.mem_cons.mp hk with rfl | hk
        · rw [i2 k hn'.1]; simp [HoonMap.get_put, hopDone, hb]
        · exact i1 k hk
      · rw [i2 k (fun h' => hk (List.mem_cons_of_mem _ h'))]
        simp [HoonMap.get_put, show k ≠ o from fun e => hk (e ▸ List.mem_cons_self)]

/-- **`+remove-hops` without a merge** leaves every block of `topo` as it
was and drops the others. -/
theorem hops_same {fuel : Nat} {bl : Map Blob} {rev : Map (List Nat)} {topo : List Nat} {bl' : Map Blob}
    (hn : topo.Nodup) (h : removeHops fuel bl rev topo = some (false, bl')) :
    (∀ k ∈ topo, HoonMap.get bl' k = HoonMap.get bl k) ∧ ∀ k, k ∉ topo → HoonMap.get bl' k = none := by
  unfold removeHops at h
  obtain ⟨r, hr, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq, decide_eq_false_iff_not, ne_eq, Decidable.not_not] at e
  obtain ⟨e1, rfl⟩ := e
  obtain ⟨i1, i2⟩ := hopsFold_same fuel bl rev topo _ r hn hr e1
  exact ⟨i1, fun k hk => by rw [i2 k hk]; exact HoonMap.get_empty k⟩

theorem hops_topoInv {fuel : Nat} {bl : Map Blob} {rev : Map (List Nat)} {topo : List Nat} {bl' : Map Blob}
    (hi : TopoInv bl topo rev) (h : removeHops fuel bl rev topo = some (false, bl')) : TopoInv bl' topo rev := by
  obtain ⟨hs, hout⟩ := hops_same hi.1.1 h
  refine topoInv_sub hi (targetsSub_eq fun k b hb => ?_) fun o ho => by rw [hs o ho]; exact hi.1.2.2.1 o ho
  by_cases hk : k ∈ topo
  · rw [← hs k hk]; exact hb
  · rw [hout k hk] at hb; cases hb

/-! ## `+remove-empty-middle` -/

theorem rewriteJump_rank {bl : Map Blob} {ρ : Nat → Nat}
    (hρ : ∀ o b j, HoonMap.get bl o = some b → j ∈ getJmps b.fin → ρ j.there < ρ o) :
    ∀ (n : Nat) (j j' : Jmp), rewriteJump bl n j = some j' → ρ j'.there ≤ ρ j.there
  | 0, _, _, h => by simp [rewriteJump] at h
  | n + 1, j, j', h => by
    simp only [rewriteJump] at h
    split at h
    · cases h; exact Nat.le_refl _
    · obtain ⟨nex, hn, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · cases h
      · split at h
        · cases h; exact Nat.le_refl _
        · split at h
          · rename_i t ht
            split at h
            · cases h; exact Nat.le_refl _
            · have h1 := rewriteJump_rank hρ n t j' h
              have h2 := hρ j.there nex t hn (by simp [getJmps, ht])
              omega
          · cases h; exact Nat.le_refl _

theorem rewriteHop_rank {bl : Map Blob} {rd : Nat → List Nat} {ρ : Nat → Nat}
    (hρ : ∀ o b j, HoonMap.get bl o = some b → j ∈ getJmps b.fin → ρ j.there < ρ o) :
    ∀ (n : Nat) (j j' : Jmp), rewriteHop bl rd n j = some j' → ρ j'.there ≤ ρ j.there
  | 0, _, _, h => by simp [rewriteHop] at h
  | n + 1, j, j', h => by
    simp only [rewriteHop] at h
    obtain ⟨nex, hn, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h; exact Nat.le_refl _
    · split at h
      · rename_i t ht
        split at h
        · cases h; exact Nat.le_refl _
        · obtain ⟨s, -, h⟩ := Option.bind_eq_some_iff.mp h
          have h1 := rewriteHop_rank hρ n _ j' h
          have h2 := hρ j.there nex t hn (by simp [getJmps, ht])
          simp only at h1
          omega
      · cases h; exact Nat.le_refl _

theorem middleFin_rank {bl : Map Blob} {rd : Nat → List Nat} {fuel : Nat} {ρ : Nat → Nat}
    (hρ : ∀ o b j, HoonMap.get bl o = some b → j ∈ getJmps b.fin → ρ j.there < ρ o) {f f' : Termin}
    (h : middleFin bl rd fuel f = some f') : ∀ j' ∈ getJmps f', ∃ j ∈ getJmps f, ρ j'.there ≤ ρ j.there := by
  intro j' hj'
  cases f with
  | hop t =>
    simp only [middleFin, Option.map_eq_some_iff] at h
    obtain ⟨t', ht', rfl⟩ := h
    simp only [getJmps, List.mem_singleton] at hj'
    subst hj'
    exact ⟨t, by simp [getJmps], rewriteHop_rank hρ _ _ _ ht'⟩
  | clq s z o | eqq _ s z o | brn s z o | brz s z o =>
    simp only [middleFin, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨z', hz, o', ho, rfl⟩ := h
    simp only [getJmps, List.mem_cons, List.not_mem_nil, or_false] at hj'
    rcases hj' with rfl | rfl
    · exact ⟨z, by simp [getJmps], rewriteJump_rank hρ _ _ _ hz⟩
    · exact ⟨o, by simp [getJmps], rewriteJump_rank hρ _ _ _ ho⟩
  | _ =>
    simp only [middleFin, Option.some.injEq] at h
    subst h
    exact ⟨j', hj', Nat.le_refl _⟩

section
variable [MapKeys Map]

theorem mid_acyclic {fuel : Nat} {bl bl' : Map Blob} {ch : Bool} (h : removeEmptyMiddle fuel bl = some (ch, bl'))
    (ha : Acyclic bl) : Acyclic bl' := by
  obtain ⟨ρ, hρ⟩ := ha
  refine ⟨ρ, fun k b' j' hb' hj' => ?_⟩
  obtain ⟨b, hb, f', hf', rfl⟩ : ∃ b, HoonMap.get bl k = some b ∧ ∃ f', middleFin bl (readersOf bl) fuel b.fin = some f' ∧
      b' = { b with fin := f' } := by
    cases e : HoonMap.get bl k with
    | none => rw [(mid_blocks h k).1 e] at hb'; cases hb'
    | some b =>
      obtain ⟨f', hf', e'⟩ := (mid_blocks h k).2 b e
      rw [e'] at hb'; cases hb'
      exact ⟨b, rfl, f', hf', rfl⟩
  obtain ⟨j, hj, hle⟩ := middleFin_rank hρ hf' j' hj'
  have := hρ k b j hb hj
  omega

theorem midFold_flag (fuel : Nat) (bl : Map Blob) : ∀ (ks : List Nat) (acc : Option (Bool × Map Blob))
    (r : Bool × Map Blob), ks.foldl (midStep fuel bl) acc = some r → r.1 = false →
    (∃ a, acc = some a ∧ a.1 = false) ∧
    ∀ k ∈ ks, ∀ b f', HoonMap.get bl k = some b → middleFin bl (readersOf bl) fuel b.fin = some f' → f' = b.fin
  | [], acc, r, h, hf => by
    simp only [List.foldl_nil] at h
    subst h
    exact ⟨⟨r, rfl, hf⟩, fun _ h => absurd h List.not_mem_nil⟩
  | k0 :: ks, acc, r, h, hf => by
    simp only [List.foldl_cons] at h
    obtain ⟨⟨a', ha', ha'f⟩, ih⟩ := midFold_flag fuel bl ks _ r h hf
    unfold midStep at ha'
    obtain ⟨⟨ch, nw⟩, ha, hs1⟩ := Option.bind_eq_some_iff.mp ha'
    obtain ⟨b0, hb0, hs2⟩ := Option.bind_eq_some_iff.mp hs1
    obtain ⟨f0, hf0, hs3⟩ := Option.map_eq_some_iff.mp hs2
    subst hs3
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, ne_eq, Decidable.not_not] at ha'f
    refine ⟨⟨(ch, nw), ha, ha'f.1⟩, fun k hk b f' hb hf' => ?_⟩
    rcases List.mem_cons.mp hk with rfl | hk
    · rw [hb0] at hb; cases hb
      rw [hf0] at hf'; cases hf'
      exact ha'f.2
    · exact ih k hk b f' hb hf'

/-- **`+remove-empty-middle` without a change** leaves every block as it
was. -/
theorem mid_same {fuel : Nat} {bl bl' : Map Blob} (h : removeEmptyMiddle fuel bl = some (false, bl')) :
    ∀ k, HoonMap.get bl' k = HoonMap.get bl k := by
  intro k
  have hf := midFold_flag fuel bl _ _ _ (by rw [← removeEmptyMiddle_eq]; exact h) rfl
  cases e : HoonMap.get bl k with
  | none => exact (mid_blocks h k).1 e
  | some b =>
    obtain ⟨f', hf', e'⟩ := (mid_blocks h k).2 b e
    rw [e', hf.2 k ((MapKeys.mem_keys bl k).mpr (by simp [e])) b f' e hf']

theorem mid_topoInv {fuel : Nat} {bl bl' : Map Blob} {topo : List Nat} {rev : Map (List Nat)}
    (h : removeEmptyMiddle fuel bl = some (false, bl')) (hi : TopoInv bl topo rev) : TopoInv bl' topo rev :=
  topoInv_sub hi (targetsSub_eq fun k b hb => by rw [← mid_same h k]; exact hb)
    fun o ho => by rw [mid_same h o]; exact hi.1.2.2.1 o ho

end

end Opt
end SkaModel
end Formalization
