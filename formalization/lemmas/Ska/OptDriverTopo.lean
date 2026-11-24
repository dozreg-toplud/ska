import lemmas.Ska.OptTopoOK
import lemmas.Ska.OptDriverFields
import lemmas.Ska.OptDead
import lemmas.Ska.OptDownPar
import lemmas.Ska.OptDeadSim

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

`+remove-dead-code` keeps the parameters and the end of every block it
keeps, and keeps every block of `rev-topo` (`dead_shape`), so it keeps
`DInv` and `TopoInv` (`dead_inv`); its semantic half is `dead_keeps`
(`OptDeadSim.lean`).

With `DInv` (`BlkInv`, `Acyclic` and `DownPar` of `OptDownPar.lean`) as the
block invariant and `TopoInv` as the invariant of `topo` and `rev`, the
fields `topo`, `hops`, `rub` and `middle` of `DriverHyp` hold (`PassOK` of
the result of `+remove-empty-middle` comes from `DownPar` of its input,
`mid_passOK_of`), and `dead` (`dead_keeps`, `dead_inv`).  `DriverRest` is
what is still assumed, the three passes that are parameters of the driver
(`driverHyp_of`, `optimize_keeps_rest`).
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

/-! ## `+remove-dead-code` -/

/-- Every block of `m` has the parameters and the end of the block of `bl` at
its label. -/
def SameShape (bl m : Map Blob) : Prop :=
  ∀ k b', HoonMap.get m k = some b' → ∃ b, HoonMap.get bl k = some b ∧ b'.par = b.par ∧ b'.fin = b.fin

theorem deadFold_shape (bl : Map Blob) : ∀ (l : List Nat) (acc r : Map Blob × List Nat),
    l.foldlM (fun (acc : Map Blob × List Nat) o =>
      (HoonMap.get bl o).map fun b =>
        let r := deadBody b.body.reverse [] (finRegs b.fin ++ acc.2)
        (HoonMap.put acc.1 o { b with body := r.1 }, r.2)) acc = some r →
    SameShape bl acc.1 → SameShape bl r.1 ∧ (∀ k, (HoonMap.get acc.1 k).isSome → (HoonMap.get r.1 k).isSome) ∧
      ∀ k ∈ l, (HoonMap.get r.1 k).isSome
  | [], acc, r, h, hs => by
    simp only [List.foldlM_nil] at h
    cases h
    exact ⟨hs, fun _ h => h, fun _ h => absurd h List.not_mem_nil⟩
  | o :: l, acc, r, h, hs => by
    rw [List.foldlM_cons] at h
    obtain ⟨acc1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h1
    have hs1 : SameShape bl (HoonMap.put acc.1 o { b with body := (deadBody b.body.reverse [] (finRegs b.fin ++ acc.2)).1 }) := by
      intro k b' hb'
      simp only [HoonMap.get_put] at hb'
      split at hb'
      · rename_i e; subst e; cases hb'; exact ⟨b, hb, rfl, rfl⟩
      · exact hs k b' hb'
    obtain ⟨i1, i2, i3⟩ := deadFold_shape bl l _ r h hs1
    refine ⟨i1, fun k hk => i2 k ?_, fun k hk => ?_⟩
    · simp only [HoonMap.get_put]; split
      · rfl
      · exact hk
    · rcases List.mem_cons.mp hk with rfl | hk
      · exact i2 k (by simp [HoonMap.get_put])
      · exact i3 k hk

/-- **The blocks after `+remove-dead-code`**: the parameters and the end of
the block before at the same label, and a block at every label walked. -/
theorem dead_shape {bl bl' : Map Blob} {revTopo : List Nat} (h : removeDeadCode bl revTopo = some bl') :
    SameShape bl bl' ∧ ∀ k ∈ revTopo, (HoonMap.get bl' k).isSome := by
  unfold removeDeadCode at h
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨i1, -, i3⟩ := deadFold_shape bl revTopo _ r hr (fun k b' hb' => by
    simp only [HoonMap.get_empty] at hb'; cases hb')
  exact ⟨i1, i3⟩

/-- The block invariant of the driver: `BlkInv`, `Acyclic` and `DownPar`. -/
def DInv (bl : Map Blob) : Prop := BlkInv bl ∧ Acyclic bl ∧ DownPar bl

theorem sameShape_inv {bl bl' : Map Blob} (hs : SameShape bl bl') (hb : DInv bl) : DInv bl' := by
  obtain ⟨⟨hn, hp⟩, ha, hd⟩ := hb
  refine ⟨⟨fun o b' hb' => ?_, fun o b' j b2' hb' hj hb2' => ?_⟩,
    acyclic_sub ha fun k b' hb' => ?_, downPar_of (bl := bl) (fun z bz' hz => ?_) (fun y b' j' hb' hj' => ?_)⟩
  · obtain ⟨b, hb, hpar, -⟩ := hs o b' hb'
    rw [hpar]; exact hn o b hb
  · obtain ⟨b, hb, -, hfin⟩ := hs o b' hb'
    obtain ⟨b2, hb2, hpar2, -⟩ := hs j.there b2' hb2'
    rw [hpar2]
    exact hp o b j b2 hb (by rw [← hfin]; exact hj) hb2
  · obtain ⟨b, hb, -, hfin⟩ := hs k b' hb'
    exact ⟨b, hb, fun j' hj' => ⟨j', by rw [← hfin]; exact hj', rfl⟩⟩
  · obtain ⟨bz, hbz, hpar, -⟩ := hs z bz' hz
    exact ⟨bz, hbz, hpar⟩
  · obtain ⟨b, hb, -, hfin⟩ := hs y b' hb'
    rw [hfin] at hj'
    exact ⟨RFrom.one hb hj', hd y b j' hb hj'⟩

/-- **`+remove-dead-code` keeps `DInv` and `TopoInv`.** -/
theorem dead_inv {bl bl' : Map Blob} {topo : List Nat} {rev : Map (List Nat)} (hb : DInv bl)
    (hi : TopoInv bl topo rev) (h : removeDeadCode bl topo.reverse = some bl') : DInv bl' ∧ TopoInv bl' topo rev := by
  obtain ⟨hs, hm⟩ := dead_shape h
  refine ⟨sameShape_inv hs hb, topoInv_sub hi (fun k b' hb' => ?_) fun o ho => hm o (List.mem_reverse.mpr ho)⟩
  obtain ⟨b, hb, -, hfin⟩ := hs k b' hb'
  exact ⟨b, hb, fun j' hj' => ⟨j', by rw [← hfin]; exact hj', rfl⟩⟩

/-! ## The fields of `DriverHyp` -/

section
variable [MapKeys Map]

/-- **The field `topo`.** -/
theorem topo_field {fuel : Nat} {bl : Map Blob} {topo : List Nat} (hb : DInv bl) (h : bbTopo fuel bl = some topo) :
    TopoInv bl topo (revCfg bl topo) :=
  topoInv_revCfg (bbTopo_ok hb.2.1 h)

/-- **The field `hops`.** -/
theorem hops_fieldD {fuel : Nat} {bl : Map Blob} {topo : List Nat} {rev : Map (List Nat)} {ch : Bool}
    {bl' : Map Blob} (hb : DInv bl) (hi : TopoInv bl topo rev) (h : removeHops fuel bl rev topo = some (ch, bl')) :
    KeepsB bl bl' ∧ DInv bl' ∧ (ch = false → TopoInv bl' topo rev) := by
  obtain ⟨k, j⟩ := hops_field hb.1 hi h
  refine ⟨k, ⟨j, hops_acyclic hi.1.1 hi.1.2.1 h hb.2.1, hops_downPar hi.1.1 hi.1.2.1 h hb.2.2⟩, fun hc => ?_⟩
  subst hc
  exact hops_topoInv hi h

/-- **The field `rub`.** -/
theorem rub_fieldD {bl : Map Blob} {topo : List Nat} {rev : Map (List Nat)} {ch : Bool} {bl' : Map Blob}
    (hb : DInv bl) (h : removeUselessBranching bl = some (ch, bl')) :
    KeepsB bl bl' ∧ DInv bl' ∧ (TopoInv bl topo rev → ch = false → TopoInv bl' topo rev) := by
  obtain ⟨k, j⟩ := rub_field hb.1 h
  exact ⟨k, ⟨j, rub_acyclic h hb.2.1, rub_downPar h hb.2.2⟩, fun hi _ => rub_topoInv h hi⟩

/-- **The field `middle`.** -/
theorem middle_fieldD {fuel : Nat} {bl : Map Blob} {topo : List Nat} {rev : Map (List Nat)} {ch : Bool}
    {bl' : Map Blob} (hb : DInv bl) (h : removeEmptyMiddle fuel bl = some (ch, bl')) :
    KeepsB bl bl' ∧ DInv bl' ∧ (TopoInv bl topo rev → ch = false → TopoInv bl' topo rev) := by
  obtain ⟨k, j⟩ := middle_field hb.1 h (mid_passOK_of h hb.2.2)
  refine ⟨k, ⟨j, mid_acyclic h hb.2.1, mid_downPar h hb.2.2⟩, fun hi hc => ?_⟩
  subst hc
  exact mid_topoInv h hi

/-- **What the driver still assumes**, at `DInv` and `TopoInv`: the three
passes that are parameters (`+alias`, `+trim-trace-hints`,
`+switch-chains`). -/
structure DriverRest (fuel : Nat) (P : Passes Map) : Prop where
  alias : ∀ n (bl : Map Blob) topo rev f bl', DInv bl → TopoInv bl topo rev → P.alias n bl rev topo = some (f, bl') →
    KeepsB bl bl' ∧ DInv bl' ∧
      TopoInv bl' (topo.filter fun o => (HoonMap.get bl' o).isSome)
        (revCfg bl' (topo.filter fun o => (HoonMap.get bl' o).isSome))
  trim : ∀ (bl : Map Blob) topo rev bl', DInv bl → TopoInv bl topo rev → P.trim bl topo rev = some bl' →
    KeepsB bl bl' ∧ DInv bl' ∧ TopoInv bl' topo rev
  switch : ∀ (bl : Map Blob) bl', DInv bl → P.switch bl = some bl' → KeepsB bl bl'

theorem driverHyp_of {fuel : Nat} {P : Passes Map} (H : DriverRest fuel P) : DriverHyp fuel P DInv TopoInv where
  topo := fun _ _ hb h => topo_field hb h
  hops := fun _ _ _ _ _ hb hi h => hops_fieldD hb hi h
  rub := fun _ _ _ _ _ hb h => rub_fieldD hb h
  middle := fun _ _ _ _ _ hb h => middle_fieldD hb h
  alias := H.alias
  trim := H.trim
  dead := fun bl topo rev bl' hb hi h =>
    ⟨fun c hc => by subst hc; exact dead_keeps c hi.1 h, dead_inv hb hi h⟩
  switch := H.switch

/-- **`+optimize` keeps the code** on blocks with `DInv` (distinct
parameters, the check of `+eval-pass`, an acyclic CFG, no jump passing a
parameter of a block below its target), given what is still assumed
(`DriverRest`). -/
theorem optimize_keeps_rest {fuel : Nat} {P : Passes Map} (H : DriverRest fuel P) {s s' : Straight Map}
    (hb : DInv s.blocks) (h : optimizeF fuel P s = some s') : Keeps s s' :=
  optimize_keeps (driverHyp_of H) hb h

end

end Opt
end SkaModel
end Formalization
