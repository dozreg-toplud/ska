import lemmas.Ska.CompNestFinal

/-!
# Growing the state when blocks may hop up

The code of `%6` under a goal `%next` has blocks that hop up: the fork
blocks `o0` and `o1` of `+fork-sure` hop to the join `barg`, which is
allocated after them.  `Grow` asks every new block to jump down, so it does
not hold of such runs.  `GrowU` is `Grow` in which a new block may also hop
up, to a label of the state whose block does not hop up (`JumpsU`), and in
which every jump down to a block that hops up, to `t`, comes from a label
above `t`.

`UpBelow g`: every block of `g` that hops up hops to a label below `g.bo`.
It holds of the empty state, and `GrowU` keeps it (`GrowU.up`).  From it,
every `Grow` is a `GrowU` (`Grow.toU`): a new block that jumps down to an
old block that hops up jumps to a label below the start, so above the
block's target.

`downRk_of_growU`: the blocks of a state that grew from the empty state go
down in the rank `upRk`, which is `3 t + 1` at a block that hops up to `t`
and `3 k` at any other label `k`.  So `toStraight_entryR` applies.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- The block at `u` hops up, to `t`. -/
def UpAt (bl : Map Blob) (u t : Nat) : Prop :=
  ∃ b j, HoonMap.get bl u = some b ∧ b.fin = Termin.hop j ∧ j.there = t ∧ u < t

/-- Every block of `g` that hops up hops to a label below `g.bo`. -/
def UpBelow (g : Gen Map) : Prop := ∀ u t, UpAt g.blocks u t → t < g.bo

/-- The jumps of the terminator `fin` of a block at `k`: down, to a label
whose block, if it hops up, hops below `k`; or a hop up, to a label below
`bo` whose block does not hop up. -/
def JumpsU (bl : Map Blob) (bo k : Nat) (fin : Termin) : Prop :=
  ∀ j ∈ finJumps fin, 1 ≤ j.there ∧
    ((j.there < k ∧ ∀ t, UpAt bl j.there t → t < k) ∨
     (fin = Termin.hop j ∧ k < j.there ∧ j.there < bo ∧ ∀ t, ¬ UpAt bl j.there t))

/-- **`g'` grew from `g`, with hops up.** -/
structure GrowU (g g' : Gen Map) : Prop where
  bo : g.bo ≤ g'.bo
  drop : g'.drop = g.drop
  keep : ∀ k b, k < g.bo → HoonMap.get g.blocks k = some b →
    ∃ b', HoonMap.get g'.blocks k = some b' ∧ b'.par = b.par ∧ b'.fin = b.fin
  new : ∀ k b', HoonMap.get g'.blocks k = some b' →
    (∃ b, HoonMap.get g.blocks k = some b ∧ b'.par = b.par ∧ b'.fin = b.fin) ∨
    (g.bo ≤ k ∧ k < g'.bo ∧ JumpsU g'.blocks g'.bo k b'.fin)

theorem GrowU.refl (g : Gen Map) : GrowU g g :=
  ⟨Nat.le_refl _, rfl, fun _ b _ hb => ⟨b, hb, rfl, rfl⟩, fun _ b hb => Or.inl ⟨b, hb, rfl, rfl⟩⟩

/-- Below the old `bo`, which blocks hop up does not change. -/
theorem GrowU.upAt_iff {g g' : Gen Map} (hg : GrowU g g') {x t : Nat} (hx : x < g.bo) :
    UpAt g'.blocks x t ↔ UpAt g.blocks x t := by
  constructor
  · rintro ⟨b, j, hb, hf, ht, hlt⟩
    rcases hg.new x b hb with ⟨b0, h0, _, f0⟩ | ⟨l, _, _⟩
    · exact ⟨b0, j, h0, f0.symm.trans hf, ht, hlt⟩
    · omega
  · rintro ⟨b, j, hb, hf, ht, hlt⟩
    obtain ⟨b', hb', _, f'⟩ := hg.keep x b hx hb
    exact ⟨b', j, hb', f'.trans hf, ht, hlt⟩

theorem JumpsU.mono {g g' : Gen Map} (hg : GrowU g g') {k : Nat} {fin : Termin} (hk : k < g.bo)
    (h : JumpsU g.blocks g.bo k fin) : JumpsU g'.blocks g'.bo k fin := by
  intro j hj
  obtain ⟨h1, h2⟩ := h j hj
  refine ⟨h1, ?_⟩
  rcases h2 with ⟨a, b⟩ | ⟨a, b, c, d⟩
  · exact Or.inl ⟨a, fun t ht => b t ((hg.upAt_iff (by omega)).mp ht)⟩
  · exact Or.inr ⟨a, b, Nat.lt_of_lt_of_le c hg.bo, fun t ht => d t ((hg.upAt_iff c).mp ht)⟩

theorem GrowU.trans {g0 g1 g2 : Gen Map} (a : GrowU g0 g1) (b : GrowU g1 g2) : GrowU g0 g2 where
  bo := Nat.le_trans a.bo b.bo
  drop := b.drop.trans a.drop
  keep := fun k x hk hx => by
    obtain ⟨x1, h1, p1, f1⟩ := a.keep k x hk hx
    obtain ⟨x2, h2, p2, f2⟩ := b.keep k x1 (Nat.lt_of_lt_of_le hk a.bo) h1
    exact ⟨x2, h2, p2.trans p1, f2.trans f1⟩
  new := fun k x hx => by
    rcases b.new k x hx with ⟨x1, h1, p1, f1⟩ | ⟨l, u, j⟩
    · rcases a.new k x1 h1 with ⟨x0, h0, p0, f0⟩ | ⟨l', u', j'⟩
      · exact Or.inl ⟨x0, h0, p1.trans p0, f1.trans f0⟩
      · exact Or.inr ⟨l', Nat.lt_of_lt_of_le u' b.bo, by rw [f1]; exact j'.mono b u'⟩
    · exact Or.inr ⟨Nat.le_trans a.bo l, u, j⟩

/-- **`GrowU` keeps `UpBelow`.** -/
theorem GrowU.up {g g' : Gen Map} (hg : GrowU g g') (hu : UpBelow g) : UpBelow g' := by
  rintro u t ⟨b, j, hb, hf, ht, hlt⟩
  rcases hg.new u b hb with ⟨b0, h0, _, f0⟩ | ⟨_, _, J⟩
  · exact Nat.lt_of_lt_of_le (hu u t ⟨b0, j, h0, f0.symm.trans hf, ht, hlt⟩) hg.bo
  · obtain ⟨_, h2⟩ := J j (by rw [hf]; simp [finJumps])
    rcases h2 with ⟨a, _⟩ | ⟨_, _, c, _⟩
    · omega
    · omega

/-- **Every `Grow` from a state with `UpBelow` is a `GrowU`.** -/
theorem Grow.toU {g g' : Gen Map} (hg : Grow g g') (hu : UpBelow g) : GrowU g g' := by
  refine ⟨hg.bo, hg.drop, hg.keep, fun k b' hb => ?_⟩
  rcases hg.new k b' hb with old | ⟨l, u, J⟩
  · exact Or.inl old
  · refine Or.inr ⟨l, u, fun jj hjj => ⟨(J jj hjj).1, Or.inl ⟨(J jj hjj).2, fun t ht => ?_⟩⟩⟩
    obtain ⟨b2, j2, hb2, hf2, ht2, hlt2⟩ := ht
    rcases hg.new _ b2 hb2 with ⟨b0, h0, _, f0⟩ | ⟨_, _, jb⟩
    · exact Nat.lt_of_lt_of_le (hu _ t ⟨b0, j2, h0, f0.symm.trans hf2, ht2, hlt2⟩) l
    · have := (jb j2 (by rw [hf2]; simp [finJumps])).2
      omega

/-- A state with the same blocks. -/
theorem growU_same {g g' : Gen Map} (hbo : g'.bo = g.bo) (hd : g'.drop = g.drop)
    (hb : ∀ k, HoonMap.get g'.blocks k = HoonMap.get g.blocks k) : GrowU g g' :=
  ⟨Nat.le_of_eq hbo.symm, hd, fun k b _ h => ⟨b, (hb k).trans h, rfl, rfl⟩,
    fun k b h => Or.inl ⟨b, (hb k).symm.trans h, rfl, rfl⟩⟩

/-- `GrowU` from the blocks: the old ones stay, and each new one is at a new
label and jumps as `JumpsU` says. -/
theorem growU_of {g g' : Gen Map} (hbo : g.bo ≤ g'.bo) (hd : g'.drop = g.drop)
    (hk : ∀ k, (k < g.bo ∨ g'.bo ≤ k) → HoonMap.get g'.blocks k = HoonMap.get g.blocks k)
    (hn : ∀ k b', g.bo ≤ k → k < g'.bo → HoonMap.get g'.blocks k = some b' → JumpsU g'.blocks g'.bo k b'.fin) :
    GrowU g g' := by
  refine ⟨hbo, hd, fun k b hk' h => ⟨b, (hk k (Or.inl hk')).trans h, rfl, rfl⟩, fun k b' h => ?_⟩
  by_cases e : k < g.bo ∨ g'.bo ≤ k
  · exact Or.inl ⟨b', (hk k e).symm.trans h, rfl, rfl⟩
  · exact Or.inr ⟨by omega, by omega, hn k b' (by omega) (by omega) h⟩

/-! ## The rank -/

/-- **The rank of a label**: `3 t + 1` if its block hops up to `t`, and
`3 k` otherwise. -/
def upRk (bl : Map Blob) (k : Nat) : Nat :=
  match HoonMap.get bl k with
  | some ⟨_, _, Termin.hop j⟩ => if k < j.there then 3 * j.there + 1 else 3 * k
  | _ => 3 * k

theorem upRk_up {bl : Map Blob} {k t : Nat} (h : UpAt bl k t) : upRk bl k = 3 * t + 1 := by
  obtain ⟨⟨p, bd, f⟩, j, hb, hf, rfl, hlt⟩ := h
  simp only at hf; subst hf
  unfold upRk; rw [hb]; simp [hlt]

theorem upRk_not {bl : Map Blob} {k : Nat} (h : ∀ t, ¬ UpAt bl k t) : upRk bl k = 3 * k := by
  unfold upRk
  split
  · rename_i p bd j hb
    split
    · rename_i hlt
      exact absurd ⟨_, j, hb, rfl, rfl, hlt⟩ (h j.there)
    · rfl
  · rfl

/-- **The blocks of a state that grew from one without blocks go down in
the rank `upRk`.** -/
theorem downRk_of_growU {g0 g : Gen Map} (hg : GrowU g0 g) (h0 : ∀ k, HoonMap.get g0.blocks k = Option.none)
    (hb0 : 1 ≤ g0.bo) : DownRk (upRk g.blocks) g.blocks := by
  intro k b hk
  rcases hg.new k b hk with ⟨b0, h0', _⟩ | ⟨l, _, J⟩
  · rw [h0 k] at h0'; cases h0'
  refine ⟨by omega, fun j hj => ?_⟩
  obtain ⟨h1, h2⟩ := J j hj
  refine ⟨h1, ?_⟩
  by_cases hup : ∃ t, UpAt g.blocks k t
  · obtain ⟨t, ht⟩ := hup
    rw [upRk_up ht]
    obtain ⟨b', j', hb', hf', ht', hlt'⟩ := ht
    rw [hk] at hb'; cases hb'
    rw [hf'] at hj; simp only [finJumps, List.mem_singleton] at hj; subst hj
    rcases h2 with ⟨a, _⟩ | ⟨_, _, _, d⟩
    · omega
    · rw [upRk_not d]; omega
  · rw [upRk_not (fun t ht => hup ⟨t, ht⟩)]
    rcases h2 with ⟨a, d⟩ | ⟨hf, hlt, _, _⟩
    · by_cases hup2 : ∃ t, UpAt g.blocks j.there t
      · obtain ⟨t, ht⟩ := hup2
        rw [upRk_up ht]; have := d t ht; omega
      · rw [upRk_not (fun t ht => hup2 ⟨t, ht⟩)]; omega
    · exact absurd ⟨_, ⟨b, j, hk, hf, rfl, hlt⟩⟩ hup

/-- Blocks with the terminators of blocks that go down in a rank go down in
it. -/
theorem downRk_of_fins {ρ : Nat → Nat} {bs bs' : Map Blob} (hd : DownRk ρ bs)
    (h : ∀ k b', HoonMap.get bs' k = some b' → ∃ b, HoonMap.get bs k = some b ∧ b'.fin = b.fin) :
    DownRk ρ bs' := by
  intro k b' hk
  obtain ⟨b, hb, hf⟩ := h k b' hk
  rw [hf]; exact hd k b hb

theorem upBelow_gen0 : UpBelow (gen0 : Gen Map) := by
  rintro u t ⟨b, j, hb, _⟩
  simp [gen0, HoonMap.get_empty] at hb

/-- The ranked fact the final pass needs, from a run that starts at `gen0`. -/
theorem downRk_gen0 {g : Gen Map} (hg : GrowU gen0 g) : DownRk (upRk g.blocks) g.blocks :=
  downRk_of_growU hg (fun k => by simp [gen0, HoonMap.get_empty]) (by simp [gen0])

/-! ## The steps -/

theorem growU_emit {g : Gen Map} {b : Blob} (h : JumpsBelow b.fin g.bo) (hu : UpBelow g) :
    GrowU g (g.emitted b) := (grow_emit h).toU hu

theorem growU_addOps {o : Nat} {ops : List Pole} {g g' : Gen Map} {u : Unit}
    (h : addOps o ops g = some (u, g')) (hu : UpBelow g) : GrowU g g' := (grow_addOps h).toU hu

end Comp
end SkaModel
end Formalization
