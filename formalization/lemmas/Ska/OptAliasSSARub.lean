import lemmas.Ska.OptAliasSSAKeep

/-!
# `+remove-useless-branching` keeps single assignment

**`ssk_rub`** (the field `rub` of `SSAKeepR`): after the pass every block is
the old one with an epilogue appended (`[%equ l r]` or `[%lob s]`, which write
no register) and a new end, a hop with no arguments to the old `z` target
(`rubFin_cases`).  So a read at place `j` after is a read at `min j |body|`
before (`ssk_rub_read`: the epilogue reads what the old two-way end read, the
new hop reads nothing), a definition after is one at the same place before, the
new jumps go to old targets (so `Reach` and `BPath` after are ones before), and
a block ending in `%bom` is unchanged, so a dead fill before is one after.
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock
variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

set_option linter.unusedSectionVars false

/-- The epilogue writes no register. -/
theorem ssk_rub_epi {bl : Map Blob} {fin : Termin} {e : List Pole × Termin} (h : rubFin bl fin = some e) :
    ∀ op ∈ e.1, aliasDst op = none := by
  rcases rubFin_cases h with rfl | ⟨z, o, nz, -, -, -, -, -, hf⟩
  · intro op hop; cases hop
  · rcases hf with ⟨s, -, he⟩ | ⟨s, -, he⟩ | ⟨l, r, -, he⟩ | ⟨s, -, he⟩ <;> rw [he] <;> intro op hop <;>
      simp at hop <;> subst hop <;> rfl

/-- The new jumps go to old targets. -/
theorem ssk_rub_jmp {bl : Map Blob} {fin : Termin} {e : List Pole × Termin} (h : rubFin bl fin = some e)
    {j : Jmp} (hj : j ∈ getJmps e.2) : ∃ j0 ∈ getJmps fin, j0.there = j.there := by
  rcases rubFin_cases h with rfl | ⟨z, o, nz, -, -, -, -, h2, hf⟩
  · exact ⟨j, hj, rfl⟩
  · rw [h2] at hj
    simp only [getJmps, List.mem_singleton] at hj
    subst hj
    refine ⟨z, ?_, rfl⟩
    rcases hf with ⟨s, hf, -⟩ | ⟨s, hf, -⟩ | ⟨l, r, hf, -⟩ | ⟨s, hf, -⟩ <;> rw [hf] <;> simp [getJmps]

theorem ssk_readAt_le {b : Blob} {j r : Nat} (h : ReadAt b j r) : j ≤ b.body.length := by
  rcases h with h | ⟨h, -⟩
  · refine Classical.byContradiction fun hn => ?_
    rw [List.drop_eq_nil_of_le (by omega)] at h
    simp at h
  · omega

/-- **A read after is a read before**, at `min j |body|`. -/
theorem ssk_rub_read {bl : Map Blob} {b : Blob} {e : List Pole × Termin} (he : rubFin bl b.fin = some e)
    {j r : Nat} (h : ReadAt (rubBlob b e) j r) : ReadAt b (min j b.body.length) r := by
  rcases rubFin_cases he with rfl | ⟨z, o, nz, hz, ho, -, -, h2, hf⟩
  · rw [rubBlob_nil] at h
    rw [Nat.min_eq_left (ssk_readAt_le h)]; exact h
  · unfold ReadAt at h ⊢
    simp only [rubBlob, h2, finRegs, jmpRegs, List.filterMap_nil, List.not_mem_nil, and_false,
      or_false] at h
    rw [List.head?_drop] at h
    by_cases hj : j < b.body.length
    · rw [List.getElem?_append_left hj] at h
      rw [Nat.min_eq_left (by omega), List.head?_drop]
      exact Or.inl h
    · rw [List.getElem?_append_right (by omega)] at h
      rw [Nat.min_eq_right (by omega)]
      right
      refine ⟨rfl, ?_⟩
      rcases hf with ⟨s, hf, he1⟩ | ⟨s, hf, he1⟩ | ⟨l, r', hf, he1⟩ | ⟨s, hf, he1⟩ <;> rw [he1] at h <;>
        rw [hf] <;> generalize j - b.body.length = k at h <;> cases k <;>
        simp [aliasReads, aliasDst, poleRegs, finRegs] at h ⊢ <;> (try simp [h]) <;>
        (rcases h with h | h <;> simp [h])

theorem ssk_rub_defs {bl : Map Blob} {b : Blob} {e : List Pole × Termin} (he : rubFin bl b.fin = some e) :
    blockDefs (rubBlob b e) = blockDefs b := by
  have : e.1.filterMap aliasDst = [] := List.filterMap_eq_nil_iff.mpr (ssk_rub_epi he)
  simp [blockDefs, rubBlob, List.filterMap_append, this]

section rub
variable {bl bl' : Map Blob} (hR : RubBlocks bl bl')
include hR

theorem ssk_rub_reach {o : Nat} (h : Reach bl' o) : Reach bl o := by
  induction h with
  | zero => exact Reach.zero
  | jump _ hb hj ih =>
    obtain ⟨b, e, hb0, he, rfl⟩ := hR.back hb
    obtain ⟨j0, hj0, heq⟩ := ssk_rub_jmp he hj
    rw [← heq]; exact Reach.jump (j := j0) ih hb0 hj0

theorem ssk_rub_bpath {l : List Nat} (h : BPath bl' l) : BPath bl l := by
  induction h with
  | start => exact BPath.start
  | step _ hb hj ih =>
    obtain ⟨b, e, hb0, he, rfl⟩ := hR.back hb
    obtain ⟨j0, hj0, heq⟩ := ssk_rub_jmp he hj
    rw [← heq]; exact BPath.step ih hb0 hj0

theorem ssk_rub_site {r : Nat} {s : Nat × Option Nat} (h : DefSite bl' r s) : DefSite bl r s := by
  obtain ⟨o, _ | i⟩ := s
  · obtain ⟨b', hb', hm⟩ := h
    obtain ⟨b, e, hb, -, rfl⟩ := hR.back hb'
    exact ⟨b, hb, hm⟩
  · obtain ⟨b', op, hb', hop, hd⟩ := h
    obtain ⟨b, e, hb, he, rfl⟩ := hR.back hb'
    refine ⟨b, op, hb, ?_, hd⟩
    simp only [rubBlob] at hop
    by_cases hi : i < b.body.length
    · rwa [List.getElem?_append_left hi] at hop
    · rw [List.getElem?_append_right (by omega)] at hop
      rw [ssk_rub_epi he op (List.mem_of_getElem? hop)] at hd; cases hd

theorem ssk_rub_fill {r o i : Nat} (h : DeadFill bl r o i) : DeadFill bl' r o i := by
  obtain ⟨b, hb, ⟨u, hu⟩, hn, himm, hrd⟩ := h
  obtain ⟨e, he, hb'⟩ := (hR o).2 b hb
  have he0 : e = ([], b.fin) := by
    rcases rubFin_cases he with h | ⟨z, o, nz, -, -, -, -, -, hf⟩
    · exact h
    · rcases hf with ⟨s, hf, -⟩ | ⟨s, hf, -⟩ | ⟨l, r, hf, -⟩ | ⟨s, hf, -⟩ <;> rw [hf] at hu <;> cases hu
  subst he0
  rw [rubBlob_nil] at hb'
  refine ⟨b, hb', ⟨u, hu⟩, hn, himm, fun o' b' j hr' hb'' hj => ?_⟩
  obtain ⟨b0, e0, hb0, he0, rfl⟩ := hR.back hb''
  obtain ⟨rfl, -⟩ := hrd o' b0 _ (ssk_rub_reach hR hr') hb0 (ssk_rub_read he0 hj)
  rw [hb] at hb0; cases hb0
  rw [he] at he0; cases he0
  rw [rubBlob_nil] at hj
  exact hrd _ b j (ssk_rub_reach hR hr') hb hj

theorem ssk_rub_live {r : Nat} {s : Nat × Option Nat} (h : LiveDef bl' r s) : LiveDef bl r s :=
  ⟨ssk_rub_reach hR h.1, ssk_rub_site hR h.2.1, fun i hi hf => h.2.2 i hi (ssk_rub_fill hR hf)⟩

theorem ssk_rub_all {r : Nat} (h : r ∈ allDefs bl') : r ∈ allDefs bl := by
  unfold allDefs at h ⊢
  obtain ⟨k, hk, hmem⟩ := List.mem_flatMap.mp h
  have hks : (HoonMap.get bl' k).isSome := (MapKeys.mem_keys bl' k).mp hk
  obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.mp hks
  obtain ⟨b, e, hb, he, rfl⟩ := hR.back hb'
  rw [hb'] at hmem
  refine List.mem_flatMap.mpr ⟨k, (MapKeys.mem_keys bl k).mpr (by rw [hb]; rfl), ?_⟩
  rw [hb]
  simpa [ssk_rub_defs he] using hmem

end rub

/-- **`+remove-useless-branching` keeps `AliasSSAB`** (the field `rub` of
`SSAKeepR`). -/
theorem ssk_rub {bl bl' : Map Blob} {ch : Bool} (h : removeUselessBranching bl = some (ch, bl'))
    (hs : AliasSSAB bl) : AliasSSAB bl' := by
  have hR := rub_blocks h
  obtain ⟨h1, h2⟩ := hs
  refine ⟨fun r s s' hs hs' => h1 r s s' (ssk_rub_live hR hs) (ssk_rub_live hR hs'),
    fun o pth b' hpath hb' i r hread hr => ?_⟩
  obtain ⟨b, e, hb, he, rfl⟩ := hR.back hb'
  rcases h2 o pth b (ssk_rub_bpath hR hpath) hb (min i b.body.length) r (ssk_rub_read he hread)
      (ssk_rub_all hR hr) with h | h | ⟨o', ho', b2, hb2, hm⟩
  · exact Or.inl h
  · right; left
    have ht : b.body.take (min i b.body.length) = b.body.take i := by
      by_cases hi : i ≤ b.body.length
      · rw [Nat.min_eq_left hi]
      · rw [Nat.min_eq_right (by omega), List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
    rw [ht] at h
    simp only [rubBlob, List.take_append, List.filterMap_append, List.mem_append]
    exact Or.inl h
  · right; right
    obtain ⟨e2, he2, hb2'⟩ := (hR o').2 b2 hb2
    exact ⟨o', ho', _, hb2', by rw [ssk_rub_defs he2]; exact hm⟩

end Opt
end SkaModel
end Formalization
