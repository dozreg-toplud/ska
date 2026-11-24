import lemmas.Ska.OptAliasRev
import lemmas.Ska.OptHopsBlocks
import lemmas.Ska.OptMiddleBlocks
import lemmas.Ska.OptTrimBr

/-!
# No end is `%lti` in the loop of `+optimize`

`aliasFin` keeps an `%lti` end as it is, without renaming its register, so
`AliasFieldSSAB` is false on blocks with such an end (Gaps 12.8: block `0` =
`[%imm 5 v1] [%imm 5 v2]` with end `%lti 3 v2 1 2`).  In the Hoon `%lti`
exists only in the type of the optimized IR that `+switch-chains` makes after
the loop, so `+alias` never sees one: raw code has none, and no pass of the
loop makes one.  **`NoLti`** says so of a map of blocks; the driver carries it
in `DInvS`.  Each pass of the loop keeps it: `nolti_shape` for the passes that
keep every end (`+trim-trace-hints`, `+remove-dead-code`), **`nolti_rub`**
(`+remove-useless-branching` turns a two-way end into a hop or keeps it),
**`nolti_mid`** (`+remove-empty-middle` retargets jumps and keeps the tag),
**`nolti_hops`** (`+remove-hops` gives a merged block the end of a block
before).  `+alias` keeps it by the field `alias` of `DriverRestSSA`.
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock
variable {Map : Type → Type} [HoonMap Map]

set_option linter.unusedSectionVars false

/-- **No end is `%lti`.** -/
def NoLti (bl : Map Blob) : Prop := ∀ o b, HoonMap.get bl o = some b → ∀ n s z o', b.fin ≠ Termin.lti n s z o'

/-- A pass that keeps every end keeps `NoLti`. -/
theorem nolti_shape {bl bl' : Map Blob} (h : NoLti bl) (hs : SameShape bl bl') : NoLti bl' := by
  intro o b' hb' n s z o'
  obtain ⟨b, hb, -, hf⟩ := hs o b' hb'
  rw [hf]; exact h o b hb n s z o'

theorem nolti_rubTwo {bl : Map Blob} {fin : Termin} {z o : Jmp} {epi : List Pole} {e : List Pole × Termin}
    (h : rubTwo bl fin z o epi = some e) : (∃ t, e.2 = Termin.hop t) ∨ e.2 = fin := by
  unfold rubTwo at h
  split at h
  · obtain ⟨nz, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨no, -, h⟩ := Option.map_eq_some_iff.mp h
    split at h
    · subst h; exact Or.inl ⟨_, rfl⟩
    · subst h; exact Or.inr rfl
  · cases h

theorem nolti_rubFin {bl : Map Blob} {fin : Termin} {e : List Pole × Termin} (h : rubFin bl fin = some e)
    (hn : ∀ n s z o', fin ≠ Termin.lti n s z o') : ∀ n s z o', e.2 ≠ Termin.lti n s z o' := by
  intro n s z o' he
  have key : (∃ t, e.2 = Termin.hop t) ∨ e.2 = fin := by
    unfold rubFin at h
    split at h
    · exact nolti_rubTwo h
    · exact nolti_rubTwo h
    · exact nolti_rubTwo h
    · exact nolti_rubTwo h
    · cases h; exact Or.inr rfl
  rcases key with ⟨t, ht⟩ | hf
  · rw [ht] at he; cases he
  · rw [hf] at he; exact hn n s z o' he

/-- **`+remove-useless-branching` keeps `NoLti`.** -/
theorem nolti_rub [MapKeys Map] {bl bl' : Map Blob} {ch : Bool} (h : NoLti bl)
    (hr : removeUselessBranching bl = some (ch, bl')) : NoLti bl' := by
  intro k b' hb' n s z o'
  have hB := rub_blocks hr k
  cases e : HoonMap.get bl k with
  | none => rw [hB.1 e] at hb'; cases hb'
  | some b =>
    obtain ⟨f, hf, hb2⟩ := hB.2 b e
    rw [hb'] at hb2; cases hb2
    exact nolti_rubFin hf (h k b e) n s z o'

theorem nolti_midFin {bl : Map Blob} {rd : Nat → List Nat} {fuel : Nat} {fin f' : Termin}
    (h : middleFin bl rd fuel fin = some f') (hn : ∀ n s z o', fin ≠ Termin.lti n s z o') :
    ∀ n s z o', f' ≠ Termin.lti n s z o' := by
  intro n s z o' he
  subst he
  cases fin with
  | clq _ _ _ =>
    simp only [middleFin, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, h⟩ := h; cases h
  | eqq _ _ _ _ =>
    simp only [middleFin, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, h⟩ := h; cases h
  | brn _ _ _ =>
    simp only [middleFin, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, h⟩ := h; cases h
  | brz _ _ _ =>
    simp only [middleFin, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, h⟩ := h; cases h
  | hop _ =>
    simp only [middleFin, Option.map_eq_some_iff] at h
    obtain ⟨_, _, h⟩ := h; cases h
  | lti n' s' z' o'' => exact hn n' s' z' o'' rfl
  | jmp _ _ => simp only [middleFin, Option.some.injEq] at h; cases h
  | jmf _ _ _ => simp only [middleFin, Option.some.injEq] at h; cases h
  | jsp _ _ => simp only [middleFin, Option.some.injEq] at h; cases h
  | jsf _ _ _ => simp only [middleFin, Option.some.injEq] at h; cases h
  | don _ => simp only [middleFin, Option.some.injEq] at h; cases h
  | bom _ => simp only [middleFin, Option.some.injEq] at h; cases h

/-- **`+remove-empty-middle` keeps `NoLti`.** -/
theorem nolti_mid [MapKeys Map] {fuel : Nat} {bl bl' : Map Blob} {ch : Bool} (h : NoLti bl)
    (hr : removeEmptyMiddle fuel bl = some (ch, bl')) : NoLti bl' := by
  intro k b' hb' n s z o'
  have hB := mid_blocks hr k
  cases e : HoonMap.get bl k with
  | none => rw [hB.1 e] at hb'; cases hb'
  | some b =>
    obtain ⟨f, hf, hb2⟩ := hB.2 b e
    rw [hb'] at hb2; cases hb2
    exact nolti_midFin hf (h k b e) n s z o'

/-- **`+remove-hops` keeps `NoLti`**: a merged block ends as a block before. -/
theorem nolti_hops {fuel : Nat} {bl : Map Blob} {rev : Map (List Nat)} {topo : List Nat} {ch : Bool}
    {bl' : Map Blob} (h : NoLti bl) (hn : topo.Nodup) (h0 : topo.head? = some 0)
    (hr : removeHops fuel bl rev topo = some (ch, bl')) : NoLti bl' := by
  intro k m hm n s z o'
  obtain ⟨b, T, F, hb, hT, rfl⟩ := (hops_blocks hn h0 hr).back k m hm
  show F ≠ _
  rcases hT.fin_of with e | ⟨e, be, hbe, e'⟩
  · rw [e]; exact h k b hb n s z o'
  · rw [e']; exact h e be hbe n s z o'

end Opt
end SkaModel
end Formalization
