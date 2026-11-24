import lemmas.Ska.OptAliasAvail

/-!
# `DefFirst` of the blocks `+alias` returns

**`tav_walk`**: `TInvA` (`OptAliasAvail.lean`) holds along the whole walk.
**`alias_defFirst`**: a read of a block after is a read before renamed by
`old` at its op (`abody_at`, `aop_rename`, `areads_rename`); the register read
before is done at that place (`awa_read_done`, from `DefFirst` before), so its
`old` is available along every path of the result to the block (`tav_pre`): no
definition, a definition after in an earlier block of the path, a parameter,
or the destination of an op kept before the read.  The reads of an end after
are `old` of the reads of the end before at the end of the body
(`afin_regs`); an end that is `%bom` reads nothing.
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock
variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

set_option linter.unusedSectionVars false

section
variable {pick : List Nat → Nat} {nargs : Nat} {bl : Map Blob} {topo : List Nat}
  {rev : Map (List Nat)} {gF : AGen Map}

/-- **`TInvA` along a part of the walk.** -/
theorem tav_walk (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (hD : DInvS bl) (hT : TopoInvR bl topo rev)
    (h : aliasWalk pick nargs bl topo (aliasInit rev) = some gF) :
    ∀ (l pre r : List Nat) (g g' : AGen Map), topo = pre ++ l ++ r →
      aliasWalk pick nargs bl pre (aliasInit rev) = some g → TInvA bl gF.new pre g →
      aliasWalk pick nargs bl l g = some g' → TInvA bl gF.new (pre ++ l) g'
  | [], pre, r, g, g', _, _, hA, hw => by
    simp only [aliasWalk, Option.some.injEq] at hw; subst hw; simpa using hA
  | o :: l, pre, r, g, g', hto, h1, hA, hw => by
    simp only [aliasWalk] at hw
    obtain ⟨g1, h2, hw⟩ := Option.bind_eq_some_iff.mp hw
    have hA1 := tav_step hpick hD hT h (l := l ++ r) (by simpa using hto) h1 h2 hA
    have h1' : aliasWalk pick nargs bl (pre ++ [o]) (aliasInit rev) = some g1 := by
      rw [awa_walk_append, h1, Option.bind_some]; simp only [aliasWalk, h2, Option.bind_some]
    have := tav_walk hpick hD hT h l (pre ++ [o]) r g1 g' (by simpa using hto) h1' hA1 hw
    simpa using this

/-- **`TInvA` at the point a block is walked.** -/
theorem tav_at (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (hD : DInvS bl) (hT : TopoInvR bl topo rev)
    (h : aliasWalk pick nargs bl topo (aliasInit rev) = some gF) {pre l : List Nat} {o : Nat} {g : AGen Map}
    (hto : topo = pre ++ o :: l) (h1 : aliasWalk pick nargs bl pre (aliasInit rev) = some g) :
    TInvA bl gF.new pre g := by
  have := tav_walk hpick hD hT h pre [] (o :: l) _ g (by simpa using hto) rfl tav_init h1
  simpa using this

/-- **`DefFirst` of the result.** -/
theorem alias_defFirst (hpick : ∀ l : List Nat, l ≠ [] → pick l ∈ l) (hD : DInvS bl) (hT : TopoInvR bl topo rev)
    (h : aliasWalk pick nargs bl topo (aliasInit rev) = some gF) : DefFirst gF.new := by
  have hS : AliasSSAB bl := hD.2.1
  have ht := hT.1.1
  have hGs := alias_targetsSub hT h
  intro o p b' hπG hb' i r hread hr
  obtain ⟨pre, l, g1, g2, b, st0, rb, rf, hto, h1, h2, h3, hne, hb, hA0, hrb, hrf, -, hbe⟩ :=
    aw_new ht hT.2 h hb'
  obtain ⟨info, imms, b1, edges, loc0, rb1, rf1, e1, e2, e3, e4, e5, e6, e7, -⟩ := awa_block_parts h2 hne
  rw [hb] at e3; cases e3
  have e0 := aStart_of_parts e1 e2 e4 e5
  rw [hA0] at e0; cases e0
  subst hbe
  have hI := sst_pre hpick hD hT hto h1
  have hA := tav_at hpick hD hT h hto h1
  have ht' : TopoOK bl (pre ++ o :: l) := hto ▸ ht
  have hopre : o ∉ pre := fun h' => (List.nodup_append.mp ht'.1).2.2 o h' o List.mem_cons_self rfl
  have hGq : ∀ q ∈ pre, HoonMap.get gF.new q = HoonMap.get g1.new q := by
    intro q hq
    have hql : q ∉ l := fun h' => (List.nodup_append.mp ht'.1).2.2 q hq q (List.mem_cons_of_mem _ h') rfl
    have hqo : q ≠ o := fun e => hopre (e ▸ hq)
    rw [((awk_walk l g2 gF h3).2 q hql).2.2, ((awk_block h2).2 q hqo).2.2]
  have hπ : BPath bl (o :: p) := bpath_sub hGs hπG
  have hr0 : r ∈ allDefs bl := alias_allDefs hT h hr
  have fin : ∀ outa : List Pole, rb.1.take i = outa →
      (AvP bl gF.new p r ∨ r ∈ b.par ∨ r ∈ outa.filterMap aliasDst) →
      r ∈ b.par ∨ r ∈ (rb.1.take i).filterMap aliasDst ∨
        ∃ o' ∈ p, ∃ b'', HoonMap.get gF.new o' = some b'' ∧ r ∈ blockDefs b'' := by
    intro outa he hav
    rcases hav with (hav | hav) | hav | hav
    · exact absurd hr0 hav
    · exact Or.inr (Or.inr hav)
    · exact Or.inl hav
    · rw [he]; exact Or.inr (Or.inl hav)
  rcases hread with hread | ⟨hi, hrf'⟩
  · -- a read of an op after
    obtain ⟨op', hop', hrd⟩ : ∃ op', rb.1[i]? = some op' ∧ r ∈ aliasReads op' := by
      simp only at hread
      rw [List.head?_drop] at hread
      cases hx : rb.1[i]? with
      | none => rw [hx] at hread; simp at hread
      | some op' => rw [hx] at hread; exact ⟨op', rfl, by simpa using hread⟩
    obtain ⟨k, op, sta, outa, st1, hk, hba, hl, hop⟩ := abody_at b.body _ rb.1 rb.2 hrb i op' hop'
    have e := aop_rename hop
    subst e
    obtain ⟨y, hy, rfl⟩ := areads_rename sta.old op hrd
    have hm : ∀ k' r', k' < k → ¬ DeadFill bl r' o k' := by
      intro k' r' hk' hdf
      obtain ⟨b5, hb5, -, -, himm, -⟩ := hdf
      rw [hb] at hb5; cases hb5
      have hmem : (b.body.drop k')[k - k']? = some op := by
        rw [List.getElem?_drop, show k' + (k - k') = k by omega]; exact hk
      obtain ⟨n, d, rfl⟩ := himm op (List.mem_of_getElem? hmem)
      simp [aliasReads, aliasDst, poleRegs] at hy
    have hT0 := tav_pre hpick hD hGs ht' hI hA hGq hb hπG e1 e2 e4 e5 hm hba
    have hdone := awa_read_done hS hπ hb hopre (k := k) (x := y) (Or.inl (by rw [List.head?_drop, hk]; exact hy))
    have hsplit := hrb
    rw [← List.take_append_drop k b.body, aliasBody_append, hba, Option.bind_some] at hsplit
    obtain ⟨⟨outb, st'⟩, -, es⟩ := Option.map_eq_some_iff.mp hsplit
    have htake : rb.1.take i = outa := by rw [← es, ← hl]; exact List.take_left
    exact fin outa htake (hT0.old y hdone)
  · -- a read of the end after
    simp only at hi hrf'
    by_cases hbom : ∃ u, b.fin = Termin.bom u
    · obtain ⟨u, hu⟩ := hbom
      rw [hu] at hrf
      simp only [aliasFin, Option.some.injEq] at hrf
      rw [← hrf] at hrf'
      simp [finRegs] at hrf'
    · have hm : ∀ k r', k < b.body.length → ¬ DeadFill bl r' o k := fun k r' _ hdf => by
        obtain ⟨b5, hb5, hu, -⟩ := hdf
        rw [hb] at hb5; cases hb5; exact hbom hu
      have hT0 := tav_pre hpick hD hGs ht' hI hA hGq hb hπG e1 e2 e4 e5 hm
        (by rw [List.take_length]; exact hrb)
      obtain ⟨y, hy, rfl⟩ := afin_regs hrf (hD.2.2 o b hb) r hrf'
      have hdone := awa_read_done hS hπ hb hopre (k := b.body.length) (x := y) (Or.inr ⟨rfl, hy⟩)
      exact fin rb.1 (by rw [hi]; exact List.take_length) (hT0.old y hdone)

end

end Opt
end SkaModel
end Formalization
