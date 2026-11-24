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

/-- Where a node of a tagged chain's tree may jump: its region, its hits,
its final miss. -/
def TagJ (t0 : STest) (tl : List STest) (k : Nat) : Prop :=
  TagIn t0 tl k ∨ (∃ t ∈ t0 :: tl, k = t.hit) ∨ k = tagMiss t0 tl

/-- What a node of a tagged chain's tree may mention: the head and the
registers of the tests. -/
def TagS (t0 : STest) (tl : List STest) (r : Nat) : Prop := r = t0.s ∨ r ∈ tagRegs (t0 :: tl)

/-- **The blocks `switchTag` puts in the region are tree nodes.** -/
theorem tag_nodes {bl out out' : Map Blob} {fuel o : Nat} {t0 : STest} {tl : List STest}
    {done done' : List Nat} (h : switchTag bl out fuel o (t0 :: tl) done = some (out', done'))
    (ho : o ∉ tagIds (t0 :: tl)) (hoy : o ≠ t0.y) :
    ∀ k b, TagIn t0 tl k → HoonMap.get out' k = some b → NodeOK (TagJ t0 tl) (TagS t0 tl) b := by
  rw [switchTag] at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨cas, hc, ⟨nb, nf, ids2, nout⟩, hs, b, hb, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hc' : casesOf ((t0 :: tl).map tagCase) = some cas := hc
  obtain ⟨-, hsp⟩ := cases_spec hc'
  have hcas : ∀ x ∈ cas, TagJ t0 tl x.hit ∧ TagS t0 tl x.r := by
    intro x hx
    have hf := (hsp x.c x).mp ⟨hx, rfl⟩
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hf)
    exact ⟨Or.inr (Or.inl ⟨t, ht, rfl⟩), Or.inr (List.mem_flatMap.mpr ⟨t, ht, by simp [tagCase]⟩)⟩
  have hdS : TagS t0 tl t0.d := Or.inr (by simp [tagRegs])
  have hids : ∀ k ∈ tl.map STest.y ++ (t0 :: tl).dropLast.map STest.miss, TagJ t0 tl k :=
    fun k hk => Or.inl (Or.inr hk)
  obtain ⟨used, eu, fr, nodes, root⟩ := stree_shape _ _ (TagJ t0 tl) (TagS t0 tl) hdS (Or.inr (Or.inr rfl))
    fuel cas _ _ nb nf ids2 nout hs hids hcas
  intro k b' hk hb'
  have hko : k ≠ o := fun e => by
    subst e; rcases hk with e | e
    · exact hoy e
    · exact ho e
  rw [HoonMap.get_put, if_neg hko, HoonMap.get_put] at hb'
  split at hb'
  · cases hb'
    obtain ⟨-, rj, rm⟩ := root
    refine ⟨rfl, rj, fun r hr => ?_⟩
    simp only [blobMentions, List.nil_append, List.mem_append, List.flatMap_cons, poleRegs,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with hr | (rfl | rfl) | hr
    · exact rm r (by simp [blobMentions, hr])
    · exact Or.inl rfl
    · exact hdS
    · exact rm r (by simp [blobMentions, hr])
  · rename_i hkt
    by_cases hku : k ∈ used
    · obtain ⟨b2, hb2, ok⟩ := nodes k hku
      rw [hb2] at hb'; cases hb'; exact ok
    · rw [fr k hku, get_foldl_del] at hb'
      have hk2 : k ∈ tl.map STest.y ++ (t0 :: tl).dropLast.map STest.miss := by
        rcases hk with e | e
        · exact absurd e hkt
        · exact e
      rw [if_pos hk2] at hb'; cases hb'

/-! ## Two chains of one walk are disjoint -/

theorem tagIn_iff (o : Nat) (t0 : STest) (tl : List STest) (k : Nat) :
    TagIn t0 tl k ↔ k ∈ (ilabs o (t0 :: tl)).tail := by
  show k = t0.y ∨ k ∈ tagIds (t0 :: tl) ↔ k ∈ t0.y :: ilabs t0.miss tl
  rw [List.mem_cons, (ilabs_perm t0 tl).mem_iff]

theorem mem_ilabs {p x : Nat} {cs : List STest} (h : x ∈ ilabs p cs) : x = p ∨ x ∈ (ilabs p cs).tail := by
  cases cs with
  | nil => simp [ilabs] at h
  | cons t rest => exact List.mem_cons.mp h

/-- The mentions of a block outside a chain's region miss the registers of
its tests (`uses = 2`). -/
theorem tag_ment_bl {bl : Map Blob} {rev : Map (List Nat)} {o : Nat} {t0 : STest} {tl : List STest}
    (hc : ChainR bl rev o (t0 :: tl)) :
    ∀ k b, ¬ TagIn t0 tl k → HoonMap.get bl k = some b → ∀ r ∈ blobMentions b, r ∉ tagRegs (t0 :: tl) := by
  intro k b hkI hb r hr hrT
  rw [tagRegs, List.mem_flatMap] at hrT
  obtain ⟨t, ht', hrt⟩ := hrT
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrt
  obtain ⟨q, hq⟩ := chainR_test hc t ht'
  obtain ⟨yb, hyb, cd, cr⟩ := test_count hq
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hud, hur⟩ := testOf_spec hq
  have hne : k ≠ t.y := fun e => hkI ((tagIn_iff o t0 tl k).mpr (by rw [e]; exact y_mem_tail o _ t ht'))
  have h1 := uses_ge2 hne hb hyb r
  have h2 : 0 < (blobMentions b).count r := List.count_pos_iff.mpr hr
  rcases hrt with rfl | rfl <;> omega

section
variable {bl : Map Blob} {rev : Map (List Nat)} {topo : List Nat}

/-- **The labels of a later chain are outside an earlier region**: from a
label `p` after the earlier head and outside its region, the chain from `p`
stays outside it, and so do its hits. -/
theorem chain_out (ht : TopoOK bl topo) (hrev : rev = revCfg bl topo) {o1 : Nat} {cs1 : List STest}
    (hc1 : ChainR bl rev o1 cs1) :
    ∀ (p : Nat) (cs : List STest), ChainR bl rev p cs → p ∈ topo → rk topo o1 < rk topo p →
      p ∉ (ilabs o1 cs1).tail →
      (∀ x ∈ ilabs p cs ++ [lastMiss p cs], x ∉ (ilabs o1 cs1).tail ∧ rk topo o1 < rk topo x ∧ x ∈ topo) ∧
      ∀ t ∈ cs, t.hit ∉ (ilabs o1 cs1).tail
  | p, [], _, hp, hr, hn => ⟨by simp [ilabs, lastMiss]; exact ⟨hn, hr, hp⟩, fun t h => absurd h List.not_mem_nil⟩
  | p, t :: rest, ⟨hto, _, hrc⟩, hp, hr, hn => by
    obtain ⟨b, yb, l, r, hb, hfin, -, hyb, -, hyf, -⟩ := testOf_spec hto
    obtain ⟨hy, h1⟩ := topo_jump ht hp hb (j := ⟨[], t.y⟩) (by rw [hfin]; simp [getJmps])
    obtain ⟨hm, h2⟩ := topo_jump ht hy hyb (j := ⟨[], t.miss⟩) (by rw [hyf]; simp [getJmps])
    simp only at hy h1 hm h2
    have out1 : ∀ (k : Nat) (bk : Blob) (j : Jmp), k ∈ topo → HoonMap.get bl k = some bk → j ∈ getJmps bk.fin →
        rk topo o1 < rk topo k → k ∉ (ilabs o1 cs1).tail → j.there ∉ (ilabs o1 cs1).tail := by
      intro k bk j hk hbk hj hrk hkn hin
      rcases mem_ilabs (labs_into hrev o1 cs1 hc1 k bk j hk hbk hj hin) with e | e
      · subst e; omega
      · exact hkn e
    have hyn := out1 p b ⟨[], t.y⟩ hp hb (by rw [hfin]; simp [getJmps]) hr hn
    have hmn := out1 t.y yb ⟨[], t.miss⟩ hy hyb (by rw [hyf]; simp [getJmps]) (by omega) hyn
    have hhn := out1 t.y yb ⟨[], t.hit⟩ hy hyb (by rw [hyf]; simp [getJmps]) (by omega) hyn
    obtain ⟨ih1, ih2⟩ := chain_out ht hrev hc1 t.miss rest hrc hm (by omega) hmn
    refine ⟨fun x hx => ?_, fun t' ht' => ?_⟩
    · change x ∈ p :: t.y :: (ilabs t.miss rest ++ [lastMiss t.miss rest]) at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨hn, hr, hp⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨hyn, by omega, hy⟩
      · exact ih1 x hx
    · rcases List.mem_cons.mp ht' with rfl | ht'
      · exact hhn
      · exact ih2 t' ht'

/-- **Two chains of one walk**: the earlier at `o1`, the later at `o2`, later
in `topo` and not in the earlier `tagIds`. -/
theorem chain_disj (ht : TopoOK bl topo) {n1 n2 o1 o2 : Nat} {t0 u0 : STest} {tl ul : List STest}
    (h1 : chainOf bl (revCfg bl topo) n1 o1 = some (t0 :: tl)) (ho1 : o1 ∈ topo)
    (h2 : chainOf bl (revCfg bl topo) n2 o2 = some (u0 :: ul)) (ho2 : o2 ∈ topo)
    (hrk : rk topo o1 < rk topo o2) (hd : o2 ∉ tagIds (t0 :: tl)) :
    (o2 ≠ o1 ∧ ¬ TagIn t0 tl o2) ∧
    (∀ k, TagIn u0 ul k → k ≠ o1 ∧ ¬ TagIn t0 tl k) ∧
    (∀ u ∈ u0 :: ul, ¬ TagIn t0 tl u.hit) ∧ ¬ TagIn t0 tl (tagMiss u0 ul) ∧
    (∀ k, TagJ t0 tl k → ¬ TagIn u0 ul k) ∧
    (∀ r, TagS t0 tl r → r ∉ tagRegs (u0 :: ul)) := by
  have hc1 := chainOf_rev n1 o1 _ h1
  have hc2 := chainOf_rev n2 o2 _ h2
  obtain ⟨_, yb0, _, _, -, -, -, hyb0, -, hyf0, -⟩ := testOf_spec hc1.1
  obtain ⟨b2, -, -, -, hb2, hf2, -⟩ := testOf_spec hc2.1
  have hno : o2 ∉ (ilabs o1 (t0 :: tl)).tail := by
    change o2 ∉ t0.y :: ilabs t0.miss tl
    intro hin
    rcases List.mem_cons.mp hin with e | e
    · subst e; rw [hyb0] at hb2; cases hb2; rw [hyf0] at hf2; cases hf2
    · exact hd ((ilabs_perm t0 tl).mem_iff.mp e)
  obtain ⟨L1, L2⟩ := chain_out ht rfl hc1 o2 (u0 :: ul) hc2 ho2 hrk hno
  have hne1 : o2 ≠ o1 := fun e => by rw [e] at hrk; omega
  have hA : ∀ k, TagIn u0 ul k → k ≠ o1 ∧ ¬ TagIn t0 tl k := by
    intro k hk
    rw [tagIn_iff o2] at hk
    have := L1 k (List.mem_append_left _ (List.mem_of_mem_tail hk))
    refine ⟨fun e => by rw [e] at this; omega, fun h => this.1 ((tagIn_iff o1 t0 tl k).mp h)⟩
  have hlm : lastMiss o2 (u0 :: ul) = tagMiss u0 ul := lastMiss_tag u0 ul
  have hD : ¬ TagIn t0 tl (tagMiss u0 ul) := fun h =>
    (L1 _ (by rw [hlm]; simp)).1 ((tagIn_iff o1 t0 tl _).mp h)
  -- the jumps of the earlier chain's yes sides stay outside the later region
  have hE : ∀ t ∈ t0 :: tl, ¬ TagIn u0 ul t.hit ∧ ¬ TagIn u0 ul t.miss := by
    intro t ht'
    obtain ⟨q, hq⟩ := chainR_test hc1 t ht'
    obtain ⟨_, yb, _, _, -, -, -, hyb, -, hyf, -⟩ := testOf_spec hq
    have hyt := y_mem_tail o1 (t0 :: tl) t ht'
    have hyT : t.y ∈ topo := (labs_sorted ht o1 _ hc1 ho1).2 _ (List.mem_append_left _ (List.mem_of_mem_tail hyt))
    have side : ∀ j ∈ getJmps yb.fin, ¬ TagIn u0 ul j.there := by
      intro j hj hI
      rw [tagIn_iff o2] at hI
      have h5 := labs_into rfl o2 (u0 :: ul) hc2 t.y yb j hyT hyb hj hI
      exact (L1 _ (List.mem_append_left _ h5)).1 hyt
    rw [hyf] at side
    exact ⟨side ⟨[], t.hit⟩ (by simp [getJmps]), side ⟨[], t.miss⟩ (by simp [getJmps])⟩
  refine ⟨⟨hne1, fun h => hno ((tagIn_iff o1 t0 tl _).mp h)⟩, hA, fun u hu h => L2 u hu ((tagIn_iff o1 t0 tl _).mp h),
    hD, ?_, ?_⟩
  · intro k hk hI
    rcases hk with hk | ⟨t, ht', rfl⟩ | rfl
    · exact (hA k hI).2 hk
    · exact (hE t ht').1 hI
    · exact (hE _ (List.getLast_mem _)).2 hI
  · intro r hr
    have hm2 := tag_ment_bl hc2
    rcases hr with rfl | hr
    · obtain ⟨b1, -, -, -, hb1, hf1, -⟩ := testOf_spec hc1.1
      exact hm2 o1 b1 (fun h => (hA o1 h).1 rfl) hb1 t0.s
        (mentions_fin b1 _ (by rw [hf1]; simp [finRegs]))
    · rw [tagRegs, List.mem_flatMap] at hr
      obtain ⟨t, ht', hrt⟩ := hr
      obtain ⟨q, hq⟩ := chainR_test hc1 t ht'
      obtain ⟨yb, hyb, cd, cr⟩ := test_count hq
      have hyI : TagIn t0 tl t.y := (tagIn_iff o1 t0 tl _).mpr (y_mem_tail o1 _ t ht')
      have hyO : ¬ TagIn u0 ul t.y := fun h => (hA _ h).2 hyI
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrt
      rcases hrt with rfl | rfl
      · exact hm2 t.y yb hyO hyb _ (List.count_pos_iff.mp (by omega))
      · exact hm2 t.y yb hyO hyb _ (List.count_pos_iff.mp (by omega))

end

end Opt
end SkaModel
end Formalization
