import lemmas.Ska.OptSwitchWalk

/-!
# `+switch-chains`: several tagged chains in one walk

The walk calls `switchTag bl out` at each head: the chain is that of `bl`,
the blocks so far are `out`.  This file carries `TagHyp` from `bl` to `out`
(`tagHyp_out`) through an invariant of the walk (`SWInv`): outside the
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

/-! ## The invariant of the walk -/

/-- A tagged chain the walk replaced: its head and its tests. -/
structure TCh where
  o : Nat
  t0 : STest
  tl : List STest

/-- **The invariant of the walk** after the tagged chains `A`: each is the
chain of `bl` at its head, a member of `topo`; their `tagIds` are in `done`;
outside their regions and heads the blocks are those of `bl`; a head is its
block of `bl` with the `%clq` to the root and the final miss; a block in a
region is a tree node. -/
structure SWInv (bl : Map Blob) (topo : List Nat) (fuel : Nat) (A : List TCh) (out : Map Blob)
    (done : List Nat) : Prop where
  ch : ∀ a ∈ A, chainOf bl (revCfg bl topo) fuel a.o = some (a.t0 :: a.tl) ∧ a.o ∈ topo
  dn : ∀ a ∈ A, ∀ k ∈ tagIds (a.t0 :: a.tl), k ∈ done
  same : ∀ k, (∀ a ∈ A, k ≠ a.o ∧ ¬ TagIn a.t0 a.tl k) → HoonMap.get out k = HoonMap.get bl k
  head : ∀ a ∈ A, ∃ b, HoonMap.get bl a.o = some b ∧
    HoonMap.get out a.o = some { b with fin := Termin.clq a.t0.s ⟨[], a.t0.y⟩ ⟨[], tagMiss a.t0 a.tl⟩ }
  node : ∀ a ∈ A, ∀ k b, TagIn a.t0 a.tl k → HoonMap.get out k = some b →
    NodeOK (TagJ a.t0 a.tl) (TagS a.t0 a.tl) b

theorem swinv_nil (bl : Map Blob) (topo : List Nat) (fuel : Nat) (done : List Nat) :
    SWInv bl topo fuel [] bl done :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil, fun _ _ => rfl,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩

theorem tagBlocks_congr {M M' : Map Blob} {s mis : Nat} : ∀ (cs : List STest), TagBlocks M s mis cs →
    (∀ t ∈ cs, HoonMap.get M' t.y = HoonMap.get M t.y) →
    (∀ t ∈ cs.dropLast, HoonMap.get M' t.miss = HoonMap.get M t.miss) → TagBlocks M' s mis cs
  | [], h, _, _ => h
  | t :: rest, ⟨a1, a2, a3, a4, ⟨l, r, body, hyb, hlr, hb⟩, hnext, hrest⟩, hY, hM => by
    refine ⟨a1, a2, a3, a4, ⟨l, r, body, by rw [hY t List.mem_cons_self]; exact hyb, hlr, hb⟩, ?_, fun hne => ?_⟩
    · cases rest with
      | nil => exact hnext
      | cons t2 r2 =>
        simp only at hnext ⊢
        rw [hM t (by simp [List.dropLast_cons_cons])]; exact hnext
    · cases rest with
      | nil => exact absurd rfl hne
      | cons t2 r2 =>
        exact tagBlocks_congr _ (hrest hne) (fun u hu => hY u (List.mem_cons_of_mem _ hu))
          (fun u hu => hM u (by rw [List.dropLast_cons_cons]; exact List.mem_cons_of_mem _ hu))

section
variable {bl : Map Blob} {topo : List Nat} {fuel : Nat}

/-- The places a tree node of a chain may jump to are members of `topo`. -/
theorem tagJ_topo (ht : TopoOK bl topo) {n o : Nat} {t0 : STest} {tl : List STest}
    (h : chainOf bl (revCfg bl topo) n o = some (t0 :: tl)) (ho : o ∈ topo) :
    ∀ k, TagJ t0 tl k → k ∈ topo := by
  have hc := chainOf_rev n o _ h
  have hT := (labs_sorted ht o _ hc ho).2
  intro k hk
  rcases hk with hk | ⟨t, ht', rfl⟩ | rfl
  · exact hT k (List.mem_append_left _ (List.mem_of_mem_tail ((tagIn_iff o t0 tl k).mp hk)))
  · obtain ⟨q, hq⟩ := chainR_test hc t ht'
    obtain ⟨_, yb, _, _, -, -, -, hyb, -, hyf, -⟩ := testOf_spec hq
    have hyT : t.y ∈ topo := hT _ (List.mem_append_left _ (List.mem_of_mem_tail (y_mem_tail o _ t ht')))
    exact (topo_jump ht hyT hyb (j := ⟨[], t.hit⟩) (by rw [hyf]; simp [getJmps])).1
  · exact hT _ (by rw [show tagMiss t0 tl = lastMiss o (t0 :: tl) from (lastMiss_tag t0 tl).symm]; simp)

/-- A block reachable in the blocks so far is a member of `topo`. -/
theorem swinv_reach {A : List TCh} {out : Map Blob} {done : List Nat} (W : SWInv bl topo fuel A out done)
    (ht : TopoOK bl topo) : ∀ k, Reach out k → k ∈ topo := by
  intro k hk
  induction hk with
  | zero => obtain ⟨-, h0, -⟩ := ht; cases topo with
    | nil => simp at h0
    | cons a t => simp at h0; subst h0; exact List.mem_cons_self
  | @jump o' b j _ hb hj ih =>
    by_cases hA : ∃ a ∈ A, o' = a.o ∨ TagIn a.t0 a.tl o'
    · obtain ⟨a, ha, e | e⟩ := hA
      · subst e
        obtain ⟨b0, -, hb0⟩ := W.head a ha
        rw [hb0] at hb; cases hb
        simp only [getJmps, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        · exact tagJ_topo ht (W.ch a ha).1 (W.ch a ha).2 _ (Or.inl (Or.inl rfl))
        · exact tagJ_topo ht (W.ch a ha).1 (W.ch a ha).2 _ (Or.inr (Or.inr rfl))
      · exact tagJ_topo ht (W.ch a ha).1 (W.ch a ha).2 _ ((W.node a ha o' b e hb).2.1 j hj).2
    · have hs : HoonMap.get out o' = HoonMap.get bl o' :=
        W.same o' fun a ha => ⟨fun e => hA ⟨a, ha, Or.inl e⟩, fun e => hA ⟨a, ha, Or.inr e⟩⟩
      rw [hs] at hb
      exact (topo_jump ht ih hb hj).1

/-- **`TagHyp` carried from `bl` to the blocks so far**, for a chain of `bl`
at a head later in `topo` than the chains done and not in `done`. -/
theorem tagHyp_out {A : List TCh} {out : Map Blob} {done : List Nat} (W : SWInv bl topo fuel A out done)
    (ht : TopoOK bl topo) {o : Nat} {u0 : STest} {ul : List STest}
    (h : chainOf bl (revCfg bl topo) fuel o = some (u0 :: ul)) (ho : o ∈ topo)
    (hrk : ∀ a ∈ A, rk topo a.o < rk topo o) (hod : o ∉ done) : TagHyp out o u0 ul := by
  have Hb := tagHyp_of ht ho h
  have hc := chainOf_rev fuel o _ h
  have D := fun a (ha : a ∈ A) =>
    chain_disj ht (W.ch a ha).1 (W.ch a ha).2 h ho (hrk a ha) (fun hm => hod (W.dn a ha _ hm))
  have sameI : ∀ k, TagIn u0 ul k → HoonMap.get out k = HoonMap.get bl k := fun k hk =>
    W.same k fun a ha => (D a ha).2.1 k hk
  have hob : HoonMap.get out o = HoonMap.get bl o := W.same o fun a ha => (D a ha).1
  have isS : ∀ k, (∀ a ∈ A, ¬ TagIn a.t0 a.tl k) → (HoonMap.get bl k).isSome → (HoonMap.get out k).isSome := by
    intro k hk hb
    by_cases hA : ∃ a ∈ A, k = a.o
    · obtain ⟨a, ha, rfl⟩ := hA
      obtain ⟨b0, -, hb0⟩ := W.head a ha
      rw [hb0]; rfl
    · rw [W.same k fun a ha => ⟨fun e => hA ⟨a, ha, e⟩, hk a ha⟩]; exact hb
  refine ⟨Hb.nd, Hb.hy, Hb.ho, Hb.hoy, Hb.hr, ?_, by rw [hob]; exact Hb.headFin, fun t ht' => ?_, ?_, ?_, ?_, Hb.zero⟩
  · refine tagBlocks_congr _ Hb.blocks (fun t ht' => sameI _ ((tagIn_iff o u0 ul _).mpr (y_mem_tail o _ t ht')))
      (fun t ht' => sameI _ (Or.inr (List.mem_append_right _ (List.mem_map_of_mem ht'))))
  · exact ⟨isS _ (fun a ha => (D a ha).2.2.1 t ht') (Hb.hits t ht').1, (Hb.hits t ht').2⟩
  · exact ⟨isS _ (fun a ha => (D a ha).2.2.2.1) Hb.miss.1, Hb.miss.2⟩
  · intro k b j hk hkI hko hb hj hjI
    by_cases hA : ∃ a ∈ A, k = a.o ∨ TagIn a.t0 a.tl k
    · obtain ⟨a, ha, e | e⟩ := hA
      · subst e
        obtain ⟨b0, -, hb0⟩ := W.head a ha
        rw [hb0] at hb; cases hb
        simp only [getJmps, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        · exact (D a ha).2.2.2.2.1 _ (Or.inl (Or.inl rfl)) hjI
        · exact (D a ha).2.2.2.2.1 _ (Or.inr (Or.inr rfl)) hjI
      · exact (D a ha).2.2.2.2.1 _ ((W.node a ha k b e hb).2.1 j hj).2 hjI
    · have hs : HoonMap.get out k = HoonMap.get bl k :=
        W.same k fun a ha => ⟨fun e => hA ⟨a, ha, Or.inl e⟩, fun e => hA ⟨a, ha, Or.inr e⟩⟩
      rw [hs] at hb
      have hkT := swinv_reach W ht k hk
      rcases mem_ilabs (labs_into rfl o _ hc k b j hkT hb hj ((tagIn_iff o u0 ul _).mp hjI)) with e | e
      · exact hko e
      · exact hkI ((tagIn_iff o u0 ul _).mpr e)
  · intro k b _ hkI hb r hr
    by_cases hA : ∃ a ∈ A, k = a.o ∨ TagIn a.t0 a.tl k
    · obtain ⟨a, ha, e | e⟩ := hA
      · subst e
        obtain ⟨b0, hbl, hb0⟩ := W.head a ha
        rw [hb0] at hb; cases hb
        obtain ⟨b1, -, -, -, hb1, hf1, -⟩ := testOf_spec (chainOf_rev fuel a.o _ (W.ch a ha).1).1
        rw [hbl] at hb1; cases hb1
        refine tag_ment_bl hc a.o b0 hkI hbl r ?_
        simp only [blobMentions, List.mem_append] at hr ⊢
        rw [hf1]
        rcases hr with (h1 | h1) | h1
        · exact Or.inl (Or.inl h1)
        · exact Or.inl (Or.inr (by simpa [finRegs, jmpRegs] using h1))
        · exact Or.inr h1
      · exact (D a ha).2.2.2.2.2 r ((W.node a ha k b e hb).2.2 r hr)
    · have hs : HoonMap.get out k = HoonMap.get bl k :=
        W.same k fun a ha => ⟨fun e => hA ⟨a, ha, Or.inl e⟩, fun e => hA ⟨a, ha, Or.inr e⟩⟩
      rw [hs] at hb
      exact tag_ment_bl hc k b hkI hb r hr

end

/-! ## The walk over tagged chains -/

theorem sw_idxOf_ne {p o : Nat} (l : List Nat) (h : p ≠ o) : (p :: l).idxOf o = l.idxOf o + 1 := by
  rw [List.idxOf_cons]
  have : (p == o) = false := by simp [h]
  rw [this]; rfl

theorem rk_pre {x o : Nat} {rest : List Nat} : ∀ (pre : List Nat), x ∈ pre → o ∉ pre →
    rk (pre ++ o :: rest) x < rk (pre ++ o :: rest) o
  | [], h, _ => absurd h List.not_mem_nil
  | p :: pre, hx, ho => by
    have hpo : p ≠ o := fun e => ho (by rw [e]; exact List.mem_cons_self)
    have e1 : (p :: pre ++ o :: rest).idxOf o = (pre ++ o :: rest).idxOf o + 1 := by
      rw [List.cons_append]; exact sw_idxOf_ne _ hpo
    unfold rk; rw [e1]
    by_cases hpx : p = x
    · subst hpx; rw [List.cons_append, List.idxOf_cons_self]; omega
    · have e2 : (p :: pre ++ o :: rest).idxOf x = (pre ++ o :: rest).idxOf x + 1 := by
        rw [List.cons_append]; exact sw_idxOf_ne _ hpx
      rw [e2]
      have := rk_pre (rest := rest) pre (by rcases List.mem_cons.mp hx with e | e; exact absurd e.symm hpx; exact e)
        (fun h => ho (List.mem_cons_of_mem _ h))
      unfold rk at this
      omega

section
variable {bl : Map Blob} {topo : List Nat} {fuel : Nat}

/-- **One tagged chain of the walk**: the invariant and `Keeps` go on. -/
theorem walk_tag_step (c : Straight Map) {A : List TCh} {out : Map Blob} {done : List Nat}
    (W : SWInv bl topo fuel A out done) (K : Keeps c (withBlocks c out)) (ht : TopoOK bl topo) {o : Nat}
    {u0 : STest} {ul : List STest} (h : chainOf bl (revCfg bl topo) fuel o = some (u0 :: ul)) (ho : o ∈ topo)
    (hrk : ∀ a ∈ A, rk topo a.o < rk topo o) (hod : o ∉ done) {out' : Map Blob} {done' : List Nat}
    (hs : switchTag bl out fuel o (u0 :: ul) done = some (out', done')) :
    SWInv bl topo fuel (A ++ [⟨o, u0, ul⟩]) out' done' ∧ Keeps c (withBlocks c out') := by
  have H := tagHyp_out W ht h ho hrk hod
  have D := fun a (ha : a ∈ A) =>
    chain_disj ht (W.ch a ha).1 (W.ch a ha).2 h ho (hrk a ha) (fun hm => hod (W.dn a ha _ hm))
  have hob : HoonMap.get bl o = HoonMap.get out o := (W.same o fun a ha => (D a ha).1).symm
  have hs' : switchTag out out fuel o (u0 :: ul) done = some (out', done') := by
    rw [← switchTag_out hob]; exact hs
  obtain ⟨b, nb, nf, hb, hbo, -, -, hfr, hdone⟩ := tag_tree hs' H.nd H.hy H.ho H.hoy H.hr
  have nodes := tag_nodes hs' H.ho H.hoy
  have K' : Keeps (withBlocks c out) (withBlocks (withBlocks c out) out') := tag_keeps_of (withBlocks c out) hs' H
  have frO : ∀ k, k ≠ o → ¬ TagIn u0 ul k → HoonMap.get out' k = HoonMap.get out k :=
    fun k h1 h2 => hfr k h1 (fun e => h2 (Or.inl e)) (fun e => h2 (Or.inr e))
  have hnew : ∀ a, a ∈ A ++ [(⟨o, u0, ul⟩ : TCh)] → a ∈ A ∨ a = ⟨o, u0, ul⟩ := by
    intro a ha; simpa using ha
  refine ⟨⟨fun a ha => ?_, fun a ha k hk => ?_, fun k hk => ?_, fun a ha => ?_, fun a ha k b' hkI hb' => ?_⟩,
    keeps_trans K K'⟩
  · rcases hnew a ha with ha | rfl
    · exact W.ch a ha
    · exact ⟨h, ho⟩
  · rw [hdone]
    rcases hnew a ha with ha | rfl
    · exact List.mem_append_right _ (W.dn a ha k hk)
    · exact List.mem_append_left _ hk
  · have h1 := hk ⟨o, u0, ul⟩ (List.mem_append_right _ (List.mem_singleton_self _))
    rw [frO k h1.1 h1.2]
    exact W.same k fun a ha => hk a (List.mem_append_left _ ha)
  · rcases hnew a ha with ha | rfl
    · rw [frO a.o (D a ha).1.1.symm (fun hI => ((D a ha).2.1 a.o hI).1 rfl)]
      exact W.head a ha
    · exact ⟨b, by rw [hob]; exact hb, hbo⟩
  · rcases hnew a ha with ha | rfl
    · rw [frO k (fun e => (D a ha).1.2 (e ▸ hkI)) (fun hI => ((D a ha).2.1 k hI).2 hkI)] at hb'
      exact W.node a ha k b' hkI hb'
    · exact nodes k b' hkI hb'

/-- **The walk keeps the code over tagged chains**: from any point of `topo`,
with the invariant and `Keeps` so far, when no plain chain of four tests or
more is met. -/
theorem switchWalk_tag (c : Straight Map) (ht : TopoOK bl topo)
    (hnp : ∀ o ∈ topo, ∀ ps, plainsOf bl (revCfg bl topo) fuel o = some ps → ps.length < 4) :
    ∀ (rest pre : List Nat) (A : List TCh) (out : Map Blob) (done : List Nat) (nex : Nat) (outF : Map Blob),
      topo = pre ++ rest → (∀ a ∈ A, a.o ∈ pre) → SWInv bl topo fuel A out done → Keeps c (withBlocks c out) →
      switchWalk bl (revCfg bl topo) fuel rest out done nex = some outF → Keeps c (withBlocks c outF)
  | [], _, _, out, _, _, outF, _, _, _, K, h => by
    simp only [switchWalk, Option.some.injEq] at h; subst h; exact K
  | o :: rest, pre, A, out, done, nex, outF, htp, hpre, W, K, h => by
    have hoT : o ∈ topo := by rw [htp]; simp
    have htp' : topo = (pre ++ [o]) ++ rest := by rw [htp]; simp
    have hpre' : ∀ a ∈ A, a.o ∈ pre ++ [o] := fun a ha => List.mem_append_left _ (hpre a ha)
    unfold switchWalk at h
    split at h
    · exact switchWalk_tag c ht hnp rest (pre ++ [o]) A out done nex outF htp' hpre' W K h
    rename_i hod
    obtain ⟨cs, hcs, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i hlen
      cases cs with
      | nil => simp at hlen
      | cons u0 ul =>
      cases hst : switchTag bl out fuel o (u0 :: ul) done with
      | none => simp [hst] at h
      | some r =>
      obtain ⟨out', done'⟩ := r
      simp only [hst, Option.bind_some] at h
      have hnd : (pre ++ o :: rest).Nodup := by rw [← htp]; exact ht.1
      have hop : o ∉ pre := fun hm => (List.nodup_append.mp hnd).2.2 o hm o List.mem_cons_self rfl
      have hrk : ∀ a ∈ A, rk topo a.o < rk topo o := fun a ha => by
        rw [htp]; exact rk_pre pre (hpre a ha) hop
      obtain ⟨W', K'⟩ := walk_tag_step c W K ht hcs hoT hrk hod hst
      refine switchWalk_tag c ht hnp rest (pre ++ [o]) _ out' done' nex outF htp' (fun a ha => ?_) W' K' h
      rcases List.mem_append.mp ha with ha | ha
      · exact hpre' a ha
      · simp only [List.mem_singleton] at ha; subst ha; simp
    · obtain ⟨ps, hps, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · exact switchWalk_tag c ht hnp rest (pre ++ [o]) A out done nex outF htp' hpre' W K h
      · rename_i hl; exact absurd (hnp o hoT ps hps) hl

/-- **`+switch-chains` keeps the code** on blocks with `DInv`, when no plain
chain of four tests or more is met. -/
theorem switchChains_keeps_tag (c : Straight Map) {fuel : Nat} {bl' : Map Blob} (hb : DInv c.blocks)
    (hnp : ∀ topo, bbTopo fuel c.blocks = some topo → ∀ o ∈ topo, ∀ ps,
      plainsOf c.blocks (revCfg c.blocks topo) fuel o = some ps → ps.length < 4)
    (h : switchChains fuel c.blocks = some bl') : Keeps c (withBlocks c bl') := by
  obtain ⟨topo, htopo, h⟩ := Option.bind_eq_some_iff.mp h
  have ht := bbTopo_ok hb.2.1 htopo
  have K0 : Keeps c (withBlocks c c.blocks) := keeps_refl c
  exact switchWalk_tag c ht (hnp topo htopo) topo [] [] c.blocks [] _ bl' rfl (fun a ha => absurd ha List.not_mem_nil)
    (swinv_nil _ _ _ _) K0 h

end

end Opt
end SkaModel
end Formalization
