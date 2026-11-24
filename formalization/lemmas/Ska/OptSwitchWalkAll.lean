import lemmas.Ska.OptSwitchGen

/-!
# `+switch-chains`: the walk over tagged and plain chains

**`switchChains_keeps`**: on blocks with `DInv`, `+switch-chains` (the model
`switchChains`) keeps the code, so **`switchKeepsM`**: `SwitchKeepsM` holds.
This removes the hypothesis `hnp` of `switchChains_keeps_tag`.

The walk invariant `SWI bl topo G out done nex` describes the chains done,
`G`, of either kind as `GC` (`OptSwitchGen.lean`): each is `GOK`; a label of
the region of one that is not in `done` is the first yes side of a tagged
chain (`YShape`: an `%eqq` whose no side is an empty block, which neither a
tagged head nor a plain head of a longer chain can be); outside the heads and
regions `out` is `bl`; a head has its parameters, jumps that pass nothing to
its region or `X`, and mentions of its block of `bl` or of `S`; a block in a
region is a tree node (`NodeOK`); `out` has no label from `nex` up, and the
labels taken from `nex` lie below it.

* `swi_cases`: a block of `out` is a head or a node of a chain done, or the
  block of `bl` outside all of them; `swi_reach`: a block reachable in `out`
  is a member of `topo` or a label a plain chain took.
* `tagHyp_outG`, `plainHyp_outG`: `TagHyp` and `PlainHyp` carried from `bl`
  to `out`, for a head later in `topo` than the chains done and outside their
  regions (`gc_disj`).
* `swi_tag_step`, `swi_plain_step`: one chain of the walk, by `tag_keeps_of`
  or `plain_keeps_of` on the blocks so far and `keeps_trans`.
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock
variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-- The first yes side of a tagged chain: an `%eqq` whose no side is an empty
block. -/
def YShape (bl : Map Blob) (k : Nat) : Prop :=
  ∃ b l r h m mb, HoonMap.get bl k = some b ∧ b.fin = Termin.eqq l r ⟨[], h⟩ ⟨[], m⟩ ∧
    HoonMap.get bl m = some mb ∧ mb.body = []

/-- **The invariant of the walk** over chains of either kind. -/
structure SWI (bl : Map Blob) (topo : List Nat) (G : List GC) (out : Map Blob) (done : List Nat) (nex : Nat) :
    Prop where
  ok : ∀ g ∈ G, GOK bl topo g
  dn : ∀ g ∈ G, ∀ k ∈ g.R, k ∈ done ∨ YShape bl k
  same : ∀ k, (∀ g ∈ G, k ≠ g.o ∧ ¬ g.In k) → HoonMap.get out k = HoonMap.get bl k
  head : ∀ g ∈ G, ∃ b b', HoonMap.get bl g.o = some b ∧ HoonMap.get out g.o = some b' ∧ b'.par = b.par ∧
    (∀ j ∈ getJmps b'.fin, j.args = [] ∧ g.J j.there) ∧ (∀ r ∈ blobMentions b', r ∈ blobMentions b ∨ r ∈ g.S)
  node : ∀ g ∈ G, ∀ k b, g.In k → HoonMap.get out k = some b → NodeOK g.J (· ∈ g.S) b
  above : ∀ k, nex ≤ k → HoonMap.get out k = none
  fr : ∀ g ∈ G, g.n2 ≤ nex
  nb : nexOf bl ≤ nex

theorem nodeOK_mono {P P' S S' : Nat → Prop} {b : Blob} (h : NodeOK P S b) (hP : ∀ k, P k → P' k)
    (hS : ∀ r, S r → S' r) : NodeOK P' S' b :=
  ⟨h.1, fun j hj => ⟨(h.2.1 j hj).1, hP _ (h.2.1 j hj).2⟩, fun r hr => hS r (h.2.2 r hr)⟩

theorem plainBlocks_congr {M M' : Map Blob} {d mis : Nat} : ∀ (ps : List (Nat × SPlain)), PlainBlocks M d mis ps →
    (∀ t ∈ ps, HoonMap.get M' t.1 = HoonMap.get M t.1) → PlainBlocks M' d mis ps
  | [], h, _ => h
  | t :: rest, ⟨a1, ⟨l, r, hb, hlr⟩, hnext, hrest⟩, hY => by
    refine ⟨a1, ⟨l, r, by rw [hY t List.mem_cons_self]; exact hb, hlr⟩, hnext, fun hne => ?_⟩
    exact plainBlocks_congr rest (hrest hne) (fun u hu => hY u (List.mem_cons_of_mem _ hu))

section
variable {bl : Map Blob} {topo : List Nat} {fuel : Nat}

theorem topo_lt (ht : TopoOK bl topo) {x : Nat} (hx : x ∈ topo) : x < nexOf bl := nexOf_gt bl (ht.2.2.1 x hx)

theorem swi_nil (bl : Map Blob) (topo : List Nat) : SWI bl topo [] bl [] (nexOf bl) :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil, fun _ _ => rfl,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun k hk => by
      cases e : HoonMap.get bl k with
      | none => rfl
      | some b => have := nexOf_gt bl (k := k) (by rw [e]; rfl); omega,
    fun _ h => absurd h List.not_mem_nil, Nat.le_refl _⟩

variable {G : List GC} {out : Map Blob} {done : List Nat} {nex : Nat}

/-- A block of the blocks so far is a head or a node of a chain done, or the
block of `bl` outside all of them. -/
theorem swi_cases (W : SWI bl topo G out done nex) {k : Nat} {b : Blob} (hb : HoonMap.get out k = some b) :
    (∃ g ∈ G, (∀ j ∈ getJmps b.fin, g.J j.there) ∧
      ∀ r ∈ blobMentions b, r ∈ g.S ∨ ∃ b0, HoonMap.get bl g.o = some b0 ∧ r ∈ blobMentions b0) ∨
    (HoonMap.get bl k = some b ∧ ∀ g ∈ G, k ≠ g.o ∧ ¬ g.In k) := by
  by_cases hA : ∃ g ∈ G, k = g.o ∨ g.In k
  · obtain ⟨g, hg, e | e⟩ := hA
    · subst e
      obtain ⟨b0, b', hb0, hb', -, hj, hm⟩ := W.head g hg
      rw [hb'] at hb; cases hb
      refine Or.inl ⟨g, hg, fun j h => (hj j h).2, fun r hr => ?_⟩
      rcases hm r hr with h1 | h1
      · exact Or.inr ⟨b0, hb0, h1⟩
      · exact Or.inl h1
    · have hn := W.node g hg k b e hb
      exact Or.inl ⟨g, hg, fun j h => (hn.2.1 j h).2, fun r hr => Or.inl (hn.2.2 r hr)⟩
  · have hs : ∀ g ∈ G, k ≠ g.o ∧ ¬ g.In k := fun g hg => ⟨fun e => hA ⟨g, hg, Or.inl e⟩, fun e => hA ⟨g, hg, Or.inr e⟩⟩
    rw [W.same k hs] at hb
    exact Or.inr ⟨hb, hs⟩

theorem gJ_topo (ht : TopoOK bl topo) {g : GC} (H : GOK bl topo g) {x : Nat} (hx : g.J x) :
    x ∈ topo ∨ (g.n1 ≤ x ∧ x < g.n2) := by
  rcases hx with (hx | hx) | hx
  · exact Or.inl ((gok_topo ht H).1 x (List.mem_cons_of_mem _ hx))
  · exact Or.inr hx
  · exact Or.inl ((gok_topo ht H).2 x hx)

/-- **A block reachable in the blocks so far is a member of `topo` or a label
a plain chain took.** -/
theorem swi_reach (W : SWI bl topo G out done nex) (ht : TopoOK bl topo) :
    ∀ k, Reach out k → k ∈ topo ∨ ∃ g ∈ G, g.n1 ≤ k ∧ k < g.n2 := by
  intro k hk
  induction hk with
  | zero => obtain ⟨-, h0, -⟩ := ht; cases topo with
    | nil => simp at h0
    | cons a t => simp at h0; subst h0; exact Or.inl List.mem_cons_self
  | @jump o' b j _ hb hj ih =>
    rcases swi_cases W hb with ⟨g, hg, hJ, -⟩ | ⟨hbl, hnot⟩
    · rcases gJ_topo ht (W.ok g hg) (hJ j hj) with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨g, hg, h1⟩
    · rcases ih with h1 | ⟨g, hg, h1⟩
      · exact Or.inl (topo_jump ht h1 hbl hj).1
      · exact absurd (Or.inr h1) (hnot g hg).2

theorem gJ_lt (ht : TopoOK bl topo) (W : SWI bl topo G out done nex) {g : GC} (hg : g ∈ G) {x : Nat}
    (hx : g.J x) : x < nex := by
  rcases gJ_topo ht (W.ok g hg) hx with h1 | h1
  · have := topo_lt ht h1; have := W.nb; omega
  · have := W.fr g hg; omega

/-- The labels of a later chain are outside the chains done. -/
theorem swi_out (ht : TopoOK bl topo) (W : SWI bl topo G out done nex) {Y : GC} (HY : GOK bl topo Y)
    (hrk : ∀ g ∈ G, rk topo g.o < rk topo Y.o) (hoR : ∀ g ∈ G, Y.o ∉ g.R) :
    ∀ x, (x ∈ Y.o :: Y.R ∨ x ∈ Y.X) → HoonMap.get out x = HoonMap.get bl x := by
  intro x hx
  refine W.same x fun g hg => ?_
  obtain ⟨hxT, hxR, hxr⟩ := (gc_disj ht (W.ok g hg) HY (hrk g hg) (hoR g hg)).1 x hx
  refine ⟨fun e => by rw [e] at hxr; omega, fun hI => ?_⟩
  rcases hI with hI | hI
  · exact hxR hI
  · have := topo_lt ht hxT; have := (W.ok g hg).fresh; omega

/-- **`TagHyp` carried from `bl` to the blocks so far.** -/
theorem tagHyp_outG (W : SWI bl topo G out done nex) (ht : TopoOK bl topo) {o : Nat} {u0 : STest}
    {ul : List STest} (h : chainOf bl (revCfg bl topo) fuel o = some (u0 :: ul)) (ho : o ∈ topo)
    (hrk : ∀ g ∈ G, rk topo g.o < rk topo o) (hoR : ∀ g ∈ G, o ∉ g.R) : TagHyp out o u0 ul := by
  have Hb := tagHyp_of ht ho h
  have hc := chainOf_rev fuel o _ h
  have HY := tagGC_ok ht ho h
  have D := fun g (hg : g ∈ G) => gc_disj ht (W.ok g hg) HY (hrk g hg) (hoR g hg)
  have sY := swi_out ht W HY hrk hoR
  have sI : ∀ k, TagIn u0 ul k → HoonMap.get out k = HoonMap.get bl k := fun k hk =>
    sY k (Or.inl (List.mem_cons_of_mem _ ((tagIn_iff o u0 ul k).mp hk)))
  have sX : ∀ k, k ∈ (tagGC bl o u0 ul).X → HoonMap.get out k = HoonMap.get bl k := fun k hk => sY k (Or.inr hk)
  refine ⟨Hb.nd, Hb.hy, Hb.ho, Hb.hoy, Hb.hr, ?_, by rw [sY o (Or.inl List.mem_cons_self)]; exact Hb.headFin,
    fun t ht' => ?_, ?_, ?_, ?_, Hb.zero⟩
  · exact tagBlocks_congr _ Hb.blocks (fun t ht' => sI _ ((tagIn_iff o u0 ul _).mpr (y_mem_tail o _ t ht')))
      (fun t ht' => sI _ (Or.inr (List.mem_append_right _ (List.mem_map_of_mem ht'))))
  · refine ⟨?_, (Hb.hits t ht').2⟩
    rw [sX _ (List.mem_append_left _ (List.mem_map_of_mem ht'))]; exact (Hb.hits t ht').1
  · refine ⟨?_, Hb.miss.2⟩
    rw [sX _ (List.mem_append_right _ (List.mem_singleton_self _))]; exact Hb.miss.1
  · intro k b j hk hkI hko hb hj hjI
    have hjR : j.there ∈ (tagGC bl o u0 ul).R := (tagIn_iff o u0 ul _).mp hjI
    rcases swi_cases W hb with ⟨g, hg, hJ, -⟩ | ⟨hbl, hnot⟩
    · exact (D g hg).2.1 _ (hJ j hj) hjR
    · have hkT : k ∈ topo := by
        rcases swi_reach W ht k hk with h1 | ⟨g, hg, h1⟩
        · exact h1
        · exact absurd (Or.inr h1) (hnot g hg).2
      rcases List.mem_cons.mp (HY.into k b j hkT hbl hj hjR) with e | e
      · exact hko e
      · exact hkI ((tagIn_iff o u0 ul k).mpr e)
  · intro k b _ hkI hb r hr hrT
    rcases swi_cases W hb with ⟨g, hg, -, hM⟩ | ⟨hbl, -⟩
    · rcases hM r hr with hS | ⟨b0, hb0, hm0⟩
      · exact (D g hg).2.2.1 r hS hrT
      · exact HY.excl g.o b0 (D g hg).2.2.2 hb0 r hm0 hrT
    · exact tag_ment_bl hc k b hkI hbl r hr hrT

/-- **`PlainHyp` carried from `bl` to the blocks so far.** -/
theorem plainHyp_outG (W : SWI bl topo G out done nex) (ht : TopoOK bl topo) {o : Nat} {p0 : Nat × SPlain}
    {pl : List (Nat × SPlain)} (h : plainsOf bl (revCfg bl topo) fuel o = some (p0 :: pl)) (ho : o ∈ topo)
    (hpl : pl ≠ []) (hrk : ∀ g ∈ G, rk topo g.o < rk topo o) (hoR : ∀ g ∈ G, o ∉ g.R) :
    PlainHyp out o nex p0 pl := by
  have Hp := plainHyp_of ht ho h hpl W.nb
  have HY := plainGC_ok ht ho h W.nb (nex' := nex)
  have D := fun g (hg : g ∈ G) => gc_disj ht (W.ok g hg) HY (hrk g hg) (hoR g hg)
  have sY := swi_out ht W HY hrk hoR
  have sX : ∀ k, k ∈ (plainGC o nex nex p0 pl).X → HoonMap.get out k = HoonMap.get bl k :=
    fun k hk => sY k (Or.inr hk)
  have hnex := W.nb
  refine ⟨Hp.nd, Hp.old, Hp.ho, Hp.ho', Hp.hr, ?_, Hp.miss0, ?_, fun t ht' => ?_, ?_, ?_, ?_, Hp.zero⟩
  · exact plainBlocks_congr _ Hp.blocks
      (fun t ht' => sY _ (Or.inl (List.mem_cons_of_mem _ (List.mem_map_of_mem ht'))))
  · obtain ⟨b, l, r, hb, rest⟩ := Hp.headB
    exact ⟨b, l, r, by rw [sY o (Or.inl List.mem_cons_self)]; exact hb, rest⟩
  · refine ⟨?_, (Hp.hits t ht').2⟩
    rw [sX _ (List.mem_append_left _ (List.mem_map_of_mem ht'))]; exact (Hp.hits t ht').1
  · refine ⟨?_, Hp.miss.2⟩
    rw [sX _ (List.mem_append_right _ (List.mem_singleton_self _))]; exact Hp.miss.1
  · intro k b j hk hkI hko hb hj hjI
    rcases swi_cases W hb with ⟨g, hg, hJ, -⟩ | ⟨hbl, hnot⟩
    · rcases hjI with hjI | hjI
      · exact (D g hg).2.1 _ (hJ j hj) hjI
      · have := gJ_lt ht W hg (hJ j hj); omega
    · have hkT : k ∈ topo := by
        rcases swi_reach W ht k hk with h1 | ⟨g, hg, h1⟩
        · exact h1
        · exact absurd (Or.inr h1) (hnot g hg).2
      rcases hjI with hjI | hjI
      · rcases List.mem_cons.mp (HY.into k b j hkT hbl hj hjI) with e | e
        · exact hko e
        · exact hkI (Or.inl e)
      · have := topo_lt ht (topo_jump ht hkT hbl hj).1; omega
  · intro k b _ hkI hko hb r hr hrT
    rcases swi_cases W hb with ⟨g, hg, -, hM⟩ | ⟨hbl, -⟩
    · rcases hM r hr with hS | ⟨b0, hb0, hm0⟩
      · exact (D g hg).2.2.1 r hS hrT
      · exact HY.excl g.o b0 (D g hg).2.2.2 hb0 r hm0 hrT
    · have hkn : k ∉ o :: pl.map Prod.fst := by
        intro e
        rcases List.mem_cons.mp e with e | e
        · exact hko e
        · exact hkI (Or.inl e)
      exact HY.excl k b hkn hbl r hr hrT

end

/-! ## One chain of the walk -/

section
variable {bl : Map Blob} {topo : List Nat} {fuel : Nat} {G : List GC} {out : Map Blob} {done : List Nat}
  {nex : Nat}

theorem yshape_y0 {rev : Map (List Nat)} {n o : Nat} {u0 : STest} {ul : List STest}
    (h : chainOf bl rev n o = some (u0 :: ul)) (hul : ul ≠ []) : YShape bl u0.y := by
  obtain ⟨hTB, -⟩ := tagHyp_shape h
  obtain ⟨-, -, -, -, ⟨l, r, body, hyb, -, -⟩, hnext, -⟩ := hTB
  cases ul with
  | nil => exact absurd rfl hul
  | cons u1 ul' =>
    simp only at hnext
    exact ⟨_, l, r, u0.hit, u0.miss, _, hyb, rfl, hnext, rfl⟩

theorem yshape_not_tag {rev : Map (List Nat)} {n o : Nat} {u0 : STest} {ul : List STest} (hy : YShape bl o)
    (h : chainOf bl rev n o = some (u0 :: ul)) : False := by
  obtain ⟨⟨b, hb, hf⟩, -⟩ := chainOf_spec n o u0 ul h
  obtain ⟨b', l, r, h', m, mb, hb', hf', -⟩ := hy
  rw [hb] at hb'; cases hb'
  rw [hf] at hf'; cases hf'

theorem yshape_not_plain {rev : Map (List Nat)} {n o : Nat} {p0 : Nat × SPlain} {pl : List (Nat × SPlain)}
    (hy : YShape bl o) (h : plainsOf bl rev n o = some (p0 :: pl)) (hpl : pl ≠ []) : False := by
  have hc := plainsOf_rev n o _ h
  obtain ⟨b, l, r, hb, hfin, -⟩ := plainOf_spec hc.2.1
  obtain ⟨-, nb, n', x, hnb, -, hbody⟩ := hc.2.2.1 hpl
  obtain ⟨b', l', r', h', m, mb, hb', hf', hmb, hmbody⟩ := hy
  rw [hb] at hb'; cases hb'
  rw [hfin] at hf'
  simp only [Termin.eqq.injEq, Jmp.mk.injEq, true_and] at hf'
  obtain ⟨-, -, -, e⟩ := hf'
  rw [← e, hnb] at hmb
  cases hmb
  rw [hbody] at hmbody
  cases hmbody

/-- **One tagged chain of the walk**: the invariant and `Keeps` go on. -/
theorem swi_tag_step (c : Straight Map) (W : SWI bl topo G out done nex) (K : Keeps c (withBlocks c out))
    (ht : TopoOK bl topo) {o : Nat} {u0 : STest} {ul : List STest}
    (h : chainOf bl (revCfg bl topo) fuel o = some (u0 :: ul)) (hul : ul ≠ []) (ho : o ∈ topo)
    (hrk : ∀ g ∈ G, rk topo g.o < rk topo o) (hoR : ∀ g ∈ G, o ∉ g.R) {out' : Map Blob} {done' : List Nat}
    (hs : switchTag bl out fuel o (u0 :: ul) done = some (out', done')) :
    SWI bl topo (G ++ [tagGC bl o u0 ul]) out' done' nex ∧ Keeps c (withBlocks c out') := by
  have H := tagHyp_outG W ht h ho hrk hoR
  have HY := tagGC_ok ht ho h
  have D := fun g (hg : g ∈ G) => gc_disj ht (W.ok g hg) HY (hrk g hg) (hoR g hg)
  have hob : HoonMap.get bl o = HoonMap.get out o :=
    (swi_out ht W HY hrk hoR o (Or.inl List.mem_cons_self)).symm
  have hs' : switchTag out out fuel o (u0 :: ul) done = some (out', done') := by
    rw [← switchTag_out hob]; exact hs
  obtain ⟨b, nb, nf, hb, hbo, -, -, hfr, hdone⟩ := tag_tree hs' H.nd H.hy H.ho H.hoy H.hr
  have hbl : HoonMap.get bl o = some b := by rw [hob]; exact hb
  have nodes := tag_nodes hs' H.ho H.hoy
  have K' := tag_keeps_of (withBlocks c out) hs' H
  have frO : ∀ k, k ≠ o → k ∉ (tagGC bl o u0 ul).R → HoonMap.get out' k = HoonMap.get out k :=
    fun k h1 h2 => hfr k h1 (fun e => h2 ((tagIn_iff o u0 ul k).mp (Or.inl e)))
      (fun e => h2 ((tagIn_iff o u0 ul k).mp (Or.inr e)))
  have hoT := topo_lt ht ho
  have hnb := W.nb
  have hnew : ∀ g, g ∈ G ++ [tagGC bl o u0 ul] → g ∈ G ∨ g = tagGC bl o u0 ul := by
    intro g hg; simpa using hg
  have oldIn : ∀ g ∈ G, ∀ k, (k = g.o ∨ g.In k) → k ≠ o ∧ k ∉ (tagGC bl o u0 ul).R := by
    intro g hg k hk
    rcases hk with e | hk
    · rw [e]
      exact ⟨fun e2 => by have := hrk g hg; rw [e2] at this; omega,
        fun hR => (D g hg).2.2.2 (List.mem_cons_of_mem _ hR)⟩
    · refine ⟨fun e => ?_, (D g hg).2.1 k (Or.inl hk)⟩
      rw [e] at hk
      rcases hk with hk | hk
      · exact hoR g hg hk
      · have := (W.ok g hg).fresh; omega
  refine ⟨⟨fun g hg => ?_, fun g hg k hk => ?_, fun k hk => ?_, fun g hg => ?_, fun g hg k b' hkI hb' => ?_,
    fun k hk => ?_, fun g hg => ?_, W.nb⟩, keeps_trans K K'⟩
  · rcases hnew g hg with hg | e
    · exact W.ok g hg
    · rw [e]; exact HY
  · rw [hdone]
    rcases hnew g hg with hg | e
    · rcases W.dn g hg k hk with h1 | h1
      · exact Or.inl (List.mem_append_right _ h1)
      · exact Or.inr h1
    · rw [e] at hk
      change k ∈ u0.y :: ilabs u0.miss ul at hk
      rcases List.mem_cons.mp hk with e2 | e2
      · rw [e2]; exact Or.inr (yshape_y0 h hul)
      · exact Or.inl (List.mem_append_left _ ((ilabs_perm u0 ul).mem_iff.mp e2))
  · have h1 := hk _ (List.mem_append_right _ (List.mem_singleton_self _))
    rw [frO k h1.1 (fun hR => h1.2 (Or.inl hR))]
    exact W.same k fun g hg => hk g (List.mem_append_left _ hg)
  · rcases hnew g hg with hg | e
    · obtain ⟨e1, e2⟩ := oldIn g hg g.o (Or.inl rfl)
      rw [frO g.o e1 e2]
      exact W.head g hg
    · rw [e]
      refine ⟨b, _, hbl, hbo, rfl, fun j hj => ?_, fun r hr => ?_⟩
      · simp only [getJmps, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with e3 | e3 <;> rw [e3]
        · exact ⟨rfl, Or.inl (Or.inl List.mem_cons_self)⟩
        · exact ⟨rfl, Or.inr (List.mem_append_right _ (List.mem_singleton_self _))⟩
      · simp only [blobMentions, List.mem_append] at hr
        rcases hr with (h1 | h1) | h1
        · exact Or.inl (by simp only [blobMentions, List.mem_append]; exact Or.inl (Or.inl h1))
        · simp [finRegs, jmpRegs] at h1
          rw [h1]; exact Or.inr List.mem_cons_self
        · exact Or.inl (by simp only [blobMentions, List.mem_append]; exact Or.inr h1)
  · rcases hnew g hg with hg | e
    · obtain ⟨e1, e2⟩ := oldIn g hg k (Or.inr hkI)
      rw [frO k e1 e2] at hb'
      exact W.node g hg k b' hkI hb'
    · rw [e] at hkI ⊢
      have hk' : k ∈ (tagGC bl o u0 ul).R := by
        rcases hkI with h1 | h1
        · exact h1
        · simp only [tagGC] at h1; omega
      refine nodeOK_mono (nodes k b' ((tagIn_iff o u0 ul k).mpr hk') hb') (fun x hx => ?_) (fun r hr => ?_)
      · rcases hx with hx | ⟨t, ht', e3⟩ | e3
        · exact Or.inl (Or.inl ((tagIn_iff o u0 ul x).mp hx))
        · rw [e3]; exact Or.inr (List.mem_append_left _ (List.mem_map_of_mem ht'))
        · rw [e3]; exact Or.inr (List.mem_append_right _ (List.mem_singleton_self _))
      · rcases hr with e3 | hr
        · rw [e3]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ hr
  · have hko : k ≠ o := fun e => by omega
    have hkR : k ∉ (tagGC bl o u0 ul).R := fun hR => by
      have := topo_lt ht ((gok_topo ht HY).1 k (List.mem_cons_of_mem _ hR)); omega
    rw [frO k hko hkR]; exact W.above k hk
  · rcases hnew g hg with hg | e
    · exact W.fr g hg
    · rw [e]; exact W.nb

/-- **One plain chain of the walk**: the invariant and `Keeps` go on. -/
theorem swi_plain_step (c : Straight Map) (W : SWI bl topo G out done nex) (K : Keeps c (withBlocks c out))
    (ht : TopoOK bl topo) {o : Nat} {p0 : Nat × SPlain} {pl : List (Nat × SPlain)}
    (h : plainsOf bl (revCfg bl topo) fuel o = some (p0 :: pl)) (hpl : pl ≠ []) (ho : o ∈ topo)
    (hrk : ∀ g ∈ G, rk topo g.o < rk topo o) (hoR : ∀ g ∈ G, o ∉ g.R) {out' : Map Blob} {done' : List Nat}
    {nex' : Nat} (hs : switchPlain bl out fuel o (p0 :: pl) done nex = some (out', done', nex')) :
    SWI bl topo (G ++ [plainGC o nex nex' p0 pl]) out' done' nex' ∧ Keeps c (withBlocks c out') := by
  have H := plainHyp_outG W ht h ho hpl hrk hoR
  have HY := plainGC_ok ht ho h W.nb (nex' := nex')
  have D := fun g (hg : g ∈ G) => gc_disj ht (W.ok g hg) HY (hrk g hg) (hoR g hg)
  have hob : HoonMap.get bl o = HoonMap.get out o :=
    (swi_out ht W HY hrk hoR o (Or.inl List.mem_cons_self)).symm
  have hs' : switchPlain out out fuel o (p0 :: pl) done nex = some (out', done', nex') := by
    rw [← switchPlain_out hob]; exact hs
  obtain ⟨b, nb, nf, hb, hbo, hroot, hnodes, hfr, habove, hle, hdone⟩ :=
    plain_tree2 hs' H.old H.ho H.ho' W.above
  have hbl : HoonMap.get bl o = some b := by rw [hob]; exact hb
  have K' := plain_keeps_of (withBlocks c out) hs' H
  have hoT := topo_lt ht ho
  have hnb := W.nb
  have hnew : ∀ g, g ∈ G ++ [plainGC o nex nex' p0 pl] → g ∈ G ∨ g = plainGC o nex nex' p0 pl := by
    intro g hg; simpa using hg
  have oldIn : ∀ g ∈ G, ∀ k, (k = g.o ∨ g.In k) → k ≠ o ∧ ¬ PRg nex nex' pl k := by
    intro g hg k hk
    have hlt : k < nex := by
      rcases hk with e | hk
      · rw [e]; have := topo_lt ht (W.ok g hg).ho; omega
      · exact gJ_lt ht W hg (Or.inl hk)
    have hkR : k ∉ pl.map Prod.fst := by
      rcases hk with e | hk
      · rw [e]; exact fun hR => (D g hg).2.2.2 (List.mem_cons_of_mem _ hR)
      · exact (D g hg).2.1 k (Or.inl hk)
    refine ⟨fun e => ?_, fun hP => ?_⟩
    · rcases hk with e2 | hk
      · have := hrk g hg; rw [← e2, e] at this; omega
      · rw [e] at hk
        rcases hk with hk | hk
        · exact hoR g hg hk
        · have := (W.ok g hg).fresh; omega
    · rcases hP with hP | hP
      · exact hkR hP
      · omega
  have pj : ∀ x, PJ nex nex' p0 pl x → (plainGC o nex nex' p0 pl).J x := by
    intro x hx
    rcases hx with hx | ⟨t, ht', e3⟩ | e3
    · exact Or.inl hx
    · rw [e3]; exact Or.inr (List.mem_append_left _ (List.mem_map_of_mem (f := fun t => t.2.hit) ht'))
    · rw [e3]; exact Or.inr (List.mem_append_right _ (List.mem_singleton_self _))
  have ps : ∀ r, PS p0 pl r → r ∈ (plainGC o nex nex' p0 pl).S := by
    intro r hr
    rcases hr with e3 | hr
    · rw [e3]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ hr
  refine ⟨⟨fun g hg => ?_, fun g hg k hk => ?_, fun k hk => ?_, fun g hg => ?_, fun g hg k b' hkI hb' => ?_,
    habove, fun g hg => ?_, Nat.le_trans W.nb hle⟩, keeps_trans K K'⟩
  · rcases hnew g hg with hg | e
    · exact W.ok g hg
    · rw [e]; exact HY
  · rw [hdone]
    rcases hnew g hg with hg | e
    · rcases W.dn g hg k hk with h1 | h1
      · exact Or.inl (List.mem_append_right _ h1)
      · exact Or.inr h1
    · rw [e] at hk
      exact Or.inl (List.mem_append_left _ hk)
  · have h1 := hk _ (List.mem_append_right _ (List.mem_singleton_self _))
    rw [hfr k h1.1 h1.2]
    exact W.same k fun g hg => hk g (List.mem_append_left _ hg)
  · rcases hnew g hg with hg | e
    · obtain ⟨e1, e2⟩ := oldIn g hg g.o (Or.inl rfl)
      rw [hfr g.o e1 e2]
      exact W.head g hg
    · rw [e]
      refine ⟨b, _, hbl, hbo, rfl, fun j hj => ⟨(hroot.2.1 j hj).1, pj _ (hroot.2.1 j hj).2⟩, fun r hr => ?_⟩
      simp only [blobMentions, List.mem_append, List.flatMap_append] at hr
      rcases hr with (h1 | h1) | (h1 | h1)
      · exact Or.inl (by simp only [blobMentions, List.mem_append]; exact Or.inl (Or.inl h1))
      · exact Or.inr (ps r (hroot.2.2 r (by simp only [blobMentions, List.mem_append]; exact Or.inl (Or.inr h1))))
      · obtain ⟨p, hp, hrp⟩ := List.mem_flatMap.mp h1
        exact Or.inl (by
          simp only [blobMentions, List.mem_append]
          exact Or.inr (List.mem_flatMap.mpr ⟨p, (List.mem_filter.mp hp).1, hrp⟩))
      · exact Or.inr (ps r (hroot.2.2 r (by simp only [blobMentions, List.mem_append]; exact Or.inr h1)))
  · rcases hnew g hg with hg | e
    · obtain ⟨e1, e2⟩ := oldIn g hg k (Or.inr hkI)
      rw [hfr k e1 e2] at hb'
      exact W.node g hg k b' hkI hb'
    · rw [e] at hkI ⊢
      exact nodeOK_mono (hnodes k b' hkI hb') pj ps
  · rcases hnew g hg with hg | e
    · exact Nat.le_trans (W.fr g hg) hle
    · rw [e]; exact Nat.le_refl _

end

/-! ## The walk -/

section
variable {bl : Map Blob} {topo : List Nat} {fuel : Nat}

/-- **The walk keeps the code**: from any point of `topo`, with the invariant
and `Keeps` so far. -/
theorem switchWalk_all (c : Straight Map) (ht : TopoOK bl topo) :
    ∀ (rest pre : List Nat) (G : List GC) (out : Map Blob) (done : List Nat) (nex : Nat) (outF : Map Blob),
      topo = pre ++ rest → (∀ g ∈ G, g.o ∈ pre) → SWI bl topo G out done nex → Keeps c (withBlocks c out) →
      switchWalk bl (revCfg bl topo) fuel rest out done nex = some outF → Keeps c (withBlocks c outF)
  | [], _, _, out, _, _, outF, _, _, _, K, h => by
    simp only [switchWalk, Option.some.injEq] at h; subst h; exact K
  | o :: rest, pre, G, out, done, nex, outF, htp, hpre, W, K, h => by
    have hoT : o ∈ topo := by rw [htp]; simp
    have htp' : topo = (pre ++ [o]) ++ rest := by rw [htp]; simp
    have hpre' : ∀ g ∈ G, g.o ∈ pre ++ [o] := fun g hg => List.mem_append_left _ (hpre g hg)
    have hnd : (pre ++ o :: rest).Nodup := by rw [← htp]; exact ht.1
    have hop : o ∉ pre := fun hm => (List.nodup_append.mp hnd).2.2 o hm o List.mem_cons_self rfl
    have hrk : ∀ g ∈ G, rk topo g.o < rk topo o := fun g hg => by
      rw [htp]; exact rk_pre pre (hpre g hg) hop
    unfold switchWalk at h
    split at h
    · exact switchWalk_all c ht rest (pre ++ [o]) G out done nex outF htp' hpre' W K h
    rename_i hod
    have hY : ∀ g ∈ G, o ∈ g.R → YShape bl o := fun g hg hR => (W.dn g hg o hR).resolve_left hod
    obtain ⟨cs, hcs, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i hlen
      cases cs with
      | nil => simp at hlen
      | cons u0 ul =>
      have hul : ul ≠ [] := by rintro rfl; simp at hlen
      cases hst : switchTag bl out fuel o (u0 :: ul) done with
      | none => simp [hst] at h
      | some r =>
      obtain ⟨out', done'⟩ := r
      simp only [hst, Option.bind_some] at h
      have hoR : ∀ g ∈ G, o ∉ g.R := fun g hg hR => yshape_not_tag (hY g hg hR) hcs
      obtain ⟨W', K'⟩ := swi_tag_step c W K ht hcs hul hoT hrk hoR hst
      refine switchWalk_all c ht rest (pre ++ [o]) _ out' done' nex outF htp' (fun g hg => ?_) W' K' h
      rcases List.mem_append.mp hg with hg | hg
      · exact hpre' g hg
      · simp only [List.mem_singleton] at hg; rw [hg]; simp [tagGC]
    · obtain ⟨ps, hps, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · exact switchWalk_all c ht rest (pre ++ [o]) G out done nex outF htp' hpre' W K h
      · rename_i hl
        cases ps with
        | nil => simp at hl
        | cons p0 pl =>
        have hpl : pl ≠ [] := by rintro rfl; simp at hl
        cases hsp : switchPlain bl out fuel o (p0 :: pl) done nex with
        | none => simp [hsp] at h
        | some r =>
        obtain ⟨out', done', nex'⟩ := r
        simp only [hsp, Option.bind_some] at h
        have hoR : ∀ g ∈ G, o ∉ g.R := fun g hg hR => yshape_not_plain (hY g hg hR) hps hpl
        obtain ⟨W', K'⟩ := swi_plain_step c W K ht hps hpl hoT hrk hoR hsp
        refine switchWalk_all c ht rest (pre ++ [o]) _ out' done' nex' outF htp' (fun g hg => ?_) W' K' h
        rcases List.mem_append.mp hg with hg | hg
        · exact hpre' g hg
        · simp only [List.mem_singleton] at hg; rw [hg]; simp [plainGC]

/-- **`+switch-chains` keeps the code** on blocks with `DInv`. -/
theorem switchChains_keeps (c : Straight Map) {fuel : Nat} {bl' : Map Blob} (hb : DInv c.blocks)
    (h : switchChains fuel c.blocks = some bl') : Keeps c (withBlocks c bl') := by
  obtain ⟨topo, htopo, h⟩ := Option.bind_eq_some_iff.mp h
  have ht := bbTopo_ok hb.2.1 htopo
  have K0 : Keeps c (withBlocks c c.blocks) := keeps_refl c
  exact switchWalk_all c ht topo [] [] c.blocks [] _ bl' rfl (fun g hg => absurd hg List.not_mem_nil)
    (swi_nil _ _) K0 h

/-- **`SwitchKeepsM`**: the model of `+switch-chains` keeps the code on blocks
with `DInv`. -/
theorem switchKeepsM (fuel : Nat) : SwitchKeepsM (Map := Map) fuel :=
  fun c _ hb h => switchChains_keeps c hb h

end

end Opt
end SkaModel
end Formalization
