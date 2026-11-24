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

end Opt
end SkaModel
end Formalization
