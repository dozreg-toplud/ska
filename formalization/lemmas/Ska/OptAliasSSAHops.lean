import lemmas.Ska.OptAliasSSADriver
import lemmas.Ska.OptHopsBlocks

/-!
# `+remove-hops` keeps `DefFirst`

**`ssk_hops_first`**: after `+remove-hops` every block is a merge of a chain of
blocks before (`MTail`), the body of each next block preceded by the moves of
the hop into it, which define its parameters (`ssk_seg_defs`) and read the
hop's arguments (`ssk_seg_ops`).  A read of the merged block is a read before:
in the first block, by a move (a read of the end of the block before it), or
in the rest of the chain, and `ssk_mt_first` (by induction on `MTail`) turns
`DefFirst` before on the chain into `DefFirst` of the merged block; a path
after lifts to a path before through the chains (`ssk_mt_path`), every
definition of a chain member being one of the merged block.

`DefOnceB` after the pass is left: it needs the positions of the merged body
mapped injectively to definitions before, the chains of two reachable merged
blocks disjoint (a chain member's one predecessor in `rev` is consumed by the
merge), and a dead fill kept at the end of the merged body.  So the driver
theorem **`optimize_keeps_ssaO`** assumes of the passes of the loop only
`HopsOnce`: that `+remove-hops` gives `DefOnceB` on `AliasSSAB` input.
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock
variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

set_option linter.unusedSectionVars false

/-- The moves of a merged hop define its target's parameters. -/
theorem ssk_seg_defs : ∀ (as : List (Option Nat)) (ps : List Nat) (acc ops : List Pole),
    hopSeg as ps acc = some ops → ∀ p, (p ∈ ps ∨ p ∈ acc.filterMap aliasDst) → p ∈ ops.filterMap aliasDst
  | [], [], acc, ops, h, p, hp => by
    simp only [hopSeg, Option.some.injEq] at h; subst h
    rcases hp with hp | hp
    · cases hp
    · exact hp
  | [], _ :: _, _, _, h, _, _ => by simp [hopSeg] at h
  | _ :: _, [], _, _, h, _, _ => by simp [hopSeg] at h
  | a :: as, q :: ps, acc, ops, h, p, hp => by
    simp only [hopSeg] at h
    refine ssk_seg_defs as ps _ ops h p ?_
    rcases hp with hp | hp
    · rcases List.mem_cons.mp hp with rfl | hp
      · right; cases a <;> simp [aliasDst]
      · left; exact hp
    · right; cases a <;> simp [aliasDst, List.mem_filterMap] at hp ⊢ <;> exact Or.inr hp

/-- A move of a merged hop reads an argument and writes a parameter. -/
theorem ssk_seg_ops : ∀ (as : List (Option Nat)) (ps : List Nat) (acc ops : List Pole),
    hopSeg as ps acc = some ops → ∀ op ∈ ops, op ∈ acc ∨
      ((∀ x ∈ aliasReads op, some x ∈ as) ∧ ∀ d, aliasDst op = some d → d ∈ ps)
  | [], [], acc, ops, h, op, hop => by
    simp only [hopSeg, Option.some.injEq] at h; subst h; exact Or.inl hop
  | [], _ :: _, _, _, h, _, _ => by simp [hopSeg] at h
  | _ :: _, [], _, _, h, _, _ => by simp [hopSeg] at h
  | a :: as, q :: ps, acc, ops, h, op, hop => by
    simp only [hopSeg] at h
    rcases ssk_seg_ops as ps _ ops h op hop with h1 | ⟨h1, h2⟩
    · rcases List.mem_cons.mp h1 with rfl | h1
      · right
        cases a with
        | none =>
          refine ⟨fun x hx => ?_, fun d hd => ?_⟩
          · simp [aliasReads, aliasDst, poleRegs] at hx
          · simp only [aliasDst, Option.some.injEq] at hd; subst hd; exact List.mem_cons_self
        | some r =>
          refine ⟨fun x hx => ?_, fun d hd => ?_⟩
          · simp only [aliasReads, aliasDst, poleRegs] at hx
            by_cases hxr : x = r
            · subst hxr; exact List.mem_cons_self
            · exfalso
              by_cases hrq : r = q <;> simp_all [List.erase_cons]
          · simp only [aliasDst, Option.some.injEq] at hd; subst hd; exact List.mem_cons_self
      · exact Or.inl h1
    · exact Or.inr ⟨fun x hx => List.mem_cons_of_mem _ (h1 x hx), fun d hd => List.mem_cons_of_mem _ (h2 d hd)⟩

/-- A read of a body `A ++ B`: in `A`, or a read of `B` shifted. -/
theorem ssk_readAt_app {A B : List Pole} {par : List Nat} {F : Termin} {i r : Nat}
    (h : ReadAt ⟨par, A ++ B, F⟩ i r) :
    (i < A.length ∧ r ∈ ((A.drop i).head?.map aliasReads).getD []) ∨
      (A.length ≤ i ∧ ReadAt ⟨par, B, F⟩ (i - A.length) r) := by
  rcases h with h | ⟨hi, h⟩
  · simp only at h; rw [List.head?_drop] at h
    by_cases hi : i < A.length
    · left; refine ⟨hi, ?_⟩; rw [List.head?_drop]; rwa [List.getElem?_append_left hi] at h
    · right; refine ⟨by omega, Or.inl ?_⟩
      simp only; rw [List.head?_drop]; rwa [List.getElem?_append_right (by omega)] at h
  · right; simp only [List.length_append] at hi
    exact ⟨by omega, Or.inr ⟨by simp only; omega, h⟩⟩

theorem ssk_take_left {A B : List Pole} {i r : Nat} (h : r ∈ (A.take i).filterMap aliasDst) :
    r ∈ ((A ++ B).take i).filterMap aliasDst := by
  rw [List.take_append, List.filterMap_append]; exact List.mem_append_left _ h

theorem ssk_take_right {A B : List Pole} {i r : Nat} (hi : A.length ≤ i)
    (h : r ∈ A.filterMap aliasDst ∨ r ∈ (B.take (i - A.length)).filterMap aliasDst) :
    r ∈ ((A ++ B).take i).filterMap aliasDst := by
  rw [List.take_append, List.filterMap_append, List.take_of_length_le hi]
  rcases h with h | h
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ h

theorem ssk_read_op {A : List Pole} {i r : Nat} (h : r ∈ ((A.drop i).head?.map aliasReads).getD []) :
    ∃ op ∈ A, r ∈ aliasReads op := by
  cases e : (A.drop i).head? with
  | none => rw [e] at h; simp at h
  | some op =>
    rw [e] at h
    exact ⟨op, List.mem_of_mem_drop (List.mem_of_mem_head? e), h⟩

section
variable {bl : Map Blob} {rev : Map (List Nat)}

/-- **`DefFirst` of a merged block over paths before.** -/
theorem ssk_mt_first (h2 : DefFirst bl) {o : Nat} {b : Blob} {T : List Pole} {F : Termin}
    (hm : MTail bl rev o b T F) : HoonMap.get bl o = some b →
    ∀ i r q, ReadAt (merge b T F) i r → r ∈ allDefs bl → BPath bl (o :: q) →
      r ∈ b.par ∨ r ∈ ((b.body ++ T).take i).filterMap aliasDst ∨
        ∃ o' ∈ q, ∃ b', HoonMap.get bl o' = some b' ∧ r ∈ blockDefs b' := by
  induction hm with
  | @stop o b _ =>
    intro hb i r q hr hall hq
    have e : merge b [] b.fin = b := by simp [merge]
    rw [e] at hr
    rw [List.append_nil]
    exact h2 o q b hq hb i r hr hall
  | @link o b t b1 ops T F hfin _ hb1 hseg _ ih =>
    intro hb i r q hr hall hq
    have hq1 : BPath bl (t.there :: o :: q) := BPath.step hq hb (by rw [hfin]; simp [getJmps])
    have hbody : ∀ x, x ∈ b.body.filterMap aliasDst → b.body.length ≤ i →
        x ∈ ((b.body ++ (ops ++ b1.body ++ T)).take i).filterMap aliasDst :=
      fun x hx hi => ssk_take_right hi (Or.inl hx)
    rcases ssk_readAt_app (A := b.body) (B := ops ++ b1.body ++ T) hr with ⟨hi, hrd⟩ | ⟨hi, hrd⟩
    · rcases h2 o q b hq hb i r (Or.inl hrd) hall with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (ssk_take_left h))
      · exact Or.inr (Or.inr h)
    · rw [List.append_assoc] at hrd
      rcases ssk_readAt_app (A := ops) (B := b1.body ++ T) hrd with ⟨hi2, hrd2⟩ | ⟨hi2, hrd2⟩
      · -- a move reads an argument of the hop, read at the end of `o` before
        obtain ⟨op, hop, hrop⟩ := ssk_read_op hrd2
        rcases ssk_seg_ops t.args b1.par [] ops hseg op hop with h | ⟨h, -⟩
        · cases h
        · have hend : ReadAt b b.body.length r := Or.inr ⟨rfl, by rw [hfin]; exact mem_jmpRegs.mpr (h r hrop)⟩
          rcases h2 o q b hq hb _ r hend hall with h | h | h
          · exact Or.inl h
          · rw [List.take_length] at h; exact Or.inr (Or.inl (hbody r h hi))
          · exact Or.inr (Or.inr h)
      · rcases ih hb1 _ r (o :: q) hrd2 hall hq1 with h | h | ⟨o', ho', b', hb', hm⟩
        · -- a parameter of the next block: defined by a move
          refine Or.inr (Or.inl (ssk_take_right hi (Or.inr ?_)))
          rw [List.append_assoc]
          exact ssk_take_right hi2 (Or.inl (ssk_seg_defs _ _ _ _ hseg r (Or.inl h)))
        · refine Or.inr (Or.inl (ssk_take_right hi (Or.inr ?_)))
          rw [List.append_assoc]
          exact ssk_take_right hi2 (Or.inr (by rw [Nat.sub_sub] at h ⊢; exact h))
        · rcases List.mem_cons.mp ho' with rfl | ho'
          · rw [hb] at hb'; cases hb'
            simp only [blockDefs, List.mem_append] at hm
            rcases hm with hm | hm
            · exact Or.inl hm
            · exact Or.inr (Or.inl (hbody r hm hi))
          · exact Or.inr (Or.inr ⟨o', ho', b', hb', hm⟩)

/-- The end of a merged chain is the end of a block reached by a path through
the chain, and every definition of a chain member is one of the merged block. -/
theorem ssk_mt_path {o : Nat} {b : Blob} {T : List Pole} {F : Termin} (hm : MTail bl rev o b T F) :
    HoonMap.get bl o = some b → ∃ e be l, HoonMap.get bl e = some be ∧ F = be.fin ∧
      (∀ Q, BPath bl (o :: Q) → BPath bl (e :: (l ++ Q))) ∧
      ∀ x ∈ e :: l, ∀ bx, HoonMap.get bl x = some bx → ∀ r ∈ blockDefs bx, r ∈ blockDefs (merge b T F) := by
  induction hm with
  | @stop o b _ =>
    intro hb
    refine ⟨o, b, [], hb, rfl, fun Q h => h, fun x hx bx hbx r hr => ?_⟩
    rw [List.mem_singleton.mp hx, hb] at hbx; cases hbx
    simpa [blockDefs, merge] using hr
  | @link o b t b1 ops T F hfin _ hb1 hseg _ ih =>
    intro hb
    obtain ⟨e, be, l, hbe, hF, hP, hD⟩ := ih hb1
    refine ⟨e, be, l ++ [o], hbe, hF, fun Q hQ => ?_, fun x hx bx hbx r hr => ?_⟩
    · have := hP (o :: Q) (BPath.step hQ hb (by rw [hfin]; simp [getJmps]))
      simpa using this
    · have hsub : ∀ r, r ∈ blockDefs (merge b1 T F) → r ∈ blockDefs (merge b (ops ++ b1.body ++ T) F) := by
        intro r hr
        simp only [blockDefs, merge, List.filterMap_append, List.mem_append] at hr ⊢
        rcases hr with hr | hr | hr
        · exact Or.inr (Or.inr (Or.inl (Or.inl (ssk_seg_defs _ _ _ _ hseg r (Or.inl hr)))))
        · exact Or.inr (Or.inr (Or.inl (Or.inr hr)))
        · exact Or.inr (Or.inr (Or.inr hr))
      simp only [List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | hx | rfl
      · exact hsub r (hD _ List.mem_cons_self bx hbx r hr)
      · exact hsub r (hD x (List.mem_cons_of_mem _ hx) bx hbx r hr)
      · rw [hb] at hbx; cases hbx
        simp only [blockDefs, merge, List.filterMap_append, List.mem_append] at hr ⊢
        rcases hr with hr | hr
        · exact Or.inl hr
        · exact Or.inr (Or.inl hr)

/-- A definition of a merged block is a definition of a chain member. -/
theorem ssk_mt_defs {o : Nat} {b : Blob} {T : List Pole} {F : Termin} (hm : MTail bl rev o b T F) :
    HoonMap.get bl o = some b → ∀ r ∈ blockDefs (merge b T F), ∃ x bx, HoonMap.get bl x = some bx ∧ r ∈ blockDefs bx := by
  induction hm with
  | @stop o b _ =>
    intro hb r hr
    exact ⟨o, b, hb, by simpa [blockDefs, merge] using hr⟩
  | @link o b t b1 ops T F _ _ hb1 hseg _ ih =>
    intro hb r hr
    simp only [blockDefs, merge, List.filterMap_append, List.mem_append] at hr
    rcases hr with hr | (hr | (hr | hr) | hr)
    · exact ⟨o, b, hb, List.mem_append_left _ hr⟩
    · exact ⟨o, b, hb, List.mem_append_right _ hr⟩
    · obtain ⟨op, hop, hd⟩ := List.mem_filterMap.mp hr
      rcases ssk_seg_ops _ _ _ _ hseg op hop with h | ⟨-, h⟩
      · cases h
      · exact ⟨t.there, b1, hb1, List.mem_append_left _ (h r hd)⟩
    · exact ih hb1 r (by simp only [blockDefs, merge, List.filterMap_append, List.mem_append]; exact Or.inr (Or.inl hr))
    · exact ih hb1 r (by simp only [blockDefs, merge, List.filterMap_append, List.mem_append]; exact Or.inr (Or.inr hr))

end

/-- **`+remove-hops` keeps `DefFirst`.** -/
theorem ssk_hops_first {bl bl' : Map Blob} {rev : Map (List Nat)} {topo : List Nat}
    (hB : HopsBlocks bl rev topo bl') (h2 : DefFirst bl) : DefFirst bl' := by
  -- a path after lifts to a path before whose blocks' definitions are those of blocks of the path after
  have lift : ∀ L, BPath bl' L → ∀ o p, L = o :: p → ∃ q, BPath bl (o :: q) ∧
      ∀ x ∈ q, ∀ bx, HoonMap.get bl x = some bx → ∀ r ∈ blockDefs bx,
        ∃ y ∈ p, ∃ m, HoonMap.get bl' y = some m ∧ r ∈ blockDefs m := by
    intro L hL
    induction hL with
    | start => intro o p e; cases e; exact ⟨[], BPath.start, fun x hx => by cases hx⟩
    | @step p0 o0 m j _ hm hj ih =>
      intro o p e
      cases e
      obtain ⟨q0, hq0, hD0⟩ := ih o0 p0 rfl
      obtain ⟨b, T, F, hb, hmt, rfl⟩ := hB.back o0 m hm
      obtain ⟨e, be, l, hbe, hF, hP, hD⟩ := ssk_mt_path hmt hb
      have hj' : j ∈ getJmps be.fin := by rw [← hF]; exact hj
      refine ⟨e :: (l ++ q0), BPath.step (hP q0 hq0) hbe hj', fun x hx bx hbx r hr => ?_⟩
      have hx' : x ∈ e :: l ∨ x ∈ q0 := by
        simp only [List.mem_cons, List.mem_append] at hx ⊢
        rcases hx with hx | hx | hx
        · exact Or.inl (Or.inl hx)
        · exact Or.inl (Or.inr hx)
        · exact Or.inr hx
      rcases hx' with hx | hx
      · exact ⟨o0, List.mem_cons_self, _, hm, hD x hx bx hbx r hr⟩
      · obtain ⟨y, hy, m', hm', hr'⟩ := hD0 x hx bx hbx r hr
        exact ⟨y, List.mem_cons_of_mem _ hy, m', hm', hr'⟩
  intro o pth m hpath hm i r hread hr
  obtain ⟨b, T, F, hb, hmt, rfl⟩ := hB.back o m hm
  obtain ⟨q, hq, hD⟩ := lift _ hpath o pth rfl
  have hr0 : r ∈ allDefs bl := by
    unfold allDefs at hr ⊢
    obtain ⟨k, hk, hmem⟩ := List.mem_flatMap.mp hr
    obtain ⟨mk, hmk⟩ := Option.isSome_iff_exists.mp ((MapKeys.mem_keys bl' k).mp hk)
    obtain ⟨bk, Tk, Fk, hbk, hmtk, rfl⟩ := hB.back k mk hmk
    rw [hmk] at hmem
    obtain ⟨x, bx, hbx, hrx⟩ := ssk_mt_defs hmtk hbk r hmem
    refine List.mem_flatMap.mpr ⟨x, (MapKeys.mem_keys bl x).mpr (by rw [hbx]; rfl), ?_⟩
    rw [hbx]; exact hrx
  rcases ssk_mt_first h2 hmt hb i r q hread hr0 hq with h | h | ⟨o', ho', b', hb', hm'⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (hD o' ho' b' hb' r hm'))

/-- What is still assumed of `+remove-hops`: it gives `DefOnceB`. -/
def HopsOnce (Map : Type → Type) [HoonMap Map] [MapKeys Map] (fuel : Nat) : Prop :=
  ∀ (bl : Map Blob) topo rev ch bl', DInvT bl → TopoInv bl topo rev → AliasSSAB bl →
    removeHops fuel bl rev topo = some (ch, bl') → DefOnceB bl'

theorem hopsSSA_of {fuel : Nat} (h : HopsOnce Map fuel) : HopsSSA Map fuel :=
  fun bl topo rev ch bl' hd hi hs hh =>
    ⟨h bl topo rev ch bl' hd hi hs hh, ssk_hops_first (hops_blocks hi.1.1 hi.1.2.1 hh) hs.2⟩

/-- **`+optimize` keeps the code** on blocks with `DInvS`, given the field
`alias` (`DriverRestSSA`) and that `+remove-hops` gives `DefOnceB`
(`HopsOnce`). -/
theorem optimize_keeps_ssaO {fuel sfuel : Nat} {P : Passes Map} (H : DriverRestSSA fuel sfuel P)
    (hh : HopsOnce Map fuel) {s s' : Straight Map} (hb : DInvS s.blocks) (h : optimizeF fuel P s = some s') :
    Keeps s s' :=
  optimize_keeps_ssaH H (hopsSSA_of hh) hb h

end Opt
end SkaModel
end Formalization
