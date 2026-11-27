import lemmas.Compiler.OptLinkTotalN
import lemmas.Ska.OptAliasSSAMid
import lemmas.Ska.OptAliasSSARub
import lemmas.Ska.RawInvBase
import lemmas.Ska.OptAliasSSAHops
import lemmas.Ska.OptAliasInv
import lemmas.Ska.OptAliasSSADead

/-!
# The passes keep `ReadsIn N`: the passes that keep every definition

`readsIn_of_lift`: `ReadsIn N` passes from `bl` to `bl'` when every read of
a reachable block of `bl'` of a register that `bl'` does not define is a read
of a reachable block of `bl`, and `bl'` keeps every definition of `bl` of
such a register.  `+remove-useless-branching` (`rub_reads`),
`+remove-empty-middle` (`mid_reads`: a substituted argument is read at the end
of the bypassed block, which is reachable) and `+trim-trace-hints`
(`trim_reads`: it drops hints, which define nothing) keep the definitions of
every block.
-/

namespace Formalization
namespace Compiler

open Nock SkaModel Opt

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

section
variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

theorem allDefs_iff {bl : Map Blob} {r : Nat} :
    r ∈ allDefs bl ↔ ∃ o b, HoonMap.get bl o = some b ∧ r ∈ blockDefs b :=
  Raw.mem_allDefs.trans Raw.defd_iff

/-- **`ReadsIn N` from a lift of the reads.** -/
theorem readsIn_of_lift {N : Nat} {bl bl' : Map Blob} (hR : ReadsIn N bl)
    (hl : ∀ o' b' i r, Reach bl' o' → HoonMap.get bl' o' = some b' → ReadAt b' i r → r ∉ allDefs bl' →
      (∃ o b i', Reach bl o ∧ HoonMap.get bl o = some b ∧ ReadAt b i' r) ∧ (r ∈ allDefs bl → r ∈ allDefs bl')) :
    ReadsIn N bl' := by
  intro o' b' i r hr hb hrd
  by_cases hd : r ∈ allDefs bl'
  · exact Or.inl hd
  · obtain ⟨⟨o, b, i', hro, hbo, hrd'⟩, hk⟩ := hl o' b' i r hr hb hrd hd
    rcases hR o b i' r hro hbo hrd' with h | h
    · exact absurd (hk h) hd
    · exact Or.inr h

/-- A map whose blocks keep the definitions of the blocks of `bl` keeps
`allDefs`. -/
theorem allDefs_mono {bl bl' : Map Blob}
    (h : ∀ o b, HoonMap.get bl o = some b → ∃ b', HoonMap.get bl' o = some b' ∧ blockDefs b' = blockDefs b)
    {r : Nat} (hr : r ∈ allDefs bl) : r ∈ allDefs bl' := by
  obtain ⟨o, b, hb, hm⟩ := allDefs_iff.mp hr
  obtain ⟨b', hb', he⟩ := h o b hb
  exact allDefs_iff.mpr ⟨o, b', hb', he ▸ hm⟩

/-- **`+remove-useless-branching` keeps `ReadsIn N`.** -/
theorem rub_reads {N : Nat} {bl bl' : Map Blob} {ch : Bool} (h : removeUselessBranching bl = some (ch, bl'))
    (hR : ReadsIn N bl) : ReadsIn N bl' := by
  have hB := rub_blocks h
  refine readsIn_of_lift hR fun o' b' i r hr hb hrd _ => ⟨?_, allDefs_mono fun o b hb0 => ?_⟩
  · obtain ⟨b, e, hb0, he, rfl⟩ := hB.back hb
    exact ⟨o', b, _, ssk_rub_reach hB hr, hb0, ssk_rub_read he hrd⟩
  · obtain ⟨e, he, hb'⟩ := (hB o).2 b hb0
    exact ⟨_, hb', ssk_rub_defs he⟩

/-- **`+remove-empty-middle` keeps `ReadsIn N`.** -/
theorem mid_reads {N fuel : Nat} {bl bl' : Map Blob} {ch : Bool} (h : removeEmptyMiddle fuel bl = some (ch, bl'))
    (hR : ReadsIn N bl) : ReadsIn N bl' := by
  have hM := mid_blocks h
  refine readsIn_of_lift hR fun o' b' i r hr hb hrd _ => ⟨?_, allDefs_mono fun o b hb0 => ?_⟩
  · obtain ⟨b, f', hb0, hf, rfl⟩ := hM.back hb
    have hro := ssk_mid_reach hM hr
    rcases hrd with hrd | ⟨hi, hrf⟩
    · exact ⟨o', b, i, hro, hb0, Or.inl hrd⟩
    · rcases (ssk_mfin hf).2 r hrf with hrf | ⟨j, hj, l, m, bm, hc, hbm, hbe, hrm, -⟩
      · exact ⟨o', b, i, hro, hb0, Or.inr ⟨hi, hrf⟩⟩
      · exact ⟨m, bm, 0, ssk_chain_reach hc (Reach.jump hro hb0 hj), hbm, Or.inr ⟨by rw [hbe]; rfl, hrm⟩⟩
  · obtain ⟨f', -, hb'⟩ := (hM o).2 b hb0
    exact ⟨_, hb', rfl⟩

/-- **Filtering bodies by a test that keeps every op writing a register keeps
`ReadsIn N`.** -/
theorem filt_reads {N : Nat} {bl bl' : Map Blob} {p : Pole → Bool}
    (hg : ∀ o, HoonMap.get bl' o = (HoonMap.get bl o).map fun b => { b with body := b.body.filter p })
    (hp : ∀ op, p op = false → aliasDst op = none) (hR : ReadsIn N bl) : ReadsIn N bl' := by
  refine readsIn_of_lift hR fun o' b' i r hr hb hrd _ => ⟨?_, allDefs_mono fun o b hb0 => ?_⟩
  · rw [hg] at hb
    obtain ⟨b, hb0, rfl⟩ := Option.map_eq_some_iff.mp hb
    exact ⟨o', b, _, reach_filt hg hr, hb0, readAt_filt hg hrd⟩
  · refine ⟨_, by rw [hg, hb0]; rfl, ?_⟩
    simp only [blockDefs, filt_defs p hp]

/-- **`+trim-trace-hints` keeps `ReadsIn N`.** -/
theorem trim_reads {N : Nat} {bl : Map Blob} {topo : List Nat} {rev : Map (List Nat)} {bl' : Map Blob}
    (h : trimTraceHints bl topo rev = some bl') (hR : ReadsIn N bl) : ReadsIn N bl' := by
  unfold trimTraceHints at h
  obtain ⟨uns, -, rfl⟩ := Option.map_eq_some_iff.mp h
  refine filt_reads (p := tkeep uns (trimOpened bl)) (trimRun_get bl uns (trimOpened bl)) (fun op hop => ?_) hR
  have hd : trimDrop uns (trimOpened bl) op = true := by simpa [tkeep] using hop
  obtain ⟨_, _, hk, -⟩ := trimDrop_true hd
  cases op <;> first | rfl | simp [traceKey] at hk

/-- A read of a merged block is a read of a reachable block of the chain. -/
theorem mt_read {bl : Map Blob} {rev : Map (List Nat)} {o : Nat} {b : Blob} {T : List Pole} {F : Termin}
    (hm : MTail bl rev o b T F) : HoonMap.get bl o = some b → Reach bl o → ∀ i r, ReadAt (merge b T F) i r →
      ∃ x bx i', Reach bl x ∧ HoonMap.get bl x = some bx ∧ ReadAt bx i' r := by
  induction hm with
  | @stop o b _ =>
    intro hb hr i r hrd
    have e : merge b [] b.fin = b := by simp [merge]
    rw [e] at hrd
    exact ⟨o, b, i, hr, hb, hrd⟩
  | @link o b t b1 ops T F hfin _ hb1 hseg _ ih =>
    intro hb hr i r hrd
    have hr1 : Reach bl t.there := Reach.jump (j := t) hr hb (by rw [hfin]; simp [getJmps])
    rcases ssk_readAt_app (A := b.body) (B := ops ++ b1.body ++ T) hrd with ⟨hi, hrd⟩ | ⟨hi, hrd⟩
    · exact ⟨o, b, i, hr, hb, Or.inl hrd⟩
    · rw [List.append_assoc] at hrd
      rcases ssk_readAt_app (A := ops) (B := b1.body ++ T) hrd with ⟨hi2, hrd2⟩ | ⟨hi2, hrd2⟩
      · obtain ⟨op, hop, hrop⟩ := ssk_read_op hrd2
        rcases ssk_seg_ops t.args b1.par [] ops hseg op hop with h | ⟨h, -⟩
        · cases h
        · exact ⟨o, b, b.body.length, hr, hb, Or.inr ⟨rfl, by rw [hfin]; exact mem_jmpRegs.mpr (h r hrop)⟩⟩
      · exact ih hb1 hr1 _ r hrd2

/-- **`+remove-hops` keeps `ReadsIn N`**: a read of a merged block is a read
of a reachable block before, and a register `bl` defines is defined before the
read on a path (`DefFirst`), so in the merged block or one of the path after
(`ssk_mt_first`, the lift of `ssk_hops_first`). -/
theorem hops_reads {N fuel : Nat} {bl bl' : Map Blob} {rev : Map (List Nat)} {topo : List Nat} {ch : Bool}
    (hn : topo.Nodup) (h0 : topo.head? = some 0) (h2 : DefFirst bl)
    (h : removeHops fuel bl rev topo = some (ch, bl')) (hR : ReadsIn N bl) : ReadsIn N bl' := by
  have hB := hops_blocks hn h0 h
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
  refine readsIn_of_lift hR fun o m i r hr hm hrd _ => ?_
  obtain ⟨b, T, F, hb, hmt, rfl⟩ := hB.back o m hm
  obtain ⟨p, hp⟩ := awi_reach_bpath hr
  obtain ⟨q, hq, hD⟩ := lift _ hp o p rfl
  refine ⟨mt_read hmt hb (ssk_bpath_reach hq o List.mem_cons_self) i r hrd, fun hr0 => ?_⟩
  rcases ssk_mt_first h2 hmt hb i r q hrd hr0 hq with h | h | ⟨o', ho', b', hb', hm'⟩
  · exact bdef_allDefs hm (List.mem_append_left _ h)
  · refine bdef_allDefs hm (List.mem_append_right _ ?_)
    obtain ⟨op, hop, hd⟩ := List.mem_filterMap.mp h
    exact List.mem_filterMap.mpr ⟨op, List.mem_of_mem_take hop, hd⟩
  · obtain ⟨y, -, m', hm'', hr'⟩ := hD o' ho' b' hb' r hm'
    exact bdef_allDefs hm'' hr'

/-- **`+remove-dead-code` keeps `ReadsIn N`**: a read after is a read before
of a live register; a register `bl` defines is defined before the read on a
path (`DefFirst`), and that definition is live, so kept (the argument of
`ssk_dead`). -/
theorem dead_reads {N : Nat} {bl bl' : Map Blob} {topo : List Nat} (ht : TopoOK bl topo)
    (h : removeDeadCode bl topo.reverse = some bl') (h2 : DefFirst bl) (hR : ReadsIn N bl) : ReadsIn N bl' := by
  obtain ⟨Sf, W, hout⟩ := ssk_dead_walk ht h
  have hback : ∀ o b', HoonMap.get bl' o = some b' → o ∈ topo ∧ ∃ b, HoonMap.get bl o = some b ∧
      b' = { b with body := (deadF b.body (Sf o)).1 } := by
    intro o b' hb'
    by_cases ho : o ∈ topo
    · obtain ⟨b, hb, hb2, -⟩ := W.blk o ho
      rw [hb2] at hb'; cases hb'
      exact ⟨ho, b, hb, rfl⟩
    · rw [hout o ho] at hb'; cases hb'
  have hreach : ∀ o, Reach bl' o → Reach bl o := by
    intro o hr
    induction hr with
    | zero => exact Reach.zero
    | jump _ hb hj ih =>
      obtain ⟨-, b, hb0, rfl⟩ := hback _ _ hb
      exact Reach.jump (j := _) ih hb0 hj
  have hbpath : ∀ L, BPath bl' L → BPath bl L := by
    intro L hL
    induction hL with
    | start => exact BPath.start
    | step _ hb hj ih =>
      obtain ⟨-, b, hb0, rfl⟩ := hback _ _ hb
      exact BPath.step ih hb0 hj
  -- a read after is a read before, of a live register
  have hrm : ∀ o b j r, HoonMap.get bl o = some b → ReadAt { b with body := (deadF b.body (Sf o)).1 } j r →
      o ∈ topo → ReadAt b (didx b.body (Sf o) j) r ∧ r ∈ (deadF (b.body.drop (didx b.body (Sf o) j)) (Sf o)).2 := by
    intro o b j r hb h ho
    rcases h with h | ⟨hj, h⟩
    · simp only at h
      cases e : ((deadF b.body (Sf o)).1.drop j).head? with
      | none => rw [e] at h; simp at h
      | some op =>
        rw [e] at h
        simp only [Option.map_some, Option.getD_some] at h
        refine ⟨Or.inl ?_, ssk_dd_read (Sf o) b.body j op e r (ssk_reads_regs h)⟩
        rw [← ssk_dd_head, e]
        simp only [Option.map_some, Option.getD_some]
        exact h
    · simp only at hj
      have hd : didx b.body (Sf o) j = b.body.length := ssk_dd_len _ _ _ (by omega)
      rw [hd]
      refine ⟨Or.inr ⟨rfl, h⟩, ?_⟩
      rw [List.drop_length]
      obtain ⟨b2, hb2, -, hfin⟩ := W.blk o ho
      rw [hb] at hb2; cases hb2
      exact hfin r h
  -- along a path, the live set at a block's start is in `Sf` of every block before
  have hlivep : ∀ L, BPath bl L → ∀ o p b, L = o :: p → HoonMap.get bl o = some b →
      ∀ x ∈ (deadF b.body (Sf o)).2, ∀ o' ∈ p, x ∈ Sf o' := by
    intro L hL
    induction hL with
    | start => intro o p b e; cases e; intro _ _ _ _ h; cases h
    | @step p0 o0 b0 j hp hb0 hj ih =>
      intro o p b e hb x hx o' ho'
      cases e
      have ho0 : o0 ∈ topo := ht.2.2.2.1 o0 (ssk_bpath_reach hp o0 List.mem_cons_self)
      have hx0 : x ∈ Sf o0 := W.jmp o0 b0 j b ho0 hb0 hj hb x hx
      rcases List.mem_cons.mp ho' with rfl | ho'
      · exact hx0
      · exact ih o0 p0 b0 rfl hb0 x (deadF_sup _ _ x hx0) o' ho'
  refine readsIn_of_lift hR fun o b' i r hr hb' hread _ => ?_
  obtain ⟨ho, b, hb, rfl⟩ := hback _ _ hb'
  obtain ⟨hrd, hlv⟩ := hrm o b i r hb hread ho
  refine ⟨⟨o, b, _, hreach _ hr, hb, hrd⟩, fun hr0 => ?_⟩
  obtain ⟨pth, hpath⟩ := awi_reach_bpath hr
  have hpb := hbpath _ hpath
  rcases h2 o pth b hpb hb _ r hrd hr0 with h | h | ⟨o', ho', b2, hb2, hm⟩
  · exact bdef_allDefs hb' (List.mem_append_left _ h)
  · refine bdef_allDefs hb' (List.mem_append_right _ ?_)
    obtain ⟨op, hop, hd⟩ := List.mem_filterMap.mp h
    obtain ⟨i', hi'⟩ := List.mem_iff_getElem?.mp hop
    rw [List.getElem?_take] at hi'
    split at hi'
    · rename_i hlt
      have := ssk_dd_def (Sf o) b.body i' i r op hi' hd (ssk_dd_live (Sf o) b.body (by omega) hlv) hlt
      obtain ⟨op2, hop2, hd2⟩ := List.mem_filterMap.mp this
      exact List.mem_filterMap.mpr ⟨op2, List.mem_of_mem_take hop2, hd2⟩
    · cases hi'
  · have ho2 : o' ∈ topo := ht.2.2.2.1 o' (ssk_bpath_reach hpb o' (List.mem_cons_of_mem _ ho'))
    obtain ⟨b3, hb3, hb3', -⟩ := W.blk o' ho2
    rw [hb2] at hb3; cases hb3
    refine bdef_allDefs hb3' ?_
    have hS : r ∈ Sf o' := hlivep _ hpb o pth b rfl hb r (ssk_dd_live (Sf o) b.body (Nat.zero_le _) hlv) o' ho'
    simp only [blockDefs, List.mem_append] at hm ⊢
    rcases hm with hm | hm
    · exact Or.inl hm
    · right
      obtain ⟨op, hop, hd⟩ := List.mem_filterMap.mp hm
      obtain ⟨i', hi'⟩ := List.mem_iff_getElem?.mp hop
      have hlen := ssk_dd_len (Sf o') b2.body _ (Nat.le_refl _)
      have := ssk_dd_def (Sf o') b2.body i' _ r op hi' hd (deadF_sup _ _ r hS)
        (by rw [hlen]; exact (List.getElem?_eq_some_iff.mp hi').1)
      rwa [List.take_length] at this

end

end Compiler
end Formalization
