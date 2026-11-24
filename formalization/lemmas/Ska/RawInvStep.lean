import lemmas.Ska.RawInvBase

/-!
# Raw `+comp` output: the invariant of the blocks and its two steps

README Gaps 14.  A run of `+comp` changes its blocks in two ways only: it
puts a block at a fresh label (`+emit`) and it puts ops in front of the body
of a block (`+add-ops`).  This file states what the blocks of a state carry
on the first fragment and proves that each step keeps it under conditions
on the new block or the new ops.

* `BlkNodup bl`: each block's definitions (parameters and destinations) are
  distinct; `Cross bl`: no register is defined in two blocks.  Together they
  give `DefUniq` (`defUniq_of`) and `ParNodup` (`parNodup_of`).
* `Par1 bl`: at most one parameter per block (the first fragment has only
  the join of `+forl`).
* `ArgsAbove bl`: every argument register of a jump is above every
  parameter of every block at or below the jump's target.  With blocks that
  jump down it gives `PassOK` and `DownPar` (`passOK_of`, `downPar_of_args`).
* `put_*`, `prepend_*`: each invariant through a new block, and through ops
  in front of a block; `live_put_*`, `live_prepend`: liveness through them.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt

variable {Map : Type → Type} [HoonMap Map]

/-! ## The invariants of the blocks -/

/-- Each block's definitions are distinct. -/
def BlkNodup (bl : Map Blob) : Prop := ∀ o b, HoonMap.get bl o = some b → (blockDefs b).Nodup

/-- No register is defined in two blocks. -/
def Cross (bl : Map Blob) : Prop :=
  ∀ o o' b b' r, HoonMap.get bl o = some b → HoonMap.get bl o' = some b' → o ≠ o' →
    r ∈ blockDefs b → r ∉ blockDefs b'

/-- Every block has at most one parameter. -/
def Par1 (bl : Map Blob) : Prop := ∀ k b, HoonMap.get bl k = some b → b.par.length ≤ 1

/-- Every argument of a jump is above every parameter of every block at or
below the jump's target. -/
def ArgsAbove (bl : Map Blob) : Prop :=
  ∀ z bz y b j r x, HoonMap.get bl z = some bz → HoonMap.get bl y = some b → j ∈ getJmps b.fin →
    some r ∈ j.args → z ≤ j.there → x ∈ bz.par → x < r

/-- Every block jumps to labels below its own. -/
def JDown (bl : Map Blob) : Prop := ∀ k b, HoonMap.get bl k = some b → ∀ j ∈ getJmps b.fin, j.there < k

theorem JDown.below {bl : Map Blob} (h : JDown bl) (L : Nat) : DownBelow bl L := fun x b _ hb => h x b hb

theorem defUniq_of {bl : Map Blob} (hn : BlkNodup bl) (hx : Cross bl) : DefUniq bl := by
  intro r s s' hs hs'
  obtain ⟨b, hb, hm⟩ := defSite_mem hs
  obtain ⟨b', hb', hm'⟩ := defSite_mem hs'
  by_cases ho : s.1 = s'.1
  · obtain ⟨o, opt⟩ := s
    obtain ⟨o', opt'⟩ := s'
    change o = o' at ho
    subst ho
    rw [hb] at hb'; cases hb'
    have hnd := hn o b hb
    unfold blockDefs at hnd
    obtain ⟨-, hnd2, hdisj⟩ := List.nodup_append.mp hnd
    cases opt with
    | none =>
      cases opt' with
      | none => rfl
      | some j' =>
        obtain ⟨b2, op, hb2, hop, hdst⟩ := hs'
        obtain ⟨b3, hb3, hm3⟩ := hs
        change HoonMap.get bl o = some b2 at hb2
        change HoonMap.get bl o = some b3 at hb3
        rw [hb] at hb2 hb3; cases hb2; cases hb3
        exact absurd rfl (hdisj r hm3 r (List.mem_filterMap.mpr ⟨op, List.mem_of_getElem? hop, hdst⟩))
    | some j =>
      cases opt' with
      | none =>
        obtain ⟨b2, op, hb2, hop, hdst⟩ := hs
        obtain ⟨b3, hb3, hm3⟩ := hs'
        change HoonMap.get bl o = some b2 at hb2
        change HoonMap.get bl o = some b3 at hb3
        rw [hb] at hb2 hb3; cases hb2; cases hb3
        exact absurd rfl (hdisj r hm3 r (List.mem_filterMap.mpr ⟨op, List.mem_of_getElem? hop, hdst⟩))
      | some j' =>
        obtain ⟨b2, op, hb2, hop, hdst⟩ := hs
        obtain ⟨b3, op', hb3, hop', hdst'⟩ := hs'
        change HoonMap.get bl o = some b2 at hb2
        change HoonMap.get bl o = some b3 at hb3
        rw [hb] at hb2 hb3; cases hb2; cases hb3
        rw [filterMap_nodup_idx b.body j j' op op' r hnd2 hop hop' hdst hdst']
  · exact absurd hm' (hx _ _ _ _ r hb hb' ho hm)

theorem parNodup_of {bl : Map Blob} (hn : BlkNodup bl) : ParNodup bl :=
  fun o b hb => (List.nodup_append.mp (hn o b hb)).1

theorem parNodup_of_par1 {bl : Map Blob} (h : Par1 bl) : ParNodup bl := by
  intro o b hb
  have := h o b hb
  match b.par, this with
  | [], _ => exact List.nodup_nil
  | [x], _ => simp
  | _ :: _ :: _, h2 => simp at h2

theorem passOK_of {bl : Map Blob} (h : ArgsAbove bl) : PassOK bl :=
  fun o b j b2 hb hj hb2 r hr hp => Nat.lt_irrefl r (h j.there b2 o b j r r hb2 hb hj hr (Nat.le_refl _) hp)

/-- Blocks that jump down reach only labels at or below their own. -/
theorem rFrom_le {bl : Map Blob} (hd : JDown bl) {x z : Nat} (h : RFrom bl x z) : z ≤ x := by
  induction h with
  | refl => exact Nat.le_refl _
  | step hb hj _ ih => exact Nat.le_trans ih (Nat.le_of_lt (hd _ _ hb _ hj))

theorem downPar_of_args {bl : Map Blob} (h : ArgsAbove bl) (hd : JDown bl) : DownPar bl :=
  fun y b j hb hj r hr z bz hz hbz hp => Nat.lt_irrefl r (h z bz y b j r r hbz hb hj hr (rFrom_le hd hz) hp)

/-- `JDown` gives a rank. -/
theorem acyclic_of_jdown {bl : Map Blob} (h : JDown bl) : Acyclic bl := ⟨id, fun o b j hb hj => h o b hb j hj⟩

/-! ## A new block -/

section Put
variable {bl : Map Blob} {l : Nat} {b : Blob}

theorem get_put_self : HoonMap.get (HoonMap.put bl l b) l = some b := by simp [HoonMap.get_put]

theorem get_put_ne {k : Nat} (h : k ≠ l) : HoonMap.get (HoonMap.put bl l b) k = HoonMap.get bl k := by
  simp [HoonMap.get_put, h]

theorem get_put_cases {k : Nat} {b' : Blob} (h : HoonMap.get (HoonMap.put bl l b) k = some b') :
    (k = l ∧ b' = b) ∨ (k ≠ l ∧ HoonMap.get bl k = some b') := by
  by_cases e : k = l
  · subst e; rw [get_put_self] at h; cases h; exact Or.inl ⟨rfl, rfl⟩
  · rw [get_put_ne e] at h; exact Or.inr ⟨e, h⟩

theorem defd_put (hl : HoonMap.get bl l = none) {r : Nat} :
    Defd (HoonMap.put bl l b) r ↔ Defd bl r ∨ r ∈ blockDefs b := by
  simp only [defd_iff]
  constructor
  · rintro ⟨o, b', hb', hm⟩
    rcases get_put_cases hb' with ⟨rfl, rfl⟩ | ⟨_, h⟩
    · exact Or.inr hm
    · exact Or.inl ⟨o, b', h, hm⟩
  · rintro (⟨o, b', hb', hm⟩ | hm)
    · have : o ≠ l := fun e => by subst e; rw [hl] at hb'; cases hb'
      exact ⟨o, b', by rw [get_put_ne this]; exact hb', hm⟩
    · exact ⟨l, b, get_put_self, hm⟩

theorem blkNodup_put (hn : BlkNodup bl) (hb : (blockDefs b).Nodup) : BlkNodup (HoonMap.put bl l b) := by
  intro o b' hb'
  rcases get_put_cases hb' with ⟨_, rfl⟩ | ⟨_, h⟩
  · exact hb
  · exact hn o b' h

theorem cross_put (hx : Cross bl) (hl : HoonMap.get bl l = none) (hf : ∀ r ∈ blockDefs b, ¬ Defd bl r) :
    Cross (HoonMap.put bl l b) := by
  intro o o' b1 b2 r h1 h2 hne hm1 hm2
  rcases get_put_cases h1 with ⟨rfl, rfl⟩ | ⟨ne1, g1⟩ <;> rcases get_put_cases h2 with ⟨rfl, rfl⟩ | ⟨ne2, g2⟩
  · exact hne rfl
  · exact hf r hm1 (defd_iff.mpr ⟨o', b2, g2, hm2⟩)
  · exact hf r hm2 (defd_iff.mpr ⟨o, b1, g1, hm1⟩)
  · exact hx o o' b1 b2 r g1 g2 hne hm1 hm2

theorem noTr_put (hn : NoTr bl) (hb : ∀ op ∈ b.body, trOp op = false) : NoTr (HoonMap.put bl l b) := by
  intro o b' hb'
  rcases get_put_cases hb' with ⟨_, rfl⟩ | ⟨_, h⟩
  · exact hb
  · exact hn o b' h

theorem par1_put (hn : Par1 bl) (hb : b.par.length ≤ 1) : Par1 (HoonMap.put bl l b) := by
  intro o b' hb'
  rcases get_put_cases hb' with ⟨_, rfl⟩ | ⟨_, h⟩
  · exact hb
  · exact hn o b' h

theorem jdown_put (hn : JDown bl) (hb : ∀ j ∈ getJmps b.fin, j.there < l) : JDown (HoonMap.put bl l b) := by
  intro o b' hb'
  rcases get_put_cases hb' with ⟨rfl, rfl⟩ | ⟨_, h⟩
  · exact hb
  · exact hn o b' h

/-- A new block above every label keeps `ArgsAbove` when its own arguments
are above every parameter at or below their target, its own included. -/
theorem argsAbove_put (ha : ArgsAbove bl) (hd : JDown bl) (hlab : ∀ k b', HoonMap.get bl k = some b' → k < l)
    (hb : ∀ j ∈ getJmps b.fin, ∀ r, some r ∈ j.args → j.there < l ∧
      ∀ z bz, HoonMap.get (HoonMap.put bl l b) z = some bz → z ≤ j.there → ∀ x ∈ bz.par, x < r) :
    ArgsAbove (HoonMap.put bl l b) := by
  intro z bz y b' j r x hz hy hj hr hzj hx
  rcases get_put_cases hy with ⟨rfl, rfl⟩ | ⟨ney, hy⟩
  · exact (hb j hj r hr).2 z bz hz hzj x hx
  · have hlt : j.there < y := hd y b' hy j hj
    have hyl := hlab y b' hy
    rcases get_put_cases hz with ⟨rfl, rfl⟩ | ⟨_, hz⟩
    · omega
    · exact ha z bz y b' j r x hz hy hj hr hzj hx

end Put

/-! ## Ops in front of a block -/

section Prepend
variable {bl : Map Blob} {o : Nat} {b : Blob} {A : List Pole}

/-- The block with `A` in front of its body. -/
abbrev pre (A : List Pole) (b : Blob) : Blob := { b with body := A ++ b.body }

theorem blockDefs_pre : blockDefs (pre A b) = b.par ++ (defsOf A ++ defsOf b.body) := by
  simp [blockDefs, defsOf, List.filterMap_append]

theorem mem_blockDefs_pre {r : Nat} : r ∈ blockDefs (pre A b) ↔ r ∈ blockDefs b ∨ r ∈ defsOf A := by
  rw [blockDefs_pre, mem_blockDefs]
  simp only [List.mem_append]
  constructor
  · rintro (h | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr h)
  · rintro ((h | h) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)

theorem defd_prepend (hb : HoonMap.get bl o = some b) {r : Nat} :
    Defd (HoonMap.put bl o (pre A b)) r ↔ Defd bl r ∨ r ∈ defsOf A := by
  simp only [defd_iff]
  constructor
  · rintro ⟨k, b', hb', hm⟩
    rcases get_put_cases hb' with ⟨rfl, rfl⟩ | ⟨_, h⟩
    · rcases mem_blockDefs_pre.mp hm with h | h
      · exact Or.inl ⟨k, b, hb, h⟩
      · exact Or.inr h
    · exact Or.inl ⟨k, b', h, hm⟩
  · rintro (⟨k, b', hb', hm⟩ | hm)
    · by_cases e : k = o
      · subst e; rw [hb] at hb'; cases hb'
        exact ⟨k, pre A b, get_put_self, mem_blockDefs_pre.mpr (Or.inl hm)⟩
      · exact ⟨k, b', by rw [get_put_ne e]; exact hb', hm⟩
    · exact ⟨o, pre A b, get_put_self, mem_blockDefs_pre.mpr (Or.inr hm)⟩

theorem blkNodup_prepend (hn : BlkNodup bl) (hb : HoonMap.get bl o = some b) (hA : (defsOf A).Nodup)
    (hf : ∀ r ∈ defsOf A, ¬ Defd bl r) : BlkNodup (HoonMap.put bl o (pre A b)) := by
  intro k b' hb'
  rcases get_put_cases hb' with ⟨rfl, rfl⟩ | ⟨_, h⟩
  · rw [blockDefs_pre]
    have h0 := hn k b hb
    unfold blockDefs at h0
    obtain ⟨n1, n2, d12⟩ := List.nodup_append.mp h0
    have nb : ∀ r ∈ defsOf A, r ∉ blockDefs b := fun r hr hm => hf r hr (defd_iff.mpr ⟨k, b, hb, hm⟩)
    refine List.nodup_append.mpr ⟨n1, List.nodup_append.mpr ⟨hA, n2, ?_⟩, ?_⟩
    · intro x hx y hy e; subst e
      exact nb x hx (mem_blockDefs.mpr (Or.inr hy))
    · intro x hx y hy e; subst e
      rcases List.mem_append.mp hy with hy | hy
      · exact nb x hy (mem_blockDefs.mpr (Or.inl hx))
      · exact d12 x hx x hy rfl
  · exact hn k b' h

theorem cross_prepend (hx : Cross bl) (hb : HoonMap.get bl o = some b) (hf : ∀ r ∈ defsOf A, ¬ Defd bl r) :
    Cross (HoonMap.put bl o (pre A b)) := by
  intro k k' b1 b2 r h1 h2 hne hm1 hm2
  rcases get_put_cases h1 with ⟨rfl, rfl⟩ | ⟨ne1, g1⟩ <;> rcases get_put_cases h2 with ⟨rfl, rfl⟩ | ⟨ne2, g2⟩
  · exact hne rfl
  · rcases mem_blockDefs_pre.mp hm1 with h | h
    · exact hx k k' b b2 r hb g2 hne h hm2
    · exact hf r h (defd_iff.mpr ⟨k', b2, g2, hm2⟩)
  · rcases mem_blockDefs_pre.mp hm2 with h | h
    · exact hx k k' b1 b r g1 hb hne hm1 h
    · exact hf r h (defd_iff.mpr ⟨k, b1, g1, hm1⟩)
  · exact hx k k' b1 b2 r g1 g2 hne hm1 hm2

theorem noTr_prepend (hn : NoTr bl) (hb : HoonMap.get bl o = some b) (hA : ∀ op ∈ A, trOp op = false) :
    NoTr (HoonMap.put bl o (pre A b)) := by
  intro k b' hb'
  rcases get_put_cases hb' with ⟨rfl, rfl⟩ | ⟨_, h⟩
  · intro op hop
    rcases List.mem_append.mp hop with h | h
    · exact hA op h
    · exact hn k b hb op h
  · exact hn k b' h

theorem par1_prepend (hn : Par1 bl) (hb : HoonMap.get bl o = some b) : Par1 (HoonMap.put bl o (pre A b)) := by
  intro k b' hb'
  rcases get_put_cases hb' with ⟨rfl, rfl⟩ | ⟨_, h⟩
  · exact hn k b hb
  · exact hn k b' h

theorem jdown_prepend (hn : JDown bl) (hb : HoonMap.get bl o = some b) : JDown (HoonMap.put bl o (pre A b)) := by
  intro k b' hb'
  rcases get_put_cases hb' with ⟨rfl, rfl⟩ | ⟨_, h⟩
  · exact hn k b hb
  · exact hn k b' h

theorem argsAbove_prepend (ha : ArgsAbove bl) (hb : HoonMap.get bl o = some b) :
    ArgsAbove (HoonMap.put bl o (pre A b)) := by
  intro z bz y b' j r x hz hy hj hr hzj hx
  have hz' : ∃ bz0, HoonMap.get bl z = some bz0 ∧ bz0.par = bz.par := by
    rcases get_put_cases hz with ⟨rfl, rfl⟩ | ⟨_, h⟩
    · exact ⟨b, hb, rfl⟩
    · exact ⟨bz, h, rfl⟩
  have hy' : ∃ b0, HoonMap.get bl y = some b0 ∧ b0.fin = b'.fin := by
    rcases get_put_cases hy with ⟨rfl, rfl⟩ | ⟨_, h⟩
    · exact ⟨b, hb, rfl⟩
    · exact ⟨b', h, rfl⟩
  obtain ⟨bz0, hz0, pz⟩ := hz'
  obtain ⟨b0, hy0, fy⟩ := hy'
  rw [← fy] at hj
  rw [← pz] at hx
  exact ha z bz0 y b0 j r x hz0 hy0 hj hr hzj hx

end Prepend

/-! ## Liveness through the two steps -/

/-- Liveness at a block whose jumps go below `L`, in a map that agrees with
`bl` below `L`. -/
theorem live_unfold {bl bl' : Map Blob} {k L : Nat} {b : Blob} (hk : HoonMap.get bl' k = some b)
    (hd : DownBelow bl L) (he : ∀ x, x < L → HoonMap.get bl' x = HoonMap.get bl x)
    (hj : ∀ j ∈ getJmps b.fin, j.there < L) {r : Nat} (h : Live bl' k r) :
    BlockRF b r ∨ ∃ j ∈ getJmps b.fin, Live bl j.there r ∧ r ∉ blockDefs b := by
  obtain ⟨b', hb', hr⟩ := live_iff.mp h
  rw [hk] at hb'; cases hb'
  rcases hr with hr | ⟨j, hjm, hl, hn⟩
  · exact Or.inl hr
  · exact Or.inr ⟨j, hjm, (live_frame hd he (hj j hjm)).mp hl, hn⟩

theorem opsRF_mem {A : List Pole} {r : Nat} (h : OpsRF A r) : ∃ op ∈ A, r ∈ aliasReads op := by
  induction A with
  | nil => exact h.elim
  | cons op A ih =>
    rcases h with h | ⟨_, h⟩
    · exact ⟨op, List.mem_cons_self, h⟩
    · obtain ⟨q, hq, hr⟩ := ih h; exact ⟨q, List.mem_cons_of_mem _ hq, hr⟩

/-- **Liveness at a block with ops in front**, when its jumps go below it. -/
theorem live_prepend {bl : Map Blob} {o : Nat} {b : Blob} {A : List Pole} (hb : HoonMap.get bl o = some b)
    (hd : DownBelow bl o) (hjb : ∀ j ∈ getJmps b.fin, j.there < o) {r : Nat}
    (h : Live (HoonMap.put bl o (pre A b)) o r) :
    (r ∉ b.par ∧ OpsRF A r) ∨ (r ∉ defsOf A ∧ Live bl o r) := by
  have he : ∀ x, x < o → HoonMap.get (HoonMap.put bl o (pre A b)) x = HoonMap.get bl x :=
    fun x hx => get_put_ne (Nat.ne_of_lt hx)
  rcases live_unfold (b := pre A b) get_put_self hd he hjb h with ⟨hp, hr⟩ | ⟨j, hj, hl, hn⟩
  · simp only [pre] at hp hr
    rcases hr with hr | ⟨hn, hf⟩
    · rcases opsRF_append.mp hr with hr | ⟨hnA, hr⟩
      · exact Or.inl ⟨hp, hr⟩
      · exact Or.inr ⟨hnA, Live.here hb ⟨hp, Or.inl hr⟩⟩
    · rw [defsOf_append, List.mem_append, not_or] at hn
      exact Or.inr ⟨hn.1, Live.here hb ⟨hp, Or.inr ⟨hn.2, hf⟩⟩⟩
  · have hn' : r ∉ blockDefs b ∧ r ∉ defsOf A := ⟨fun e => hn (mem_blockDefs_pre.mpr (Or.inl e)),
      fun e => hn (mem_blockDefs_pre.mpr (Or.inr e))⟩
    exact Or.inr ⟨hn'.2, Live.next hb hj hl hn'.1⟩

end Raw
end SkaModel
end Formalization
