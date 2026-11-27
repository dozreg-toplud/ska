import lemmas.Ska.RawInvCLForl

/-!
# The run-level liveness with calls: the spec of `+collapse-lazy-atom`

README Gaps 14 (b), track D.

* `CW r B C0 g`: the state invariant of the walk of `+collapse-lazy-atom`
  from a state with `re = B` and `cond = C0`: every block's registers below
  `re`, no key of `cond` defined, `r` neither defined nor a key, every key
  of `cond` below `re` and either a key of `C0` or a new one from `B` on
  standing for `r`.
* `cw_src`, `cw_addOps`: the source step (`r` or a fresh proxy of `r`) and
  `+add-ops` keep it; **`collapseGate_cw`**: the gate keeps it at an entry
  whose need is old and names no key, and asks `r` only at the root.
* **`collapseSpecL`**: the spec `CollapseSpecL` (the cases on `nedSure`,
  then the walk: `IL` of "`r` at `there`" by `CW`, the liveness by
  `collapseWalk_prep` and `liveK_walkR`).
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The state invariant of the walk of `+collapse-lazy-atom`.** -/
structure CW (r B : Nat) (C0 : Map (Nat × List Nat)) (g : Comp.Gen Map) : Prop where
  drop : g.drop = false
  le : B ≤ g.re
  rlt : r < B
  clt : CondLt g
  regs : ∀ k b, HoonMap.get g.blocks k = some b → BlobIn (· < g.re) b
  nokey : ∀ y, Defd g.blocks y → HoonMap.get g.cond y = Option.none
  rdef : ¬ Defd g.blocks r
  rkey : HoonMap.get g.cond r = Option.none
  keys : ∀ k v, HoonMap.get g.cond k = some v → HoonMap.get C0 k = some v ∨ (v.1 = r ∧ B ≤ k)

theorem CW.old {r B : Nat} {C0 : Map (Nat × List Nat)} {g : Comp.Gen Map} (h : CW r B C0 g) {y : Nat}
    (hy : y < B) (h0 : HoonMap.get C0 y = Option.none) : HoonMap.get g.cond y = Option.none := by
  cases e : HoonMap.get g.cond y with
  | none => rfl
  | some v =>
    rcases h.keys y v e with h1 | h1
    · rw [h0] at h1; cases h1
    · omega

theorem cw_re {r B : Nat} {C0 : Map (Nat × List Nat)} {g : Comp.Gen Map} (h : CW r B C0 g) {k : Nat}
    (hk : g.re ≤ k) : CW r B C0 ({ g with re := k } : Comp.Gen Map) :=
  ⟨h.drop, Nat.le_trans h.le hk, h.rlt, fun k' v e => Nat.lt_of_lt_of_le (h.clt k' v e) hk,
    fun k' b hb => (h.regs k' b hb).mono fun _ hx => Nat.lt_of_lt_of_le hx hk, h.nokey, h.rdef, h.rkey, h.keys⟩

/-- **The source step keeps `CW`**: `r` itself, or a fresh proxy of `r`. -/
theorem cw_src {r B o oLaz src : Nat} {C0 : Map (Nat × List Nat)} {g g' : Comp.Gen Map} (hW : CW r B C0 g)
    (h : (if oLaz = o then pure r else proxy r oLaz : CM Map Nat) g = some (src, g')) :
    CW r B C0 g' ∧ g'.blocks = g.blocks ∧ src < g'.re ∧ g.re ≤ g'.re ∧
      (∀ y, y < g.re → HoonMap.get g'.cond y = HoonMap.get g.cond y) ∧ (oLaz = o → src = r) := by
  have hd : g.drop = false := hW.drop
  split at h
  · rename_i e
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hW, rfl, by have := hW.rlt; have := hW.le; omega, Nat.le_refl _, fun _ _ => rfl, fun _ => rfl⟩
  · rename_i e
    unfold proxy at h
    dsimp only at h
    simp only [hd, Bool.false_eq_true, if_false] at h
    obtain ⟨tag, -, e'⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at e'
    obtain ⟨rfl, rfl⟩ := e'
    have hput : ∀ y, HoonMap.get (HoonMap.put g.cond g.re (r, tag)) y =
        if y = g.re then some (r, tag) else HoonMap.get g.cond y := fun y => HoonMap.get_put ..
    have hrl : r < g.re := Nat.lt_of_lt_of_le hW.rlt hW.le
    refine ⟨⟨rfl, Nat.le_succ_of_le hW.le, hW.rlt, fun k v hk => ?_, fun k b hb => ?_, fun y hy => ?_,
      hW.rdef, ?_, fun k v hk => ?_⟩, rfl, Nat.lt_succ_self _, Nat.le_succ _, fun y hy => ?_,
      fun h => absurd h e⟩
    · change HoonMap.get (HoonMap.put g.cond g.re (r, tag)) k = some v at hk
      show k < g.re + 1
      rw [hput] at hk
      split at hk
      · omega
      · exact Nat.lt_succ_of_lt (hW.clt k v hk)
    · exact (hW.regs k b hb).mono fun _ hx => Nat.lt_succ_of_lt hx
    · show HoonMap.get (HoonMap.put g.cond g.re (r, tag)) y = Option.none
      have := defd_lt hW.regs hy
      rw [hput, if_neg (by omega)]
      exact hW.nokey y hy
    · show HoonMap.get (HoonMap.put g.cond g.re (r, tag)) r = Option.none
      rw [hput, if_neg (by omega)]
      exact hW.rkey
    · change HoonMap.get (HoonMap.put g.cond g.re (r, tag)) k = some v at hk
      rw [hput] at hk
      split at hk
      · rename_i ek
        cases hk
        exact Or.inr ⟨rfl, by have := hW.le; omega⟩
      · exact hW.keys k v hk
    · show HoonMap.get (HoonMap.put g.cond g.re (r, tag)) y = _
      rw [hput, if_neg (by omega)]

/-- **`+add-ops` keeps `CW`** when its ops mention registers below `re` and
define no key and not `r`. -/
theorem cw_addOps {r B x : Nat} {C0 : Map (Nat × List Nat)} {A : List Pole} {g g' : Comp.Gen Map}
    (hW : CW r B C0 g) (hA : ∀ p ∈ A, ∀ y ∈ Comp.poleRegs p, y < g.re)
    (hD : ∀ y ∈ defsOf A, HoonMap.get g.cond y = Option.none ∧ y ≠ r)
    (h : addOps x A g = some ((), g')) : CW r B C0 g' := by
  obtain ⟨⟨-, hdr, -, hre, -, -⟩, hc, hP⟩ := addOps_step hW.drop h
  have hdef : ∀ y, Defd g'.blocks y → Defd g.blocks y ∨ y ∈ defsOf A := by
    intro y hy
    obtain ⟨k, b, hb, hm⟩ := (defd_prep hP).mp hy
    rcases hm with hm | hm
    · exact Or.inl (defd_iff.mpr ⟨k, b, hb, hm⟩)
    · split at hm
      · exact Or.inr hm
      · simp [defsOf] at hm
  refine ⟨hdr.trans hW.drop, Nat.le_trans hW.le hre, hW.rlt, fun k v hk => ?_, fun k b hb => ?_, fun y hy => ?_,
    fun hy => ?_, by rw [hc]; exact hW.rkey, fun k v hk => by rw [hc] at hk; exact hW.keys k v hk⟩
  · rw [hc] at hk; exact Nat.lt_of_lt_of_le (hW.clt k v hk) hre
  · rw [hP k] at hb
    obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp hb
    have B0 := (hW.regs k b0 h0).mono fun x hx => Nat.lt_of_lt_of_le hx hre
    refine ⟨B0.1, ?_, B0.2.2⟩
    show RegsIn _ ((if k = x then A else []) ++ b0.body)
    refine RegsIn.append ?_ B0.2.1
    split
    · exact fun p hp y hy => Nat.lt_of_lt_of_le (hA p hp y hy) hre
    · exact RegsIn.nil _
  · rw [hc]
    rcases hdef y hy with h | h
    · exact hW.nokey y h
    · exact (hD y h).1
  · rcases hdef r hy with h | h
    · exact hW.rdef h
    · exact (hD r h).2 rfl

/-- **The gate of `+collapse-lazy-atom` keeps `CW`** at an entry whose need
is old and names no key of `C0`, and asks `r` only at the root `o`. -/
theorem collapseGate_cw {r o B x : Nat} {C0 : Map (Nat × List Nat)} {s : Sure S}
    (hs : ∀ y, NMem s.ned y → y < B ∧ HoonMap.get C0 y = Option.none) (hr : NMem s.ned r → x = o)
    {g g' : Comp.Gen Map} (hW : CW r B C0 g) (h : collapseGate r o x s g = some ((), g')) : CW r B C0 g' := by
  unfold collapseGate at h
  obtain ⟨ned, g1, h1, h2⟩ := bind_some h
  have L := sureRequireLook_spec h1
  obtain ⟨k, rfl⟩ := L.gen
  have hgk : g.re ≤ k := L.le
  have W1 := cw_re hW hgk
  have hm : ∀ y, NMem ned y → y < k ∧ HoonMap.get g.cond y = Option.none ∧ (y = r → x = o) := by
    intro y hy
    rcases L.mem y hy with h | ⟨h1, h2⟩
    · obtain ⟨a, b⟩ := hs y h
      exact ⟨by have := hW.le; omega, hW.old a b, fun e => hr (e ▸ h)⟩
    · refine ⟨h2, ?_, fun e => by have := hW.rlt; have := hW.le; omega⟩
      cases e : HoonMap.get g.cond y with
      | none => rfl
      | some v => have := hW.clt y v e; omega
  have crashC : ∀ ned' : Need, (∀ y, NMem ned' y → NMem ned y) →
      (do let src ← (if x = o then pure r else proxy r x : CM Map Nat); crashNeed x (Sum.inr src) ned' : CM Map Unit)
        ({ g with re := k } : Comp.Gen Map) = some ((), g') → CW r B C0 g' := by
    intro ned' hkeep h2
    obtain ⟨src, g2, h3, h4⟩ := bind_some h2
    obtain ⟨W2, -, hsrc, hre2, hc2, hxo⟩ := cw_src W1 h3
    simp only [crashNeed] at h4
    refine cw_addOps W2 (fun p hp y hy => ?_) (fun y hy => ?_) h4
    · rcases List.mem_cons.mp hp with rfl | hp
      · simp only [Comp.poleRegs, List.mem_singleton] at hy
        subst hy; exact hsrc
      · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hp
        simp only [Comp.poleRegs, List.mem_singleton] at hy
        subst hy
        have := (hm _ (hkeep _ ((mem_flatten ned' _).mp (List.mem_filter.mp hz).1))).1
        show _ < g2.re
        have : k ≤ g2.re := hre2
        omega
    · simp only [defsOf_cons, aliasDst, Option.toList_none, List.nil_append, defsOf_fill] at hy
      obtain ⟨hf, hne⟩ := List.mem_filter.mp hy
      have hne' : y ≠ src := by simpa using hne
      obtain ⟨hyk, hyc, hyr⟩ := hm y (hkeep y ((mem_flatten ned' y).mp hf))
      refine ⟨by rw [hc2 y hyk]; exact hyc, fun e => hne' ?_⟩
      rw [hxo (hyr e), e]
  cases ned with
  | none =>
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq, true_and] at h2
    subst h2; exact W1
  | this r' =>
    dsimp only at h2
    split at h2
    · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq, true_and] at h2
      subst h2; exact W1
    · rename_i hne
      obtain ⟨src, g2, h3, h4⟩ := bind_some h2
      obtain ⟨W2, -, hsrc, hre2, hc2, -⟩ := cw_src W1 h3
      obtain ⟨hk', hc', -⟩ := hm r' rfl
      refine cw_addOps W2 (fun p hp y hy => ?_) (fun y hy => ?_) h4
      · simp only [List.mem_singleton] at hp
        subst hp
        simp only [Comp.poleRegs, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl
        · exact hsrc
        · have : k ≤ g2.re := hre2
          show _ < g2.re
          omega
      · simp only [defsOf, aliasDst, List.filterMap_cons, List.filterMap_nil, List.mem_singleton] at hy
        subst hy
        exact ⟨by rw [hc2 _ hk']; exact hc', fun e => hne e.symm⟩
  | pair p q => exact crashC _ (fun y hy => hy) h2
  | both r0 p q => exact crashC _ (fun y hy => hy) h2

end Raw
end SkaModel
end Formalization
