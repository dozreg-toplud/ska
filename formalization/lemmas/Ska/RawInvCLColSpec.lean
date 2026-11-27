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

/-- `entries` read only the forks and the bonds. -/
theorem entries_mkSure (s : Sure S) (laz : Lazy S) : entries (mk s laz.fork laz.bond) = entries laz := by
  cases laz; rfl

/-- **The spec of `+collapse-lazy-atom`.** -/
theorem collapseSpecL : CollapseSpecL S Map := by
  intro K laz th g0 g1 r there hI h
  have hd : g0.drop = false := hI.ats.1
  obtain ⟨hth, hap, hent⟩ := (hI.goal : GoalL g0 (CGoalL.next laz th))
  obtain ⟨bt, hbt, hpt, targs⟩ := hth
  obtain ⟨A1, KP1, hfr⟩ := (ht_collapse (⟨laz, th⟩ : NextL S)).run g0 _ g1 hI.ats ⟨bt, hbt, hpt, targs⟩ h
  have hfr' : Fresh g1 (jmp0 there) := hfr r there rfl
  have hroot : ∀ y, NMem laz.sure.ned y → y < g0.re ∧ ¬ Defd g0.blocks y := (hent _ (List.mem_cons_self ..)).2.2
  have hents : ∀ e ∈ entries laz, ∀ y, NMem e.2.sure.ned y → y < g0.re :=
    fun e he y hy => ((hent e (List.mem_cons_of_mem _ he)).2.2 y hy).1
  have hER := hI.entry_regs (o := th.there)
  have hapart : ∀ y, (NMem laz.sure.ned y ∨ g0.re ≤ y) → ∀ e ∈ entries laz, ¬ NMem e.2.sure.ned y := by
    intro y hy e he hm
    rcases hy with hy | hy
    · exact (List.pairwise_cons.mp hap).1 e he y hy hm
    · have := hents e he y hm; omega
  have hkey0 : ∀ y, (NMem laz.sure.ned y ∨ g0.re ≤ y) → HoonMap.get g0.cond y = Option.none := by
    intro y hy
    rcases hy with hy | hy
    · exact (hER _ (List.mem_cons_self ..) y hy).2
    · exact hI.cond_ge hy
  have hdef0 : ∀ y, (NMem laz.sure.ned y ∨ g0.re ≤ y) → ¬ Defd g0.blocks y := by
    intro y hy hdy
    rcases hy with hy | hy
    · exact (hroot y hy).2 hdy
    · have := defd_lt hI.regs hdy; omega
  have hthere : th.there < g0.bo := hI.lab hbt
  simp only [collapseLazyAtomL] at h
  have ha : ¬ (th.args ≠ []) := fun h' => h' targs
  rw [if_neg ha] at h
  by_cases hn : noneEquivalentL laz = true
  · rw [if_pos hn] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq, reduceCtorEq, false_and] at h
  rw [if_neg hn] at h
  obtain ⟨ned, ga, hga, h⟩ := bind_some h
  have L := sureRequireLook_spec hga
  obtain ⟨k, rfl⟩ := L.gen
  have hk : g0.re ≤ k := L.le
  obtain ⟨⟨r', there'⟩, gb, hb, h⟩ := bind_some h
  -- the emitted `%bom` block
  have hbomD : ∀ R y, Defd ((({ g0 with re := R } : Comp.Gen Map)).emitted ⟨[], [], Termin.bom Option.none⟩).blocks y →
      Defd g0.blocks y := by
    intro R y hy
    have e := (defd_put (b := (⟨[], [], Termin.bom Option.none⟩ : Blob)) hI.ats.free (r := y)).mp
      (by simpa [Gen.emitted, hd] using hy)
    rcases e with e | e
    · exact e
    · simp [blockDefs] at e
  have hbomR : ∀ R, g0.re ≤ R → ∀ k b, HoonMap.get ((({ g0 with re := R } : Comp.Gen Map)).emitted
      ⟨[], [], Termin.bom Option.none⟩).blocks k = some b → BlobIn (· < R) b := by
    intro R hR k b hb
    rw [em_get (g := ({ g0 with re := R } : Comp.Gen Map)) hd] at hb
    split at hb
    · cases hb; exact blobIn_nil_fin trivial
    · exact (hI.regs k b hb).mono fun _ hx => Nat.lt_of_lt_of_le hx hR
  have hbomL : ∀ R, ∃ b, HoonMap.get (unpM ((({ g0 with re := R } : Comp.Gen Map)).emitted
      ⟨[], [], Termin.bom Option.none⟩)) g0.bo = some b ∧ (∀ y, ¬ BlockRF b y) ∧ getJmps b.fin = [] := by
    intro R
    refine ⟨_, unpM_emitted_self (g := ({ g0 with re := R } : Comp.Gen Map)) hd _, fun y hy => ?_, rfl⟩
    obtain ⟨-, hy | ⟨-, hy⟩⟩ := hy
    · simp [renBlob, OpsRF] at hy
    · simp [renBlob, renFin, finRegs] at hy
  have hbomU : ∀ R x, x < g0.bo → HoonMap.get (unpM ((({ g0 with re := R } : Comp.Gen Map)).emitted
      ⟨[], [], Termin.bom Option.none⟩)) x = HoonMap.get (unpM g0) x := fun R x hx =>
    (unpM_emitted_lt (g := ({ g0 with re := R } : Comp.Gen Map)) hd _ hx).trans rfl
  -- the facts before the walk
  have P : gb.drop = false ∧ gb.cond = g0.cond ∧ g0.re ≤ gb.re ∧ r' < gb.re ∧
      (∀ k b, HoonMap.get gb.blocks k = some b → BlobIn (· < gb.re) b) ∧
      (∀ y, Defd gb.blocks y → Defd g0.blocks y) ∧
      (NMem laz.sure.ned r' ∨ g0.re ≤ r') ∧
      (∀ x, x < g0.bo → HoonMap.get (unpM gb) x = HoonMap.get (unpM g0) x) ∧
      ((there' = th.there ∧ ∀ y, NMem laz.sure.ned y → y = r') ∨
        (∃ b, HoonMap.get (unpM gb) there' = some b ∧ (∀ y, ¬ BlockRF b y) ∧ getJmps b.fin = [])) := by
    cases ned with
    | this r0 =>
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hb
      have hm := L.mem r0 rfl
      refine ⟨hd, rfl, hk, ?_, fun k b hb => (hI.regs k b hb).mono fun _ hx => Nat.lt_of_lt_of_le hx hk,
        fun y hy => hy, hm.imp id fun h => h.1, fun _ _ => rfl,
        Or.inl ⟨rfl, fun y hy => sureRequireLook_keeps hga hy⟩⟩
      rcases hm with hm | hm
      · have := (hroot r0 hm).1; show r0 < k; omega
      · exact hm.2
    | none =>
      obtain ⟨x, gx, hx, hb⟩ := bind_some hb
      rw [re_apply] at hx
      simp only [Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hb
      refine ⟨hd, rfl, Nat.le_succ_of_le hk, Nat.lt_succ_self _,
        fun k' b hb => (hI.regs k' b hb).mono fun _ hx => Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le hx hk),
        fun y hy => hy, Or.inr hk, fun _ _ => rfl,
        Or.inl ⟨rfl, fun y hy => (sureRequireLook_keeps hga hy).elim⟩⟩
    | pair p q =>
      obtain ⟨x, gx, hx, hb⟩ := bind_some hb
      rw [re_apply] at hx
      simp only [Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      obtain ⟨o, gy, hy, hb⟩ := bind_some hb
      rw [emit_apply] at hy
      simp only [Option.some.injEq, Prod.mk.injEq] at hy
      obtain ⟨rfl, rfl⟩ := hy
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hb
      exact ⟨hd, rfl, Nat.le_succ_of_le hk, Nat.lt_succ_self _, hbomR _ (Nat.le_succ_of_le hk),
        hbomD _, Or.inr hk, hbomU _, Or.inr (hbomL _)⟩
    | both r0 p q =>
      obtain ⟨o, gy, hy, hb⟩ := bind_some hb
      rw [emit_apply] at hy
      simp only [Option.some.injEq, Prod.mk.injEq] at hy
      obtain ⟨rfl, rfl⟩ := hy
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hb
      have hm := L.mem r0 (Or.inl rfl)
      refine ⟨hd, rfl, hk, ?_, hbomR _ hk, hbomD _, hm.imp id fun h => h.1, hbomU _, Or.inr (hbomL _)⟩
      rcases hm with hm | hm
      · have := (hroot r0 hm).1; show r0 < k; omega
      · exact hm.2
  obtain ⟨Pd, Pc, Pre, Pr, Preg, Pdef, Pold, Pun, Plive⟩ := P
  obtain ⟨g', gc, hc, h⟩ := bind_some h
  simp only [get_apply, Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  simp only [Pd, Bool.false_eq_true, if_false] at h
  obtain ⟨u, gd, hw, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  subst r' there' gd
  -- the walk keeps `CW`
  have W0 : CW r gb.re gb.cond gb := by
    refine ⟨Pd, Nat.le_refl _, Pr, fun k v hk => ?_, Preg, fun y hy => ?_, fun hy => hdef0 r Pold (Pdef r hy), ?_,
      fun k v hk => Or.inl hk⟩
    · rw [Pc] at hk; exact Nat.lt_of_lt_of_le (hI.cond_lt k v hk) Pre
    · rw [Pc]
      cases e : HoonMap.get g0.cond y with
      | none => rfl
      | some v => exact absurd (Pdef y hy) (hI.cond y v e).2.1
    · rw [Pc]; exact hkey0 r Pold
  have W1 : CW r gb.re gb.cond g1 := by
    refine walkLazy_inv (W := CW r gb.re gb.cond) (fun e he a b hW hg => ?_) W0 hw
    rcases List.mem_cons.mp he with rfl | he
    · refine collapseGate_cw (fun y hy => ?_) (fun _ => rfl) hW hg
      have e : y = r := hy
      subst e
      exact ⟨Pr, by rw [Pc]; exact hkey0 _ Pold⟩
    · rw [entries_mkSure] at he
      exact collapseGate_cw (fun y hy => ⟨Nat.lt_of_lt_of_le (hents e he y hy) Pre,
        by rw [Pc]; exact (hER e (List.mem_cons_of_mem _ he) y hy).2⟩)
        (fun hm => (hapart r Pold e he hm).elim) hW hg
  have hre1 : gb.re ≤ g1.re := W1.le
  refine ⟨⟨A1, W1.regs, fun k v hk => ?_, hI.kvan.mono KP1.2.1, hfr', ?_, fun e he => ?_⟩, ?_⟩
  · refine ⟨W1.clt k v hk, fun hdk => ?_, fun hg => ?_, ?_, ?_⟩
    · rw [W1.nokey k hdk] at hk; cases hk
    · have e : k = r := gregL_ofSure.mp hg
      subst e; rw [W1.rkey] at hk; cases hk
    · rcases W1.keys k v hk with h | ⟨h, -⟩
      · rw [Pc] at h; exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (hI.cond k v h).2.2.2.1 Pre) hre1
      · rw [h]; exact Nat.lt_of_lt_of_le Pr hre1
    · rcases W1.keys k v hk with h | ⟨h, -⟩
      · rw [Pc] at h
        obtain ⟨-, -, -, k4, k5⟩ := hI.cond k v h
        exact W1.old (Nat.lt_of_lt_of_le k4 Pre) (by rw [Pc]; exact k5)
      · rw [h]; exact W1.rkey
  · rw [entries_ofSure]; exact List.pairwise_singleton _ _
  · rw [entries_ofSure, List.mem_singleton] at he
    subst he
    obtain ⟨b, hb, hp, -⟩ := hfr'
    refine ⟨⟨b, hb, hp⟩, trivial, fun y hy => ?_⟩
    have e : y = r := hy
    subst e
    exact ⟨Nat.lt_of_lt_of_le Pr hre1, W1.rdef⟩
  -- the liveness
  intro y hl
  have hyr : y ≠ r := by
    intro e; subst e
    cases hl with
    | here _ _ hk => exact hk (Or.inr (lazK_ofSure.mpr ⟨rfl, rfl⟩))
    | next _ _ _ _ hk => exact hk (Or.inr (lazK_ofSure.mpr ⟨rfl, rfl⟩))
  obtain ⟨St, P, hP, hkill, hread, -⟩ := collapseWalk_prep Pd (fun k v hk => W0.clt k v hk) hw
  have hc : ∀ x, x < gb.re → HoonMap.get g1.cond x = HoonMap.get gb.cond x := fun x hx => St.1.cond_below hx
  have hl2 := liveK_walkR (R0 := r) hP hc Preg (fun k x hx => rCol_unproxy W1.rkey (hread k x hx)) hyr hl
  rcases Plive with ⟨ethere, hroot'⟩ | ⟨b, hb, hrf, hj⟩
  · subst ethere
    have hl3 := (liveK_frameP hI.downU Pun hthere).mp hl2
    refine hl3.mono_r fun x hx => ?_
    rcases hx with hk | ⟨e, he, ex, hm⟩
    · exact Or.inl (Or.inl hk)
    · rcases List.mem_cons.mp he with rfl | he
      · exact (hyr (hroot' y hm)).elim
      · refine Or.inr ?_
        have hm' := hkill e (List.mem_cons_of_mem _ (by rw [entries_mkSure]; exact he)) y hm
        rcases hm' with (h | h) | h
        · exact (hyr h).elim
        · have := hents e he y hm; omega
        · rw [defsOf_ren]
          refine List.mem_map.mpr ⟨y, ex ▸ h, unproxy_none ?_⟩
          exact W1.old (Nat.lt_of_lt_of_le (hents e he y hm) Pre)
            (by rw [Pc]; exact (hER e (List.mem_cons_of_mem _ he) y hm).2)
  · exact (liveK_dead hb hrf hj y hl2).elim

end Raw
end SkaModel
end Formalization
