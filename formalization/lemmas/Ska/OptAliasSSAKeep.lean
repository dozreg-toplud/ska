import lemmas.Ska.OptAliasSSA

/-!
# Passes that keep single assignment

**`filt_ssa`**: a map whose blocks are those of `bl` with every body filtered
by a test that keeps every op writing a register (same labels, parameters and
ends) keeps `AliasSSAB`.  The `j`-th op kept sits at place `fidx p l j` of the
body before (`|l|` past the last), which is monotone and strictly so on the
ops kept (`fidx_mono`, `fidx_lt_of`), sees the same op (`fidx_head`), the same
definitions before it (`fidx_defs`) and the same ops after it filtered
(`fidx_drop`).  A read after is a read before at `fidx`, a definition that
counts after is one before, and a dead fill before is one after.

**`trim_ssa`**: `+trim-trace-hints` drops trace hint ops only, which write no
register, so it keeps `AliasSSAB` (the field `trim` of `SSAKeep`), and
**`optimize_keeps_ssaR`** is `optimize_keeps_ssa` with the other four fields
(`SSAKeepR`) assumed.
-/

namespace Formalization
namespace SkaModel
namespace Opt
open Nock
variable {Map : Type → Type} [HoonMap Map] [MapKeys Map]

set_option linter.unusedSectionVars false

/-- The place in `l` of the `j`-th op that `p` keeps (`|l|` past the last). -/
def fidx (p : Pole → Bool) : List Pole → Nat → Nat
  | [], _ => 0
  | a :: l, j => if p a then (match j with | 0 => 0 | j + 1 => fidx p l j + 1) else fidx p l j + 1

theorem fidx_len (p : Pole → Bool) : ∀ (l : List Pole) (j : Nat), (l.filter p).length ≤ j → fidx p l j = l.length
  | [], _, _ => rfl
  | a :: l, j, h => by
    unfold fidx
    by_cases ha : p a = true
    · rw [List.filter_cons_of_pos ha, List.length_cons] at h
      obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      simp only [ha, if_true, List.length_cons]
      rw [fidx_len p l j (by omega)]
    · rw [List.filter_cons_of_neg ha] at h
      simp only [ha, List.length_cons]
      rw [fidx_len p l j h]; rfl

theorem fidx_head (p : Pole → Bool) : ∀ (l : List Pole) (j : Nat),
    ((l.filter p).drop j).head? = (l.drop (fidx p l j)).head?
  | [], _ => by simp [fidx]
  | a :: l, j => by
    unfold fidx
    by_cases ha : p a = true
    · rw [List.filter_cons_of_pos ha]
      cases j with
      | zero => simp [ha]
      | succ j => simp only [ha, if_true, List.drop_succ_cons]; exact fidx_head p l j
    · rw [List.filter_cons_of_neg ha]
      simp only [ha, Bool.false_eq_true, if_false, List.drop_succ_cons]; exact fidx_head p l j

theorem fidx_drop (p : Pole → Bool) : ∀ (l : List Pole) (j : Nat),
    (l.filter p).drop j = (l.drop (fidx p l j)).filter p
  | [], _ => by simp [fidx]
  | a :: l, j => by
    unfold fidx
    by_cases ha : p a = true
    · rw [List.filter_cons_of_pos ha]
      cases j with
      | zero => simp [ha]
      | succ j => simp only [ha, if_true, List.drop_succ_cons]; exact fidx_drop p l j
    · rw [List.filter_cons_of_neg ha]
      simp only [ha, Bool.false_eq_true, if_false, List.drop_succ_cons]; exact fidx_drop p l j

theorem filt_defs (p : Pole → Bool) (hp : ∀ op, p op = false → aliasDst op = none) :
    ∀ l : List Pole, (l.filter p).filterMap aliasDst = l.filterMap aliasDst
  | [] => rfl
  | a :: l => by
    by_cases ha : p a = true
    · rw [List.filter_cons_of_pos ha, List.filterMap_cons, List.filterMap_cons, filt_defs p hp l]
    · rw [List.filter_cons_of_neg ha, List.filterMap_cons, hp a (by simpa using ha), filt_defs p hp l]

theorem fidx_defs (p : Pole → Bool) (hp : ∀ op, p op = false → aliasDst op = none) :
    ∀ (l : List Pole) (j : Nat), ((l.filter p).take j).filterMap aliasDst = (l.take (fidx p l j)).filterMap aliasDst
  | [], _ => by simp [fidx]
  | a :: l, j => by
    unfold fidx
    by_cases ha : p a = true
    · rw [List.filter_cons_of_pos ha]
      cases j with
      | zero => simp [ha]
      | succ j =>
        simp only [ha, if_true, List.take_succ_cons, List.filterMap_cons]
        rw [fidx_defs p hp l j]
    · rw [List.filter_cons_of_neg ha]
      simp only [ha, Bool.false_eq_true, if_false, List.take_succ_cons, List.filterMap_cons]
      rw [hp a (by simpa using ha), fidx_defs p hp l j]

theorem fidx_mono (p : Pole → Bool) : ∀ (l : List Pole) (j₁ j₂ : Nat), j₁ ≤ j₂ → fidx p l j₁ ≤ fidx p l j₂
  | [], _, _, _ => Nat.le_refl _
  | a :: l, j₁, j₂, h => by
    unfold fidx
    by_cases ha : p a = true
    · simp only [ha, if_true]
      cases j₁ with
      | zero => cases j₂ <;> simp
      | succ j₁ =>
        cases j₂ with
        | zero => omega
        | succ j₂ => have := fidx_mono p l j₁ j₂ (by omega); simp only; omega
    · simp only [ha, Bool.false_eq_true, if_false]
      have := fidx_mono p l j₁ j₂ h; omega

theorem fidx_lt_of (p : Pole → Bool) : ∀ (l : List Pole) (j₁ j₂ : Nat), j₁ < j₂ → j₁ < (l.filter p).length →
    fidx p l j₁ < fidx p l j₂
  | [], _, _, _, h => by simp at h
  | a :: l, j₁, j₂, h, hl => by
    unfold fidx
    by_cases ha : p a = true
    · rw [List.filter_cons_of_pos ha, List.length_cons] at hl
      simp only [ha, if_true]
      cases j₁ with
      | zero =>
        cases j₂ with
        | zero => omega
        | succ j₂ => simp only; omega
      | succ j₁ =>
        cases j₂ with
        | zero => omega
        | succ j₂ => have := fidx_lt_of p l j₁ j₂ (by omega) (by omega); simp only; omega
    · rw [List.filter_cons_of_neg ha] at hl
      simp only [ha, Bool.false_eq_true, if_false]
      have := fidx_lt_of p l j₁ j₂ h hl; omega

section filt
variable {bl bl' : Map Blob} {p : Pole → Bool}
  (hg : ∀ o, HoonMap.get bl' o = (HoonMap.get bl o).map fun b => { b with body := b.body.filter p })
include hg

theorem reach_filt {o : Nat} (h : Reach bl' o) : Reach bl o := by
  induction h with
  | zero => exact Reach.zero
  | jump _ hb hj ih =>
    rw [hg] at hb
    obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.mp hb
    exact Reach.jump (j := _) ih hb0 hj

theorem bpath_filt {l : List Nat} (h : BPath bl' l) : BPath bl l := by
  induction h with
  | start => exact BPath.start
  | step _ hb hj ih =>
    rw [hg] at hb
    obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.mp hb
    exact BPath.step ih hb0 hj

theorem readAt_filt {b : Blob} {j r : Nat} (h : ReadAt { b with body := b.body.filter p } j r) :
    ReadAt b (fidx p b.body j) r := by
  rcases h with h | ⟨hj, h⟩
  · left; rw [← fidx_head]; exact h
  · right; exact ⟨fidx_len p b.body j (by simp at hj; omega), h⟩

end filt

/-- **Filtering bodies by a test that keeps every op writing a register keeps
`AliasSSAB`.** -/
theorem filt_ssa {bl bl' : Map Blob} {p : Pole → Bool}
    (hg : ∀ o, HoonMap.get bl' o = (HoonMap.get bl o).map fun b => { b with body := b.body.filter p })
    (hp : ∀ op, p op = false → aliasDst op = none) (h : AliasSSAB bl) : AliasSSAB bl' := by
  obtain ⟨h1, h2⟩ := h
  -- the place before of a definition after
  let sm : Nat × Option Nat → Nat × Option Nat := fun s =>
    match s.2 with
    | none => s
    | some i => (s.1, some (((HoonMap.get bl s.1).map fun b => fidx p b.body i).getD i))
  have live : ∀ r s, LiveDef bl' r s → LiveDef bl r (sm s) ∧
      (∀ i, s.2 = some i → ∃ b, HoonMap.get bl s.1 = some b ∧ i < (b.body.filter p).length ∧
        sm s = (s.1, some (fidx p b.body i))) := by
    rintro r ⟨o, _ | i⟩ ⟨hr, hd, hf⟩
    · obtain ⟨b', hb', hm⟩ := hd
      rw [hg] at hb'
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hb'
      exact ⟨⟨reach_filt hg hr, ⟨b, hb, hm⟩, fun _ h => by cases h⟩, fun _ h => by cases h⟩
    · obtain ⟨b', op, hb', hop, hdst⟩ := hd
      rw [hg] at hb'
      obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hb'
      have hlt : i < (b.body.filter p).length := (List.getElem?_eq_some_iff.mp hop).1
      have hop0 : b.body[fidx p b.body i]? = some op := by
        rw [← List.head?_drop, ← fidx_head, List.head?_drop]; exact hop
      have hsm : sm (o, some i) = (o, some (fidx p b.body i)) := by simp only [sm, hb, Option.map_some, Option.getD_some]
      refine ⟨?_, fun i2 h => by cases h; exact ⟨b, hb, hlt, hsm⟩⟩
      rw [hsm]
      refine ⟨reach_filt hg hr, ⟨b, op, hb, hop0, hdst⟩, fun i0 hi0 hdf => ?_⟩
      cases hi0
      apply hf i rfl
      obtain ⟨b1, hb1, hbom, ⟨n, hn⟩, himm, hrd⟩ := hdf
      rw [hb] at hb1; cases hb1
      refine ⟨{ b with body := b.body.filter p }, by rw [hg, hb]; rfl, hbom, ⟨n, ?_⟩, fun op' hop' => ?_, fun o' b'' j hr' hb'' hj => ?_⟩
      · rw [hop]; rw [hop0] at hn; exact hn
      · simp only at hop'
        rw [fidx_drop] at hop'
        exact himm op' (List.mem_filter.mp hop').1
      · rw [hg] at hb''
        obtain ⟨b2, hb2, rfl⟩ := Option.map_eq_some_iff.mp hb''
        obtain ⟨ho', hlt'⟩ := hrd o' b2 _ (reach_filt hg hr') hb2 (readAt_filt hg hj)
        subst ho'
        rw [hb] at hb2; cases hb2
        refine ⟨rfl, Classical.byContradiction fun hn' => ?_⟩
        have := fidx_mono p b.body i j (by omega)
        omega
  refine ⟨fun r s s' hs hs' => ?_, fun o pth b' hpath hb' i r hread hr => ?_⟩
  · obtain ⟨l1, e1⟩ := live r s hs
    obtain ⟨l2, e2⟩ := live r s' hs'
    have heq := h1 r _ _ l1 l2
    obtain ⟨o, _ | i⟩ := s <;> obtain ⟨o', _ | i'⟩ := s'
    · exact heq
    · obtain ⟨b, -, -, hsm⟩ := e2 i' rfl
      rw [hsm] at heq; cases heq
    · obtain ⟨b, -, -, hsm⟩ := e1 i rfl
      rw [hsm] at heq; cases heq
    · obtain ⟨b, hb, hlt, hsm⟩ := e1 i rfl
      obtain ⟨b2, hb2, hlt2, hsm2⟩ := e2 i' rfl
      rw [hsm, hsm2] at heq
      simp only [Prod.mk.injEq, Option.some.injEq] at heq
      obtain ⟨rfl, hfi⟩ := heq
      rw [hb] at hb2; cases hb2
      rcases Nat.lt_trichotomy i i' with hc | hc | hc
      · have := fidx_lt_of p b.body i i' hc hlt; omega
      · rw [hc]
      · have := fidx_lt_of p b.body i' i hc hlt2; omega
  · rw [hg] at hb'
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hb'
    have hr0 : r ∈ allDefs bl := by
      unfold allDefs at hr ⊢
      obtain ⟨k, hk, hmem⟩ := List.mem_flatMap.mp hr
      have hks : (HoonMap.get bl' k).isSome := (MapKeys.mem_keys bl' k).mp hk
      rw [hg] at hks hmem
      obtain ⟨bk, hbk⟩ := Option.isSome_iff_exists.mp (by simpa using hks)
      rw [hbk] at hmem
      refine List.mem_flatMap.mpr ⟨k, (MapKeys.mem_keys bl k).mpr (by rw [hbk]; rfl), ?_⟩
      rw [hbk]
      simpa [blockDefs, filt_defs p hp] using hmem
    rcases h2 o pth b (bpath_filt hg hpath) hb (fidx p b.body i) r (readAt_filt hg hread) hr0 with h | h | ⟨o', ho', b2, hb2, hm⟩
    · exact Or.inl h
    · right; left; rw [fidx_defs p hp]; exact h
    · right; right
      refine ⟨o', ho', _, by rw [hg, hb2]; rfl, ?_⟩
      simpa [blockDefs, filt_defs p hp] using hm

/-- **`+trim-trace-hints` keeps `AliasSSAB`** (the field `trim` of
`SSAKeep`): it drops trace hint ops only, which write no register. -/
theorem trim_ssa {bl : Map Blob} {topo : List Nat} {rev : Map (List Nat)} {bl' : Map Blob}
    (h : trimTraceHints bl topo rev = some bl') (hs : AliasSSAB bl) : AliasSSAB bl' := by
  unfold trimTraceHints at h
  obtain ⟨uns, -, rfl⟩ := Option.map_eq_some_iff.mp h
  refine filt_ssa (p := tkeep uns (trimOpened bl)) (trimRun_get bl uns (trimOpened bl)) (fun op hop => ?_) hs
  have hd : trimDrop uns (trimOpened bl) op = true := by simpa [tkeep] using hop
  obtain ⟨_, _, hk, -⟩ := trimDrop_true hd
  cases op <;> first | rfl | simp [traceKey] at hk

/-- **What is still assumed of the passes of the loop**: `SSAKeep` without
the field `trim`, which `trim_ssa` gives. -/
structure SSAKeepR (Map : Type → Type) [HoonMap Map] [MapKeys Map] (fuel : Nat) : Prop where
  hops : ∀ (bl : Map Blob) topo rev ch bl', DInvT bl → TopoInv bl topo rev → AliasSSAB bl →
    removeHops fuel bl rev topo = some (ch, bl') → AliasSSAB bl'
  rub : ∀ (bl : Map Blob) ch bl', DInvT bl → AliasSSAB bl → removeUselessBranching bl = some (ch, bl') →
    AliasSSAB bl'
  middle : ∀ (bl : Map Blob) ch bl', DInvT bl → AliasSSAB bl → removeEmptyMiddle fuel bl = some (ch, bl') →
    AliasSSAB bl'
  dead : ∀ (bl : Map Blob) topo rev bl', DInvT bl → TopoInv bl topo rev → AliasSSAB bl →
    removeDeadCode bl topo.reverse = some bl' → AliasSSAB bl'

theorem ssaKeep_of {fuel : Nat} (K : SSAKeepR Map fuel) : SSAKeep Map fuel :=
  ⟨K.hops, K.rub, K.middle, fun _ _ _ _ _ _ hs h => trim_ssa h hs, K.dead⟩

/-- **`+optimize` keeps the code** on blocks with `DInvS`, given the field
`alias` (`DriverRestSSA`) and that `+remove-hops`, `+remove-useless-branching`,
`+remove-empty-middle` and `+remove-dead-code` keep `AliasSSAB` (`SSAKeepR`). -/
theorem optimize_keeps_ssaR {fuel sfuel : Nat} {P : Passes Map} (H : DriverRestSSA fuel sfuel P)
    (K : SSAKeepR Map fuel) {s s' : Straight Map} (hb : DInvS s.blocks) (h : optimizeF fuel P s = some s') :
    Keeps s s' :=
  optimize_keeps_ssa H (ssaKeep_of K) hb h

end Opt
end SkaModel
end Formalization
