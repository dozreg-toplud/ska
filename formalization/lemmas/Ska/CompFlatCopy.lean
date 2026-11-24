import lemmas.Ska.CompFlat

/-!
# `+copy` of flat lazy needs: the merge of two entries at one label

README Gaps 12.24.  `+copy-lazy` of two flat needs copies the sure needs at
its block, keeps the bonds of the first need whose label the second has not,
merges those it has (`+copy-lazy` of the two bonds' needs at the bond's own
block: `+copy-need-make-ops` puts its moves in front of that block,
`mergeBonds`), and appends the second need's bonds whose label the first has
not.  `%bc2`: `5: mov v0 v4, mov v4 v5, hop 3`, the halves `v3`, `v4` of the
tail's bond merged into `v3` with `mov v3 v4` in front of the bond block.

* `get_index_mem`: `index` of a list with distinct keys finds each entry.
* `MergeBs`, `mergeBonds_flat`: the loop of the merge over flat bonds.
* `copyLazy_ok`: `+copy-lazy` of two sure needs at a block, with the ops.
* `MergeBs.spec`: per label, the merged need and the ops in front of its
  block; the bonds the second need has not are kept.
* `copyLazyL_flat`, `copyL_flat`: `+copy` of two flat needs.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The index -/

theorem get_foldl_put_mem {α : Type} (key : α → Nat) : ∀ (l : List α) (m : Map α) {e : α},
    (l.map key).Nodup → e ∈ l → HoonMap.get (l.foldl (fun m e => HoonMap.put m (key e) e) m) (key e) = some e
  | [], _, _, _, he => by cases he
  | a :: rest, m, e, hn, he => by
    simp only [List.foldl_cons]
    have hn' : key a ∉ rest.map key ∧ (rest.map key).Nodup := List.nodup_cons.mp hn
    rcases List.mem_cons.mp he with rfl | he
    · rw [get_foldl_put_none key _ rest _ (fun e' he' x => hn'.1 (by rw [← x]; exact List.mem_map_of_mem he')),
        HoonMap.get_put, if_pos rfl]
    · exact get_foldl_put_mem key rest _ hn'.2 he

/-- **`index` of a list with distinct keys finds each entry.** -/
theorem get_index_mem {α : Type} (key : α → Nat) {l : List α} (hn : (l.map key).Nodup) {e : α} (he : e ∈ l) :
    HoonMap.get (index (Map := Map) key l) (key e) = some e :=
  get_foldl_put_mem key l HoonMap.empty hn he

/-- **`index` finds only entries of the list, under their key.** -/
theorem mem_of_get_index {α : Type} (key : α → Nat) {l : List α} {k : Nat} {e : α}
    (h : HoonMap.get (index (Map := Map) key l) k = some e) : e ∈ l ∧ key e = k := by
  unfold index at h
  suffices H : ∀ (l : List α) (m : Map α), HoonMap.get (l.foldl (fun m e => HoonMap.put m (key e) e) m) k = some e →
      (e ∈ l ∧ key e = k) ∨ HoonMap.get m k = some e by
    rcases H l HoonMap.empty h with h | h
    · exact h
    · rw [HoonMap.get_empty] at h; cases h
  intro l
  induction l with
  | nil => intro m h; exact Or.inr h
  | cons a rest ih =>
    intro m h
    simp only [List.foldl_cons] at h
    rcases ih _ h with ⟨h1, h2⟩ | h
    · exact Or.inl ⟨List.mem_cons_of_mem _ h1, h2⟩
    · rw [HoonMap.get_put] at h
      by_cases e1 : k = key a
      · rw [if_pos e1] at h
        cases h
        exact Or.inl ⟨List.mem_cons_self, e1.symm⟩
      · rw [if_neg e1] at h; exact Or.inr h

theorem seen_iff {α : Type} (key : α → Nat) (l : List α) (k : Nat) :
    seen (S := S) key l k = true ↔ k ∈ l.map key := by
  unfold seen
  rw [decide_eq_true_iff, mem_foldl_put]
  exact ⟨fun h => h.elim id (fun h => absurd h (HoonSet.mem_empty k)), Or.inl⟩

/-! ## `+copy-lazy` of two sure needs -/

/-- **`+copy-lazy` of two sure needs at a block**: `+copy-need-make-ops`,
then its ops in front of the block. -/
theorem copyLazy_ok {o : Nat} {s1 s2 s' : Sure S} {g g' : Gen Map} (h : copyLazy o s1 s2 g = some (s', g'))
    (hd : g.drop = false) :
    ∃ (A : List Pole) (g1 : Gen Map), Pref g g' (fun k => if k = o then A else []) ∧
      CopyOK s1.ned s2.ned g g1 s'.ned A ∧ g1.re = g'.re ∧ s'.lok = HoonSet.uni s1.lok s2.lok ∧
      (∀ (Pr : Nat → Prop), NA Pr s1.ned → NA Pr s2.ned → Ple Pr g.re → RegsIn Pr A) ∧
      (NB g.re s1.ned → NB g.re s2.ned → RegsIn (· < g'.re) A) := by
  simp only [copyLazy] at h
  obtain ⟨⟨ned, ops⟩, g1, h1, h⟩ := bind_some h
  obtain ⟨_, g2, h2, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨A, eA, O⟩ := copyNeed_spec _ _ _ _ _ _ h1
  simp only [List.append_nil] at eA
  subst eA
  have d1 : g1.drop = false := by rw [O.gen]; exact hd
  have P1 : Pref g g1 (fun _ => []) := pref_re O.gen O.le
  have P2 := pref_addOps h2 d1
  have e2 : g1.re = g2.re := by obtain ⟨b, hb, he⟩ := addOps_spec h2 d1; rw [he]
  exact ⟨ops, g1, (P1.trans P2).congr (fun k => by simp), O, e2, rfl,
    fun Pr ha hb hm => (keepsA_copyNeed h1 hm ha hb).2.2,
    fun ha hb => by rw [← e2]; exact copyNeed_regs _ _ _ _ _ _ h1 ha hb (RegsIn.nil _)⟩

/-! ## The merge of the bonds -/

/-- **The loop of the merge over flat bonds**: a bond whose label the index
has not is kept, one whose label it has is merged at its own block. -/
inductive MergeBs (idx : Map (Nat × Lazy S)) : List (Nat × Lazy S) → List (Nat × Lazy S) → Gen Map → Gen Map → Prop
  | nil (g : Gen Map) : MergeBs idx [] [] g g
  | keep {ob : Nat} {l : Lazy S} {rest r : List (Nat × Lazy S)} {g g' : Gen Map} :
      HoonMap.get idx ob = Option.none → MergeBs idx rest r g g' → MergeBs idx ((ob, l) :: rest) ((ob, l) :: r) g g'
  | merge {ob x : Nat} {s1 s2 s' : Sure S} {rest r : List (Nat × Lazy S)} {g g1 g' : Gen Map} :
      HoonMap.get idx ob = some (x, ofSure s2) → copyLazy ob s1 s2 g = some (s', g1) → MergeBs idx rest r g1 g' →
      MergeBs idx ((ob, ofSure s1) :: rest) ((ob, ofSure s') :: r) g g'

theorem mergeBonds_flat (idx : Map (Nat × Lazy S)) (hidx : ∀ k e, HoonMap.get idx k = some e → e.2 = ofSure e.2.sure) :
    ∀ (b : List (Nat × Lazy S)) (g g' : Gen Map) (r : List (Nat × Lazy S)),
    FlatB b → mergeBonds idx b g = some (r, g') → MergeBs idx b r g g'
  | [], g, g', r, _, h => by
    rw [mergeBonds, pure_apply] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact MergeBs.nil g
  | (ob, l) :: rest, g, g', r, hf, h => by
    rw [mergeBonds] at h
    obtain ⟨e, g1, h1, h⟩ := bind_some h
    obtain ⟨r', g2, h2, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ih := mergeBonds_flat idx hidx rest _ _ r' (fun e he => hf e (List.mem_cons_of_mem _ he)) h2
    cases hk : HoonMap.get idx ob with
    | none =>
      simp only [hk, pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      exact MergeBs.keep hk ih
    | some m =>
      rcases m with ⟨x, m⟩
      rw [hk] at h1
      simp only at h1
      obtain ⟨l', g3, h3, h1⟩ := bind_some h1
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      have el : l = ofSure l.sure := hf (ob, l) List.mem_cons_self
      have em : m = ofSure m.sure := hidx ob (x, m) hk
      rw [el, em, copyLazyL_ofSure] at h3
      obtain ⟨s', g4, h4, h3⟩ := bind_some h3
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
      obtain ⟨rfl, rfl⟩ := h3
      rw [em] at hk
      rw [el]
      exact MergeBs.merge hk h4 ih

/-- **What the merge does**: the labels of the first bonds kept, each bond
kept when the index has not its label, merged at its own block when the
index has it; nothing else but registers. -/
theorem MergeBs.spec {idx : Map (Nat × Lazy S)} {b r : List (Nat × Lazy S)} {g g' : Gen Map}
    (h : MergeBs idx b r g g') (hd : g.drop = false) (hn : (b.map Prod.fst).Nodup)
    (hb : ∀ e ∈ b, (HoonMap.get idx e.1).isSome → ∃ B fin, HoonMap.get g.blocks e.1 = some ⟨[], B, fin⟩) :
    r.map Prod.fst = b.map Prod.fst ∧
    ∃ P : Nat → List Pole, Pref g g' P ∧
      (∀ k, (k ∉ b.map Prod.fst ∨ HoonMap.get idx k = Option.none) → P k = []) ∧
      ∀ e ∈ b, (HoonMap.get idx e.1 = Option.none → e ∈ r) ∧
        ∀ x s2, HoonMap.get idx e.1 = some (x, ofSure s2) →
          ∃ (s1 s' : Sure S) (g1 g2 : Gen Map), e.2 = ofSure s1 ∧ (e.1, ofSure s') ∈ r ∧
            g.re ≤ g1.re ∧ g2.re ≤ g'.re ∧ g1.drop = false ∧
            (∀ B fin, HoonMap.get g.blocks e.1 = some ⟨[], B, fin⟩ →
              HoonMap.get g1.blocks e.1 = some ⟨[], B, fin⟩) ∧
            copyLazy e.1 s1 s2 g1 = some (s', g2) ∧
            (∀ A, Pref g1 g2 (fun k => if k = e.1 then A else []) → P e.1 = A) := by
  induction h with
  | nil g => exact ⟨rfl, fun _ => [], Pref.refl g, fun _ _ => rfl, fun e he => by cases he⟩
  | @keep ob l rest r g g' hk hr ih =>
    have hn' : (rest.map Prod.fst).Nodup := (List.nodup_cons.mp hn).2
    have ho : ob ∉ rest.map Prod.fst := (List.nodup_cons.mp hn).1
    obtain ⟨er, P, PP, Pout, Pin⟩ := ih hd hn' (fun e he hs => hb e (List.mem_cons_of_mem _ he) hs)
    refine ⟨by simp [er], P, PP, fun k hk' => ?_, fun e he => ?_⟩
    · rcases hk' with hk' | hk'
      · exact Pout k (Or.inl fun hm => hk' (List.mem_cons_of_mem _ hm))
      · exact Pout k (Or.inr hk')
    · rcases List.mem_cons.mp he with rfl | he
      · refine ⟨fun _ => List.mem_cons_self, fun x s2 hs => ?_⟩
        rw [hk] at hs; cases hs
      · obtain ⟨i1, i2⟩ := Pin e he
        refine ⟨fun h0 => List.mem_cons_of_mem _ (i1 h0), fun x s2 hs => ?_⟩
        obtain ⟨s1, s', g1, g2, e1, m1, l1, l2, dd, bb, cp, pp⟩ := i2 x s2 hs
        exact ⟨s1, s', g1, g2, e1, List.mem_cons_of_mem _ m1, l1, l2, dd, bb, cp, pp⟩
  | @merge ob x s1 s2 s' rest r g g1 g' hk hc hr ih =>
    have hn' : (rest.map Prod.fst).Nodup := (List.nodup_cons.mp hn).2
    have ho : ob ∉ rest.map Prod.fst := (List.nodup_cons.mp hn).1
    obtain ⟨B0, fin0, hb0⟩ := hb (ob, ofSure s1) List.mem_cons_self (by simp [hk])
    obtain ⟨A, -, P1, -, -, -, -⟩ := copyLazy_ok hc hd
    have d1 : g1.drop = false := P1.drop.trans hd
    obtain ⟨er, P, PP, Pout, Pin⟩ := ih d1 hn' (fun e he hs => by
      obtain ⟨B, fin, hbe⟩ := hb e (List.mem_cons_of_mem _ he) hs
      exact ⟨_, fin, P1.blk hbe⟩)
    refine ⟨by simp [er], fun k => P k ++ (if k = ob then A else []), P1.trans PP, fun k hk' => ?_, fun e he => ?_⟩
    · show P k ++ (if k = ob then A else []) = []
      rcases hk' with hk' | hk'
      · simp only [List.map_cons, List.mem_cons, not_or] at hk'
        rw [Pout k (Or.inl hk'.2), if_neg hk'.1]; rfl
      · have : k ≠ ob := fun e => by rw [e, hk] at hk'; cases hk'
        rw [Pout k (Or.inr hk'), if_neg this]; rfl
    · rcases List.mem_cons.mp he with rfl | he
      · refine ⟨fun h0 => (by rw [hk] at h0; cases h0), fun x' s2' hs => ?_⟩
        rw [hk] at hs
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        obtain ⟨rfl, hs⟩ := hs
        have e2 : s2' = s2 := by
          have := congrArg Lazy.sure hs; simpa [ofSure] using this.symm
        subst e2
        refine ⟨s1, s', g, g1, rfl, List.mem_cons_self, Nat.le_refl _, PP.re, hd, fun B fin h => h, hc,
          fun A' PA' => ?_⟩
        dsimp only
        rw [Pout ob (Or.inl ho), List.nil_append, if_pos rfl]
        have a1 := PA'.blk hb0
        have a2 := P1.blk hb0
        simp only [if_true] at a1 a2
        rw [a1] at a2
        simp only [Option.some.injEq, Blob.mk.injEq, true_and] at a2
        exact (List.append_cancel_right a2.1).symm
      · obtain ⟨i1, i2⟩ := Pin e he
        have hne : e.1 ≠ ob := fun x => ho (x ▸ List.mem_map_of_mem he)
        refine ⟨fun h0 => List.mem_cons_of_mem _ (i1 h0), fun x' s2' hs => ?_⟩
        obtain ⟨s1', s'', g1', g2', e1, m1, l1, l2, dd, bb, cp, pp⟩ := i2 x' s2' hs
        exact ⟨s1', s'', g1', g2', e1, List.mem_cons_of_mem _ m1, Nat.le_trans P1.re l1, l2, dd,
          fun B fin hB => bb B fin (by rw [P1.same (by simp [hne])]; exact hB), cp,
          fun A' PA' => by dsimp only; rw [pp A' PA', if_neg hne, List.append_nil]⟩

/-! ## `+copy` of flat needs -/

theorem index_nil_none (k : Nat) : HoonMap.get (index (Map := Map) (fun e : Nat × Lazy S => e.1) []) k = Option.none := by
  simp [index, HoonMap.get_empty]

theorem mergeBs_keepAll {idx : Map (Nat × Lazy S)} (hidx : ∀ k, HoonMap.get idx k = Option.none) :
    ∀ (b : List (Nat × Lazy S)) (g : Gen Map), MergeBs idx b b g g
  | [], g => MergeBs.nil g
  | (o, l) :: rest, g => MergeBs.keep (hidx o) (mergeBs_keepAll hidx rest g)

/-- The bonds of `+copy-lazy` are always the merge followed by the second's
other bonds (the two shortcuts of the Hoon agree with it). -/
theorem copyBonds_uni (b1 b2 : List (Nat × Lazy S)) :
    (if b2.isEmpty then pure b1 else if b1.isEmpty then pure b2 else do
      let merged ← mergeBonds (index (Map := Map) (fun e : Nat × Lazy S => e.1) b2) b1
      pure (merged ++ b2.filter fun e => !(seen (S := S) (fun e : Nat × Lazy S => e.1) b1 e.1)) :
        CM Map (List (Nat × Lazy S))) = (do
      let merged ← mergeBonds (index (Map := Map) (fun e : Nat × Lazy S => e.1) b2) b1
      pure (merged ++ b2.filter fun e => !(seen (S := S) (fun e : Nat × Lazy S => e.1) b1 e.1))) := by
  by_cases e2 : b2.isEmpty = true
  · rw [if_pos e2]
    have : b2 = [] := List.isEmpty_iff.mp e2
    subst this
    rw [mergeBonds_fresh _ b1 (fun e _ => index_nil_none (S := S) e.1), pure_bind]
    simp
  rw [if_neg e2]
  by_cases e1 : b1.isEmpty = true
  · rw [if_pos e1]
    have : b1 = [] := List.isEmpty_iff.mp e1
    subst this
    rw [mergeBonds, pure_bind, List.nil_append]
    congr 1
    exact (List.filter_eq_self.mpr fun e he => by
      have : seen (S := S) (fun e : Nat × Lazy S => e.1) ([] : List (Nat × Lazy S)) e.1 = false := by
        cases hs : seen (S := S) (fun e : Nat × Lazy S => e.1) ([] : List (Nat × Lazy S)) e.1
        · rfl
        · have := (seen_iff (S := S) _ _ _).mp hs; simp at this
      rw [this]; rfl).symm
  rw [if_neg e1]

/-- `+copy-lazy` when the second need has no fork: the bonds through the
merge. -/
theorem copyLazyL_uni (o : Nat) (s1 : Sure S) (f1 : List (ForkE S)) (b1 : List (Nat × Lazy S)) (second : Lazy S)
    (hf : second.fork = []) :
    (copyLazyL o (mk s1 f1 b1) second : CM Map (Lazy S)) = (do
      let (ned, ops) ← copyNeed s1.ned second.sure.ned []
      addOps o ops
      let merged ← mergeBonds (index (Map := Map) (fun e : Nat × Lazy S => e.1) second.bond) b1
      pure (mk ⟨ned, HoonSet.uni s1.lok second.sure.lok⟩ f1
        (merged ++ second.bond.filter fun e => !(seen (S := S) (fun e : Nat × Lazy S => e.1) b1 e.1)))) := by
  rw [copyLazyL]
  simp only [copyBonds_uni, hf, List.isEmpty_nil, ↓reduceIte, pure_bind, bind_assoc]

/-- **`+copy-lazy` of two flat needs**: the sure needs copied at the block,
the bonds merged, the second's other bonds appended. -/
theorem copyLazyL_flat {o : Nat} {s1 s2 : Sure S} {b1 b2 : List (Nat × Lazy S)} (h1 : FlatB b1) (h2 : FlatB b2)
    {g g' : Gen Map} {l : Lazy S} (h : copyLazyL o (mk s1 [] b1) (mk s2 [] b2) g = some (l, g')) :
    ∃ (ned : Need) (ops : List Pole) (g1 g2 : Gen Map) (r : List (Nat × Lazy S)),
      copyNeed s1.ned s2.ned [] g = some ((ned, ops), g1) ∧ addOps o ops g1 = some ((), g2) ∧
      MergeBs (index (Map := Map) (fun e : Nat × Lazy S => e.1) b2) b1 r g2 g' ∧
      l = mk ⟨ned, HoonSet.uni s1.lok s2.lok⟩ [] (r ++ b2.filter fun e => !(seen (S := S) (fun e : Nat × Lazy S => e.1) b1 e.1)) := by
  rw [copyLazyL_uni o s1 [] b1 (mk s2 [] b2) rfl] at h
  obtain ⟨⟨ned, ops⟩, g1, hc, h⟩ := bind_some h
  obtain ⟨u, g2, ha, h⟩ := bind_some h
  cases u
  obtain ⟨merged, g5, hm, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨ned, ops, g1, g2, merged, hc, ha,
    mergeBonds_flat _ (fun k e he => h2 e (mem_of_get_index _ he).1) b1 _ _ merged h1 hm, rfl⟩

/-- **`+copy` of two flat needs.** -/
theorem copyL_flat {first : NextL S} {second : Lazy S} (hf1 : Flat first.laz) (hf2 : Flat second)
    {g g' : Gen Map} {nex : NextL S} (h : copyL first second g = some (nex, g')) :
    nex.th = jmp0 g.bo ∧
    copyLazyL g.bo (mk first.laz.sure [] first.laz.bond) (mk second.sure [] second.bond)
      (g.emitted ⟨[], [], Termin.hop first.th⟩) = some (nex.laz, g') := by
  unfold copyL at h
  obtain ⟨o, g0, h0, h⟩ := bind_some h
  rw [emit_apply] at h0
  simp only [Option.some.injEq, Prod.mk.injEq] at h0
  obtain ⟨rfl, rfl⟩ := h0
  obtain ⟨laz, g1, h1, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨rfl, ?_⟩
  have e1 : first.laz = mk first.laz.sure [] first.laz.bond := by
    rw [← hf1.1]; exact (eta _).symm
  have e2 : second = mk second.sure [] second.bond := by
    rw [← hf2.1]; exact (eta _).symm
  rw [← e1, ← e2]
  exact h1

end Comp
end SkaModel
end Formalization
