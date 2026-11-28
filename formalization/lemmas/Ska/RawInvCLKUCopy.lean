import lemmas.Ska.RawInvCLKUBase

/-!
# The state-free count of `+copy` and `+past`; `re` and `bo` of the walks

README Gaps 14 (b), track D.  Fields of `KUSteps` (`RawInvCLKUBase.lean`),
with no precondition on the state: the count of `RawInvCLSACountCopy.lean`
without the definitions of the map.

* `kucR La Lc g g'`: the count of a merge of the entries `La` into `Lc`
  (`re`, `bo` grow; registers of `Lc` at most those of `La` plus one per
  fresh register); `kucR.keep`, `kucR.seq`, `kucR.congr`, `kuc_root`.
* **`kuc_copyLazyL`** (mutual with `kuc_mergeForks`, `kuc_mergeBonds`):
  both trees `LabUniq`, the induction of `sccp_copyLazyL`.
* **`kuc_copy`**: the field `copy`; **`kuc_past`**: the field `past`.
* `RB` of the gates and walks: `kuc_sure`, `kuc_crashNeed`, `kuc_kernBoth`,
  `kuc_kernLoop`, `kuc_walkLazy` (mutual with `kuc_walkForks`,
  `kuc_walkBonds`), `kuc_collapseGate`, `kuc_kern`; **`kuc_collapse`**,
  **`kuc_kerf`**: the fields `collapse` and `kerf`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The count of a merge -/

/-- **The count of a merge** of the entries `La` into `Lc`, with no state
clause. -/
structure kucR (La Lc : List (Nat × Lazy S)) (g g' : Comp.Gen Map) : Prop where
  le : g.re ≤ g'.re
  bo : g.bo ≤ g'.bo
  cnt : ∀ y, List.count y (regsL Lc) ≤ List.count y (regsL La) + fr g.re g'.re y

theorem kucR.keep (L : List (Nat × Lazy S)) (g : Comp.Gen Map) : kucR L L g g :=
  ⟨Nat.le_refl _, Nat.le_refl _, fun _ => Nat.le_add_right _ _⟩

theorem kucR.seq {La1 Lc1 La2 Lc2 : List (Nat × Lazy S)} {g g1 g2 : Comp.Gen Map} (h1 : kucR La1 Lc1 g g1)
    (h2 : kucR La2 Lc2 g1 g2) : kucR (La1 ++ La2) (Lc1 ++ Lc2) g g2 := by
  refine ⟨Nat.le_trans h1.le h2.le, Nat.le_trans h1.bo h2.bo, fun y => ?_⟩
  have a1 := h1.cnt y
  have a2 := h2.cnt y
  have f := fr_add h1.le h2.le y
  simp only [regsL_append, List.count_append]
  omega

theorem kucR.congr {La Lc La' Lc' : List (Nat × Lazy S)} {g g' : Comp.Gen Map} (h : kucR La Lc g g')
    (ha : ∀ y, List.count y (regsL La) ≤ List.count y (regsL La'))
    (hc : ∀ y, List.count y (regsL Lc') ≤ List.count y (regsL Lc)) : kucR La' Lc' g g' := by
  refine ⟨h.le, h.bo, fun y => ?_⟩
  have := h.cnt y
  have := ha y
  have := hc y
  omega

theorem kuc_root {t : Nat} {a b c : Lazy S} {ned : Need} {ops : List Pole} {g g1 g2 : Comp.Gen Map}
    (hc : c.sure.ned = ned) (h1 : copyNeed a.sure.ned b.sure.ned [] g = some ((ned, ops), g1))
    (h2 : addOps t ops g1 = some ((), g2)) : kucR [(t, a), (t, b)] [(t, c)] g g2 := by
  obtain ⟨A, -, C⟩ := copyNeed_spec _ _ _ _ _ _ h1
  obtain ⟨new, enew, -, cn⟩ := cn_count _ _ _ _ _ _ h1
  dsimp only at cn
  have hb1 : g1.bo = g.bo := by rw [C.gen]
  obtain ⟨l2, b2⟩ := rb_addOps (Map := Map) t ops g1 () g2 h2
  refine ⟨Nat.le_trans C.le l2, by omega, fun y => ?_⟩
  have h3 := cn y
  have f := fr_add C.le l2 y
  simp only [regsL_cons, regsL_nil, List.append_nil, hc, List.count_append] at h3 ⊢
  omega

/-! ## The merge -/

mutual
/-- **The count of the merge of two `LabUniq` trees at `t`**, with no state
clause. -/
theorem kuc_copyLazyL (t : Nat) : ∀ (a b : Lazy S) (g g' : Comp.Gen Map) (c : Lazy S),
    copyLazyL t a b g = some (c, g') → LabUniq a → LabUniq b →
    kucR (((t, a) :: entries a) ++ ((t, b) :: entries b)) ((t, c) :: entries c) g g'
  | mk s1 f1 b1, second, g, g', c, h, hUa, hU => by
    rw [copyLazyL] at h
    obtain ⟨⟨ned, ops⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨u, g2, h2, h⟩ := bind_some h
    obtain ⟨fork, g3, h3, h⟩ := bind_some h
    obtain ⟨bond, g4, h4, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hea : entries (mk s1 f1 b1) = bondEntries b1 ++ forkEntries f1 := rfl
    have heb := entries_parts second
    have hU0 := hU (0, second) List.mem_cons_self
    have hUa0 := hUa (0, mk s1 f1 b1) List.mem_cons_self
    have R1 := kuc_root (t := t) (c := mk ⟨ned, HoonSet.uni s1.lok second.sure.lok⟩ fork bond)
      (a := mk s1 f1 b1) rfl h1 (by cases u; exact h2)
    -- the forks
    have R2 : kucR (forkEntries f1 ++ forkEntries second.fork) (forkEntries fork) g2 g3 := by
      by_cases c1 : second.fork.isEmpty = true
      · rw [if_pos c1] at h3
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
        obtain ⟨rfl, rfl⟩ := h3
        exact (kucR.keep _ g2).congr (fun x => by rw [regsL_append, List.count_append]; omega)
          (fun x => Nat.le_refl _)
      rw [if_neg c1] at h3
      by_cases c2 : f1.isEmpty = true
      · rw [if_pos c2] at h3
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
        obtain ⟨rfl, rfl⟩ := h3
        exact (kucR.keep _ g2).congr (fun x => by rw [regsL_append, List.count_append]; omega)
          (fun x => Nat.le_refl _)
      rw [if_neg c2] at h3
      obtain ⟨merged, g3', hm, h3⟩ := bind_some h3
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
      obtain ⟨rfl, rfl⟩ := h3
      have M := kuc_mergeForks (index (Map := Map) (fun e : ForkE S => e.1.1) second.fork) f1 g2 g3' merged
        hm (fun v hv => by
          have hsub := fe_sub hv
          rw [fe_single] at hsub
          exact ⟨labUniq_of hUa (o := v.1.1) fun e he => by
              rw [hea]; exact List.mem_append_right _ (hsub e (List.mem_append_left _ he)),
            labUniq_of hUa (o := v.2.1) fun e he => by
              rw [hea]; exact List.mem_append_right _ (hsub e (List.mem_append_right _ he))⟩)
        (fun k v hk => by
          obtain ⟨hv, hkv⟩ := gm_index_get _ hk
          have hsub := fe_sub hv
          rw [fe_single] at hsub
          exact ⟨labUniq_of hU (o := v.1.1) fun e he => by
              rw [heb]; exact List.mem_append_right _ (hsub e (List.mem_append_left _ he)),
            labUniq_of hU (o := v.2.1) fun e he => by
              rw [heb]; exact List.mem_append_right _ (hsub e (List.mem_append_right _ he)), hkv⟩)
      refine (M.seq (kucR.keep (forkEntries (second.fork.filter fun e =>
        !(seen (S := S) (fun e : ForkE S => e.1.1) f1 e.1.1))) g3')).congr (fun x => ?_) (fun x => ?_)
      · have := count_split_fe (Map := Map) (f1 := f1) (sf := second.fork) hUa0.2 hU0.2 x
        simp only [regsL_append, List.count_append] at this ⊢
        omega
      · rw [fe_append]; exact Nat.le_refl _
    -- the bonds
    have R3 : kucR (bondEntries b1 ++ bondEntries second.bond) (bondEntries bond) g3 g4 := by
      by_cases c1 : second.bond.isEmpty = true
      · rw [if_pos c1] at h4
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h4
        obtain ⟨rfl, rfl⟩ := h4
        exact (kucR.keep _ g3).congr (fun x => by rw [regsL_append, List.count_append]; omega)
          (fun x => Nat.le_refl _)
      rw [if_neg c1] at h4
      by_cases c2 : b1.isEmpty = true
      · rw [if_pos c2] at h4
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h4
        obtain ⟨rfl, rfl⟩ := h4
        exact (kucR.keep _ g3).congr (fun x => by rw [regsL_append, List.count_append]; omega)
          (fun x => Nat.le_refl _)
      rw [if_neg c2] at h4
      obtain ⟨merged, g4', hm, h4⟩ := bind_some h4
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h4
      obtain ⟨rfl, rfl⟩ := h4
      have M := kuc_mergeBonds (index (Map := Map) (fun e : Nat × Lazy S => e.1) second.bond) b1 g3 g4'
        merged hm (fun v hv => by
          have hsub := be_sub hv
          rw [be_single] at hsub
          exact labUniq_of hUa (o := v.1) fun e he => by rw [hea]; exact List.mem_append_left _ (hsub e he))
        (fun k v hk => by
          obtain ⟨hv, hkv⟩ := gm_index_get _ hk
          have hsub := be_sub hv
          rw [be_single] at hsub
          exact ⟨labUniq_of hU (o := v.1) fun e he => by rw [heb]; exact List.mem_append_left _ (hsub e he), hkv⟩)
      refine (M.seq (kucR.keep (bondEntries (second.bond.filter fun e =>
        !(seen (S := S) (fun e : Nat × Lazy S => e.1) b1 e.1))) g4')).congr (fun x => ?_) (fun x => ?_)
      · have := count_split_be (Map := Map) (b1 := b1) (sb := second.bond) hUa0.1 hU0.1 x
        simp only [regsL_append, List.count_append] at this ⊢
        omega
      · rw [be_append]; exact Nat.le_refl _
    refine ((R1.seq R2).seq R3).congr (fun x => ?_) (fun x => ?_)
    · rw [hea, heb]
      simp only [regsL_append, regsL_cons, regsL_nil, List.count_append, List.cons_append, List.nil_append]
      omega
    · show List.count x (regsL ((t, _) :: (bondEntries bond ++ forkEntries fork))) ≤ _
      simp only [regsL_append, regsL_cons, regsL_nil, List.count_append, List.cons_append, List.nil_append]
      omega

/-- The forks of the merge, counted. -/
theorem kuc_mergeForks (idx : Map (ForkE S)) :
    ∀ (l : List (ForkE S)) (g g' : Comp.Gen Map) (l' : List (ForkE S)),
    mergeForks idx l g = some (l', g') → (∀ v ∈ l, LabUniq v.1.2 ∧ LabUniq v.2.2) →
    (∀ k v, HoonMap.get idx k = some v → LabUniq v.1.2 ∧ LabUniq v.2.2 ∧ v.1.1 = k) →
    kucR (forkEntries l ++ forkEntries (l.filterMap fun fe => HoonMap.get idx fe.1.1)) (forkEntries l') g g'
  | [], g, g', l', h, _, _ => by
    rw [mergeForks] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (kucR.keep [] g).congr (fun x => by simp [forkEntries, regsL]) (fun x => by simp [forkEntries, regsL])
  | ((oy, y), (on, n)) :: rest, g, g', l', h, hUl, hidx => by
    rw [mergeForks] at h
    obtain ⟨e, g1, h1, h⟩ := bind_some h
    obtain ⟨r, g2, h2, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hcons : ∀ (w : ForkE S) (ws : List (ForkE S)), forkEntries (w :: ws) = forkEntries [w] ++ forkEntries ws :=
      fun w ws => fe_append [w] ws
    have hU1 := hUl _ List.mem_cons_self
    have hUr : ∀ v ∈ rest, LabUniq v.1.2 ∧ LabUniq v.2.2 := fun v hv => hUl v (List.mem_cons_of_mem _ hv)
    have E : kucR (forkEntries [((oy, y), (on, n))] ++ forkEntries (HoonMap.get idx oy).toList)
        (forkEntries [e]) g g1 := by
      rcases hk : HoonMap.get idx oy with _ | ⟨⟨z, my⟩, ⟨mon, mn⟩⟩
      · rw [hk] at h1
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        exact (kucR.keep _ g).congr (fun x => by rw [regsL_append, List.count_append]; omega)
          (fun x => Nat.le_refl _)
      · rw [hk] at h1
        obtain ⟨hU1', hU2', hz⟩ := hidx oy _ hk
        dsimp only at hz
        subst hz
        dsimp only at h1
        by_cases ce : on = mon
        · rw [if_pos ce] at h1
          subst ce
          obtain ⟨y', ga, hya, h1⟩ := bind_some h1
          obtain ⟨n', gb, hnb, h1⟩ := bind_some h1
          simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
          obtain ⟨rfl, rfl⟩ := h1
          have A := kuc_copyLazyL z y my g ga y' hya hU1.1 hU1'
          have B := kuc_copyLazyL on n mn ga gb n' hnb hU1.2 hU2'
          refine (A.seq B).congr (fun x => ?_) (fun x => ?_)
          · simp only [Option.toList, fe_single, regsL_append, regsL_cons, List.count_append]
            omega
          · simp only [fe_single, regsL_append, regsL_cons, List.count_append]
            omega
        · rw [if_neg ce] at h1
          cases h1
    have R := kuc_mergeForks idx rest g1 g2 r h2 hUr hidx
    refine (E.seq R).congr (fun x => ?_) (fun x => ?_)
    · rw [hcons ((oy, y), (on, n)) rest]
      simp only [filterMap_cons_toList, fe_append, regsL_append, List.count_append]
      omega
    · rw [hcons e r]; exact Nat.le_refl _

/-- The bonds of the merge, counted. -/
theorem kuc_mergeBonds (idx : Map (Nat × Lazy S)) :
    ∀ (l : List (Nat × Lazy S)) (g g' : Comp.Gen Map) (l' : List (Nat × Lazy S)),
    mergeBonds idx l g = some (l', g') → (∀ v ∈ l, LabUniq v.2) →
    (∀ k v, HoonMap.get idx k = some v → LabUniq v.2 ∧ v.1 = k) →
    kucR (bondEntries l ++ bondEntries (l.filterMap fun e => HoonMap.get idx e.1)) (bondEntries l') g g'
  | [], g, g', l', h, _, _ => by
    rw [mergeBonds] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (kucR.keep [] g).congr (fun x => by simp [bondEntries, regsL]) (fun x => by simp [bondEntries, regsL])
  | (ob, lb) :: rest, g, g', l', h, hUl, hidx => by
    rw [mergeBonds] at h
    obtain ⟨e, g1, h1, h⟩ := bind_some h
    obtain ⟨r, g2, h2, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hcons : ∀ (w : Nat × Lazy S) (ws : List (Nat × Lazy S)), bondEntries (w :: ws) = bondEntries [w] ++ bondEntries ws :=
      fun w ws => be_append [w] ws
    have hU1 := hUl _ List.mem_cons_self
    have hUr : ∀ v ∈ rest, LabUniq v.2 := fun v hv => hUl v (List.mem_cons_of_mem _ hv)
    have E : kucR (bondEntries [(ob, lb)] ++ bondEntries (HoonMap.get idx ob).toList) (bondEntries [e]) g g1 := by
      rcases hk : HoonMap.get idx ob with _ | ⟨z, m⟩
      · rw [hk] at h1
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        exact (kucR.keep _ g).congr (fun x => by rw [regsL_append, List.count_append]; omega)
          (fun x => Nat.le_refl _)
      · rw [hk] at h1
        obtain ⟨hU1', hz⟩ := hidx ob _ hk
        dsimp only at hz
        subst hz
        dsimp only at h1
        obtain ⟨l2, ga, hla, h1⟩ := bind_some h1
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        have A := kuc_copyLazyL z lb m g ga l2 hla hU1 hU1'
        refine A.congr (fun x => ?_) (fun x => ?_)
        · simp only [Option.toList, be_single, regsL_append, regsL_cons, List.count_append]
          omega
        · simp only [be_single, regsL_append, regsL_cons, List.count_append]
          omega
    have R := kuc_mergeBonds idx rest g1 g2 r h2 hUr hidx
    refine (E.seq R).congr (fun x => ?_) (fun x => ?_)
    · rw [hcons (ob, lb) rest]
      simp only [filterMap_cons_toList, be_append, regsL_append, List.count_append]
      omega
    · rw [hcons e r]; exact Nat.le_refl _
end

/-! ## The fields `copy` and `past` -/

/-- **The field `copy`**, with no state clause. -/
theorem kuc_copy : ∀ (first : NextL S) (second : Lazy S), LabUniq first.laz → LabUniq second →
    KUC (Map := Map) (sarR first.laz ++ sarR second) (copyL first second) (fun x => sarR x.laz) := by
  intro first second hU1 hU2
  unfold copyL
  refine ku_bind (ku_emit _ _) fun o => ?_
  refine ku_bind (r1 := fun l => sarR l) ?_ fun l => ku_pure fun _ => Nat.le_refl _
  intro g c g' h
  have R := kuc_copyLazyL o first.laz second g g' c h hU1 hU2
  refine ⟨R.le, R.bo, fun y => ?_⟩
  have := R.cnt y
  simp only [List.cons_append, regsL_cons, regsL_append, sarR, List.count_append] at this ⊢
  omega

/-- **The field `past`**: `+past` keeps the registers of the tree. -/
theorem kuc_past (cod : Bell → Option Bool) (nex : NextL S) (nom : Nomm) (region : List Nat) :
    KUC (Map := Map) (sarR nex.laz) (pastL cod nex nom region) (fun x => sarR x.laz) := by
  unfold pastL
  refine ku_ite _ (ku_pure fun _ => Nat.le_refl _) ?_
  split
  · exact ku_fail
  · exact ku_pure fun _ => Nat.le_refl _
  · refine ku_bind (ku_emit (sarR nex.laz) _) fun o => ku_bind (ku_setTag _ _ _) fun _ => ku_pure fun y => ?_
    obtain ⟨s, f, b⟩ := nex.laz
    simp [sarR, entries, bondEntries, forkEntries, regsL_append, regsL_cons, regsL_nil, List.count_append,
      Sure.bunt, flattenNeed]
    omega

/-! ## `re` and `bo` of the gates and walks -/

theorem kuc_sure (sur : Sure S) : RB (Map := Map) (sureRequireLook sur : CM Map Need) := by
  intro g x g' h
  have L := sureRequireLook_spec h
  obtain ⟨k, e⟩ := L.gen
  refine ⟨L.le, ?_⟩
  subst e
  exact Nat.le_refl _

theorem kuc_crashNeed (o : Nat) (atom : Sum Nat Nat) (ned : Need) : RB (Map := Map) (crashNeed o atom ned) := by
  unfold crashNeed
  split
  · exact rb_addOps _ _
  · exact rb_bind rb_re fun _ => rb_addOps _ _

theorem kuc_kernBoth (r d : Nat) {kh kt : Nat → List Pole → CM Map (List Pole)}
    (hh : ∀ x a, RB (Map := Map) (kh x a)) (ht : ∀ x a, RB (Map := Map) (kt x a)) (ops : List Pole) :
    RB (Map := Map) (kernBoth r d kh kt ops) := by
  unfold kernBoth
  exact rb_bind rb_re fun _ => rb_bind (ht _ _) fun _ => rb_bind rb_re fun _ =>
    rb_bind (hh _ _) fun _ => rb_ite _ rb_fail (rb_pure _)

theorem kuc_kernLoop : ∀ (r : Nat) (ned : Need) (ops : List Pole), RB (Map := Map) (kernLoop r ned ops)
  | _, Need.none, _ => by unfold kernLoop; exact rb_pure _
  | _, Need.this _, _ => by unfold kernLoop; exact rb_ite _ rb_fail (rb_pure _)
  | _, Need.pair p q, _ => by
    unfold kernLoop
    exact rb_bind rb_re fun _ =>
      kuc_kernBoth _ _ (fun x a => kuc_kernLoop x p a) (fun x a => kuc_kernLoop x q a) _
  | _, Need.both _ h t, _ => by
    unfold kernLoop
    exact kuc_kernBoth _ _ (fun x a => kuc_kernLoop x h a) (fun x a => kuc_kernLoop x t a) _

mutual
theorem kuc_walkLazy {f : Nat → Sure S → CM Map Unit} (hf : ∀ o s, RB (Map := Map) (f o s)) :
    ∀ (o : Nat) (l : Lazy S), RB (Map := Map) (walkLazy f o l)
  | o, mk s fk bd => by
    rw [walkLazy]
    exact rb_bind (hf o s) fun _ => rb_ite _ (rb_pure _)
      (rb_bind (kuc_walkForks hf fk) fun _ => kuc_walkBonds hf bd)

theorem kuc_walkForks {f : Nat → Sure S → CM Map Unit} (hf : ∀ o s, RB (Map := Map) (f o s)) :
    ∀ (l : List ((Nat × Lazy S) × (Nat × Lazy S))), RB (Map := Map) (walkForks f l)
  | [] => by rw [walkForks]; exact rb_pure _
  | ((oy, y), (on, n)) :: rest => by
    rw [walkForks]
    exact rb_bind (kuc_walkLazy hf oy y) fun _ => rb_bind (kuc_walkLazy hf on n) fun _ =>
      kuc_walkForks hf rest

theorem kuc_walkBonds {f : Nat → Sure S → CM Map Unit} (hf : ∀ o s, RB (Map := Map) (f o s)) :
    ∀ (l : List (Nat × Lazy S)), RB (Map := Map) (walkBonds f l)
  | [] => by rw [walkBonds]; exact rb_pure _
  | (o, l) :: rest => by
    rw [walkBonds]
    exact rb_bind (kuc_walkLazy hf o l) fun _ => kuc_walkBonds hf rest
end

theorem kuc_collapseGate (r o oLaz : Nat) (sur : Sure S) : RB (Map := Map) (collapseGate r o oLaz sur) := by
  unfold collapseGate
  refine rb_bind (kuc_sure _) fun ned => ?_
  split
  · exact rb_pure _
  · exact rb_ite _ (rb_pure _) (rb_bind (rb_ite _ (rb_pure _) (rb_proxy _ _)) fun _ => rb_addOps _ _)
  · exact rb_bind (rb_ite _ (rb_pure _) (rb_proxy _ _)) fun _ => kuc_crashNeed _ _ _

theorem kuc_kern (o : Nat) (laz : Lazy S) : RB (Map := Map) (kern o laz) := by
  unfold kern
  refine rb_bind rb_re fun r => rb_bind rb_get fun g => ?_
  refine rb_ite _ (rb_pure _) (rb_bind (kuc_walkLazy (fun oLaz sur => ?_) o laz) fun _ => rb_pure _)
  refine rb_bind (kuc_sure _) fun ned => rb_ite _ (rb_pure _) ?_
  refine rb_bind (rb_ite _ (rb_pure _) (rb_proxy _ _)) fun src => rb_ite _ rb_fail ?_
  exact rb_bind (kuc_kernLoop _ _ _) fun _ => rb_addOps _ _

/-! ## The fields `collapse` and `kerf` -/

/-- **The field `kerf`.** -/
theorem kuc_kerf (nex : NextL S) : RB (Map := Map) (kerf nex) := by
  unfold kerf
  exact rb_bind (rb_emit _) fun _ => rb_bind (kuc_kern _ _) fun _ => rb_pure _

/-- **The field `collapse`.** -/
theorem kuc_collapse (nex : NextL S) : RB (Map := Map) (collapseLazyAtomL nex) := by
  unfold collapseLazyAtomL
  refine rb_ite _ rb_fail ?_
  refine rb_ite _ (rb_pure _) ?_
  refine rb_bind (kuc_sure _) fun nedSure => ?_
  refine rb_bind ?_ fun p => ?_
  · split
    · exact rb_pure _
    · exact rb_bind rb_re fun _ => rb_pure _
    · exact rb_bind rb_re fun _ => rb_bind (rb_emit _) fun _ => rb_pure _
    · exact rb_bind (rb_emit _) fun _ => rb_pure _
  · obtain ⟨r, there⟩ := p
    exact rb_bind rb_get fun _ => rb_ite _ (rb_pure _)
      (rb_bind (kuc_walkLazy (fun _ _ => kuc_collapseGate _ _ _ _) _ _) fun _ => rb_pure _)

end Raw
end SkaModel
end Formalization
