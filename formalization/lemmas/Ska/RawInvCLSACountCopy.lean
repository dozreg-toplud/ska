import lemmas.Ska.RawInvCLSARunBase

/-!
# Single assignment with calls: the count of `+copy`

README Gaps 14 (b), track D.  The field `copy` of `SarStepsW`
(`RawInvCLSARun.lean`), with the definitions of the whole map counted (the
`IL` count `CR` of `RawInvCLCopyIL.lean` bounds them by membership only).

* `sccp_tr`: `+copy-need-make-ops` adds no trace op (only moves).
* `sccpR La Lc g g'`: the count of a merge of the entries `La` into `Lc`
  (state clause kept; definitions after and registers of `Lc` at most the
  definitions before, the registers of `La` and one per fresh register);
  `sccpR.keep`, `sccpR.seq`, `sccpR.congr`, `sccp_root` (`cn_count` and
  `addOps`).
* **`sccp_copyLazyL`** (mutual with `sccp_mergeForks`, `sccp_mergeBonds`),
  when both trees are `LabUniq` (each entry of `second` is merged at most
  once), the same induction as `cr_copyLazyL`.
* **`sccp_copy`**: the field `copy`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map] [MapKeys Map]

/-! ## The moves of `+copy-need-make-ops` -/

theorem sccp_mov_tr {s d : Nat} {ops : List Pole} (ht : ∀ op ∈ ops, trOp op = false) :
    ∀ op ∈ Pole.mov s d :: ops, trOp op = false := by
  intro op hop
  rcases List.mem_cons.mp hop with rfl | hop
  · rfl
  · exact ht op hop

/-- **`+copy-need-make-ops` adds only moves.** -/
theorem sccp_tr : ∀ (a b : Need) (ops : List Pole) (g g' : Comp.Gen Map) (x : Need × List Pole),
    copyNeed a b ops g = some (x, g') → (∀ op ∈ ops, trOp op = false) → ∀ op ∈ x.2, trOp op = false := by
  intro a
  induction a with
  | none =>
    intro b ops g g' x h ht
    simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ht
  | this rl =>
    intro b ops g g' x h ht
    cases b with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ht
    | this rr =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact sccp_mov_tr ht
    | both x' hh tt =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact sccp_mov_tr ht
    | pair p q =>
      simp only [copyNeed, bind_apply, re_apply, Option.bind_some, pure_apply, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact sccp_mov_tr ht
  | pair pl ql ihp ihq =>
    intro b ops g g' x h ht
    cases b with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ht
    | this rr =>
      simp only [copyNeed, bind_apply, re_apply, Option.bind_some, pure_apply, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact sccp_mov_tr ht
    | both x' hr tr =>
      simp only [copyNeed] at h
      obtain ⟨⟨a', ops1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨b', ops2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ihq tr _ g1 g2 (b', ops2) h2 (ihp hr _ g g1 (a', ops1) h1 ht)
    | pair pr qr =>
      simp only [copyNeed] at h
      obtain ⟨⟨a', ops1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨b', ops2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ihq qr _ g1 g2 (b', ops2) h2 (ihp pr _ g g1 (a', ops1) h1 ht)
  | both rl hl tl ihh iht =>
    intro b ops g g' x h ht
    cases b with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ht
    | this rr =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact sccp_mov_tr ht
    | both x' hr tr =>
      simp only [copyNeed] at h
      obtain ⟨⟨a', ops1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨b', ops2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact iht tr _ g1 g2 (b', ops2) h2 (ihh hr _ g g1 (a', ops1) h1 (sccp_mov_tr ht))
    | pair p q =>
      simp only [copyNeed] at h
      obtain ⟨x0, g0', h0, h⟩ := bind_some h
      rw [re_apply] at h0
      simp only [Option.some.injEq, Prod.mk.injEq] at h0
      obtain ⟨rfl, rfl⟩ := h0
      obtain ⟨⟨a', ops1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨b', ops2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact iht q _ g1 g2 (b', ops2) h2 (ihh p _ _ g1 (a', ops1) h1 (sccp_mov_tr ht))

/-! ## The count of a merge -/

/-- **The count of a merge** of the entries `La` into `Lc`, the definitions
of the whole map counted. -/
structure sccpR (La Lc : List (Nat × Lazy S)) (g g' : Comp.Gen Map) : Prop where
  st : SarSt g'
  le : g.re ≤ g'.re
  cnt : ∀ y, sarDc g'.blocks y + List.count y (regsL Lc) ≤
    sarDc g.blocks y + List.count y (regsL La) + fr g.re g'.re y

theorem sccpR.keep (L : List (Nat × Lazy S)) (g : Comp.Gen Map) (hs : SarSt g) : sccpR L L g g :=
  ⟨hs, Nat.le_refl _, fun _ => Nat.le_add_right _ _⟩

theorem sccpR.seq {La1 Lc1 La2 Lc2 : List (Nat × Lazy S)} {g g1 g2 : Comp.Gen Map} (h1 : sccpR La1 Lc1 g g1)
    (h2 : sccpR La2 Lc2 g1 g2) : sccpR (La1 ++ La2) (Lc1 ++ Lc2) g g2 := by
  refine ⟨h2.st, Nat.le_trans h1.le h2.le, fun y => ?_⟩
  have a1 := h1.cnt y
  have a2 := h2.cnt y
  have f := fr_add h1.le h2.le y
  simp only [regsL_append, List.count_append]
  omega

theorem sccpR.congr {La Lc La' Lc' : List (Nat × Lazy S)} {g g' : Comp.Gen Map} (h : sccpR La Lc g g')
    (ha : ∀ y, List.count y (regsL La) ≤ List.count y (regsL La'))
    (hc : ∀ y, List.count y (regsL Lc') ≤ List.count y (regsL Lc)) : sccpR La' Lc' g g' := by
  refine ⟨h.st, h.le, fun y => ?_⟩
  have := h.cnt y
  have := ha y
  have := hc y
  omega

theorem sccp_root {t : Nat} {a b c : Lazy S} {ned : Need} {ops : List Pole} {g g1 g2 : Comp.Gen Map}
    (hc : c.sure.ned = ned) (h1 : copyNeed a.sure.ned b.sure.ned [] g = some ((ned, ops), g1)) (hs : SarSt g)
    (h2 : addOps t ops g1 = some ((), g2)) : sccpR [(t, a), (t, b)] [(t, c)] g g2 := by
  obtain ⟨A, -, C⟩ := copyNeed_spec _ _ _ _ _ _ h1
  obtain ⟨new, enew, -, cn⟩ := cn_count _ _ _ _ _ _ h1
  have ht := sccp_tr _ _ _ _ _ _ h1 (fun _ h => absurd h List.not_mem_nil)
  dsimp only at enew cn ht
  rw [List.append_nil] at enew
  subst enew
  have s1 : SarSt g1 := by rw [C.gen]; exact ⟨hs.drop, hs.lab, hs.tr, hs.args⟩
  have hb : g1.blocks = g.blocks := by rw [C.gen]
  obtain ⟨s2, l2, c2⟩ := sc_addOps (Map := Map) (o := t) (ri := defsOf ops) (ro := []) ht (fun y => by simp)
    g1 () g2 s1 h2
  refine ⟨s2, Nat.le_trans C.le l2, fun y => ?_⟩
  have a2 := c2 y
  have h3 := cn y
  have f := fr_add C.le l2 y
  rw [hb] at a2
  simp only [regsL_cons, regsL_nil, List.append_nil, hc, List.count_append, List.count_nil] at h3 a2 ⊢
  omega

/-! ## The merge -/

mutual
/-- **The count of the merge of two `LabUniq` trees at `t`.** -/
theorem sccp_copyLazyL (t : Nat) : ∀ (a b : Lazy S) (g g' : Comp.Gen Map) (c : Lazy S),
    copyLazyL t a b g = some (c, g') → SarSt g → LabUniq a → LabUniq b →
    sccpR (((t, a) :: entries a) ++ ((t, b) :: entries b)) ((t, c) :: entries c) g g'
  | mk s1 f1 b1, second, g, g', c, h, hs, hUa, hU => by
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
    have R1 := sccp_root (t := t) (c := mk ⟨ned, HoonSet.uni s1.lok second.sure.lok⟩ fork bond)
      (a := mk s1 f1 b1) rfl h1 hs (by cases u; exact h2)
    have hs2 : SarSt g2 := R1.st
    -- the forks
    have R2 : sccpR (forkEntries f1 ++ forkEntries second.fork) (forkEntries fork) g2 g3 := by
      by_cases c1 : second.fork.isEmpty = true
      · rw [if_pos c1] at h3
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
        obtain ⟨rfl, rfl⟩ := h3
        exact (sccpR.keep _ g2 hs2).congr (fun x => by rw [regsL_append, List.count_append]; omega)
          (fun x => Nat.le_refl _)
      rw [if_neg c1] at h3
      by_cases c2 : f1.isEmpty = true
      · rw [if_pos c2] at h3
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
        obtain ⟨rfl, rfl⟩ := h3
        exact (sccpR.keep _ g2 hs2).congr (fun x => by rw [regsL_append, List.count_append]; omega)
          (fun x => Nat.le_refl _)
      rw [if_neg c2] at h3
      obtain ⟨merged, g3', hm, h3⟩ := bind_some h3
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
      obtain ⟨rfl, rfl⟩ := h3
      have M := sccp_mergeForks (index (Map := Map) (fun e : ForkE S => e.1.1) second.fork) f1 g2 g3' merged
        hm hs2 (fun v hv => by
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
      refine (M.seq (sccpR.keep (forkEntries (second.fork.filter fun e =>
        !(seen (S := S) (fun e : ForkE S => e.1.1) f1 e.1.1))) g3' M.st)).congr (fun x => ?_) (fun x => ?_)
      · have := count_split_fe (Map := Map) (f1 := f1) (sf := second.fork) hUa0.2 hU0.2 x
        simp only [regsL_append, List.count_append] at this ⊢
        omega
      · rw [fe_append]; exact Nat.le_refl _
    have hs3 : SarSt g3 := R2.st
    -- the bonds
    have R3 : sccpR (bondEntries b1 ++ bondEntries second.bond) (bondEntries bond) g3 g4 := by
      by_cases c1 : second.bond.isEmpty = true
      · rw [if_pos c1] at h4
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h4
        obtain ⟨rfl, rfl⟩ := h4
        exact (sccpR.keep _ g3 hs3).congr (fun x => by rw [regsL_append, List.count_append]; omega)
          (fun x => Nat.le_refl _)
      rw [if_neg c1] at h4
      by_cases c2 : b1.isEmpty = true
      · rw [if_pos c2] at h4
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h4
        obtain ⟨rfl, rfl⟩ := h4
        exact (sccpR.keep _ g3 hs3).congr (fun x => by rw [regsL_append, List.count_append]; omega)
          (fun x => Nat.le_refl _)
      rw [if_neg c2] at h4
      obtain ⟨merged, g4', hm, h4⟩ := bind_some h4
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h4
      obtain ⟨rfl, rfl⟩ := h4
      have M := sccp_mergeBonds (index (Map := Map) (fun e : Nat × Lazy S => e.1) second.bond) b1 g3 g4'
        merged hm hs3 (fun v hv => by
          have hsub := be_sub hv
          rw [be_single] at hsub
          exact labUniq_of hUa (o := v.1) fun e he => by rw [hea]; exact List.mem_append_left _ (hsub e he))
        (fun k v hk => by
          obtain ⟨hv, hkv⟩ := gm_index_get _ hk
          have hsub := be_sub hv
          rw [be_single] at hsub
          exact ⟨labUniq_of hU (o := v.1) fun e he => by rw [heb]; exact List.mem_append_left _ (hsub e he), hkv⟩)
      refine (M.seq (sccpR.keep (bondEntries (second.bond.filter fun e =>
        !(seen (S := S) (fun e : Nat × Lazy S => e.1) b1 e.1))) g4' M.st)).congr (fun x => ?_) (fun x => ?_)
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
theorem sccp_mergeForks (idx : Map (ForkE S)) :
    ∀ (l : List (ForkE S)) (g g' : Comp.Gen Map) (l' : List (ForkE S)),
    mergeForks idx l g = some (l', g') → SarSt g → (∀ v ∈ l, LabUniq v.1.2 ∧ LabUniq v.2.2) →
    (∀ k v, HoonMap.get idx k = some v → LabUniq v.1.2 ∧ LabUniq v.2.2 ∧ v.1.1 = k) →
    sccpR (forkEntries l ++ forkEntries (l.filterMap fun fe => HoonMap.get idx fe.1.1)) (forkEntries l') g g'
  | [], g, g', l', h, hs, _, _ => by
    rw [mergeForks] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (sccpR.keep [] g hs).congr (fun x => by simp [forkEntries, regsL]) (fun x => by simp [forkEntries, regsL])
  | ((oy, y), (on, n)) :: rest, g, g', l', h, hs, hUl, hidx => by
    rw [mergeForks] at h
    obtain ⟨e, g1, h1, h⟩ := bind_some h
    obtain ⟨r, g2, h2, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hcons : ∀ (w : ForkE S) (ws : List (ForkE S)), forkEntries (w :: ws) = forkEntries [w] ++ forkEntries ws :=
      fun w ws => fe_append [w] ws
    have hU1 := hUl _ List.mem_cons_self
    have hUr : ∀ v ∈ rest, LabUniq v.1.2 ∧ LabUniq v.2.2 := fun v hv => hUl v (List.mem_cons_of_mem _ hv)
    have E : sccpR (forkEntries [((oy, y), (on, n))] ++ forkEntries (HoonMap.get idx oy).toList)
        (forkEntries [e]) g g1 := by
      rcases hk : HoonMap.get idx oy with _ | ⟨⟨z, my⟩, ⟨mon, mn⟩⟩
      · rw [hk] at h1
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        exact (sccpR.keep _ g hs).congr (fun x => by rw [regsL_append, List.count_append]; omega)
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
          have A := sccp_copyLazyL z y my g ga y' hya hs hU1.1 hU1'
          have B := sccp_copyLazyL on n mn ga gb n' hnb A.st hU1.2 hU2'
          refine (A.seq B).congr (fun x => ?_) (fun x => ?_)
          · simp only [Option.toList, fe_single, regsL_append, regsL_cons, List.count_append]
            omega
          · simp only [fe_single, regsL_append, regsL_cons, List.count_append]
            omega
        · rw [if_neg ce] at h1
          cases h1
    have R := sccp_mergeForks idx rest g1 g2 r h2 E.st hUr hidx
    refine (E.seq R).congr (fun x => ?_) (fun x => ?_)
    · rw [hcons ((oy, y), (on, n)) rest]
      simp only [filterMap_cons_toList, fe_append, regsL_append, List.count_append]
      omega
    · rw [hcons e r]; exact Nat.le_refl _

/-- The bonds of the merge, counted. -/
theorem sccp_mergeBonds (idx : Map (Nat × Lazy S)) :
    ∀ (l : List (Nat × Lazy S)) (g g' : Comp.Gen Map) (l' : List (Nat × Lazy S)),
    mergeBonds idx l g = some (l', g') → SarSt g → (∀ v ∈ l, LabUniq v.2) →
    (∀ k v, HoonMap.get idx k = some v → LabUniq v.2 ∧ v.1 = k) →
    sccpR (bondEntries l ++ bondEntries (l.filterMap fun e => HoonMap.get idx e.1)) (bondEntries l') g g'
  | [], g, g', l', h, hs, _, _ => by
    rw [mergeBonds] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact (sccpR.keep [] g hs).congr (fun x => by simp [bondEntries, regsL]) (fun x => by simp [bondEntries, regsL])
  | (ob, lb) :: rest, g, g', l', h, hs, hUl, hidx => by
    rw [mergeBonds] at h
    obtain ⟨e, g1, h1, h⟩ := bind_some h
    obtain ⟨r, g2, h2, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hcons : ∀ (w : Nat × Lazy S) (ws : List (Nat × Lazy S)), bondEntries (w :: ws) = bondEntries [w] ++ bondEntries ws :=
      fun w ws => be_append [w] ws
    have hU1 := hUl _ List.mem_cons_self
    have hUr : ∀ v ∈ rest, LabUniq v.2 := fun v hv => hUl v (List.mem_cons_of_mem _ hv)
    have E : sccpR (bondEntries [(ob, lb)] ++ bondEntries (HoonMap.get idx ob).toList) (bondEntries [e]) g g1 := by
      rcases hk : HoonMap.get idx ob with _ | ⟨z, m⟩
      · rw [hk] at h1
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        exact (sccpR.keep _ g hs).congr (fun x => by rw [regsL_append, List.count_append]; omega)
          (fun x => Nat.le_refl _)
      · rw [hk] at h1
        obtain ⟨hU1', hz⟩ := hidx ob _ hk
        dsimp only at hz
        subst hz
        dsimp only at h1
        obtain ⟨l2, ga, hla, h1⟩ := bind_some h1
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        have A := sccp_copyLazyL z lb m g ga l2 hla hs hU1 hU1'
        refine A.congr (fun x => ?_) (fun x => ?_)
        · simp only [Option.toList, be_single, regsL_append, regsL_cons, List.count_append]
          omega
        · simp only [be_single, regsL_append, regsL_cons, List.count_append]
          omega
    have R := sccp_mergeBonds idx rest g1 g2 r h2 E.st hUr hidx
    refine (E.seq R).congr (fun x => ?_) (fun x => ?_)
    · rw [hcons (ob, lb) rest]
      simp only [filterMap_cons_toList, be_append, regsL_append, List.count_append]
      omega
    · rw [hcons e r]; exact Nat.le_refl _
end

/-! ## The field -/

/-- **The field `copy`.** -/
theorem sccp_copy : ∀ (first : NextL S) (second : Lazy S), first.th.args = [] → LabUniq first.laz →
    LabUniq second → SCR (Map := Map) (sarR first.laz ++ sarR second) (copyL first second) (fun x => sarR x.laz) := by
  intro first second ha hU1 hU2
  unfold copyL
  refine sc_bind (sc_emit (ro := sarR first.laz ++ sarR second) (by simp) (by simp [getJmps, ha])
    fun y => by simp [blockDefs]) fun o => ?_
  refine sc_bind (r1 := fun l => sarR l) ?_ fun l => sc_pure fun _ => Nat.le_refl _
  intro g c g' hs h
  have R := sccp_copyLazyL o first.laz second g g' c h hs hU1 hU2
  refine ⟨R.st, R.le, fun y => ?_⟩
  have := R.cnt y
  simp only [List.cons_append, regsL_cons, regsL_append, sarR, List.count_append] at this ⊢
  omega

end Raw
end SkaModel
end Formalization
