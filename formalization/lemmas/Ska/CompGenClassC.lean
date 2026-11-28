import lemmas.Ska.CompGenClassB

/-!
# The copy of the general cons: its preconditions and its result in the class

README Gaps 12.39, item 12.  Stated on the parts' frames (`FrameG`), the
class's premises (`PremG`) and results (`ResG`) and the split's halves
(`HalvesApart`, `HalfOK`), not on `ConsGAt`, so the copy of `%5` can reuse it.

* `OrigAt`: where a register of a run's result need at a label comes from (a
  goal entry at that label, the goal's sure need, or fresh); `cc_orig`,
  `cc_orig_root`, `cc_orig_up` (through a half of the split to the cons's
  goal), and `cc_cross`: a register of `p`'s result and one of `q`'s at the
  same label are never the same (`HalvesApart` for the old ones, the fresh
  ranges `[gS.re, g2.re)` and `[g2.re, g3.re)` apart).
* **`copyPreG`**: `CopyPreAt` of the copy's two inputs at every label.
* `CleanT`, `cc_cleanT_mk`, `cc_cleanT_copy` (mutual with
  `cc_cleanT_mergeForks`, `cc_cleanT_mergeBonds`): `+copy-lazy` keeps every
  need of the tree clean.
* `cc_fresh_count`: a fresh register of the copy occurs at most once over
  the merged tree (track D's count `Raw.cr_copyLazyL`).
* **`resG_copy`**: the merged result is in `ResG` for the cons's goal, and
  `LabDisj`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Origins of the registers at a label -/

/-- **Where a register at label `k` comes from**: a goal entry at `k`, the
goal's sure need, or fresh in `[lo, hi)`. -/
def OrigAt (L : Lazy S) (lo hi k r : Nat) : Prop :=
  (∃ e0 ∈ entries L, e0.1 = k ∧ NMem e0.2.sure.ned r) ∨ NMem L.sure.ned r ∨ (lo ≤ r ∧ r < hi)

/-- A need of a run's result list (root at any label `o`) at label `k`. -/
theorem cc_orig {L : Lazy S} {th : Jmp} {Q : Wit} {g0 g1 : Gen Map} {nex : NextL S}
    (F : FrameG (Map := Map) L th Q g0 g1 nex) (E : EregsAt (Map := Map) L g0 g1 nex.laz) {o k : Nat}
    {M : Sure S} (hM : M ∈ atL ((o, nex.laz) :: entries nex.laz) k) {r : Nat} (hr : NMem M.ned r) :
    OrigAt L g0.re g1.re k r := by
  obtain ⟨e, he, ek, eM⟩ := mem_atL hM
  subst eM
  rcases List.mem_cons.mp he with rfl | he
  · rcases F.regs r hr with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rcases E e he r hr with ⟨e0, he0, e1, h⟩ | h | h
    · exact Or.inl ⟨e0, he0, e1.trans ek, h⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

/-- The result's sure need, at any label. -/
theorem cc_orig_root {L : Lazy S} {th : Jmp} {Q : Wit} {g0 g1 : Gen Map} {nex : NextL S}
    (F : FrameG (Map := Map) L th Q g0 g1 nex) {r : Nat} (hr : NMem nex.laz.sure.ned r) (k : Nat) :
    OrigAt L g0.re g1.re k r :=
  (F.regs r hr).elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h))

/-- **Through a half of the split** to the cons's goal. -/
theorem cc_orig_up {L h : Lazy S} {lo hi a b c k r : Nat} (H : HalfOK L lo hi h) (hp : OrigAt h a b k r)
    (ha : lo ≤ a) (hb : b ≤ c) (hc : hi ≤ c) : OrigAt L lo c k r := by
  rcases hp with ⟨e0, he0, ek, hm⟩ | hs | ⟨f1, f2⟩
  · rcases H.er e0 he0 r hm with ⟨e1, he1, e1k, h1⟩ | ⟨f1, f2⟩
    · exact Or.inl ⟨e1, he1, e1k.trans ek, h1⟩
    · exact Or.inr (Or.inr ⟨f1, by omega⟩)
  · rcases H.sr r hs with h1 | ⟨f1, f2⟩
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨f1, by omega⟩)
  · exact Or.inr (Or.inr ⟨by omega, by omega⟩)

/-- **`p`'s and `q`'s registers at one label are apart**: `p` ran under the
head half from `m` to `hi`, `q` under the tail half from `lo` to `m`. -/
theorem cc_cross {hed tel : Lazy S} {lo m hi k r : Nat} (H : HalvesApart hed tel lo) (h1 : lo ≤ m)
    (hp : OrigAt hed m hi k r) (hq : OrigAt tel lo m k r) : False := by
  rcases hp with ⟨e0, he0, ek, hm⟩ | hs | ⟨f1, f2⟩ <;>
    rcases hq with ⟨e1, he1, ek', hm'⟩ | ht | ⟨f1', f2'⟩
  · exact H.ee e0 he0 e1 he1 (ek.trans ek'.symm) r hm hm'
  · exact H.es e0 he0 r ht hm
  · have := H.hlo.2 e0 he0 r hm; omega
  · exact H.se e1 he1 r hs hm'
  · exact H.ss r hs ht
  · have := H.hlo.1 r hs; omega
  · have := H.tlo.2 e1 he1 r hm'; omega
  · have := H.tlo.1 r ht; omega
  · omega

/-! ## The copy's preconditions -/

/-- `CopyPreAt` reads only `re`. -/
theorem cc_copyPreAt_re {g g' : Gen Map} (e : g.re = g'.re) {fs ss : List (Nat × Lazy S)}
    (h : CopyPreAt (Map := Map) g fs ss) : CopyPreAt (Map := Map) g' fs ss := by
  unfold CopyPreAt at *
  rw [← e]
  exact h

/-- The needs of a result list with its root at a label above all entries
are pairwise apart at every label. -/
theorem cc_pw {o : Nat} {l : Lazy S} (hl : ∀ e ∈ entries l, e.1 < o) (hd : LabDisj l) (k : Nat) :
    (atL ((o, l) :: entries l) k).Pairwise (fun L L' => ∀ r, NMem L.ned r → ¬ NMem L'.ned r) := by
  by_cases hk : o = k
  · subst hk
    have e := atL_cons_eq (o, l) (entries l)
    dsimp only at e
    rw [e, atL_none (fun e he => by have := hl e he; omega)]
    exact List.pairwise_singleton _ _
  · rw [atL_cons_ne (e := (o, l)) (by exact hk)]
    exact labDisj_at hd k

/-- **The copy's inputs meet `CopyPreAt`** at every label: `p`'s result
(under the head half, from `g2` to `g3`) and `q`'s (under the tail half, from
`gS` to `g2`), both rooted at the copy's block `g3.bo`. -/
theorem copyPreG {hed tel : Lazy S} {thq thp : Jmp} {Qq Qp : Wit} {gS g2 g3 : Gen Map} {nq np : NextL S}
    (Fq : FrameG (Map := Map) tel thq Qq gS g2 nq) (Fp : FrameG (Map := Map) hed thp Qp g2 g3 np)
    (Pq : PremG (Map := Map) tel thq gS) (Pp : PremG (Map := Map) hed thp g2)
    (Rq : ResG (Map := Map) tel gS g2 nq.laz) (Rp : ResG (Map := Map) hed g2 g3 np.laz)
    (H : HalvesApart hed tel gS.re) :
    CopyPreAt (Map := Map) g3 ((g3.bo, np.laz) :: entries np.laz) ((g3.bo, nq.laz) :: entries nq.laz) := by
  have Gq := Fq.goalOut Pq.goal
  have Gp := Fp.goalOut Pp.goal
  have e1 := Fq.re
  have e2 := Fp.re
  have b2 := Fp.bo
  have lp : ∀ e ∈ entries np.laz, e.1 < g3.bo := fun e he => (Gp.lab e he).2.1
  have lq : ∀ e ∈ entries nq.laz, e.1 < g3.bo := fun e he => by have := (Gq.lab e he).2.1; omega
  intro k
  refine ⟨fun F hF => ?_, ?_⟩
  · rcases List.mem_append.mp hF with h | h
    · obtain ⟨e, he, -, rfl⟩ := mem_atL h
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨Rp.cl, Fp.dist, Gp.sregs⟩
      · exact ⟨Rp.ecl e he, (Gp.eregs e he).1, (Gp.eregs e he).2⟩
    · obtain ⟨e, he, -, rfl⟩ := mem_atL h
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨Rq.cl, Fq.dist, fun y hy => by have := Gq.sregs y hy; omega⟩
      · exact ⟨Rq.ecl e he, (Gq.eregs e he).1, fun y hy => by have := (Gq.eregs e he).2 y hy; omega⟩
  · refine List.pairwise_append.mpr ⟨cc_pw lp Fp.labDisj k, cc_pw lq Fq.labDisj k, fun F hF T hT r hr hr' => ?_⟩
    exact cc_cross H e1 (cc_orig Fp Rp.eat hF hr) (cc_orig Fq Rq.eat hT hr')

/-! ## `+copy-lazy` keeps the needs clean -/

/-- **Every need of the tree is clean.** -/
def CleanT (l : Lazy S) : Prop := Clean l.sure.ned ∧ ∀ e ∈ entries l, Clean e.2.sure.ned

theorem cc_cleanT_mk (s : Sure S) (f : List (ForkE S)) (b : List (Nat × Lazy S)) :
    CleanT (mk s f b) ↔ Clean s.ned ∧ (∀ e ∈ b, CleanT e.2) ∧ ∀ x ∈ f, CleanT x.1.2 ∧ CleanT x.2.2 := by
  constructor
  · rintro ⟨hs, hE⟩
    refine ⟨hs, fun e he => ?_, fun x hx => ⟨?_, ?_⟩⟩
    · obtain ⟨h1, h2⟩ := Raw.bondEntries_of_mem he
      exact ⟨hE e (by simp only [entries, List.mem_append]; exact Or.inl h1),
        fun y hy => hE y (by simp only [entries, List.mem_append]; exact Or.inl (h2 y hy))⟩
    · obtain ⟨h1, h2, _, _⟩ := Raw.forkEntries_of_mem hx
      exact ⟨hE x.1 (by simp only [entries, List.mem_append]; exact Or.inr h1),
        fun y hy => hE y (by simp only [entries, List.mem_append]; exact Or.inr (h2 y hy))⟩
    · obtain ⟨_, _, h3, h4⟩ := Raw.forkEntries_of_mem hx
      exact ⟨hE x.2 (by simp only [entries, List.mem_append]; exact Or.inr h3),
        fun y hy => hE y (by simp only [entries, List.mem_append]; exact Or.inr (h4 y hy))⟩
  · rintro ⟨hs, hB, hF⟩
    refine ⟨hs, fun e he => ?_⟩
    simp only [entries, List.mem_append] at he
    rcases he with he | he
    · obtain ⟨x, hx, h⟩ := Raw.mem_bondEntries he
      rcases h with rfl | h
      · exact (hB e hx).1
      · exact (hB x hx).2 e h
    · obtain ⟨x, hx, h⟩ := Raw.mem_forkEntries he
      rcases h with rfl | h | rfl | h
      · exact (hF x hx).1.1
      · exact (hF x hx).1.2 e h
      · exact (hF x hx).2.1
      · exact (hF x hx).2.2 e h

theorem cc_cleanT_parts {l : Lazy S} (h : CleanT l) :
    Clean l.sure.ned ∧ (∀ e ∈ l.bond, CleanT e.2) ∧ ∀ x ∈ l.fork, CleanT x.1.2 ∧ CleanT x.2.2 := by
  rcases l with ⟨s, f, b⟩
  exact (cc_cleanT_mk s f b).mp h

mutual
/-- **`+copy-lazy` keeps every need clean.** -/
theorem cc_cleanT_copy (o : Nat) : ∀ (a b : Lazy S) (g g' : Gen Map) (l : Lazy S),
    copyLazyL o a b g = some (l, g') → CleanT a → CleanT b → CleanT l
  | mk s1 f1 b1, second, g, g', l, h, ha, hb => by
    rw [copyLazyL] at h
    obtain ⟨⟨ned, ops⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨_, g2, h2, h⟩ := bind_some h
    obtain ⟨fork, g3, h3, h⟩ := bind_some h
    obtain ⟨bond, g4, h4, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hs1, hB1, hF1⟩ := (cc_cleanT_mk s1 f1 b1).mp ha
    obtain ⟨hs2, hB2, hF2⟩ := cc_cleanT_parts hb
    have cn : Clean ned := clean_copyNeed _ _ _ _ _ _ h1 hs1 hs2
    have F : ∀ x ∈ fork, CleanT x.1.2 ∧ CleanT x.2.2 := by
      by_cases c1 : second.fork.isEmpty = true
      · rw [if_pos c1, pure_apply] at h3
        simp only [Option.some.injEq, Prod.mk.injEq] at h3
        obtain ⟨rfl, rfl⟩ := h3
        exact hF1
      · rw [if_neg c1] at h3
        by_cases c2 : f1.isEmpty = true
        · rw [if_pos c2, pure_apply] at h3
          simp only [Option.some.injEq, Prod.mk.injEq] at h3
          obtain ⟨rfl, rfl⟩ := h3
          exact hF2
        · rw [if_neg c2] at h3
          obtain ⟨merged, g5, h5, h3⟩ := bind_some h3
          simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
          obtain ⟨rfl, rfl⟩ := h3
          have M2 := cc_cleanT_mergeForks o _ (fun k e' hk => hF2 e' (Raw.gm_index_get _ hk).1) f1 g2 g5 merged h5
            hF1
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact M2 x hx
          · exact hF2 x (List.mem_filter.mp hx).1
    have B : ∀ x ∈ bond, CleanT x.2 := by
      by_cases c1 : second.bond.isEmpty = true
      · rw [if_pos c1, pure_apply] at h4
        simp only [Option.some.injEq, Prod.mk.injEq] at h4
        obtain ⟨rfl, rfl⟩ := h4
        exact hB1
      · rw [if_neg c1] at h4
        by_cases c2 : b1.isEmpty = true
        · rw [if_pos c2, pure_apply] at h4
          simp only [Option.some.injEq, Prod.mk.injEq] at h4
          obtain ⟨rfl, rfl⟩ := h4
          exact hB2
        · rw [if_neg c2] at h4
          obtain ⟨merged, g5, h5, h4⟩ := bind_some h4
          simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h4
          obtain ⟨rfl, rfl⟩ := h4
          have M2 := cc_cleanT_mergeBonds o _ (fun k e' hk => hB2 e' (Raw.gm_index_get _ hk).1) b1 g3 g5 merged h5
            hB1
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact M2 x hx
          · exact hB2 x (List.mem_filter.mp hx).1
    exact (cc_cleanT_mk _ _ _).mpr ⟨cn, B, F⟩

theorem cc_cleanT_mergeForks (o : Nat) (idx : Map (ForkE S))
    (hidx : ∀ k e, HoonMap.get idx k = some e → CleanT e.1.2 ∧ CleanT e.2.2) :
    ∀ (l : List (ForkE S)) (g g' : Gen Map) (r : List (ForkE S)),
    mergeForks idx l g = some (r, g') → (∀ x ∈ l, CleanT x.1.2 ∧ CleanT x.2.2) →
    ∀ x ∈ r, CleanT x.1.2 ∧ CleanT x.2.2
  | [], g, g', r, h, _ => by
    rw [mergeForks] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact fun _ h => absurd h List.not_mem_nil
  | ((oy, y), (on, n)) :: rest, g, g', r, h, hq => by
    rw [mergeForks] at h
    obtain ⟨e1, g1, h1, h⟩ := bind_some h
    obtain ⟨r1, g2, h2, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have R := cc_cleanT_mergeForks o idx hidx rest g1 g2 r1 h2 (fun x hx => hq x (List.mem_cons_of_mem _ hx))
    have q0 : CleanT y ∧ CleanT n := hq _ List.mem_cons_self
    have E : CleanT e1.1.2 ∧ CleanT e1.2.2 := by
      cases hget : HoonMap.get idx oy with
      | none =>
        simp only [hget, pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        exact q0
      | some v =>
        rcases v with ⟨⟨fst, my⟩, ⟨mon, mn⟩⟩
        simp only [hget] at h1
        by_cases hon : on = mon
        · rw [if_pos hon] at h1
          obtain ⟨y', g3, h3, h1⟩ := bind_some h1
          obtain ⟨n', g4, h4, h1⟩ := bind_some h1
          simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
          obtain ⟨rfl, rfl⟩ := h1
          have I := hidx _ _ hget
          exact ⟨cc_cleanT_copy oy y my g g3 y' h3 q0.1 I.1, cc_cleanT_copy on n mn g3 g4 n' h4 q0.2 I.2⟩
        · rw [if_neg hon] at h1; cases h1
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact E
    · exact R x hx

theorem cc_cleanT_mergeBonds (o : Nat) (idx : Map (Nat × Lazy S))
    (hidx : ∀ k e, HoonMap.get idx k = some e → CleanT e.2) :
    ∀ (l : List (Nat × Lazy S)) (g g' : Gen Map) (r : List (Nat × Lazy S)),
    mergeBonds idx l g = some (r, g') → (∀ x ∈ l, CleanT x.2) → ∀ x ∈ r, CleanT x.2
  | [], g, g', r, h, _ => by
    rw [mergeBonds] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact fun _ h => absurd h List.not_mem_nil
  | (ob, l) :: rest, g, g', r, h, hq => by
    rw [mergeBonds] at h
    obtain ⟨e1, g1, h1, h⟩ := bind_some h
    obtain ⟨r1, g2, h2, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have R := cc_cleanT_mergeBonds o idx hidx rest g1 g2 r1 h2 (fun x hx => hq x (List.mem_cons_of_mem _ hx))
    have q0 : CleanT l := hq _ List.mem_cons_self
    have E : CleanT e1.2 := by
      cases hget : HoonMap.get idx ob with
      | none =>
        simp only [hget, pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        exact q0
      | some v =>
        rcases v with ⟨fst, m⟩
        simp only [hget] at h1
        obtain ⟨l', g3, h3, h1⟩ := bind_some h1
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        exact cc_cleanT_copy ob l m g g3 l' h3 q0 (hidx _ _ hget)
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact E
    · exact R x hx
end

/-! ## The merged result -/

/-- **A fresh register of `+copy` occurs at most once** over the merged
tree (the count of `labDisj_copyLazyL`). -/
theorem cc_fresh_count {o : Nat} {a b c : Lazy S} {g g' : Gen Map} (h : copyLazyL o a b g = some (c, g'))
    (hd : g.drop = false) (ha : Raw.LabUniq a) (hb : Raw.LabUniq b)
    (hlo : ∀ k, ∀ F ∈ atL ((o, a) :: entries a) k ++ atL ((o, b) :: entries b) k, ∀ y, NMem F.ned y → y < g.re) :
    ∀ r, g.re ≤ r → List.count r (Raw.regsL ((o, c) :: entries c)) ≤ 1 := by
  have CRr := Raw.cr_copyLazyL o a b g g' c h hd ha hb
  obtain ⟨D, -, hcnt⟩ := CRr.cnt
  have low : ∀ e ∈ ((o, a) :: entries a) ++ ((o, b) :: entries b), ∀ y, NMem e.2.sure.ned y → y < g.re := by
    intro e he y hy
    refine hlo e.1 e.2.sure ?_ y hy
    rcases List.mem_append.mp he with he | he
    · exact List.mem_append_left _ (cg_mem_atL he)
    · exact List.mem_append_right _ (cg_mem_atL he)
  intro r hr
  have h1 := hcnt r
  have h0 : List.count r (Raw.regsL (((o, a) :: entries a) ++ ((o, b) :: entries b))) = 0 :=
    List.count_eq_zero.mpr (fun hm => by
      obtain ⟨e, he, hm⟩ := Raw.mem_regsL.mp hm
      have := low e he r hm
      omega)
  have h2 := Raw.fr_le_one g.re g'.re r
  rw [List.count_append, h0] at h1
  omega

/-- **The merged result of the cons's copy is in the class's result side**
for the cons's goal `L` (the halves `hed`, `tel` of `+split` from `g0` to
`gS`, `HalfOK`), and `LabDisj`. -/
theorem resG_copy {L hed tel : Lazy S} {thq thp : Jmp} {Qq Qp : Wit} {g0 gS g2 g3 g1 : Gen Map}
    {nq np nex : NextL S}
    (Fq : FrameG (Map := Map) tel thq Qq gS g2 nq) (Fp : FrameG (Map := Map) hed thp Qp g2 g3 np)
    (Pq : PremG (Map := Map) tel thq gS) (Pp : PremG (Map := Map) hed thp g2)
    (Rq : ResG (Map := Map) tel gS g2 nq.laz) (Rp : ResG (Map := Map) hed g2 g3 np.laz)
    (H : HalvesApart hed tel gS.re) (Hh : HalfOK L g0.re gS.re hed) (Ht : HalfOK L g0.re gS.re tel)
    (h0 : g0.re ≤ gS.re) (hd : g3.drop = false)
    (cp : copyL np nq.laz g3 = some (nex, g1))
    (hc : copyLazyL g3.bo np.laz nq.laz (g3.emitted ⟨[], [], Termin.hop np.th⟩) = some (nex.laz, g1))
    (CO : CopyOKL (g3.emitted ⟨[], [], Termin.hop np.th⟩) g1 ((g3.bo, np.laz) :: entries np.laz)
      ((g3.bo, nq.laz) :: entries nq.laz) ((g3.bo, nex.laz) :: entries nex.laz)) :
    ResG (Map := Map) L g0 g1 nex.laz ∧ LabDisj nex.laz := by
  have Gq := Fq.goalOut Pq.goal
  have Gp := Fp.goalOut Pp.goal
  have e1 := Fq.re
  have e2 := Fp.re
  have b2 := Fp.bo
  have lp : ∀ e ∈ entries np.laz, e.1 < g3.bo := fun e he => (Gp.lab e he).2.1
  have lq : ∀ e ∈ entries nq.laz, e.1 < g3.bo := fun e he => by have := (Gq.lab e he).2.1; omega
  obtain ⟨lu, lab⟩ := Raw.lab_copyL (Q := fun k => k < g3.bo) cp Rp.lu Rq.lu lp lq
  have CP : CopyPreAt (Map := Map) (g3.emitted ⟨[], [], Termin.hop np.th⟩) ((g3.bo, np.laz) :: entries np.laz)
      ((g3.bo, nq.laz) :: entries nq.laz) :=
    cc_copyPreAt_re (emitted_re _ _).symm (copyPreG Fq Fp Pq Pp Rq Rp H)
  have hd' : (g3.emitted ⟨[], [], Termin.hop np.th⟩).drop = false := (emitted_drop _ _).trans hd
  have g31 : g3.re ≤ g1.re := by
    obtain ⟨_, PP, _⟩ := CO
    have := PP.re
    simpa only [emitted_re] using this
  obtain ⟨PC, PPC, OC, AC⟩ := CopyOKL.runAt CO
  have ORG : ∀ k, ∀ M ∈ atL ((g3.bo, nex.laz) :: entries nex.laz) k, ∀ y, NMem M.ned y →
      (∃ F ∈ atL ((g3.bo, np.laz) :: entries np.laz) k ++ atL ((g3.bo, nq.laz) :: entries nq.laz) k,
        NMem F.ned y) ∨ (g3.re ≤ y ∧ y < g1.re) :=
    fun k M hM y hy => ((AC k (CP k).1 (CP k).2).2.1 M hM).2 y hy
  have OL : ∀ k (F : Sure S) y,
      F ∈ atL ((g3.bo, np.laz) :: entries np.laz) k ++ atL ((g3.bo, nq.laz) :: entries nq.laz) k →
      NMem F.ned y → OrigAt L g0.re g1.re k y := by
    intro k F y hF hy
    rcases List.mem_append.mp hF with hF | hF
    · exact cc_orig_up Hh (cc_orig Fp Rp.eat hF hy) (by omega) g31 (by omega)
    · exact cc_orig_up Ht (cc_orig Fq Rq.eat hF hy) h0 (by omega) (by omega)
  have CT := cc_cleanT_copy g3.bo np.laz nq.laz _ g1 nex.laz hc ⟨Rp.cl, Rp.ecl⟩ ⟨Rq.cl, Rq.ecl⟩
  have LD : LabDisj nex.laz := labDisj_copyLazyL hc hd' Rp.lu Rq.lu (fun k F hF => ((CP k).1 F hF).2.2)
    (fun k => (AC k (CP k).1 (CP k).2).2.2.1)
  refine ⟨⟨lu, CT.1, CT.2, ?_, ?_⟩, LD⟩
  · -- `SureApart`: fresh registers by the count, old ones by their origins
    intro e he r hr hs
    by_cases hf : g3.re ≤ r
    · have c1 := cc_fresh_count hc hd' Rp.lu Rq.lu (fun k F hF => ((CP k).1 F hF).2.2)
      have Pw := cg_pw_count (fun r => (g3.emitted ⟨[], [], Termin.hop np.th⟩).re ≤ r) _ c1
      exact (List.pairwise_cons.mp Pw).1 e he r hf hs hr
    · have hk := lab e he
      obtain ⟨F, hF, hFr⟩ := (ORG g3.bo nex.laz.sure (cb_mem_atL_self _ _ _) r hs).resolve_right
        (fun h => hf h.1)
      obtain ⟨F', hF', hF'r⟩ := (ORG e.1 e.2.sure (cb_mem_atL_of he _) r hr).resolve_right (fun h => hf h.1)
      rcases List.mem_append.mp hF with hF | hF <;> rcases List.mem_append.mp hF' with hF' | hF'
      · obtain rfl := cb_atL_root lp hF
        obtain ⟨e', he', ek', rfl⟩ := mem_atL hF'
        rcases List.mem_cons.mp he' with rfl | he'
        · simp only at ek'; omega
        · exact Rp.sa e' he' r hF'r hFr
      · obtain rfl := cb_atL_root lp hF
        exact cc_cross H e1 (cc_orig_root Fp hFr e.1) (cc_orig Fq Rq.eat hF' hF'r)
      · obtain rfl := cb_atL_root lq hF
        exact cc_cross H e1 (cc_orig Fp Rp.eat hF' hF'r) (cc_orig_root Fq hFr e.1)
      · obtain rfl := cb_atL_root lq hF
        obtain ⟨e', he', ek', rfl⟩ := mem_atL hF'
        rcases List.mem_cons.mp he' with rfl | he'
        · simp only at ek'; omega
        · exact Rq.sa e' he' r hF'r hFr
  · -- `EregsAt` of the cons's goal
    intro e he r hr
    rcases ORG e.1 e.2.sure (cb_mem_atL_of he _) r hr with ⟨F, hF, hFr⟩ | ⟨f1, f2⟩
    · exact OL e.1 F r hF hFr
    · exact Or.inr (Or.inr ⟨by omega, f2⟩)

end Comp
end SkaModel
end Formalization
