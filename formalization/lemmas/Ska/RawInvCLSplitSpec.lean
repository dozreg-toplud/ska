import lemmas.Ska.RawInvCLConsArm
import lemmas.Ska.RawInvCLCopyIL
import lemmas.Ska.RawInvCLFrameSplit

/-!
# The run-level liveness with calls: the spec of `+split`

README Gaps 14 (b), track D.  `SplitSpecL` (`RawInvCLConsArm.lean`) proved.

* `spsK L x y`: the kills of a list of entries (`lazK o l` is `spsK` of
  `(o, l) :: entries l`).
* **`SpsI Li Lh Lt P g g'`**: what a split of the entries `Li` into the
  entries `Lh` and `Lt` does: only ops `P` in front of the blocks, reading
  first only the halves' registers at their labels, defining only the
  input's registers at their labels, mentioning only the input's registers
  and fresh ones; every input register at a label is a half's there or
  defined there; the halves' labels are the input's; and the registers of
  both halves and the definitions, counted, are at most the input's and one
  per fresh register.  `SpsI.seq`, `SpsI.swap`, `SpsI.congr`.
* `sps_must`, `sps_need` (`+split-need`), `sps_sure`, the pruned halves
  (`sps_fe_keep`, `sps_be_keep`, `sps_prune`), **`spsLoop`** (mutual with
  `spsForks`, `spsBonds`).
* `sps_liveK_prep` (`liveK_prepK` when the ops read first only what is
  killed at their label), `sps_split`, `sps_il` (`IL` of a half),
  `sps_apart`, `sps_live`, **`splitSpecL : SplitSpecL S Map`**.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The invariant of a split -/

/-- The kills of a list of entries: at each entry's label, its sure need. -/
def spsK (L : List (Nat × Lazy S)) (x y : Nat) : Prop := ∃ e ∈ L, e.1 = x ∧ NMem e.2.sure.ned y

theorem spsK_append {a b : List (Nat × Lazy S)} {x y : Nat} : spsK (a ++ b) x y ↔ spsK a x y ∨ spsK b x y := by
  simp only [spsK, List.mem_append, or_and_right, exists_or]

theorem spsK_eregs {L : List (Nat × Lazy S)} {x y : Nat} (h : spsK L x y) : ERegs L y := by
  obtain ⟨e, he, -, hm⟩ := h
  exact ⟨e, he, hm⟩

/-- **What a split of the entries `Li` into `Lh` and `Lt` does.** -/
structure SpsI (Li Lh Lt : List (Nat × Lazy S)) (P : Nat → List Pole) (g g' : Comp.Gen Map) : Prop where
  le : g.re ≤ g'.re
  cond : g'.cond = g.cond
  drop : g'.drop = g.drop
  prep : Prep P g.blocks g'.blocks
  rd : ∀ x y, OpsRF (P x) y → spsK Lh x y ∨ spsK Lt x y
  df : ∀ x y, y ∈ defsOf (P x) → spsK Li x y
  rg : ∀ x, RegsIn (fun y => ERegs Li y ∨ (g.re ≤ y ∧ y < g'.re)) (P x)
  cov : ∀ x y, spsK Li x y → spsK Lh x y ∨ spsK Lt x y ∨ y ∈ defsOf (P x)
  lh : ∀ e ∈ Lh, ∃ e' ∈ Li, e'.1 = e.1
  lt : ∀ e ∈ Lt, ∃ e' ∈ Li, e'.1 = e.1
  cnt : ∃ D : List Nat, (∀ x y, y ∈ defsOf (P x) → y ∈ D) ∧
    ∀ y, List.count y (regsL Lh ++ regsL Lt ++ D) ≤ List.count y (regsL Li) + fr g.re g'.re y

theorem SpsI.seq {L1 H1 T1 L2 H2 T2 : List (Nat × Lazy S)} {P1 P2 : Nat → List Pole} {g g1 g2 : Comp.Gen Map}
    (h1 : SpsI L1 H1 T1 P1 g g1) (h2 : SpsI L2 H2 T2 P2 g1 g2) :
    SpsI (L1 ++ L2) (H1 ++ H2) (T1 ++ T2) (fun k => P2 k ++ P1 k) g g2 where
  le := Nat.le_trans h1.le h2.le
  cond := h2.cond.trans h1.cond
  drop := h2.drop.trans h1.drop
  prep := prep_trans h1.prep h2.prep
  rd x y h := by
    rcases opsRF_append.mp h with h | ⟨-, h⟩
    · rcases h2.rd x y h with h | h
      · exact Or.inl (spsK_append.mpr (Or.inr h))
      · exact Or.inr (spsK_append.mpr (Or.inr h))
    · rcases h1.rd x y h with h | h
      · exact Or.inl (spsK_append.mpr (Or.inl h))
      · exact Or.inr (spsK_append.mpr (Or.inl h))
  df x y h := by
    rw [defsOf_append, List.mem_append] at h
    rcases h with h | h
    · exact spsK_append.mpr (Or.inr (h2.df x y h))
    · exact spsK_append.mpr (Or.inl (h1.df x y h))
  rg x p hp z hz := by
    rcases List.mem_append.mp hp with hp | hp
    · rcases h2.rg x p hp z hz with h | ⟨a, b⟩
      · exact Or.inl (eregs_append.mpr (Or.inr h))
      · exact Or.inr ⟨Nat.le_trans h1.le a, b⟩
    · rcases h1.rg x p hp z hz with h | ⟨a, b⟩
      · exact Or.inl (eregs_append.mpr (Or.inl h))
      · exact Or.inr ⟨a, Nat.lt_of_lt_of_le b h2.le⟩
  cov x y h := by
    rcases spsK_append.mp h with h | h
    · rcases h1.cov x y h with h | h | h
      · exact Or.inl (spsK_append.mpr (Or.inl h))
      · exact Or.inr (Or.inl (spsK_append.mpr (Or.inl h)))
      · exact Or.inr (Or.inr (by rw [defsOf_append, List.mem_append]; exact Or.inr h))
    · rcases h2.cov x y h with h | h | h
      · exact Or.inl (spsK_append.mpr (Or.inr h))
      · exact Or.inr (Or.inl (spsK_append.mpr (Or.inr h)))
      · exact Or.inr (Or.inr (by rw [defsOf_append, List.mem_append]; exact Or.inl h))
  lh e he := by
    rcases List.mem_append.mp he with he | he
    · obtain ⟨e', h, h'⟩ := h1.lh e he; exact ⟨e', List.mem_append_left _ h, h'⟩
    · obtain ⟨e', h, h'⟩ := h2.lh e he; exact ⟨e', List.mem_append_right _ h, h'⟩
  lt e he := by
    rcases List.mem_append.mp he with he | he
    · obtain ⟨e', h, h'⟩ := h1.lt e he; exact ⟨e', List.mem_append_left _ h, h'⟩
    · obtain ⟨e', h, h'⟩ := h2.lt e he; exact ⟨e', List.mem_append_right _ h, h'⟩
  cnt := by
    obtain ⟨D1, hD1, c1⟩ := h1.cnt
    obtain ⟨D2, hD2, c2⟩ := h2.cnt
    refine ⟨D1 ++ D2, fun x y hy => ?_, fun y => ?_⟩
    · rw [defsOf_append, List.mem_append] at hy
      rcases hy with h | h
      · exact List.mem_append_right _ (hD2 x y h)
      · exact List.mem_append_left _ (hD1 x y h)
    · have a1 := c1 y
      have a2 := c2 y
      have f := fr_add h1.le h2.le y
      simp only [regsL_append, List.count_append] at a1 a2 ⊢
      omega

theorem SpsI.swap {Li Lh Lt : List (Nat × Lazy S)} {P : Nat → List Pole} {g g' : Comp.Gen Map}
    (h : SpsI Li Lh Lt P g g') : SpsI Li Lt Lh P g g' where
  le := h.le
  cond := h.cond
  drop := h.drop
  prep := h.prep
  rd x y hr := (h.rd x y hr).symm
  df := h.df
  rg := h.rg
  cov x y hk := by
    rcases h.cov x y hk with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  lh := h.lt
  lt := h.lh
  cnt := by
    obtain ⟨D, hD, c⟩ := h.cnt
    refine ⟨D, hD, fun y => ?_⟩
    have := c y
    simp only [List.count_append] at this ⊢
    omega

theorem SpsI.congr {Li Lh Lt Li' Lh' Lt' : List (Nat × Lazy S)} {P : Nat → List Pole} {g g' : Comp.Gen Map}
    (h : SpsI Li Lh Lt P g g') (hi : Li.Perm Li')
    (hh1 : ∀ x y, spsK Lh x y → spsK Lh' x y) (hh2 : ∀ e ∈ Lh', ∃ e' ∈ Lh, e'.1 = e.1)
    (hh3 : ∀ y, List.count y (regsL Lh') ≤ List.count y (regsL Lh))
    (ht1 : ∀ x y, spsK Lt x y → spsK Lt' x y) (ht2 : ∀ e ∈ Lt', ∃ e' ∈ Lt, e'.1 = e.1)
    (ht3 : ∀ y, List.count y (regsL Lt') ≤ List.count y (regsL Lt)) :
    SpsI Li' Lh' Lt' P g g' where
  le := h.le
  cond := h.cond
  drop := h.drop
  prep := h.prep
  rd x y hr := by
    rcases h.rd x y hr with h | h
    · exact Or.inl (hh1 x y h)
    · exact Or.inr (ht1 x y h)
  df x y hy := by
    obtain ⟨e, he, h1, h2⟩ := h.df x y hy
    exact ⟨e, hi.subset he, h1, h2⟩
  rg x p hp z hz := by
    rcases h.rg x p hp z hz with h | h
    · obtain ⟨e, he, hm⟩ := h
      exact Or.inl ⟨e, hi.subset he, hm⟩
    · exact Or.inr h
  cov x y hk := by
    obtain ⟨e, he, h1, h2⟩ := hk
    rcases h.cov x y ⟨e, hi.symm.subset he, h1, h2⟩ with h | h | h
    · exact Or.inl (hh1 x y h)
    · exact Or.inr (Or.inl (ht1 x y h))
    · exact Or.inr (Or.inr h)
  lh e he := by
    obtain ⟨e1, he1, h1⟩ := hh2 e he
    obtain ⟨e2, he2, h2⟩ := h.lh e1 he1
    exact ⟨e2, hi.subset he2, h2.trans h1⟩
  lt e he := by
    obtain ⟨e1, he1, h1⟩ := ht2 e he
    obtain ⟨e2, he2, h2⟩ := h.lt e1 he1
    exact ⟨e2, hi.subset he2, h2.trans h1⟩
  cnt := by
    obtain ⟨D, hD, c⟩ := h.cnt
    refine ⟨D, hD, fun y => ?_⟩
    have a := c y
    have b1 := hh3 y
    have b2 := ht3 y
    have e := (regsL_perm hi).count_eq y
    simp only [List.count_append] at a ⊢
    omega

/-- A register of the first half is the input's or fresh. -/
theorem SpsI.memH {Li Lh Lt : List (Nat × Lazy S)} {P : Nat → List Pole} {g g' : Comp.Gen Map}
    (h : SpsI Li Lh Lt P g g') {y : Nat} (hy : y ∈ regsL Lh) : ERegs Li y ∨ (g.re ≤ y ∧ y < g'.re) := by
  obtain ⟨D, -, c⟩ := h.cnt
  have a := c y
  have b : 0 < List.count y (regsL Lh) := List.count_pos_iff.mpr hy
  simp only [List.count_append] at a
  by_cases hc : 0 < List.count y (regsL Li)
  · exact Or.inl (mem_regsL.mp (List.count_pos_iff.mp hc))
  · exact Or.inr (fr_pos (by omega))

/-! ## `+must` and `+split-need` -/

theorem sps_must {n : Need} {g g1 : Comp.Gen Map} {rr : Nat} {n' : Need}
    (h : (must n : CM Map (Nat × Need)) g = some ((rr, n'), g1)) :
    g1 = { g with re := g1.re } ∧ g.re ≤ g1.re ∧ g1.re ≤ g.re + 1 ∧ NMem n' rr ∧
    (∀ y, NMem n y → NMem n' y) ∧ (∀ y, NMem n' y → NMem n y ∨ (g.re ≤ y ∧ y < g1.re)) ∧
    ∀ y, List.count y (flattenNeed n') ≤ List.count y (flattenNeed n) + fr g.re g1.re y := by
  cases n with
  | none =>
    simp only [must, bind_apply, re_apply, pure_apply, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    refine ⟨rfl, Nat.le_succ _, Nat.le_refl _, rfl, fun y hy => hy.elim, fun y hy => ?_, fun y => ?_⟩
    · have hy' : y = g.re := hy
      exact Or.inr ⟨Nat.le_of_eq hy'.symm, show y < g.re + 1 by omega⟩
    · show List.count y [g.re] ≤ 0 + fr g.re (g.re + 1) y
      simp only [fr, List.count_cons, List.count_nil]
      split <;> split <;> simp_all
  | this r =>
    simp only [must, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact ⟨rfl, Nat.le_refl _, Nat.le_succ _, rfl, fun y hy => hy, fun y hy => Or.inl hy,
      fun y => Nat.le_add_right _ _⟩
  | pair p q =>
    simp only [must, bind_apply, re_apply, pure_apply, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    refine ⟨rfl, Nat.le_succ _, Nat.le_refl _, Or.inl rfl, fun y hy => Or.inr hy, fun y hy => ?_, fun y => ?_⟩
    · rcases hy with hy | hy
      · have hy' : y = g.re := hy
        exact Or.inr ⟨Nat.le_of_eq hy'.symm, show y < g.re + 1 by omega⟩
      · exact Or.inl hy
    · show List.count y (g.re :: (flattenNeed p ++ flattenNeed q)) ≤
        List.count y (flattenNeed p ++ flattenNeed q) + fr g.re (g.re + 1) y
      simp only [fr, List.count_cons]
      split <;> split <;> simp_all
  | both r p q =>
    simp only [must, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact ⟨rfl, Nat.le_refl _, Nat.le_succ _, Or.inl rfl, fun y hy => hy, fun y hy => Or.inl hy,
      fun y => Nat.le_add_right _ _⟩


theorem spsK_single {o x y : Nat} {L : Lazy S} : spsK [(o, L)] x y ↔ x = o ∧ NMem L.sure.ned y := by
  simp only [spsK, List.mem_singleton, exists_eq_left]
  exact ⟨fun ⟨a, b⟩ => ⟨a.symm, b⟩, fun ⟨a, b⟩ => ⟨a.symm, b⟩⟩

theorem sps_lab1 {o : Nat} {L X : Lazy S} : ∀ e ∈ [(o, X)], ∃ e' ∈ [(o, L)], e'.1 = e.1 := by
  intro e he
  rw [List.mem_singleton] at he
  subst he
  exact ⟨(o, L), List.mem_singleton_self _, rfl⟩

theorem sps_regs1 {o : Nat} {L : Lazy S} : regsL [(o, L)] = flattenNeed L.sure.ned := by
  simp [regsL]

theorem sps_eregs1 {o y : Nat} {L : Lazy S} : ERegs [(o, L)] y ↔ NMem L.sure.ned y := by
  simp [ERegs]

theorem sps_P1 {o x : Nat} {A : List Pole} {y : Nat} (h : y ∈ defsOf (if x = o then A else [])) :
    x = o ∧ y ∈ defsOf A := by
  by_cases e : x = o
  · rw [if_pos e] at h; exact ⟨e, h⟩
  · rw [if_neg e] at h; simp [defsOf] at h

/-- **`+split-need`** as a split of one entry. -/
theorem sps_need {ned : Need} {o : Nat} {g g' : Comp.Gen Map} {nh nt : Need}
    (h : (splitNeed ned o : CM Map (Need × Need)) g = some ((nh, nt), g')) (hd : g.drop = false)
    (hlt : ∀ y, NMem ned y → y < g.re)
    {L X Y : Lazy S} (hL : L.sure.ned = ned) (hX : X.sure.ned = nh) (hY : Y.sure.ned = nt) :
    ∃ P, SpsI [(o, L)] [(o, X)] [(o, Y)] P g g' := by
  cases ned with
  | pair p q =>
    simp only [splitNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    refine ⟨fun _ => [], Nat.le_refl _, rfl, rfl, prep_nil _, fun x y h => h.elim,
      fun x y h => by simp [defsOf] at h, fun x => RegsIn.nil _, fun x y hk => ?_, sps_lab1, sps_lab1,
      [], fun x y h => by simp [defsOf] at h, fun y => ?_⟩
    · obtain ⟨h1, h2⟩ := spsK_single.mp hk
      rw [hL] at h2
      rcases h2 with h2 | h2
      · exact Or.inl (spsK_single.mpr ⟨h1, by rw [hX]; exact h2⟩)
      · exact Or.inr (Or.inl (spsK_single.mpr ⟨h1, by rw [hY]; exact h2⟩))
    · rw [sps_regs1, sps_regs1, sps_regs1, hL, hX, hY]
      simp only [flattenNeed, List.count_append, List.count_nil]
      omega
  | none =>
    simp only [splitNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    refine ⟨fun _ => [], Nat.le_refl _, rfl, rfl, prep_nil _, fun x y h => h.elim,
      fun x y h => by simp [defsOf] at h, fun x => RegsIn.nil _, fun x y hk => ?_, sps_lab1, sps_lab1,
      [], fun x y h => by simp [defsOf] at h, fun y => ?_⟩
    · obtain ⟨-, h2⟩ := spsK_single.mp hk
      rw [hL] at h2
      exact h2.elim
    · rw [sps_regs1, sps_regs1, sps_regs1, hL, hX, hY]
      simp only [flattenNeed, List.count_append, List.count_nil]
      omega
  | this r =>
    have hr : r < g.re := hlt r rfl
    obtain ⟨h1, ga, e1, h⟩ := bind_some h
    rw [re_apply] at e1
    simp only [Option.some.injEq, Prod.mk.injEq] at e1
    obtain ⟨rfl, rfl⟩ := e1
    obtain ⟨t1, gb, e2, h⟩ := bind_some h
    rw [re_apply] at e2
    simp only [Option.some.injEq, Prod.mk.injEq] at e2
    obtain ⟨rfl, rfl⟩ := e2
    obtain ⟨u, gc, e3, h⟩ := bind_some h
    cases u
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    obtain ⟨A3, c3, P3⟩ := addOps_step (g := { g with re := g.re + 1 + 1 }) hd e3
    have hre : g.re + 1 + 1 ≤ gc.re := A3.2.2.2.1
    refine ⟨fun k => if k = o then [Pole.con g.re (g.re + 1) r] else [], by omega, c3, A3.2.1, P3,
      fun x y hr' => ?_, fun x y hy => ?_, fun x => ?_, fun x y hk => ?_, sps_lab1, sps_lab1,
      [r], fun x y hy => ?_, fun y => ?_⟩
    · by_cases e : x = o
      · rw [if_pos e] at hr'
        rcases opsRF_con.mp hr' with rfl | rfl
        · exact Or.inl (spsK_single.mpr ⟨e, by rw [hX]; rfl⟩)
        · exact Or.inr (spsK_single.mpr ⟨e, by rw [hY]; rfl⟩)
      · rw [if_neg e] at hr'; exact hr'.elim
    · obtain ⟨e, hy⟩ := sps_P1 hy
      rw [defsOf_con, List.mem_singleton] at hy
      exact spsK_single.mpr ⟨e, by rw [hL, hy]; rfl⟩
    · by_cases e : x = o
      · rw [if_pos e]
        intro p hp z hz
        rw [List.mem_singleton] at hp
        subst hp
        simp only [Comp.poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hz
        rcases hz with rfl | rfl | rfl
        · exact Or.inr ⟨Nat.le_refl _, by omega⟩
        · exact Or.inr ⟨by omega, by omega⟩
        · exact Or.inl (sps_eregs1.mpr (by rw [hL]; rfl))
      · rw [if_neg e]; exact RegsIn.nil _
    · obtain ⟨e, h2⟩ := spsK_single.mp hk
      rw [hL] at h2
      have h2' : y = r := h2
      refine Or.inr (Or.inr ?_)
      rw [if_pos e, defsOf_con, h2']
      exact List.mem_singleton_self _
    · obtain ⟨-, hy⟩ := sps_P1 hy
      rw [defsOf_con] at hy
      exact hy
    · rw [sps_regs1, sps_regs1, sps_regs1, hL, hX, hY]
      show List.count y ([g.re] ++ [g.re + 1] ++ [r]) ≤ List.count y [r] + fr g.re gc.re y
      simp only [fr, List.count_append, List.count_cons, List.count_nil, beq_iff_eq]
      repeat' split
      all_goals omega
  | both r hh tt =>
    have hr : r < g.re := hlt r (Or.inl rfl)
    obtain ⟨⟨r1, h'⟩, ga, e1, k⟩ := bind_some h
    obtain ⟨⟨r2, t'⟩, gb, e2, k⟩ := bind_some k
    obtain ⟨u, gc, e3, k⟩ := bind_some k
    cases u
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at k
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := k
    obtain ⟨ea, la1, la2, ma, sa, ta, ca⟩ := sps_must e1
    obtain ⟨eb, lb1, lb2, mb, sb, tb, cb⟩ := sps_must e2
    have hc1 : gb.cond = ga.cond := by rw [eb]
    have hc2 : ga.cond = g.cond := by rw [ea]
    have hb1 : gb.blocks = ga.blocks := by rw [eb]
    have hb2 : ga.blocks = g.blocks := by rw [ea]
    have hd1 : gb.drop = ga.drop := by rw [eb]
    have hd2 : ga.drop = g.drop := by rw [ea]
    have hcb : gb.cond = g.cond := hc1.trans hc2
    have hbb : gb.blocks = g.blocks := hb1.trans hb2
    have hdb : gb.drop = g.drop := hd1.trans hd2
    obtain ⟨A3, c3, P3⟩ := addOps_step (hdb.trans hd) e3
    have hre : gb.re ≤ gc.re := A3.2.2.2.1
    refine ⟨fun k => if k = o then [Pole.con r1 r2 r] else [], by omega, c3.trans hcb, A3.2.1.trans hdb,
      by rw [← hbb]; exact P3, fun x y hr' => ?_, fun x y hy => ?_, fun x => ?_, fun x y hk => ?_, sps_lab1,
      sps_lab1, [r], fun x y hy => ?_, fun y => ?_⟩
    · by_cases e : x = o
      · rw [if_pos e] at hr'
        rcases opsRF_con.mp hr' with rfl | rfl
        · exact Or.inl (spsK_single.mpr ⟨e, by rw [hX]; exact ma⟩)
        · exact Or.inr (spsK_single.mpr ⟨e, by rw [hY]; exact mb⟩)
      · rw [if_neg e] at hr'; exact hr'.elim
    · obtain ⟨e, hy⟩ := sps_P1 hy
      rw [defsOf_con, List.mem_singleton] at hy
      exact spsK_single.mpr ⟨e, by rw [hL, hy]; exact Or.inl rfl⟩
    · by_cases e : x = o
      · rw [if_pos e]
        intro p hp z hz
        rw [List.mem_singleton] at hp
        subst hp
        simp only [Comp.poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hz
        rcases hz with rfl | rfl | rfl
        · rcases ta _ ma with h | ⟨a, b⟩
          · exact Or.inl (sps_eregs1.mpr (by rw [hL]; exact Or.inr (Or.inl h)))
          · exact Or.inr ⟨a, by omega⟩
        · rcases tb _ mb with h | ⟨a, b⟩
          · exact Or.inl (sps_eregs1.mpr (by rw [hL]; exact Or.inr (Or.inr h)))
          · exact Or.inr ⟨by omega, by omega⟩
        · exact Or.inl (sps_eregs1.mpr (by rw [hL]; exact Or.inl rfl))
      · rw [if_neg e]; exact RegsIn.nil _
    · obtain ⟨e, h2⟩ := spsK_single.mp hk
      rw [hL] at h2
      rcases h2 with h2 | h2 | h2
      · refine Or.inr (Or.inr ?_)
        rw [if_pos e, defsOf_con, h2]
        exact List.mem_singleton_self _
      · exact Or.inl (spsK_single.mpr ⟨e, by rw [hX]; exact sa _ h2⟩)
      · exact Or.inr (Or.inl (spsK_single.mpr ⟨e, by rw [hY]; exact sb _ h2⟩))
    · obtain ⟨-, hy⟩ := sps_P1 hy
      rw [defsOf_con] at hy
      exact hy
    · rw [sps_regs1, sps_regs1, sps_regs1, hL, hX, hY]
      show List.count y (flattenNeed h' ++ flattenNeed t' ++ [r]) ≤
        List.count y ([r] ++ (flattenNeed hh ++ flattenNeed tt)) + fr g.re gc.re y
      have a1 := ca y
      have a2 := cb y
      have f1 := fr_add la1 lb1 y
      have f2 := fr_mono (a := g.re) hre y
      simp only [List.count_append] at a1 a2 ⊢
      omega

/-- **`+split-sure`** as a split of one entry. -/
theorem sps_sure {s : Sure S} {o : Nat} {g g' : Comp.Gen Map} {sh st : Sure S}
    (h : (splitSure s o : CM Map (Sure S × Sure S)) g = some ((sh, st), g')) (hd : g.drop = false)
    (hlt : ∀ y, NMem s.ned y → y < g.re)
    {L X Y : Lazy S} (hL : L.sure = s) (hX : X.sure = sh) (hY : Y.sure = st) :
    ∃ P, SpsI [(o, L)] [(o, X)] [(o, Y)] P g g' := by
  unfold splitSure at h
  obtain ⟨⟨lh, lt⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨⟨nh, nt⟩, g2⟩, h2, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
  exact sps_need h2 hd hlt (by rw [hL]) (by rw [hX]) (by rw [hY])

/-! ## The pruned halves -/

theorem sps_lazyEmpty {l : Lazy S} (h : lazyEmpty l = true) : l.sure.ned = Need.none ∧ entries l = [] := by
  rcases l with ⟨s, f, b⟩
  simp only [lazyEmpty, sure_mk, fork_mk, bond_mk, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at h
  obtain ⟨⟨⟨h1, -⟩, rfl⟩, rfl⟩ := h
  exact ⟨of_decide_eq_true h1, by simp [entries, bondEntries, forkEntries]⟩

theorem sps_fe_keep : ∀ (f : List (ForkE S)) (e : Nat × Lazy S), e ∈ forkEntries f → ∀ y, NMem e.2.sure.ned y →
    e ∈ forkEntries (f.filter fun e => !(lazyEmpty e.1.2 && lazyEmpty e.2.2))
  | [], e, he, _, _ => by simp [forkEntries] at he
  | ((oy, a), (on, b)) :: rest, e, he, y, hy => by
    have he' : e ∈ ((oy, a) :: entries a) ++ ((on, b) :: entries b) ++ forkEntries rest := he
    rw [List.filter_cons]
    split
    · show e ∈ ((oy, a) :: entries a) ++ ((on, b) :: entries b) ++
        forkEntries (rest.filter fun e => !(lazyEmpty e.1.2 && lazyEmpty e.2.2))
      rcases List.mem_append.mp he' with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (sps_fe_keep rest e h y hy)
    · rename_i hp
      have ha : lazyEmpty a = true := by cases h1 : lazyEmpty a <;> simp_all
      have hb : lazyEmpty b = true := by cases h1 : lazyEmpty b <;> simp_all
      obtain ⟨na, ea⟩ := sps_lazyEmpty ha
      obtain ⟨nb, eb⟩ := sps_lazyEmpty hb
      rcases List.mem_append.mp he' with h | h
      · rcases List.mem_append.mp h with h | h
        · rw [ea, List.mem_singleton] at h
          subst h
          rw [na] at hy; exact hy.elim
        · rw [eb, List.mem_singleton] at h
          subst h
          rw [nb] at hy; exact hy.elim
      · exact sps_fe_keep rest e h y hy

theorem sps_be_keep : ∀ (b : List (Nat × Lazy S)) (e : Nat × Lazy S), e ∈ bondEntries b → ∀ y, NMem e.2.sure.ned y →
    e ∈ bondEntries (b.filter fun e => !(lazyEmpty e.2))
  | [], e, he, _, _ => by simp [bondEntries] at he
  | (o, a) :: rest, e, he, y, hy => by
    have he' : e ∈ ((o, a) :: entries a) ++ bondEntries rest := he
    rw [List.filter_cons]
    split
    · show e ∈ ((o, a) :: entries a) ++ bondEntries (rest.filter fun e => !(lazyEmpty e.2))
      rcases List.mem_append.mp he' with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (sps_be_keep rest e h y hy)
    · rename_i hp
      have ha : lazyEmpty a = true := by cases h1 : lazyEmpty a <;> simp_all
      obtain ⟨na, ea⟩ := sps_lazyEmpty ha
      rcases List.mem_append.mp he' with h | h
      · rw [ea, List.mem_singleton] at h
        subst h
        rw [na] at hy; exact hy.elim
      · exact sps_be_keep rest e h y hy

theorem sps_fe_sub (p : ForkE S → Bool) : ∀ (f : List (ForkE S)) (e : Nat × Lazy S),
    e ∈ forkEntries (f.filter p) → e ∈ forkEntries f
  | [], e, he => by simp [forkEntries] at he
  | ((oy, a), (on, b)) :: rest, e, he => by
    show e ∈ ((oy, a) :: entries a) ++ ((on, b) :: entries b) ++ forkEntries rest
    rw [List.filter_cons] at he
    split at he
    · have he' : e ∈ ((oy, a) :: entries a) ++ ((on, b) :: entries b) ++ forkEntries (rest.filter p) := he
      rcases List.mem_append.mp he' with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (sps_fe_sub p rest e h)
    · exact List.mem_append_right _ (sps_fe_sub p rest e he)

theorem sps_be_sub (p : Nat × Lazy S → Bool) : ∀ (b : List (Nat × Lazy S)) (e : Nat × Lazy S),
    e ∈ bondEntries (b.filter p) → e ∈ bondEntries b
  | [], e, he => by simp [bondEntries] at he
  | (o, a) :: rest, e, he => by
    show e ∈ ((o, a) :: entries a) ++ bondEntries rest
    rw [List.filter_cons] at he
    split at he
    · have he' : e ∈ ((o, a) :: entries a) ++ bondEntries (rest.filter p) := he
      rcases List.mem_append.mp he' with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (sps_be_sub p rest e h)
    · exact List.mem_append_right _ (sps_be_sub p rest e he)

theorem sps_fe_count (p : ForkE S → Bool) : ∀ (f : List (ForkE S)) (y : Nat),
    List.count y (regsL (forkEntries (f.filter p))) ≤ List.count y (regsL (forkEntries f))
  | [], y => by simp [forkEntries]
  | ((oy, a), (on, b)) :: rest, y => by
    have ih := sps_fe_count p rest y
    rw [List.filter_cons]
    have e0 : forkEntries (((oy, a), (on, b)) :: rest) =
        ((oy, a) :: entries a) ++ ((on, b) :: entries b) ++ forkEntries rest := rfl
    split
    · have e1 : forkEntries (((oy, a), (on, b)) :: rest.filter p) =
          ((oy, a) :: entries a) ++ ((on, b) :: entries b) ++ forkEntries (rest.filter p) := rfl
      rw [e0, e1]
      simp only [regsL_append, List.count_append]
      omega
    · rw [e0]
      simp only [regsL_append, List.count_append]
      omega

theorem sps_be_count (p : Nat × Lazy S → Bool) : ∀ (b : List (Nat × Lazy S)) (y : Nat),
    List.count y (regsL (bondEntries (b.filter p))) ≤ List.count y (regsL (bondEntries b))
  | [], y => by simp [bondEntries]
  | (o, a) :: rest, y => by
    have ih := sps_be_count p rest y
    rw [List.filter_cons]
    have e0 : bondEntries ((o, a) :: rest) = ((o, a) :: entries a) ++ bondEntries rest := rfl
    split
    · have e1 : bondEntries ((o, a) :: rest.filter p) = ((o, a) :: entries a) ++ bondEntries (rest.filter p) := rfl
      rw [e0, e1]
      simp only [regsL_append, List.count_append]
      omega
    · rw [e0]
      simp only [regsL_append, List.count_append]
      omega

/-- **A pruned half** against the entries the walk returned. -/
theorem sps_prune (o : Nat) (s : Sure S) (f : List (ForkE S)) (b : List (Nat × Lazy S)) :
    (∀ x y, spsK ([(o, mk s f b)] ++ (forkEntries f ++ bondEntries b)) x y →
      spsK ((o, lazyPrune (mk s f b)) :: entries (lazyPrune (mk s f b))) x y) ∧
    (∀ e ∈ (o, lazyPrune (mk s f b)) :: entries (lazyPrune (mk s f b)),
      ∃ e' ∈ [(o, mk s f b)] ++ (forkEntries f ++ bondEntries b), e'.1 = e.1) ∧
    (∀ y, List.count y (regsL ((o, lazyPrune (mk s f b)) :: entries (lazyPrune (mk s f b)))) ≤
      List.count y (regsL ([(o, mk s f b)] ++ (forkEntries f ++ bondEntries b)))) := by
  have ep : lazyPrune (mk s f b) = mk s (f.filter fun e => !(lazyEmpty e.1.2 && lazyEmpty e.2.2))
      (b.filter fun e => !(lazyEmpty e.2)) := rfl
  have ee : entries (lazyPrune (mk s f b)) = bondEntries (b.filter fun e => !(lazyEmpty e.2)) ++
      forkEntries (f.filter fun e => !(lazyEmpty e.1.2 && lazyEmpty e.2.2)) := by
    rw [ep]; rfl
  refine ⟨fun x y hk => ?_, fun e he => ?_, fun y => ?_⟩
  · obtain ⟨e, he, h1, h2⟩ := hk
    rcases List.mem_append.mp he with he | he
    · rw [List.mem_singleton] at he
      subst he
      exact ⟨(o, lazyPrune (mk s f b)), List.mem_cons_self, h1, by rw [ep]; exact h2⟩
    · refine ⟨e, List.mem_cons_of_mem _ ?_, h1, h2⟩
      rw [ee]
      rcases List.mem_append.mp he with he | he
      · exact List.mem_append_right _ (sps_fe_keep f e he y h2)
      · exact List.mem_append_left _ (sps_be_keep b e he y h2)
  · rcases List.mem_cons.mp he with rfl | he
    · exact ⟨(o, mk s f b), List.mem_append_left _ (List.mem_singleton_self _), rfl⟩
    · rw [ee] at he
      refine ⟨e, List.mem_append_right _ ?_, rfl⟩
      rcases List.mem_append.mp he with he | he
      · exact List.mem_append_right _ (sps_be_sub _ b e he)
      · exact List.mem_append_left _ (sps_fe_sub _ f e he)
  · rw [regsL_cons, ee]
    have a1 := sps_fe_count (fun e => !(lazyEmpty e.1.2 && lazyEmpty e.2.2)) f y
    have a2 := sps_be_count (fun e => !(lazyEmpty e.2)) b y
    have er : (lazyPrune (mk s f b)).sure = s := by rw [ep]; rfl
    rw [er]
    simp only [regsL_append, sps_regs1, sure_mk, List.count_append]
    omega

theorem sps_perm (o : Nat) (s : Sure S) (f : List (ForkE S)) (b : List (Nat × Lazy S)) :
    ([(o, mk s f b)] ++ (forkEntries f ++ bondEntries b)).Perm ((o, mk s f b) :: entries (mk s f b)) := by
  show ((o, mk s f b) :: (forkEntries f ++ bondEntries b)).Perm ((o, mk s f b) :: (bondEntries b ++ forkEntries f))
  exact List.Perm.cons _ List.perm_append_comm

theorem sps_nil (g : Comp.Gen Map) : SpsI ([] : List (Nat × Lazy S)) [] [] (fun _ => []) g g where
  le := Nat.le_refl _
  cond := rfl
  drop := rfl
  prep := prep_nil _
  rd _ _ h := h.elim
  df _ _ h := by simp [defsOf] at h
  rg _ := RegsIn.nil _
  cov _ _ h := by obtain ⟨e, he, -⟩ := h; exact absurd he List.not_mem_nil
  lh _ he := absurd he List.not_mem_nil
  lt _ he := absurd he List.not_mem_nil
  cnt := ⟨[], fun _ _ h => by simp [defsOf] at h, fun y => by simp [regsL]⟩

/-! ## The walk -/

mutual
/-- **`split-loop` is a split of the tree's entries.** -/
theorem spsLoop : ∀ (l : Lazy S) (o : Nat) (g g' : Comp.Gen Map) (x : Lazy S × Lazy S),
    splitLoop l o g = some (x, g') → g.drop = false →
    (∀ y, ERegs ((o, l) :: entries l) y → y < g.re) →
    ∃ P, SpsI ((o, l) :: entries l) ((o, x.1) :: entries x.1) ((o, x.2) :: entries x.2) P g g'
  | mk s f b, o, g, g', x, h, hd, hlt => by
    rw [splitLoop] at h
    obtain ⟨⟨sh, st⟩, g1, h1, h⟩ := bind_some h
    dsimp only at h
    have hs : ∀ y, NMem s.ned y → y < g.re := fun y hy => hlt y (eregs_cons.mpr (Or.inl hy))
    split at h
    · rename_i hfb
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hfb
      obtain ⟨rfl, rfl⟩ := hfb
      obtain ⟨P, A⟩ := sps_sure h1 hd hs (L := mk s [] []) (X := ofSure sh) (Y := ofSure st) rfl rfl rfl
      refine ⟨P, ?_⟩
      have e1 : entries (mk s ([] : List (ForkE S)) []) = [] := by simp [entries, bondEntries, forkEntries]
      simp only [e1, entries_ofSure]
      exact A
    · obtain ⟨⟨fh, ft⟩, g2, h2, h⟩ := bind_some h
      dsimp only at h
      obtain ⟨⟨bh, bt⟩, g3, h3, h⟩ := bind_some h
      dsimp only at h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hlt' : ∀ y, ERegs (bondEntries b ++ forkEntries f) y → y < g.re :=
        fun y hy => hlt y (eregs_cons.mpr (Or.inr hy))
      obtain ⟨P1, A1⟩ := sps_sure h1 hd hs (L := mk s f b) (X := mk sh fh bh) (Y := mk st ft bt) rfl rfl rfl
      obtain ⟨P2, A2⟩ := spsForks f g1 g2 _ h2 (A1.drop.trans hd)
        (fun y hy => Nat.lt_of_lt_of_le (hlt' y (eregs_append.mpr (Or.inr hy))) A1.le)
      obtain ⟨P3, A3⟩ := spsBonds b g2 g3 _ h3 (A2.drop.trans (A1.drop.trans hd))
        (fun y hy => Nat.lt_of_lt_of_le (hlt' y (eregs_append.mpr (Or.inl hy))) (Nat.le_trans A1.le A2.le))
      have A := A1.seq (A2.seq A3)
      obtain ⟨p1, p2, p3⟩ := sps_prune o sh fh bh
      obtain ⟨q1, q2, q3⟩ := sps_prune o st ft bt
      exact ⟨_, A.congr (sps_perm o s f b) p1 p2 p3 q1 q2 q3⟩

theorem spsForks : ∀ (f : List (ForkE S)) (g g' : Comp.Gen Map) (x : List (ForkE S) × List (ForkE S)),
    splitForks f g = some (x, g') → g.drop = false → (∀ y, ERegs (forkEntries f) y → y < g.re) →
    ∃ P, SpsI (forkEntries f) (forkEntries x.1) (forkEntries x.2) P g g'
  | [], g, g', x, h, _, _ => by
    rw [splitForks] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, sps_nil g⟩
  | ((oy, y), (on, n)) :: rest, g, g', x, h, hd, hlt => by
    rw [splitForks] at h
    obtain ⟨⟨yh, yt⟩, g1, h1, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨⟨nh, nt⟩, g2, h2, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨⟨rh, rt⟩, g3, h3, h⟩ := bind_some h
    dsimp only at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hl : ∀ z, ERegs (((oy, y) :: entries y) ++ ((on, n) :: entries n) ++ forkEntries rest) z → z < g.re :=
      hlt
    obtain ⟨P1, A1⟩ := spsLoop y oy g g1 _ h1 hd
      (fun z hz => hl z (eregs_append.mpr (Or.inl (eregs_append.mpr (Or.inl hz)))))
    obtain ⟨P2, A2⟩ := spsLoop n on g1 g2 _ h2 (A1.drop.trans hd)
      (fun z hz => Nat.lt_of_lt_of_le (hl z (eregs_append.mpr (Or.inl (eregs_append.mpr (Or.inr hz))))) A1.le)
    obtain ⟨P3, A3⟩ := spsForks rest g2 g3 _ h3 (A2.drop.trans (A1.drop.trans hd))
      (fun z hz => Nat.lt_of_lt_of_le (hl z (eregs_append.mpr (Or.inr hz))) (Nat.le_trans A1.le A2.le))
    exact ⟨_, (A1.seq A2).seq A3⟩

theorem spsBonds : ∀ (b : List (Nat × Lazy S)) (g g' : Comp.Gen Map) (x : List (Nat × Lazy S) × List (Nat × Lazy S)),
    splitBonds b g = some (x, g') → g.drop = false → (∀ y, ERegs (bondEntries b) y → y < g.re) →
    ∃ P, SpsI (bondEntries b) (bondEntries x.1) (bondEntries x.2) P g g'
  | [], g, g', x, h, _, _ => by
    rw [splitBonds] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, sps_nil g⟩
  | (o, l) :: rest, g, g', x, h, hd, hlt => by
    rw [splitBonds] at h
    obtain ⟨⟨lh, lt⟩, g1, h1, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨⟨rh, rt⟩, g2, h2, h⟩ := bind_some h
    dsimp only at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hl : ∀ z, ERegs (((o, l) :: entries l) ++ bondEntries rest) z → z < g.re := hlt
    obtain ⟨P1, A1⟩ := spsLoop l o g g1 _ h1 hd (fun z hz => hl z (eregs_append.mpr (Or.inl hz)))
    obtain ⟨P2, A2⟩ := spsBonds rest g1 g2 _ h2 (A1.drop.trans hd)
      (fun z hz => Nat.lt_of_lt_of_le (hl z (eregs_append.mpr (Or.inr hz))) A1.le)
    exact ⟨_, A1.seq A2⟩
end

/-! ## The spec -/

/-- **`liveK_prepK` when the ops read first only what is killed at their
label**: no path is lost to the ops. -/
theorem sps_liveK_prep {P : Nat → List Pole} {bl bl' : Map Blob} (hP : Prep P bl bl') {K : Nat → Nat → Prop}
    (hR : ∀ k y, OpsRF (P k) y → K k y) {k r : Nat} (h : LiveK bl' K k r) :
    LiveK bl (fun x y => K x y ∨ y ∈ defsOf (P x)) k r := by
  induction h with
  | here hb hr hk =>
    rw [hP] at hb
    obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp hb
    rcases blockRF_pre hr with h | ⟨hd, h⟩
    · exact absurd (hR _ _ h) hk
    · exact LiveK.here h0 h fun hk' => hk'.elim hk hd
  | next hb hj _ hd hk ih =>
    rw [hP] at hb
    obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp hb
    exact LiveK.next h0 hj ih (fun hm => hd (mem_blockDefs_pre.mpr (Or.inl hm)))
      fun hk' => hk'.elim hk fun h' => hd (mem_blockDefs_pre.mpr (Or.inr h'))

theorem sps_defd {P : Nat → List Pole} {bl bl' : Map Blob} (hP : Prep P bl bl') {y : Nat} (h : Defd bl' y) :
    Defd bl y ∨ ∃ x, y ∈ defsOf (P x) := by
  obtain ⟨o, b, hb, hm⟩ := defd_iff.mp h
  rw [hP] at hb
  obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp hb
  rcases mem_blockDefs_pre.mp hm with hm | hm
  · exact Or.inl (defd_iff.mpr ⟨o, b0, h0, hm⟩)
  · exact Or.inr ⟨o, hm⟩

/-- **`+split` is a split of the goal's entries**, rooted at the fresh hop
block `o`. -/
theorem sps_split {K : Nat → Nat → Prop} {laz : Lazy S} {th : Jmp} {g0 g1 : Comp.Gen Map} {hed tel : Lazy S}
    {o : Nat} (hI : IL K (CGoalL.next laz th) g0) (h : splitL ⟨laz, th⟩ g0 = some ((hed, tel, o), g1)) :
    o = g0.bo ∧ ATS g1 ∧ KP g0 g1 ∧ Fresh g1 (jmp0 o) ∧
    ∃ P, SpsI ((g0.bo, laz) :: entries laz) ((g0.bo, hed) :: entries hed) ((g0.bo, tel) :: entries tel) P
      (g0.emitted ⟨[], [], Termin.hop th⟩) g1 := by
  obtain ⟨hth, -, -⟩ := (hI.goal : GoalL g0 (CGoalL.next laz th))
  obtain ⟨A1, KP1, hfr⟩ := (ht_splitL (⟨laz, th⟩ : NextL S)).run g0 _ g1 hI.ats hth h
  unfold splitL at h
  obtain ⟨o1, ge, he, h⟩ := bind_some h
  rw [emit_apply] at he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨⟨hh, tt⟩, g2, h2, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
  refine ⟨rfl, A1, KP1, hfr, ?_⟩
  have hER := hI.entry_regs (o := g0.bo)
  exact spsLoop laz g0.bo _ _ _ h2 hI.ats.1 (fun y ⟨e, he, hy⟩ => (hER e he y hy).1)

/-- The registers of both halves and the definitions have no repetition. -/
theorem sps_nodup {K : Nat → Nat → Prop} {laz : Lazy S} {th : Jmp} {g0 g1 : Comp.Gen Map}
    {Lh Lt : List (Nat × Lazy S)} {P : Nat → List Pole} (hI : IL K (CGoalL.next laz th) g0)
    (A : SpsI ((g0.bo, laz) :: entries laz) Lh Lt P (g0.emitted ⟨[], [], Termin.hop th⟩) g1) :
    ∃ D, (∀ x y, y ∈ defsOf (P x) → y ∈ D) ∧ (regsL Lh ++ regsL Lt ++ D).Nodup := by
  obtain ⟨-, hna, hent⟩ := (hI.goal : GoalL g0 (CGoalL.next laz th))
  have hn : (regsL ((th.there, laz) :: entries laz)).Nodup :=
    nodup_regsL_iff.mpr ⟨hna, fun e he => (hent e he).2.1⟩
  have hn' : (regsL ((g0.bo, laz) :: entries laz)).Nodup := by
    rw [regsL_cons] at hn ⊢; exact hn
  have hER := hI.entry_regs (o := g0.bo)
  obtain ⟨D, hD, c⟩ := A.cnt
  refine ⟨D, hD, nodup_of_count fun y => ?_⟩
  have a := c y
  have b := count_le_one_of_nodup hn' y
  have hre : (g0.emitted ⟨[], [], Termin.hop th⟩).re = g0.re := rfl
  by_cases hy : y ∈ regsL ((g0.bo, laz) :: entries laz)
  · obtain ⟨e, he, hm⟩ := mem_regsL.mp hy
    have hlt := (hER e he y hm).1
    have : fr (g0.emitted ⟨[], [], Termin.hop th⟩).re g1.re y = 0 := by
      rw [hre]; unfold fr; split
      · rename_i h; omega
      · rfl
    omega
  · have : List.count y (regsL ((g0.bo, laz) :: entries laz)) = 0 := List.count_eq_zero.mpr hy
    have := fr_le_one (g0.emitted ⟨[], [], Termin.hop th⟩).re g1.re y
    omega

/-- **`IL` of the first half** as a goal at `o`. -/
theorem sps_il {K : Nat → Nat → Prop} {laz : Lazy S} {th : Jmp} {g0 g1 : Comp.Gen Map} {hed tel : Lazy S}
    {P : Nat → List Pole} (hI : IL K (CGoalL.next laz th) g0)
    (A : SpsI ((g0.bo, laz) :: entries laz) ((g0.bo, hed) :: entries hed) ((g0.bo, tel) :: entries tel) P
      (g0.emitted ⟨[], [], Termin.hop th⟩) g1)
    (hats : ATS g1) (hkp : KP g0 g1) (hfr : Fresh g1 (jmp0 g0.bo)) :
    IL K (CGoalL.next hed (jmp0 g0.bo)) g1 := by
  have hd : g0.drop = false := hI.ats.1
  obtain ⟨hth, -, hent⟩ := (hI.goal : GoalL g0 (CGoalL.next laz th))
  obtain ⟨bt, hbt, hpt, targs⟩ := hth
  have hER := hI.entry_regs (o := g0.bo)
  have hle : g0.re ≤ g1.re := A.le
  have hc1 : g1.cond = g0.cond := A.cond
  have hbD : blockDefs (⟨[], [], Termin.hop th⟩ : Blob) = [] := by simp [blockDefs]
  obtain ⟨D, hD, hN⟩ := sps_nodup hI A
  have hNh : (regsL ((g0.bo, hed) :: entries hed)).Nodup := (List.nodup_append.mp (List.nodup_append.mp hN).1).1
  obtain ⟨hnah, hdsh⟩ := nodup_regsL_iff.mp hNh
  have hmem : ∀ y, ERegs ((g0.bo, hed) :: entries hed) y →
      GRegL (CGoalL.next laz th) y ∨ (g0.re ≤ y ∧ y < g1.re) := by
    intro y ⟨e, he, hm⟩
    rcases A.memH (mem_regsL.mpr ⟨e, he, hm⟩) with h | h
    · exact Or.inl (gregL_next.mpr (eregs_cons.mp h))
    · exact Or.inr h
  have hnD : ∀ y, ERegs ((g0.bo, hed) :: entries hed) y → y ∉ D := by
    intro y ⟨e, he, hm⟩ hyD
    have h1 : y ∈ regsL ((g0.bo, hed) :: entries hed) ++ regsL ((g0.bo, tel) :: entries tel) :=
      List.mem_append_left _ (mem_regsL.mpr ⟨e, he, hm⟩)
    exact (List.nodup_append.mp hN).2.2 y h1 y hyD rfl
  have hdef : ∀ y, Defd g1.blocks y → Defd g0.blocks y ∨ (GRegL (CGoalL.next laz th) y ∧ y ∈ D) := by
    intro y hy
    rcases sps_defd A.prep hy with h | ⟨x, hx⟩
    · exact Or.inl ((defd_emitted_nil hI.ats hbD).mp h)
    · exact Or.inr ⟨gregL_next.mpr (eregs_cons.mp (spsK_eregs (A.df x y hx))), hD x y hx⟩
  have hblk : ∀ e' ∈ (g0.bo, laz) :: entries laz,
      ∃ b, HoonMap.get (g0.emitted (⟨[], [], Termin.hop th⟩ : Blob)).blocks e'.1 = some b ∧ b.par = [] := by
    intro e' he'
    rw [em_get hd]
    rcases List.mem_cons.mp he' with rfl | he'
    · exact ⟨_, if_pos rfl, rfl⟩
    · obtain ⟨⟨b, hb, hp⟩, -, -⟩ := hent e' (List.mem_cons_of_mem _ he')
      have := hI.lab hb
      rw [if_neg (Nat.ne_of_lt this)]
      exact ⟨b, hb, hp⟩
  refine ⟨hats, fun k b hb => ?_, fun k v hk => ?_, hI.kvan.mono hkp.2.1, hfr, hnah, fun e he => ?_⟩
  · rw [A.prep k] at hb
    obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp hb
    have hPk : RegsIn (· < g1.re) (P k) := (A.rg k).mono fun y h => by
      rcases h with ⟨e, he, hm⟩ | ⟨-, h⟩
      · exact Nat.lt_of_lt_of_le (hER e he y hm).1 hle
      · exact h
    have hb0 : BlobIn (· < g1.re) b0 := by
      rw [em_get hd] at h0
      split at h0
      · cases h0; exact blobIn_nil_fin (jmpIn_nil targs)
      · exact (hI.regs k b0 h0).mono fun _ hx => Nat.lt_of_lt_of_le hx hle
    exact ⟨hb0.1, RegsIn.append hPk hb0.2.1, hb0.2.2⟩
  · rw [hc1] at hk
    obtain ⟨k1, k2, k3, k4, k5⟩ := hI.cond k v hk
    refine ⟨Nat.lt_of_lt_of_le k1 hle, fun hdk => ?_, fun hg => ?_, Nat.lt_of_lt_of_le k4 hle,
      by rw [hc1]; exact k5⟩
    · rcases hdef k hdk with h | ⟨h, -⟩
      · exact k2 h
      · exact k3 h
    · rcases hmem k (eregs_cons.mpr (gregL_next.mp hg)) with h | h
      · exact k3 h
      · omega
  · obtain ⟨e', he', hl⟩ := A.lh e he
    obtain ⟨b, hb, hp⟩ := hblk e' he'
    refine ⟨⟨pre (P e.1) b, by rw [A.prep e.1, ← hl, hb]; rfl, hp⟩, hdsh e he, fun y hy => ?_⟩
    have hy' : ERegs ((g0.bo, hed) :: entries hed) y := ⟨e, he, hy⟩
    refine ⟨?_, fun hdy => ?_⟩
    · rcases hmem y hy' with h | h
      · exact Nat.lt_of_lt_of_le (hI.greg_lt h).1 hle
      · exact h.2
    · rcases hdef y hdy with h | ⟨-, h⟩
      · rcases hmem y hy' with h' | h'
        · exact (hI.greg_lt h').2 h
        · have := defd_lt hI.regs h; omega
      · exact hnD y hy' h

/-- **The two halves are apart.** -/
theorem sps_apart {K : Nat → Nat → Prop} {laz : Lazy S} {th : Jmp} {g0 g1 : Comp.Gen Map} {hed tel : Lazy S}
    {P : Nat → List Pole} (hI : IL K (CGoalL.next laz th) g0)
    (A : SpsI ((g0.bo, laz) :: entries laz) ((g0.bo, hed) :: entries hed) ((g0.bo, tel) :: entries tel) P
      (g0.emitted ⟨[], [], Termin.hop th⟩) g1) :
    TreesApart g0.bo hed g0.bo tel := by
  obtain ⟨D, -, hN⟩ := sps_nodup hI A
  intro e he e' he' y hy hy'
  exact (List.nodup_append.mp (List.nodup_append.mp hN).1).2.2 y (mem_regsL.mpr ⟨e, he, hy⟩) y
    (mem_regsL.mpr ⟨e', he', hy'⟩) rfl

/-- **The liveness clause of the spec.** -/
theorem sps_live {K : Nat → Nat → Prop} {laz : Lazy S} {th : Jmp} {g0 g1 : Comp.Gen Map} {hed tel : Lazy S}
    {P : Nat → List Pole} (hI : IL K (CGoalL.next laz th) g0)
    (A : SpsI ((g0.bo, laz) :: entries laz) ((g0.bo, hed) :: entries hed) ((g0.bo, tel) :: entries tel) P
      (g0.emitted ⟨[], [], Termin.hop th⟩) g1) :
    ∀ r, LiveK (unpM g1) (fun x y => (K x y ∨ lazK g0.bo hed x y) ∨ lazK g0.bo tel x y) g0.bo r →
      GLiveKL (unpM g0) K (CGoalL.next laz th) r := by
  have hd : g0.drop = false := hI.ats.1
  obtain ⟨hth, -, hent⟩ := (hI.goal : GoalL g0 (CGoalL.next laz th))
  obtain ⟨bt, hbt, hpt, targs⟩ := hth
  have hthere : th.there < g0.bo := hI.lab hbt
  have hid : ∀ x, (P x).map (renPole (unproxy g0.cond)) = P x := by
    intro x
    conv => rhs; rw [← List.map_id (P x)]
    apply List.map_congr_left
    intro op hop
    rw [renPole_congr (P := fun y => unproxy g0.cond y = y) (v := id) (fun y h => h) (fun y hy => ?_), renPole_id]
    · rfl
    rcases A.rg x op hop y hy with ⟨e, he, hm⟩ | ⟨h1, -⟩
    · exact hI.unproxy_greg (gregL_next.mpr (eregs_cons.mp ⟨e, he, hm⟩))
    · apply unproxy_none
      cases e : HoonMap.get g0.cond y with
      | none => rfl
      | some v =>
        have := hI.cond_lt y v e
        have h1' : g0.re ≤ y := h1
        omega
  have hP : Prep P (unpM (g0.emitted ⟨[], [], Termin.hop th⟩)) (unpM g1) := by
    intro k
    have := prep_mapVals A.prep (unproxy g0.cond) k
    dsimp only at this
    rw [hid k] at this
    unfold unpM
    rw [A.cond]
    exact this
  have hget : HoonMap.get (unpM (g0.emitted (⟨[], [], Termin.hop th⟩ : Blob))) g0.bo =
      some ⟨[], [], Termin.hop th⟩ := by
    have := unpM_emitted_self (g := g0) hd (⟨[], [], Termin.hop th⟩ : Blob)
    simp only [renBlob, renFin, renJmp_nil _ targs, List.map_nil] at this
    exact this
  have hent' : ∀ e ∈ entries laz, e.1 ≠ g0.bo := fun e he => by
    obtain ⟨⟨b, hb, -⟩, -, -⟩ := hent e (List.mem_cons_of_mem _ he)
    exact Nat.ne_of_lt (hI.lab hb)
  intro r hl
  have h1 := sps_liveK_prep hP (fun k y hr => (A.rd k y hr).elim (fun h => Or.inl (Or.inr h)) Or.inr) hl
  have h2 : LiveK (unpM (g0.emitted (⟨[], [], Termin.hop th⟩ : Blob))) (fun x y => K x y ∨ lazK g0.bo laz x y)
      g0.bo r := h1.mono_r fun x hx => by
    rcases hx with hk | hk
    · exact Or.inl (Or.inl (Or.inl hk))
    · rcases A.cov x r hk with h | h | h
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  have h3 := liveK_hop_root hget targs (fun y => hI.kvan.van g0.bo y (Nat.le_refl _)) hent'
    (Nat.ne_of_lt hthere) h2
  exact (liveK_frameP hI.downU (fun x hx => unpM_emitted_lt hd _ hx) hthere).mp h3

/-- **The spec of `+split`** (`SplitSpecL`, checked at every split of
`PlainN`): proved. -/
theorem splitSpecL : SplitSpecL S Map := by
  intro K laz th g0 g1 hed tel o hI h
  obtain ⟨rfl, hats, hkp, hfr, P, A⟩ := sps_split hI h
  have IH := sps_il hI A hats hkp hfr
  have IT := sps_il hI A.swap hats hkp hfr
  exact ⟨IH, il_addKillsOf IT IH, sps_apart hI A, sps_live hI A⟩

end Raw
end SkaModel
end Formalization
