import lemmas.Ska.RawInvCLFrame

/-!
# The frame of a run with calls: `+split`, `+into`, `+kerf`

README Gaps 14 (b), track D.  The local steps of cons, `%10` and the call
`%2` that take a goal's lazy need apart, with their frame `DF` (no
precondition): they write only fresh registers and registers of the goal's
lazy tree, and the halves they return have only such registers.

* `ERegs`: the registers of the needs of a list of entries; `lReg_mk`,
  `eregs_fork`, `eregs_bond`, `lReg_prune`, `lReg_of_entry`.
* `df_splitLoop` (with `df_splitForks`, `df_splitBonds`), **`frame_splitL`**.
* `df_intoLoop`, `df_intoSure`, `df_intoLoopL` (with `df_intoForks`,
  `df_intoBonds`), **`frame_intoL`**.
* `df_kern`, **`frame_kerf`**.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## Registers of entries -/

/-- The registers of the sure needs of a list of entries. -/
def ERegs (es : List (Nat × Lazy S)) (y : Nat) : Prop := ∃ e ∈ es, NMem e.2.sure.ned y

theorem eregs_append {a b : List (Nat × Lazy S)} {y : Nat} : ERegs (a ++ b) y ↔ ERegs a y ∨ ERegs b y := by
  simp only [ERegs, List.mem_append, or_and_right, exists_or]

theorem eregs_cons {e : Nat × Lazy S} {es : List (Nat × Lazy S)} {y : Nat} :
    ERegs (e :: es) y ↔ NMem e.2.sure.ned y ∨ ERegs es y := by
  simp only [ERegs, List.mem_cons, exists_eq_or_imp]

theorem eregs_nil {y : Nat} : ¬ ERegs ([] : List (Nat × Lazy S)) y := by simp [ERegs]

theorem lReg_mk {s : Sure S} {f : List (ForkE S)} {b : List (Nat × Lazy S)} {y : Nat} :
    LReg (mk s f b) y ↔ NMem s.ned y ∨ ERegs (bondEntries b) y ∨ ERegs (forkEntries f) y := by
  show NMem s.ned y ∨ ERegs (entries (mk s f b)) y ↔ _
  rw [show entries (mk s f b) = bondEntries b ++ forkEntries f by simp only [entries], eregs_append]

theorem eregs_fork {oy on : Nat} {y n : Lazy S} {rest : List (ForkE S)} {z : Nat} :
    ERegs (forkEntries (((oy, y), (on, n)) :: rest)) z ↔ LReg y z ∨ LReg n z ∨ ERegs (forkEntries rest) z := by
  simp only [forkEntries]
  rw [eregs_append, eregs_append, eregs_cons, eregs_cons]
  simp only [LReg, ERegs, or_assoc]

theorem eregs_bond {o : Nat} {l : Lazy S} {rest : List (Nat × Lazy S)} {z : Nat} :
    ERegs (bondEntries ((o, l) :: rest)) z ↔ LReg l z ∨ ERegs (bondEntries rest) z := by
  simp only [bondEntries]
  rw [eregs_append, eregs_cons]
  simp only [LReg, ERegs, or_assoc]

theorem eregs_forkNil {z : Nat} : ¬ ERegs (forkEntries ([] : List (ForkE S))) z := by
  simp [forkEntries, ERegs]

theorem eregs_bondNil {z : Nat} : ¬ ERegs (bondEntries ([] : List (Nat × Lazy S))) z := by
  simp [bondEntries, ERegs]

theorem eregs_forkFilter (p : ForkE S → Bool) :
    ∀ (f : List (ForkE S)) {z : Nat}, ERegs (forkEntries (f.filter p)) z → ERegs (forkEntries f) z
  | [], z, h => by simp at h; exact absurd h eregs_forkNil
  | ((oy, y), (on, n)) :: rest, z, h => by
    rw [List.filter_cons] at h
    split at h
    · rcases eregs_fork.mp h with e | e | e
      · exact eregs_fork.mpr (Or.inl e)
      · exact eregs_fork.mpr (Or.inr (Or.inl e))
      · exact eregs_fork.mpr (Or.inr (Or.inr (eregs_forkFilter p rest e)))
    · exact eregs_fork.mpr (Or.inr (Or.inr (eregs_forkFilter p rest h)))

theorem eregs_bondFilter (p : Nat × Lazy S → Bool) :
    ∀ (b : List (Nat × Lazy S)) {z : Nat}, ERegs (bondEntries (b.filter p)) z → ERegs (bondEntries b) z
  | [], z, h => by simp at h; exact absurd h eregs_bondNil
  | (o, l) :: rest, z, h => by
    rw [List.filter_cons] at h
    split at h
    · rcases eregs_bond.mp h with e | e
      · exact eregs_bond.mpr (Or.inl e)
      · exact eregs_bond.mpr (Or.inr (eregs_bondFilter p rest e))
    · exact eregs_bond.mpr (Or.inr (eregs_bondFilter p rest h))

theorem lReg_prune {l : Lazy S} {y : Nat} (h : LReg (lazyPrune l) y) : LReg l y := by
  rcases l with ⟨s, f, b⟩
  unfold lazyPrune at h
  rcases lReg_mk.mp h with e | e | e
  · exact lReg_mk.mpr (Or.inl e)
  · exact lReg_mk.mpr (Or.inr (Or.inl (eregs_bondFilter _ b e)))
  · exact lReg_mk.mpr (Or.inr (Or.inr (eregs_forkFilter _ f e)))

theorem lReg_of_entry {o : Nat} {l : Lazy S} {e : Nat × Lazy S} (he : e ∈ (o, l) :: entries l) {y : Nat}
    (hy : NMem e.2.sure.ned y) : LReg l y := by
  rcases List.mem_cons.mp he with rfl | he
  · exact Or.inl hy
  · exact Or.inr ⟨e, he, hy⟩

/-! ## `+split` -/

theorem df_splitSure {Q : Nat → Prop} {s : Sure S} {o : Nat} {g g' : Comp.Gen Map} {sh st : Sure S}
    (h : splitSure s o g = some ((sh, st), g')) (hs : NA Q s.ned) (hm : Ple Q g.re) :
    DF Q g g' ∧ NA Q sh.ned ∧ NA Q st.ned := by
  unfold splitSure at h
  obtain ⟨⟨lh, lt⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨⟨nh, nt⟩, g2⟩, h2, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
  obtain ⟨k, n1, n2⟩ := keepsA_splitNeed (P := Q) hs hm h2
  exact ⟨df_wroteIn k.le ((kc_splitNeed _ _).keep _ _ _ h2) ((wr_splitNeed h2).mono hs), n1, n2⟩

mutual
theorem df_splitLoop {Q : Nat → Prop} : ∀ (l : Lazy S) (o : Nat) (g g' : Comp.Gen Map) (x : Lazy S × Lazy S),
    splitLoop l o g = some (x, g') → (∀ y, LReg l y → Q y) → Ple Q g.re →
    DF Q g g' ∧ (∀ y, LReg x.1 y → Q y) ∧ (∀ y, LReg x.2 y → Q y)
  | mk s f b, o, g, g', x, h, hl, hm => by
    rw [splitLoop] at h
    obtain ⟨⟨sh, st⟩, g1, h1, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨d1, n1, n2⟩ := df_splitSure h1 (fun y hy => hl y (lReg_mk.mpr (Or.inl hy))) hm
    split at h
    · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨d1, fun y hy => n1 y (lReg_ofSure.mp hy), fun y hy => n2 y (lReg_ofSure.mp hy)⟩
    · obtain ⟨⟨fh, ft⟩, g2, h2, h⟩ := bind_some h
      dsimp only at h
      obtain ⟨d2, f1, f2⟩ := df_splitForks f g1 g2 _ h2
        (fun y hy => hl y (lReg_mk.mpr (Or.inr (Or.inr hy)))) (ple_trans hm d1.1)
      obtain ⟨⟨bh, bt⟩, g3, h3, h⟩ := bind_some h
      dsimp only at h
      obtain ⟨d3, b1, b2⟩ := df_splitBonds b g2 g3 _ h3
        (fun y hy => hl y (lReg_mk.mpr (Or.inr (Or.inl hy)))) (ple_trans hm (Nat.le_trans d1.1 d2.1))
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨d1.trans (d2.trans d3), fun y hy => ?_, fun y hy => ?_⟩
      · rcases lReg_mk.mp (lReg_prune hy) with e | e | e
        · exact n1 y e
        · exact b1 y e
        · exact f1 y e
      · rcases lReg_mk.mp (lReg_prune hy) with e | e | e
        · exact n2 y e
        · exact b2 y e
        · exact f2 y e

theorem df_splitForks {Q : Nat → Prop} : ∀ (f : List (ForkE S)) (g g' : Comp.Gen Map)
    (x : List (ForkE S) × List (ForkE S)),
    splitForks f g = some (x, g') → (∀ y, ERegs (forkEntries f) y → Q y) → Ple Q g.re →
    DF Q g g' ∧ (∀ y, ERegs (forkEntries x.1) y → Q y) ∧ (∀ y, ERegs (forkEntries x.2) y → Q y)
  | [], g, g', x, h, _, _ => by
    rw [splitForks] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨DF.refl _ _, fun y hy => absurd hy eregs_forkNil, fun y hy => absurd hy eregs_forkNil⟩
  | ((oy, y), (on, n)) :: rest, g, g', x, h, hl, hm => by
    rw [splitForks] at h
    obtain ⟨⟨yh, yt⟩, g1, h1, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨d1, y1, y2⟩ := df_splitLoop y oy g g1 _ h1 (fun z hz => hl z (eregs_fork.mpr (Or.inl hz))) hm
    obtain ⟨⟨nh, nt⟩, g2, h2, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨d2, m1, m2⟩ := df_splitLoop n on g1 g2 _ h2
      (fun z hz => hl z (eregs_fork.mpr (Or.inr (Or.inl hz)))) (ple_trans hm d1.1)
    obtain ⟨⟨rh, rt⟩, g3, h3, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨d3, r1, r2⟩ := df_splitForks rest g2 g3 _ h3
      (fun z hz => hl z (eregs_fork.mpr (Or.inr (Or.inr hz)))) (ple_trans hm (Nat.le_trans d1.1 d2.1))
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨d1.trans (d2.trans d3), fun z hz => ?_, fun z hz => ?_⟩
    · rcases eregs_fork.mp hz with e | e | e
      · exact y1 z e
      · exact m1 z e
      · exact r1 z e
    · rcases eregs_fork.mp hz with e | e | e
      · exact y2 z e
      · exact m2 z e
      · exact r2 z e

theorem df_splitBonds {Q : Nat → Prop} : ∀ (b : List (Nat × Lazy S)) (g g' : Comp.Gen Map)
    (x : List (Nat × Lazy S) × List (Nat × Lazy S)),
    splitBonds b g = some (x, g') → (∀ y, ERegs (bondEntries b) y → Q y) → Ple Q g.re →
    DF Q g g' ∧ (∀ y, ERegs (bondEntries x.1) y → Q y) ∧ (∀ y, ERegs (bondEntries x.2) y → Q y)
  | [], g, g', x, h, _, _ => by
    rw [splitBonds] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨DF.refl _ _, fun y hy => absurd hy eregs_bondNil, fun y hy => absurd hy eregs_bondNil⟩
  | (o, l) :: rest, g, g', x, h, hl, hm => by
    rw [splitBonds] at h
    obtain ⟨⟨lh, lt⟩, g1, h1, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨d1, l1, l2⟩ := df_splitLoop l o g g1 _ h1 (fun z hz => hl z (eregs_bond.mpr (Or.inl hz))) hm
    obtain ⟨⟨rh, rt⟩, g2, h2, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨d2, r1, r2⟩ := df_splitBonds rest g1 g2 _ h2
      (fun z hz => hl z (eregs_bond.mpr (Or.inr hz))) (ple_trans hm d1.1)
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨d1.trans d2, fun z hz => ?_, fun z hz => ?_⟩
    · rcases eregs_bond.mp hz with e | e
      · exact l1 z e
      · exact r1 z e
    · rcases eregs_bond.mp hz with e | e
      · exact l2 z e
      · exact r2 z e
end

/-- **`+split` has the frame of its goal's lazy tree**, and so do its two
halves. -/
theorem frame_splitL {nex : NextL S} {g g' : Comp.Gen Map} {hed tel : Lazy S} {o : Nat}
    (h : splitL nex g = some ((hed, tel, o), g')) :
    DF (fun y => g.re ≤ y ∨ LReg nex.laz y) g g' ∧ (∀ y, LReg hed y → LReg nex.laz y ∨ g.re ≤ y) ∧
      (∀ y, LReg tel y → LReg nex.laz y ∨ g.re ≤ y) := by
  unfold splitL at h
  obtain ⟨o1, g1, h1, h⟩ := bind_some h
  obtain ⟨d1, -, e1⟩ := df_emit (blobWr_nil (fun y => g.re ≤ y ∨ LReg nex.laz y) _) h1
  obtain ⟨⟨hh, tt⟩, g2, h2, h⟩ := bind_some h
  dsimp only at h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
  obtain ⟨d2, n1, n2⟩ := df_splitLoop (Q := fun y => g.re ≤ y ∨ LReg nex.laz y) nex.laz o1 g1 g2 _ h2 (fun y hy => Or.inr hy)
    (fun y hy => Or.inl (by omega))
  exact ⟨d1.trans d2, fun y hy => (n1 y hy).symm, fun y hy => (n2 y hy).symm⟩

/-! ## `+into` -/

theorem df_intoLoop {Q : Nat → Prop} {o : Nat} : ∀ (axe : Nat) (ned : Need) (tack : List (Bool × Need))
    (ops : List Pole) (g g' : Comp.Gen Map) (x : Need × Need), intoLoop o axe ned tack ops g = some (x, g') →
    NA Q ned → (∀ e ∈ tack, NA Q e.2) → OpsWr Q ops → Ple Q g.re →
    DF Q g g' ∧ NA Q x.1 ∧ NA Q x.2 := by
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
  intro ned tack ops g g' x h hc ht hA hm
  rw [intoLoop] at h
  by_cases h1 : axe ≤ 1
  · rw [dif_pos h1] at h
    obtain ⟨u, g1, h2, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨df_addOps hA h2, hc, na_rollTack tack Need.none (na_none _) ht⟩
  rw [dif_neg h1] at h
  have lt := mas_lt axe (by omega)
  cases ned with
  | none =>
    exact ih _ lt _ _ _ _ _ _ h (na_none _) (by
      intro e he; rcases List.mem_cons.mp he with e' | he
      · rw [e']; exact na_none _
      · exact ht e he) hA hm
  | this r =>
    simp only at h
    obtain ⟨l, g1, h1', h⟩ := bind_some h
    obtain ⟨r', g2, h2, h⟩ := bind_some h
    obtain ⟨d1, e1, q1⟩ := df_re (Q := Q) h1'
    obtain ⟨d2, e2, q2⟩ := df_re (Q := Q) h2
    have hl : Q l := hm _ (by omega)
    have hr' : Q r' := hm _ (by omega)
    obtain ⟨k, n1, n2⟩ := ih _ lt _ _ _ _ _ _ h (na_this (by split <;> assumption)) (by
      intro e he; rcases List.mem_cons.mp he with e' | he
      · rw [e']; exact na_this (by split <;> assumption)
      · exact ht e he)
      (opsWr_cons (fun z hz => by
        simp only [poleWr, List.mem_cons, List.mem_nil_iff, or_false] at hz; rw [hz]; exact hc r rfl) hA)
      (fun z hz => hm z (by omega))
    exact ⟨d1.trans (d2.trans k), n1, n2⟩
  | pair p q =>
    simp only at h
    exact ih _ lt _ _ _ _ _ _ h
      (by split <;> first | exact fun y hy => hc y (Or.inl hy) | exact fun y hy => hc y (Or.inr hy))
      (by
        intro e he; rcases List.mem_cons.mp he with e' | he
        · rw [e']; show NA _ (if _ then _ else _); split
          · exact fun y hy => hc y (Or.inr hy)
          · exact fun y hy => hc y (Or.inl hy)
        · exact ht e he) hA hm
  | both r hh t =>
    simp only at h
    obtain ⟨⟨lr, ln⟩, g1, h1', h⟩ := bind_some h
    obtain ⟨⟨rr, rn⟩, g2, h2, h⟩ := bind_some h
    obtain ⟨k1, nl, -⟩ := keepsA_must (P := Q) (fun y hy => hc y (Or.inr (Or.inl hy))) hm h1'
    obtain ⟨k2, nr, -⟩ := keepsA_must (P := Q) (fun y hy => hc y (Or.inr (Or.inr hy))) (ple_trans hm k1.le) h2
    have e1 := (must_spec h1').1
    have e2 := (must_spec h2).1
    obtain ⟨k, n1, n2⟩ := ih _ lt _ _ _ _ _ _ h (by split; exact nl; exact nr) (by
      intro e he; rcases List.mem_cons.mp he with e' | he
      · rw [e']; show NA _ (if _ then _ else _); split
        · exact nr
        · exact nl
      · exact ht e he)
      (opsWr_cons (fun z hz => by
        simp only [poleWr, List.mem_cons, List.mem_nil_iff, or_false] at hz; rw [hz]; exact hc r (Or.inl rfl)) hA)
      (ple_trans hm (Nat.le_trans k1.le k2.le))
    exact ⟨(df_gen e1 k1.le).trans ((df_gen e2 k2.le).trans k), n1, n2⟩

theorem df_intoSure {Q : Nat → Prop} {axe : Nat} {s : Sure S} {o : Nat} {g g' : Comp.Gen Map} {sd sr : Sure S}
    (h : intoSure axe s o g = some ((sd, sr), g')) (hs : NA Q s.ned) (hm : Ple Q g.re) :
    DF Q g g' ∧ NA Q sd.ned ∧ NA Q sr.ned := by
  unfold intoSure at h
  obtain ⟨⟨ld, lr⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨⟨nd, nr⟩, g2⟩, h2, e⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at e
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := e
  unfold intoNeed at h2
  by_cases a0 : axe = 0
  · rw [if_pos a0] at h2; cases h2
  rw [if_neg a0] at h2
  by_cases a1 : axe = 1
  · rw [if_pos a1] at h2
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
    exact ⟨DF.refl _ _, hs, na_none _⟩
  rw [if_neg a1] at h2
  exact df_intoLoop axe _ [] [] g g2 _ h2 hs (fun e he => absurd he List.not_mem_nil) (opsWr_nil Q) hm

mutual
theorem df_intoLoopL {Q : Nat → Prop} (axe : Nat) : ∀ (l : Lazy S) (o : Nat) (g g' : Comp.Gen Map)
    (x : Lazy S × Lazy S),
    intoLoopL axe l o g = some (x, g') → (∀ y, LReg l y → Q y) → Ple Q g.re →
    DF Q g g' ∧ (∀ y, LReg x.1 y → Q y) ∧ (∀ y, LReg x.2 y → Q y)
  | mk s f b, o, g, g', x, h, hl, hm => by
    rw [intoLoopL] at h
    obtain ⟨⟨sh, st⟩, g1, h1, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨d1, n1, n2⟩ := df_intoSure h1 (fun y hy => hl y (lReg_mk.mpr (Or.inl hy))) hm
    split at h
    · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨d1, fun y hy => n1 y (lReg_ofSure.mp hy), fun y hy => n2 y (lReg_ofSure.mp hy)⟩
    · obtain ⟨⟨fh, ft⟩, g2, h2, h⟩ := bind_some h
      dsimp only at h
      obtain ⟨d2, f1, f2⟩ := df_intoForks axe f g1 g2 _ h2
        (fun y hy => hl y (lReg_mk.mpr (Or.inr (Or.inr hy)))) (ple_trans hm d1.1)
      obtain ⟨⟨bh, bt⟩, g3, h3, h⟩ := bind_some h
      dsimp only at h
      obtain ⟨d3, b1, b2⟩ := df_intoBonds axe b g2 g3 _ h3
        (fun y hy => hl y (lReg_mk.mpr (Or.inr (Or.inl hy)))) (ple_trans hm (Nat.le_trans d1.1 d2.1))
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨d1.trans (d2.trans d3), fun y hy => ?_, fun y hy => ?_⟩
      · rcases lReg_mk.mp (lReg_prune hy) with e | e | e
        · exact n1 y e
        · exact b1 y e
        · exact f1 y e
      · rcases lReg_mk.mp (lReg_prune hy) with e | e | e
        · exact n2 y e
        · exact b2 y e
        · exact f2 y e

theorem df_intoForks {Q : Nat → Prop} (axe : Nat) : ∀ (f : List (ForkE S)) (g g' : Comp.Gen Map)
    (x : List (ForkE S) × List (ForkE S)),
    intoForks axe f g = some (x, g') → (∀ y, ERegs (forkEntries f) y → Q y) → Ple Q g.re →
    DF Q g g' ∧ (∀ y, ERegs (forkEntries x.1) y → Q y) ∧ (∀ y, ERegs (forkEntries x.2) y → Q y)
  | [], g, g', x, h, _, _ => by
    rw [intoForks] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨DF.refl _ _, fun y hy => absurd hy eregs_forkNil, fun y hy => absurd hy eregs_forkNil⟩
  | ((oy, y), (on, n)) :: rest, g, g', x, h, hl, hm => by
    rw [intoForks] at h
    obtain ⟨⟨yh, yt⟩, g1, h1, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨d1, y1, y2⟩ := df_intoLoopL axe y oy g g1 _ h1 (fun z hz => hl z (eregs_fork.mpr (Or.inl hz))) hm
    obtain ⟨⟨nh, nt⟩, g2, h2, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨d2, m1, m2⟩ := df_intoLoopL axe n on g1 g2 _ h2
      (fun z hz => hl z (eregs_fork.mpr (Or.inr (Or.inl hz)))) (ple_trans hm d1.1)
    obtain ⟨⟨rh, rt⟩, g3, h3, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨d3, r1, r2⟩ := df_intoForks axe rest g2 g3 _ h3
      (fun z hz => hl z (eregs_fork.mpr (Or.inr (Or.inr hz)))) (ple_trans hm (Nat.le_trans d1.1 d2.1))
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨d1.trans (d2.trans d3), fun z hz => ?_, fun z hz => ?_⟩
    · rcases eregs_fork.mp hz with e | e | e
      · exact y1 z e
      · exact m1 z e
      · exact r1 z e
    · rcases eregs_fork.mp hz with e | e | e
      · exact y2 z e
      · exact m2 z e
      · exact r2 z e

theorem df_intoBonds {Q : Nat → Prop} (axe : Nat) : ∀ (b : List (Nat × Lazy S)) (g g' : Comp.Gen Map)
    (x : List (Nat × Lazy S) × List (Nat × Lazy S)),
    intoBonds axe b g = some (x, g') → (∀ y, ERegs (bondEntries b) y → Q y) → Ple Q g.re →
    DF Q g g' ∧ (∀ y, ERegs (bondEntries x.1) y → Q y) ∧ (∀ y, ERegs (bondEntries x.2) y → Q y)
  | [], g, g', x, h, _, _ => by
    rw [intoBonds] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨DF.refl _ _, fun y hy => absurd hy eregs_bondNil, fun y hy => absurd hy eregs_bondNil⟩
  | (o, l) :: rest, g, g', x, h, hl, hm => by
    rw [intoBonds] at h
    obtain ⟨⟨lh, lt⟩, g1, h1, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨d1, l1, l2⟩ := df_intoLoopL axe l o g g1 _ h1 (fun z hz => hl z (eregs_bond.mpr (Or.inl hz))) hm
    obtain ⟨⟨rh, rt⟩, g2, h2, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨d2, r1, r2⟩ := df_intoBonds axe rest g1 g2 _ h2
      (fun z hz => hl z (eregs_bond.mpr (Or.inr hz))) (ple_trans hm d1.1)
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨d1.trans d2, fun z hz => ?_, fun z hz => ?_⟩
    · rcases eregs_bond.mp hz with e | e
      · exact l1 z e
      · exact r1 z e
    · rcases eregs_bond.mp hz with e | e
      · exact l2 z e
      · exact r2 z e
end

/-- **`+into` has the frame of its goal's lazy tree**, and so do the donor
and the recipient. -/
theorem frame_intoL {nex : NextL S} {axe : Nat} {g g' : Comp.Gen Map} {d r : Lazy S} {o : Nat}
    (h : intoL nex axe g = some ((d, r, o), g')) :
    DF (fun y => g.re ≤ y ∨ LReg nex.laz y) g g' ∧ (∀ y, LReg d y → LReg nex.laz y ∨ g.re ≤ y) ∧
      (∀ y, LReg r y → LReg nex.laz y ∨ g.re ≤ y) := by
  unfold intoL at h
  obtain ⟨o1, g1, h1, h⟩ := bind_some h
  obtain ⟨d1, -, e1⟩ := df_emit (blobWr_nil (fun y => g.re ≤ y ∨ LReg nex.laz y) _) h1
  obtain ⟨⟨dd, rr⟩, g2, h2, h⟩ := bind_some h
  dsimp only at h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
  obtain ⟨d2, n1, n2⟩ := df_intoLoopL (Q := fun y => g.re ≤ y ∨ LReg nex.laz y) axe nex.laz o1 g1 g2 _ h2 (fun y hy => Or.inr hy)
    (fun y hy => Or.inl (by omega))
  exact ⟨d1.trans d2, fun y hy => (n1 y hy).symm, fun y hy => (n2 y hy).symm⟩

/-! ## `+kerf` -/

theorem poleWr_regs {p : Pole} {x : Nat} (h : x ∈ poleWr p) : x ∈ Comp.poleRegs p := by
  cases p <;> simp_all [poleWr, Comp.poleRegs]

theorem opsWr_of_regsIn {Q : Nat → Prop} {A : List Pole} (h : Comp.RegsIn Q A) : OpsWr Q A :=
  fun p hp x hx => h p hp x (poleWr_regs hx)

/-- **`+kern` writes only fresh registers and registers of its lazy tree.** -/
theorem df_kern {Q : Nat → Prop} {o : Nat} {laz : Lazy S} {g g' : Comp.Gen Map} {r : Nat}
    (h : kern o laz g = some (r, g')) (hl : ∀ y, LReg laz y → Q y) (hm : Ple Q g.re) :
    DF Q g g' ∧ r = g.re := by
  unfold kern at h
  obtain ⟨r0, g1, h1, h⟩ := bind_some h
  obtain ⟨d1, e1, q1⟩ := df_re (Q := Q) h1
  obtain ⟨g2, g3, h2, h⟩ := bind_some h
  cases h2
  split at h
  · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨d1, e1⟩
  obtain ⟨u, g4, h4, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨d1.trans (df_walkLazy (fun e he a b ha hb => ?_) h4), e1⟩
  have hra : g1.re ≤ a.re := ha.1
  obtain ⟨ned, a1, ha1, hb⟩ := bind_some hb
  obtain ⟨da1, hn⟩ := df_sureRequireLook (Q := Q) ha1
  split at hb
  · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨-, rfl⟩ := hb
    exact da1
  obtain ⟨src, a2, ha2, hb⟩ := bind_some hb
  have hs : DF Q a1 a2 ∧ Q src := by
    split at ha2
    · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at ha2
      obtain ⟨rfl, rfl⟩ := ha2
      exact ⟨DF.refl _ _, hm _ (by omega)⟩
    · obtain ⟨dp, ep, -⟩ := df_proxy (Q := Q) ha2
      have := da1.1
      exact ⟨dp, hm _ (by omega)⟩
  split at hb
  · cases hb
  obtain ⟨ops, a3, ha3, hb⟩ := bind_some hb
  have K := kernLoop_spec ned src [] a2 a3 ops ha3
  obtain ⟨A, -, KO⟩ := K
  obtain ⟨n, e3⟩ := KO.gen
  have hR := kernLoop_regs Q ned src [] a2 a3 ops ha3 hs.2
    (fun z hz => by
      rcases hn z hz with h' | h'
      · exact hl z (lReg_of_entry he h')
      · exact hm z (by have := da1.1; omega))
    (fun z hz => hm z (by have := da1.1; have := hs.1.1; omega)) (Comp.RegsIn.nil Q)
  have d3 : DF Q a2 a3 := df_gen (by rw [e3]) KO.le
  exact da1.trans (hs.1.trans (d3.trans (df_addOps (opsWr_of_regsIn hR) hb)))

/-- **`+kerf` has the frame of its lazy tree**, and its register is fresh. -/
theorem frame_kerf {nex : NextL S} {g g' : Comp.Gen Map} {out pro : Nat}
    (h : kerf nex g = some ((out, pro), g')) :
    DF (fun y => g.re ≤ y ∨ LReg nex.laz y) g g' ∧ (g.re ≤ pro ∨ LReg nex.laz pro) := by
  unfold kerf at h
  obtain ⟨o, g1, h1, h⟩ := bind_some h
  obtain ⟨d1, -, e1⟩ := df_emit (blobWr_nil (fun y => g.re ≤ y ∨ LReg nex.laz y) _) h1
  obtain ⟨r, g2, h2, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  obtain ⟨d2, hr⟩ := df_kern (Q := fun y => g.re ≤ y ∨ LReg nex.laz y) h2 (fun y hy => Or.inr hy)
    (fun y hy => Or.inl (by omega))
  exact ⟨d1.trans d2, Or.inl (by omega)⟩

end Raw
end SkaModel
end Formalization
