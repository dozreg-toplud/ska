import lemmas.Ska.RawInvCLFrame

/-!
# The frame of a run with calls: `+past`, `+copy` and the chain of `%5`, cons, `%10`, `%2`

README Gaps 14 (b), track D.  The frames (`DF` of `RawInvCLFrame.lean`) of
the steps that close the binary arms.

* `lReg_iff_parts`: the registers of a lazy tree are its sure need's and
  those of its bonds' and forks' trees (`fc_ex_bondEntries`,
  `fc_ex_forkEntries`).
* **`frame_pastL`**: `+past` writes nothing, and the registers of its result
  are its input's.
* `fc_copyNeed_wr`: the ops of `+copy-need-make-ops` write registers of the
  two needs; `fc_index_mem`: what `index` finds is in the list.
* `frame_copyLazyL`, `frame_mergeForks`, `frame_mergeBonds` (mutual): the
  merge writes registers of the two trees or fresh ones, and its result's
  registers are the two trees' or fresh; **`frame_copyL`**.
* **`frame_chain`**: run `q`, `+past`, run `p`, `+copy`: the shared tail of
  `%5`, cons, `%10` and `%2`, with any footprint `G` that holds the fresh
  registers and those of the two goals.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The registers of a lazy tree by parts -/

theorem fc_ex_append {α : Type} {P : α → Prop} {a b : List α} :
    (∃ e ∈ a ++ b, P e) ↔ (∃ e ∈ a, P e) ∨ ∃ e ∈ b, P e := by
  constructor
  · rintro ⟨e, he, h⟩
    rcases List.mem_append.mp he with he | he
    · exact Or.inl ⟨e, he, h⟩
    · exact Or.inr ⟨e, he, h⟩
  · rintro (⟨e, he, h⟩ | ⟨e, he, h⟩)
    · exact ⟨e, List.mem_append_left _ he, h⟩
    · exact ⟨e, List.mem_append_right _ he, h⟩

theorem fc_ex_cons {α : Type} {P : α → Prop} {a : α} {l : List α} :
    (∃ e ∈ a :: l, P e) ↔ P a ∨ ∃ e ∈ l, P e := by
  constructor
  · rintro ⟨e, he, h⟩
    rcases List.mem_cons.mp he with rfl | he
    · exact Or.inl h
    · exact Or.inr ⟨e, he, h⟩
  · rintro (h | ⟨e, he, h⟩)
    · exact ⟨a, List.mem_cons_self, h⟩
    · exact ⟨e, List.mem_cons_of_mem _ he, h⟩

theorem fc_ex_cons_entries {o : Nat} {l : Lazy S} {y : Nat} :
    (∃ e ∈ (o, l) :: entries l, NMem e.2.sure.ned y) ↔ LReg l y := by
  rw [fc_ex_cons]; exact Iff.rfl

theorem fc_ex_bondEntries : ∀ (b : List (Nat × Lazy S)) (y : Nat),
    (∃ e ∈ bondEntries b, NMem e.2.sure.ned y) ↔ ∃ e ∈ b, LReg e.2 y
  | [], y => by
    simp only [bondEntries]
    exact ⟨fun ⟨_, h, _⟩ => absurd h List.not_mem_nil, fun ⟨_, h, _⟩ => absurd h List.not_mem_nil⟩
  | (o, l) :: rest, y => by
    simp only [bondEntries]
    rw [fc_ex_append, fc_ex_cons_entries, fc_ex_bondEntries rest y, fc_ex_cons]

theorem fc_ex_forkEntries : ∀ (f : List ((Nat × Lazy S) × (Nat × Lazy S))) (y : Nat),
    (∃ e ∈ forkEntries f, NMem e.2.sure.ned y) ↔ ∃ e ∈ f, LReg e.1.2 y ∨ LReg e.2.2 y
  | [], y => by
    simp only [forkEntries]
    exact ⟨fun ⟨_, h, _⟩ => absurd h List.not_mem_nil, fun ⟨_, h, _⟩ => absurd h List.not_mem_nil⟩
  | ((oy, a), (on, n)) :: rest, y => by
    simp only [forkEntries]
    rw [fc_ex_append, fc_ex_append, fc_ex_cons_entries, fc_ex_cons_entries, fc_ex_forkEntries rest y, fc_ex_cons]

/-- **The registers of a lazy tree, by parts.** -/
theorem lReg_iff_parts {l : Lazy S} {y : Nat} :
    LReg l y ↔ NMem l.sure.ned y ∨ (∃ e ∈ l.bond, LReg e.2 y) ∨ ∃ e ∈ l.fork, LReg e.1.2 y ∨ LReg e.2.2 y := by
  cases l with
  | mk s f b =>
    show (NMem s.ned y ∨ ∃ e ∈ entries (mk s f b), NMem e.2.sure.ned y) ↔
      NMem s.ned y ∨ (∃ e ∈ b, LReg e.2 y) ∨ ∃ e ∈ f, LReg e.1.2 y ∨ LReg e.2.2 y
    have e : entries (mk s f b) = bondEntries b ++ forkEntries f := by simp only [entries]
    rw [e, fc_ex_append, fc_ex_bondEntries, fc_ex_forkEntries]

/-! ## `+past` -/

/-- **`+past` writes nothing**, and its result's registers are its input's. -/
theorem frame_pastL {cod : Bell → Option Bool} {nex nex' : NextL S} {nom : Nomm} {region : List Nat}
    {g g' : Comp.Gen Map} (h : pastL cod nex nom region g = some (nex', g')) :
    DF (fun _ => False) g g' ∧ ∀ y, LReg nex'.laz y → LReg nex.laz y := by
  unfold pastL at h
  split at h
  · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨DF.refl _ _, fun y hy => hy⟩
  rcases hh : hinted cod nom with _ | ⟨_ | _⟩
  · rw [hh] at h; cases h
  · rw [hh] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨DF.refl _ _, fun y hy => hy⟩
  rw [hh] at h
  dsimp only at h
  obtain ⟨o, ga, ha, h⟩ := bind_some h
  obtain ⟨d1, -, -⟩ := df_emit (blobWr_nil (fun _ => False) _) ha
  obtain ⟨u, gb, hb, h⟩ := bind_some h
  have d2 : DF (fun _ => False) ga gb := df_setTag hb
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨d1.trans d2, fun y hy => ?_⟩
  rcases lReg_iff_parts.mp hy with hy | ⟨e, he, hy⟩ | ⟨e, he, -⟩
  · exact absurd hy (by simp [Sure.bunt, NMem])
  · rcases List.mem_cons.mp he with rfl | he
    · rcases lReg_iff_parts.mp hy with hy | ⟨e', he', -⟩ | ⟨e', he', hy⟩
      · exact lReg_iff_parts.mpr (Or.inl hy)
      · exact absurd he' List.not_mem_nil
      · exact lReg_iff_parts.mpr (Or.inr (Or.inr ⟨e', he', hy⟩))
    · exact lReg_iff_parts.mpr (Or.inr (Or.inl ⟨e, he, hy⟩))
  · exact absurd he List.not_mem_nil

/-! ## `+copy-need-make-ops` and `index` -/

theorem fc_mov_wr {Q : Nat → Prop} {s d : Nat} (h : Q d) : ∀ x ∈ poleWr (Pole.mov s d), Q x := fun x hx => by
  simp only [poleWr, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rw [hx]; exact h

/-- **The ops of `+copy-need-make-ops` write registers of the two needs.** -/
theorem fc_copyNeed_wr {Q : Nat → Prop} : ∀ (a b : Need) (ops : List Pole) (g g' : Comp.Gen Map)
    (x : Need × List Pole), copyNeed a b ops g = some (x, g') → (∀ y, NMem a y → Q y) →
    (∀ y, NMem b y → Q y) → OpsWr Q ops → OpsWr Q x.2 := by
  intro a
  induction a with
  | none =>
    intro b ops g g' x h _ _ hw
    simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact hw
  | this rl =>
    intro b ops g g' x h ha hb hw
    cases b with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact hw
    | this rr =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact opsWr_cons (fc_mov_wr (hb rr rfl)) hw
    | both xr hr tr =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact opsWr_cons (fc_mov_wr (ha rl rfl)) hw
    | pair p q =>
      simp only [copyNeed, bind_apply, re_apply, Option.bind_some, pure_apply, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact opsWr_cons (fc_mov_wr (ha rl rfl)) hw
  | pair pl ql ihp ihq =>
    intro b ops g g' x h ha hb hw
    cases b with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact hw
    | this rr =>
      simp only [copyNeed, bind_apply, re_apply, Option.bind_some, pure_apply, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact opsWr_cons (fc_mov_wr (hb rr rfl)) hw
    | pair pr qr =>
      simp only [copyNeed] at h
      obtain ⟨⟨a1, o1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨a2, o2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have w1 := ihp _ _ _ _ _ h1 (fun y hy => ha y (Or.inl hy)) (fun y hy => hb y (Or.inl hy)) hw
      exact ihq _ _ _ _ (a2, o2) h2 (fun y hy => ha y (Or.inr hy)) (fun y hy => hb y (Or.inr hy)) w1
    | both xr hr tr =>
      simp only [copyNeed] at h
      obtain ⟨⟨a1, o1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨a2, o2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have w1 := ihp _ _ _ _ _ h1 (fun y hy => ha y (Or.inl hy)) (fun y hy => hb y (Or.inr (Or.inl hy))) hw
      exact ihq _ _ _ _ (a2, o2) h2 (fun y hy => ha y (Or.inr hy)) (fun y hy => hb y (Or.inr (Or.inr hy))) w1
  | both rl hl tl ihh iht =>
    intro b ops g g' x h ha hb hw
    cases b with
    | none =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact hw
    | this rr =>
      simp only [copyNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact opsWr_cons (fc_mov_wr (hb rr rfl)) hw
    | both xr hr tr =>
      simp only [copyNeed] at h
      obtain ⟨⟨a1, o1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨a2, o2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have w1 := ihh _ _ _ _ _ h1 (fun y hy => ha y (Or.inr (Or.inl hy))) (fun y hy => hb y (Or.inr (Or.inl hy)))
        (opsWr_cons (fc_mov_wr (ha rl (Or.inl rfl))) hw)
      exact iht _ _ _ _ (a2, o2) h2 (fun y hy => ha y (Or.inr (Or.inr hy))) (fun y hy => hb y (Or.inr (Or.inr hy))) w1
    | pair p q =>
      simp only [copyNeed] at h
      obtain ⟨xr, g0', h0, h⟩ := bind_some h
      obtain ⟨⟨a1, o1⟩, g1, h1, h⟩ := bind_some h
      obtain ⟨⟨a2, o2⟩, g2, h2, h⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have w1 := ihh _ _ _ _ _ h1 (fun y hy => ha y (Or.inr (Or.inl hy))) (fun y hy => hb y (Or.inl hy))
        (opsWr_cons (fc_mov_wr (ha rl (Or.inl rfl))) hw)
      exact iht _ _ _ _ (a2, o2) h2 (fun y hy => ha y (Or.inr (Or.inr hy))) (fun y hy => hb y (Or.inr hy)) w1

theorem fc_foldl_put_mem {α : Type} (key : α → Nat) (k : Nat) :
    ∀ (l : List α) (m : Map α) (e : α),
      HoonMap.get (l.foldl (fun m e => HoonMap.put m (key e) e) m) k = some e → e ∈ l ∨ HoonMap.get m k = some e
  | [], _, _, h => Or.inr h
  | x :: l, m, e, h => by
    simp only [List.foldl_cons] at h
    rcases fc_foldl_put_mem key k l _ e h with h' | h'
    · exact Or.inl (List.mem_cons_of_mem _ h')
    · by_cases hk : k = key x
      · subst hk
        simp only [HoonMap.get_put, if_true, Option.some.injEq] at h'
        subst h'
        exact Or.inl List.mem_cons_self
      · simp only [HoonMap.get_put, hk, if_false] at h'
        exact Or.inr h'

/-- **What `index` finds is in the list.** -/
theorem fc_index_mem {α : Type} (key : α → Nat) {l : List α} {k : Nat} {e : α}
    (h : HoonMap.get (index (Map := Map) key l) k = some e) : e ∈ l := by
  unfold index at h
  rcases fc_foldl_put_mem key k l _ e h with h | h
  · exact h
  · rw [HoonMap.get_empty] at h; cases h

/-! ## `+copy-lazy` -/

theorem DF.up {P : Nat → Prop} {g a b : Comp.Gen Map} (h : DF (fun y => a.re ≤ y ∨ P y) a b) (hr : g.re ≤ a.re) :
    DF (fun y => g.re ≤ y ∨ P y) a b :=
  h.mono fun _ hy => hy.imp_left (Nat.le_trans hr)

mutual
/-- **The frame of the merge of two lazy trees.** -/
theorem frame_copyLazyL (o : Nat) : ∀ (a b : Lazy S) (P : Nat → Prop) (g g' : Comp.Gen Map) (c : Lazy S),
    copyLazyL o a b g = some (c, g') → (∀ y, LReg a y → P y) → (∀ y, LReg b y → P y) →
    DF (fun y => g.re ≤ y ∨ P y) g g' ∧ ∀ y, LReg c y → P y ∨ g.re ≤ y
  | mk s1 f1 b1, second, P, g, g', c, h, ha, hb => by
    rw [copyLazyL] at h
    obtain ⟨⟨ned, ops⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨A, -, C⟩ := copyNeed_spec _ _ _ _ _ _ h1
    have wA : OpsWr P ops := fc_copyNeed_wr _ _ _ _ _ _ h1
      (fun y hy => ha y (lReg_iff_parts.mpr (Or.inl hy))) (fun y hy => hb y (lReg_iff_parts.mpr (Or.inl hy)))
      (opsWr_nil _)
    have d1 : DF (fun y => g.re ≤ y ∨ P y) g g1 := df_gen C.gen C.le
    obtain ⟨u, g2, h2, h⟩ := bind_some h
    have d2 : DF (fun y => g.re ≤ y ∨ P y) g1 g2 := df_addOps (OpsWr.mono (fun y hy => Or.inr hy) wA) h2
    have r2 : g.re ≤ g2.re := Nat.le_trans d1.1 d2.1
    obtain ⟨fork, g3, h3, h⟩ := bind_some h
    have F : DF (fun y => g.re ≤ y ∨ P y) g2 g3 ∧
        ∀ e ∈ fork, (∀ y, LReg e.1.2 y → P y ∨ g.re ≤ y) ∧ (∀ y, LReg e.2.2 y → P y ∨ g.re ≤ y) := by
      have hf1 : ∀ e ∈ f1, (∀ y, LReg e.1.2 y → P y) ∧ (∀ y, LReg e.2.2 y → P y) := fun e he =>
        ⟨fun y hy => ha y (lReg_iff_parts.mpr (Or.inr (Or.inr ⟨e, he, Or.inl hy⟩))),
          fun y hy => ha y (lReg_iff_parts.mpr (Or.inr (Or.inr ⟨e, he, Or.inr hy⟩)))⟩
      have hf2 : ∀ e ∈ second.fork, (∀ y, LReg e.1.2 y → P y) ∧ (∀ y, LReg e.2.2 y → P y) := fun e he =>
        ⟨fun y hy => hb y (lReg_iff_parts.mpr (Or.inr (Or.inr ⟨e, he, Or.inl hy⟩))),
          fun y hy => hb y (lReg_iff_parts.mpr (Or.inr (Or.inr ⟨e, he, Or.inr hy⟩)))⟩
      by_cases c1 : second.fork.isEmpty = true
      · rw [if_pos c1] at h3
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
        obtain ⟨rfl, rfl⟩ := h3
        exact ⟨DF.refl _ _, fun e he => ⟨fun y hy => Or.inl ((hf1 e he).1 y hy), fun y hy => Or.inl ((hf1 e he).2 y hy)⟩⟩
      rw [if_neg c1] at h3
      by_cases c2 : f1.isEmpty = true
      · rw [if_pos c2] at h3
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
        obtain ⟨rfl, rfl⟩ := h3
        exact ⟨DF.refl _ _, fun e he => ⟨fun y hy => Or.inl ((hf2 e he).1 y hy), fun y hy => Or.inl ((hf2 e he).2 y hy)⟩⟩
      rw [if_neg c2] at h3
      obtain ⟨merged, g3', hm, h3⟩ := bind_some h3
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
      obtain ⟨rfl, rfl⟩ := h3
      have M := frame_mergeForks (index (Map := Map) (fun e : ForkE S => e.1.1) second.fork) f1 P g2 g3' merged hm
        (fun k e hk => hf2 e (fc_index_mem _ hk)) hf1
      refine ⟨M.1.up r2, fun e he => ?_⟩
      rcases List.mem_append.mp he with he | he
      · exact ⟨fun y hy => ((M.2 e he).1 y hy).imp_right (Nat.le_trans r2),
          fun y hy => ((M.2 e he).2 y hy).imp_right (Nat.le_trans r2)⟩
      · have he2 := (List.mem_filter.mp he).1
        exact ⟨fun y hy => Or.inl ((hf2 e he2).1 y hy), fun y hy => Or.inl ((hf2 e he2).2 y hy)⟩
    have r3 : g.re ≤ g3.re := Nat.le_trans r2 F.1.1
    obtain ⟨bond, g4, h4, h⟩ := bind_some h
    have B : DF (fun y => g.re ≤ y ∨ P y) g3 g4 ∧ ∀ e ∈ bond, ∀ y, LReg e.2 y → P y ∨ g.re ≤ y := by
      have hb1 : ∀ e ∈ b1, ∀ y, LReg e.2 y → P y := fun e he y hy =>
        ha y (lReg_iff_parts.mpr (Or.inr (Or.inl ⟨e, he, hy⟩)))
      have hb2 : ∀ e ∈ second.bond, ∀ y, LReg e.2 y → P y := fun e he y hy =>
        hb y (lReg_iff_parts.mpr (Or.inr (Or.inl ⟨e, he, hy⟩)))
      by_cases c1 : second.bond.isEmpty = true
      · rw [if_pos c1] at h4
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h4
        obtain ⟨rfl, rfl⟩ := h4
        exact ⟨DF.refl _ _, fun e he y hy => Or.inl (hb1 e he y hy)⟩
      rw [if_neg c1] at h4
      by_cases c2 : b1.isEmpty = true
      · rw [if_pos c2] at h4
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h4
        obtain ⟨rfl, rfl⟩ := h4
        exact ⟨DF.refl _ _, fun e he y hy => Or.inl (hb2 e he y hy)⟩
      rw [if_neg c2] at h4
      obtain ⟨merged, g4', hm, h4⟩ := bind_some h4
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h4
      obtain ⟨rfl, rfl⟩ := h4
      have M := frame_mergeBonds (index (Map := Map) (fun e : Nat × Lazy S => e.1) second.bond) b1 P g3 g4' merged hm
        (fun k e hk => hb2 e (fc_index_mem _ hk)) hb1
      refine ⟨M.1.up r3, fun e he y hy => ?_⟩
      rcases List.mem_append.mp he with he | he
      · exact (M.2 e he y hy).imp_right (Nat.le_trans r3)
      · exact Or.inl (hb2 e (List.mem_filter.mp he).1 y hy)
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨d1.trans (d2.trans (F.1.trans B.1)), fun y hy => ?_⟩
    rcases lReg_iff_parts.mp hy with hy | ⟨e, he, hy⟩ | ⟨e, he, hy | hy⟩
    · rcases C.mem y hy with hy | ⟨hy, -⟩
      · rcases hy with hy | hy
        · exact Or.inl (ha y (lReg_iff_parts.mpr (Or.inl hy)))
        · exact Or.inl (hb y (lReg_iff_parts.mpr (Or.inl hy)))
      · exact Or.inr hy
    · exact B.2 e he y hy
    · exact (F.2 e he).1 y hy
    · exact (F.2 e he).2 y hy

/-- The forks of the merge. -/
theorem frame_mergeForks (idx : Map (ForkE S)) : ∀ (l : List (ForkE S)) (P : Nat → Prop) (g g' : Comp.Gen Map)
    (l' : List (ForkE S)), mergeForks idx l g = some (l', g') →
    (∀ k e, HoonMap.get idx k = some e → (∀ y, LReg e.1.2 y → P y) ∧ (∀ y, LReg e.2.2 y → P y)) →
    (∀ e ∈ l, (∀ y, LReg e.1.2 y → P y) ∧ (∀ y, LReg e.2.2 y → P y)) →
    DF (fun y => g.re ≤ y ∨ P y) g g' ∧
      ∀ e ∈ l', (∀ y, LReg e.1.2 y → P y ∨ g.re ≤ y) ∧ (∀ y, LReg e.2.2 y → P y ∨ g.re ≤ y)
  | [], P, g, g', l', h, _, _ => by
    rw [mergeForks] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨DF.refl _ _, fun e he => absurd he List.not_mem_nil⟩
  | ((oy, y), (on, n)) :: rest, P, g, g', l', h, hidx, hl => by
    rw [mergeForks] at h
    obtain ⟨e, g1, h1, h⟩ := bind_some h
    obtain ⟨r, g2, h2, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hl0 := hl _ List.mem_cons_self
    have E : DF (fun y => g.re ≤ y ∨ P y) g g1 ∧ (∀ x, LReg e.1.2 x → P x ∨ g.re ≤ x) ∧
        (∀ x, LReg e.2.2 x → P x ∨ g.re ≤ x) := by
      rcases hk : HoonMap.get idx oy with _ | ⟨⟨z, my⟩, ⟨mon, mn⟩⟩
      · rw [hk] at h1
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        exact ⟨DF.refl _ _, fun x hx => Or.inl (hl0.1 x hx), fun x hx => Or.inl (hl0.2 x hx)⟩
      · rw [hk] at h1
        have hm := hidx oy _ hk
        dsimp only at h1
        by_cases ce : on = mon
        · rw [if_pos ce] at h1
          obtain ⟨y', ga, hya, h1⟩ := bind_some h1
          obtain ⟨n', gb, hnb, h1⟩ := bind_some h1
          simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
          obtain ⟨rfl, rfl⟩ := h1
          have A := frame_copyLazyL oy y my P g ga y' hya hl0.1 hm.1
          have B := frame_copyLazyL on n mn P ga gb n' hnb hl0.2 hm.2
          exact ⟨A.1.trans (B.1.up A.1.1), A.2, fun x hx => (B.2 x hx).imp_right (Nat.le_trans A.1.1)⟩
        · rw [if_neg ce] at h1
          cases h1
    have R := frame_mergeForks idx rest P g1 g2 r h2 hidx (fun e he => hl e (List.mem_cons_of_mem _ he))
    refine ⟨E.1.trans (R.1.up E.1.1), fun e' he' => ?_⟩
    rcases List.mem_cons.mp he' with rfl | he'
    · exact E.2
    · exact ⟨fun x hx => ((R.2 e' he').1 x hx).imp_right (Nat.le_trans E.1.1),
        fun x hx => ((R.2 e' he').2 x hx).imp_right (Nat.le_trans E.1.1)⟩

/-- The bonds of the merge. -/
theorem frame_mergeBonds (idx : Map (Nat × Lazy S)) : ∀ (l : List (Nat × Lazy S)) (P : Nat → Prop)
    (g g' : Comp.Gen Map) (l' : List (Nat × Lazy S)), mergeBonds idx l g = some (l', g') →
    (∀ k e, HoonMap.get idx k = some e → ∀ y, LReg e.2 y → P y) →
    (∀ e ∈ l, ∀ y, LReg e.2 y → P y) →
    DF (fun y => g.re ≤ y ∨ P y) g g' ∧ ∀ e ∈ l', ∀ y, LReg e.2 y → P y ∨ g.re ≤ y
  | [], P, g, g', l', h, _, _ => by
    rw [mergeBonds] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨DF.refl _ _, fun e he => absurd he List.not_mem_nil⟩
  | (ob, lb) :: rest, P, g, g', l', h, hidx, hl => by
    rw [mergeBonds] at h
    obtain ⟨e, g1, h1, h⟩ := bind_some h
    obtain ⟨r, g2, h2, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hl0 := hl _ List.mem_cons_self
    have E : DF (fun y => g.re ≤ y ∨ P y) g g1 ∧ ∀ x, LReg e.2 x → P x ∨ g.re ≤ x := by
      rcases hk : HoonMap.get idx ob with _ | ⟨z, m⟩
      · rw [hk] at h1
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        exact ⟨DF.refl _ _, fun x hx => Or.inl (hl0 x hx)⟩
      · rw [hk] at h1
        have hm := hidx ob _ hk
        dsimp only at h1
        obtain ⟨l2, ga, hla, h1⟩ := bind_some h1
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        exact frame_copyLazyL ob lb m P g ga l2 hla hl0 hm
    have R := frame_mergeBonds idx rest P g1 g2 r h2 hidx (fun e he => hl e (List.mem_cons_of_mem _ he))
    refine ⟨E.1.trans (R.1.up E.1.1), fun e' he' => ?_⟩
    rcases List.mem_cons.mp he' with rfl | he'
    · exact E.2
    · exact fun x hx => (R.2 e' he' x hx).imp_right (Nat.le_trans E.1.1)
end

/-- **`+copy`**: the merge writes registers of the two trees or fresh ones,
and its result's registers are the two trees' or fresh. -/
theorem frame_copyL {first : NextL S} {second : Lazy S} {g g' : Comp.Gen Map} {nex : NextL S}
    (h : copyL first second g = some (nex, g')) :
    DF (fun y => g.re ≤ y ∨ LReg first.laz y ∨ LReg second y) g g' ∧
      ∀ y, LReg nex.laz y → LReg first.laz y ∨ LReg second y ∨ g.re ≤ y := by
  simp only [copyL] at h
  obtain ⟨o, g1, h1, h⟩ := bind_some h
  obtain ⟨d1, -, e1⟩ := df_emit (blobWr_nil (fun y => g.re ≤ y ∨ LReg first.laz y ∨ LReg second y) _) h1
  obtain ⟨laz, g2, h2, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨d2, r2⟩ := frame_copyLazyL o first.laz second (fun y => LReg first.laz y ∨ LReg second y) g1 g2 laz h2
    (fun y hy => Or.inl hy) (fun y hy => Or.inr hy)
  refine ⟨d1.trans (d2.mono fun y hy => hy.imp_left fun h => by omega), fun y hy => ?_⟩
  rcases r2 y hy with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (by omega))

/-! ## The chain -/

/-- **Run `q`, `+past`, run `p`, `+copy`**: the shared tail of `%5`, cons,
`%10` and `%2`. -/
theorem frame_chain {G : Nat → Prop} {rq rp : CGoalL S → List Nat → CM Map (NextL S)} (hq : FrameRun rq)
    (hp : FrameRun rp) {cod : Bell → Option Bool} {p : Nomm} {region : List Nat} {lq lp : Lazy S} {j : Jmp}
    {g1 g2 g3 g4 g5 : Comp.Gen Map} {nq nq' np nex : NextL S} (hlq : ∀ y, LReg lq y → G y)
    (hlp : ∀ y, LReg lp y → G y) (hG : ∀ y, g1.re ≤ y → G y)
    (h1 : rq (CGoalL.next lq j) region g1 = some (nq, g2)) (h2 : pastL cod nq p region g2 = some (nq', g3))
    (h3 : rp (CGoalL.next lp nq'.th) region g3 = some (np, g4)) (h4 : copyL np nq'.laz g4 = some (nex, g5)) :
    DF G g1 g5 ∧ ∀ y, LReg nex.laz y → G y := by
  obtain ⟨F1, R1⟩ := hq _ _ _ _ _ h1
  obtain ⟨D2, L2⟩ := frame_pastL h2
  obtain ⟨F3, R3⟩ := hp _ _ _ _ _ h3
  obtain ⟨D4, L4⟩ := frame_copyL h4
  have r12 : g1.re ≤ g2.re := F1.1
  have r23 : g2.re ≤ g3.re := D2.1
  have r34 : g3.re ≤ g4.re := F3.1
  have Gq : ∀ y, LReg nq.laz y → G y := fun y hy => by
    rcases R1 y (gregL_goal.mpr hy) with h | h
    · exact hlq y (gregL_next.mp h)
    · exact hG y h
  have Gp : ∀ y, LReg np.laz y → G y := fun y hy => by
    rcases R3 y (gregL_goal.mpr hy) with h | h
    · exact hlp y (gregL_next.mp h)
    · exact hG y (by omega)
  refine ⟨((frL_iff.mp F1).mono fun y hy => ?_).trans ((D2.mono fun y hy => hy.elim).trans
    (((frL_iff.mp F3).mono fun y hy => ?_).trans (D4.mono fun y hy => ?_))), fun y hy => ?_⟩
  · rcases hy with hy | hy
    · exact hG y hy
    · exact hlq y (gregL_next.mp hy)
  · rcases hy with hy | hy
    · exact hG y (by omega)
    · exact hlp y (gregL_next.mp hy)
  · rcases hy with hy | hy | hy
    · exact hG y (by omega)
    · exact Gp y hy
    · exact Gq y (L2 y hy)
  · rcases L4 y hy with h | h | h
    · exact Gp y h
    · exact Gq y (L2 y h)
    · exact hG y (by omega)

end Raw
end SkaModel
end Formalization
