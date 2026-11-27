import lemmas.Ska.RawInvCLTen

/-!
# The spec of `+into` is a theorem

README Gaps 14 (b), track D.  **`intoSpecL : IntoSpecL S Map`**: `+into`
(a fresh hop block `o` to the goal, then `intoLoopL`, the walk of the goal's
lazy tree with `+into-sure` at every entry) gives `IL` of the donor and of
the recipient as goals at `o`, their registers apart, and a register live at
`o` with both halves' kills is one the goal may leave live.

* `its_sure`: `+into-sure` at one entry: ops `A` in front of the entry's
  block (`intoRec_raw`, `intoRec_wr`, `intoRec_ok` of the fork-free work),
  which read first only the halves' registers, define every register of the
  need that neither half holds, write registers of the need or fresh ones
  that no half holds; the halves' registers are the need's or fresh,
  distinct, apart.
* `ItsPre` (the walked entries' needs apart, distinct, below `re`), `ItsW`
  (what a walk over the entries `Es` with the halves' entries `Ed`, `Er`
  does: ops `P` in front, the seven facts above at every label, the halves'
  needs pairwise apart and at labels of `Es`), `its_nil`, `its_one`,
  **`its_app`** (two walks in a row), `its_weak` (fewer entries in the
  halves, the same kills: the pruning and the order of the entries).
* `its_bondKeep`, `its_forkKeep`, `its_bondSub`, `its_forkSub`,
  `its_pruneSub`, `its_pruneKeep`: `+lazy-prune` drops only entries with an
  empty need and none below.
* **`its_loop`** mutual with `its_forks`, `its_bonds`: `intoLoopL` is such a
  walk over the entries of the tree.
* `its_liveK`: a register live after ops in front that read first only the
  new kills, and define the old kills that are not new ones, was live before.
* **`intoSpecL`**.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## `+into-sure` at one entry -/

/-- What the ops `A` of `+into-sure` on the need `s` with halves `sd`, `sr`
do, from `g` to `g'`. -/
structure ItsSure (A : List Pole) (s sd sr : Need) (g g' : Comp.Gen Map) : Prop where
  rd : ∀ y, OpsRF A y → NMem sd y ∨ NMem sr y
  df : ∀ y, NMem s y → y ∈ defsOf A ∨ NMem sd y ∨ NMem sr y
  wr : ∀ y ∈ defsOf A, (NMem s y ∨ (g.re ≤ y ∧ y < g'.re)) ∧ ¬ NMem sd y ∧ ¬ NMem sr y
  rg : RegsIn (· < g'.re) A
  mem : ∀ y, NMem sd y ∨ NMem sr y → NMem s y ∨ (g.re ≤ y ∧ y < g'.re)
  dd : Distinct sd
  dr : Distinct sr
  ap : ∀ y, NMem sd y → ¬ NMem sr y

/-- **`+into-sure` at one entry.** -/
theorem its_sure {axe x : Nat} {s sd sr : Sure S} {g g' : Comp.Gen Map}
    (h : intoSure axe s x g = some ((sd, sr), g')) (hd : g.drop = false) (hds : Distinct s.ned)
    (hlo : NB g.re s.ned) :
    ∃ A, Prep (fun k => if k = x then A else []) g.blocks g'.blocks ∧ AddSt g g' ∧ g'.cond = g.cond ∧
      ItsSure A s.ned sd.ned sr.ned g g' := by
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
    refine ⟨[], prep_same, AddSt.refl _, rfl, ⟨fun y hy => hy.elim, fun y hy => Or.inr (Or.inl hy),
      fun y hy => by simp [defsOf] at hy, RegsIn.nil _, fun y hy => ?_, hds, trivial, fun y _ h => h⟩⟩
    rcases hy with hy | hy
    · exact Or.inl hy
    · exact hy.elim
  rw [if_neg a1] at h2
  obtain ⟨d, r, ops, g1, e1, e2, ex⟩ := intoLoop_rec _ _ _ _ _ _ _ h2
  simp only [List.foldl_nil, Prod.mk.injEq] at ex
  obtain ⟨rfl, rfl⟩ := ex
  have ha : 1 ≤ axe := by omega
  have I := intoRec_ok axe s.ned g g1 _ _ ops ha e1
  obtain ⟨-, rf1, cv1, -, rg1⟩ := intoRec_raw axe s.ned g g1 _ _ ops ha e1 hds hlo
  have W := intoRec_wr axe s.ned g g1 _ _ ops ha e1 hds hlo
  obtain ⟨dd, dr, dap, -⟩ := I.sem hds hlo
  rw [List.append_nil] at e2
  have hd1 : g1.drop = false := by rw [I.gen]; exact hd
  obtain ⟨A2, c2, P2⟩ := addOps_step hd1 e2
  have hb1 : g1.blocks = g.blocks := by rw [I.gen]
  have hc1 : g1.cond = g.cond := by rw [I.gen]
  have A1 : AddSt g g1 := ⟨by rw [I.gen], by rw [I.gen], by rw [I.gen], I.le, fun k v h => by rw [hc1]; exact h,
    fun k v h => Or.inl (by rw [← hc1]; exact h)⟩
  have hre := A2.2.2.2.1
  refine ⟨ops, hb1 ▸ P2, A1.trans A2, c2.trans hc1, ⟨rf1, cv1, fun y hy => ?_, rg1.mono fun z hz => by omega,
    fun y hy => ?_, dd, dr, dap⟩⟩
  · obtain ⟨op, hop, hdst⟩ := mem_defsOf.mp hy
    obtain ⟨w1, w2, w3⟩ := W op hop y (aliasDst_poleWr hdst)
    refine ⟨?_, w2, w3⟩
    rcases w1 with w | w
    · exact Or.inl w
    · exact Or.inr ⟨w.1, by omega⟩
  · rcases hy with hy | hy
    · rcases I.md y hy with w | w
      · exact Or.inl w
      · exact Or.inr ⟨w.1, by omega⟩
    · rcases I.mr y hy with w | w
      · exact Or.inl w
      · exact Or.inr ⟨w.1, by omega⟩

/-! ## Walks over entries -/

/-- The kills of a list of entries: each entry first defines its sure need. -/
def itsK (es : List (Nat × Lazy S)) (k y : Nat) : Prop := ∃ e ∈ es, e.1 = k ∧ NMem e.2.sure.ned y

theorem itsK_append {a b : List (Nat × Lazy S)} {k y : Nat} : itsK (a ++ b) k y ↔ itsK a k y ∨ itsK b k y := by
  simp only [itsK, List.mem_append, or_and_right, exists_or]

theorem itsK_eregs {es : List (Nat × Lazy S)} {k y : Nat} (h : itsK es k y) : ERegs es y :=
  let ⟨e, he, _, hm⟩ := h
  ⟨e, he, hm⟩

/-- What a walk asks of its entries and its state. -/
structure ItsPre (es : List (Nat × Lazy S)) (g : Comp.Gen Map) : Prop where
  ap : NeedsApart es
  ds : ∀ e ∈ es, Distinct e.2.sure.ned
  lo : ∀ y, ERegs es y → y < g.re
  dr : g.drop = false

theorem ItsPre.sub {es es' : List (Nat × Lazy S)} {g g' : Comp.Gen Map} (h : ItsPre es g) (hs : List.Sublist es' es)
    (hre : g.re ≤ g'.re) (hd : g'.drop = g.drop) : ItsPre es' g' :=
  ⟨List.Pairwise.sublist hs h.ap, fun e he => h.ds e (hs.subset he),
    fun y ⟨e, he, hm⟩ => Nat.lt_of_lt_of_le (h.lo y ⟨e, hs.subset he, hm⟩) hre, hd.trans h.dr⟩

theorem its_apart_symm {a b : Nat × Lazy S} (h : ∀ r, NMem a.2.sure.ned r → ¬ NMem b.2.sure.ned r) :
    ∀ r, NMem b.2.sure.ned r → ¬ NMem a.2.sure.ned r :=
  fun r hb ha => h r ha hb

theorem ItsPre.perm {es es' : List (Nat × Lazy S)} {g : Comp.Gen Map} (h : ItsPre es g) (hp : es.Perm es') :
    ItsPre es' g :=
  ⟨(List.Perm.pairwise_iff (fun h' => its_apart_symm h') hp).mp h.ap, fun e he => h.ds e (hp.mem_iff.mpr he),
    fun y ⟨e, he, hm⟩ => h.lo y ⟨e, hp.mem_iff.mpr he, hm⟩, h.dr⟩

/-- **What a walk over the entries `Es` does**, with the halves' entries
`Ed`, `Er`: the ops `P` in front of the blocks. -/
structure ItsW (Es Ed Er : List (Nat × Lazy S)) (ga gb : Comp.Gen Map) (P : Nat → List Pole) : Prop where
  prep : Prep P ga.blocks gb.blocks
  st : AddSt ga gb
  cnd : gb.cond = ga.cond
  rd : ∀ k y, OpsRF (P k) y → itsK Ed k y ∨ itsK Er k y
  df : ∀ e ∈ Es, ∀ y, NMem e.2.sure.ned y → y ∈ defsOf (P e.1) ∨ itsK Ed e.1 y ∨ itsK Er e.1 y
  wr : ∀ k y, y ∈ defsOf (P k) → (ERegs Es y ∨ (ga.re ≤ y ∧ y < gb.re)) ∧ ¬ ERegs Ed y ∧ ¬ ERegs Er y
  rg : ∀ k, RegsIn (· < gb.re) (P k)
  mem : ∀ y, ERegs Ed y ∨ ERegs Er y → ERegs Es y ∨ (ga.re ≤ y ∧ y < gb.re)
  ap : NeedsApart (Ed ++ Er)
  ds : ∀ e ∈ Ed ++ Er, Distinct e.2.sure.ned
  lab : ∀ e ∈ Ed ++ Er, ∃ e' ∈ Es, e'.1 = e.1

theorem its_nil (g : Comp.Gen Map) : ItsW ([] : List (Nat × Lazy S)) [] [] g g (fun _ => []) :=
  ⟨prep_nil _, AddSt.refl _, rfl, fun _ _ h => h.elim, fun _ h => absurd h List.not_mem_nil,
    fun _ _ h => by simp [defsOf] at h, fun _ => RegsIn.nil _,
    fun y h => by rcases h with h | h <;> exact absurd h eregs_nil, List.Pairwise.nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩

theorem eregs_single {x : Nat} {l : Lazy S} {y : Nat} : ERegs [(x, l)] y ↔ NMem l.sure.ned y := by
  simp [ERegs]

theorem itsK_single {x : Nat} {l : Lazy S} {k y : Nat} : itsK [(x, l)] k y ↔ x = k ∧ NMem l.sure.ned y := by
  simp [itsK]

/-- **One entry.** -/
theorem its_one {axe x : Nat} {l : Lazy S} {sd sr : Sure S} {ga gb : Comp.Gen Map}
    (h : intoSure axe l.sure x ga = some ((sd, sr), gb)) (hp : ItsPre [(x, l)] ga) (ld lr : Lazy S)
    (hd : ld.sure = sd) (hr : lr.sure = sr) :
    ∃ P, ItsW [(x, l)] [(x, ld)] [(x, lr)] ga gb P := by
  subst hd hr
  obtain ⟨A, hP, hA, hc, I⟩ := its_sure h hp.dr (hp.ds _ List.mem_cons_self)
    (fun y hy => hp.lo y (eregs_single.mpr hy))
  refine ⟨_, ⟨hP, hA, hc, fun k y hy => ?_, fun e he y hy => ?_, fun k y hy => ?_, fun k => ?_, fun y hy => ?_,
    ?_, fun e he => ?_, fun e he => ?_⟩⟩
  · by_cases e : k = x
    · subst e; rw [if_pos rfl] at hy
      rcases I.rd y hy with h | h
      · exact Or.inl (itsK_single.mpr ⟨rfl, h⟩)
      · exact Or.inr (itsK_single.mpr ⟨rfl, h⟩)
    · rw [if_neg e] at hy; exact hy.elim
  · rw [List.mem_singleton] at he; subst he
    rw [if_pos rfl]
    rcases I.df y hy with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (itsK_single.mpr ⟨rfl, h⟩))
    · exact Or.inr (Or.inr (itsK_single.mpr ⟨rfl, h⟩))
  · by_cases e : k = x
    · subst e; rw [if_pos rfl] at hy
      obtain ⟨w1, w2, w3⟩ := I.wr y hy
      refine ⟨?_, fun h => w2 (eregs_single.mp h), fun h => w3 (eregs_single.mp h)⟩
      rcases w1 with w | w
      · exact Or.inl (eregs_single.mpr w)
      · exact Or.inr w
    · rw [if_neg e] at hy; simp [defsOf] at hy
  · by_cases e : k = x
    · rw [if_pos e]; exact I.rg
    · rw [if_neg e]; exact RegsIn.nil _
  · rcases I.mem y (by rcases hy with h | h; exact Or.inl (eregs_single.mp h); exact Or.inr (eregs_single.mp h))
      with w | w
    · exact Or.inl (eregs_single.mpr w)
    · exact Or.inr w
  · show List.Pairwise _ [(x, ld), (x, lr)]
    exact List.pairwise_pair.mpr I.ap
  · simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact I.dd
    · exact I.dr
  · simp only [List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> exact ⟨(x, l), List.mem_cons_self, rfl⟩

/-- Two walks in a row write and hold registers apart. -/
theorem its_dis {Es1 Es2 : List (Nat × Lazy S)} {ga gb gc : Comp.Gen Map} (hp : ItsPre (Es1 ++ Es2) ga)
    (hab : ga.re ≤ gb.re) {y : Nat} (h1 : ERegs Es1 y ∨ (ga.re ≤ y ∧ y < gb.re))
    (h2 : ERegs Es2 y ∨ (gb.re ≤ y ∧ y < gc.re)) : False := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · obtain ⟨e1, he1, m1⟩ := h1
    obtain ⟨e2, he2, m2⟩ := h2
    have hx := (List.pairwise_append.mp hp.ap).2.2
    exact hx e1 he1 e2 he2 y m1 m2
  · have := hp.lo y (eregs_append.mpr (Or.inl h1)); omega
  · have := hp.lo y (eregs_append.mpr (Or.inr h2)); omega
  · omega

theorem its_ap4 {A B C D : List (Nat × Lazy S)} (h1 : NeedsApart (A ++ C)) (h2 : NeedsApart (B ++ D))
    (hx : ∀ a ∈ A ++ C, ∀ b ∈ B ++ D, ∀ y, NMem a.2.sure.ned y → ¬ NMem b.2.sure.ned y) :
    NeedsApart ((A ++ B) ++ (C ++ D)) := by
  unfold NeedsApart at *
  obtain ⟨pA, pC, xAC⟩ := List.pairwise_append.mp h1
  obtain ⟨pB, pD, xBD⟩ := List.pairwise_append.mp h2
  refine List.pairwise_append.mpr ⟨List.pairwise_append.mpr ⟨pA, pB, fun a ha b hb => ?_⟩,
    List.pairwise_append.mpr ⟨pC, pD, fun a ha b hb => ?_⟩, fun a ha b hb => ?_⟩
  · exact hx a (List.mem_append_left _ ha) b (List.mem_append_left _ hb)
  · exact hx a (List.mem_append_right _ ha) b (List.mem_append_right _ hb)
  · rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
    · exact xAC a ha b hb
    · exact hx a (List.mem_append_left _ ha) b (List.mem_append_right _ hb)
    · exact its_apart_symm (hx b (List.mem_append_right _ hb) a (List.mem_append_left _ ha))
    · exact xBD a ha b hb

/-- **Two walks in a row.** -/
theorem its_app {Es1 Ed1 Er1 Es2 Ed2 Er2 : List (Nat × Lazy S)} {ga gb gc : Comp.Gen Map}
    {P1 P2 : Nat → List Pole} (W1 : ItsW Es1 Ed1 Er1 ga gb P1) (W2 : ItsW Es2 Ed2 Er2 gb gc P2)
    (hp : ItsPre (Es1 ++ Es2) ga) :
    ItsW (Es1 ++ Es2) (Ed1 ++ Ed2) (Er1 ++ Er2) ga gc (fun k => P2 k ++ P1 k) := by
  have hab : ga.re ≤ gb.re := W1.st.2.2.2.1
  have hbc : gb.re ≤ gc.re := W2.st.2.2.2.1
  -- a register of the first walk's halves is not one of the second's
  have m1 : ∀ y, ERegs Ed1 y ∨ ERegs Er1 y → ERegs Es1 y ∨ (ga.re ≤ y ∧ y < gb.re) := W1.mem
  have m2 : ∀ y, ERegs Ed2 y ∨ ERegs Er2 y → ERegs Es2 y ∨ (gb.re ≤ y ∧ y < gc.re) := W2.mem
  refine ⟨prep_trans W1.prep W2.prep, W1.st.trans W2.st, W2.cnd.trans W1.cnd, fun k y hy => ?_,
    fun e he y hy => ?_, fun k y hy => ?_, fun k => ?_, fun y hy => ?_, ?_, fun e he => ?_, fun e he => ?_⟩
  · rcases opsRF_append.mp hy with h | ⟨-, h⟩
    · rcases W2.rd k y h with h | h
      · exact Or.inl (itsK_append.mpr (Or.inr h))
      · exact Or.inr (itsK_append.mpr (Or.inr h))
    · rcases W1.rd k y h with h | h
      · exact Or.inl (itsK_append.mpr (Or.inl h))
      · exact Or.inr (itsK_append.mpr (Or.inl h))
  · rw [defsOf_append, List.mem_append]
    rcases List.mem_append.mp he with he | he
    · rcases W1.df e he y hy with h | h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inl (itsK_append.mpr (Or.inl h)))
      · exact Or.inr (Or.inr (itsK_append.mpr (Or.inl h)))
    · rcases W2.df e he y hy with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl (itsK_append.mpr (Or.inr h)))
      · exact Or.inr (Or.inr (itsK_append.mpr (Or.inr h)))
  · rw [defsOf_append, List.mem_append] at hy
    rcases hy with hy | hy
    · obtain ⟨w1, w2, w3⟩ := W2.wr k y hy
      refine ⟨?_, fun h => ?_, fun h => ?_⟩
      · rcases w1 with w | w
        · exact Or.inl (eregs_append.mpr (Or.inr w))
        · exact Or.inr ⟨by omega, w.2⟩
      · rcases eregs_append.mp h with h | h
        · exact its_dis hp hab (m1 y (Or.inl h)) w1
        · exact w2 h
      · rcases eregs_append.mp h with h | h
        · exact its_dis hp hab (m1 y (Or.inr h)) w1
        · exact w3 h
    · obtain ⟨w1, w2, w3⟩ := W1.wr k y hy
      refine ⟨?_, fun h => ?_, fun h => ?_⟩
      · rcases w1 with w | w
        · exact Or.inl (eregs_append.mpr (Or.inl w))
        · exact Or.inr ⟨w.1, by omega⟩
      · rcases eregs_append.mp h with h | h
        · exact w2 h
        · exact its_dis hp hab w1 (m2 y (Or.inl h))
      · rcases eregs_append.mp h with h | h
        · exact w3 h
        · exact its_dis hp hab w1 (m2 y (Or.inr h))
  · exact RegsIn.append (W2.rg k) ((W1.rg k).mono fun z hz => by omega)
  · rcases hy with hy | hy <;> rcases eregs_append.mp hy with h | h
    · rcases m1 y (Or.inl h) with w | w
      · exact Or.inl (eregs_append.mpr (Or.inl w))
      · exact Or.inr ⟨w.1, by omega⟩
    · rcases m2 y (Or.inl h) with w | w
      · exact Or.inl (eregs_append.mpr (Or.inr w))
      · exact Or.inr ⟨by omega, w.2⟩
    · rcases m1 y (Or.inr h) with w | w
      · exact Or.inl (eregs_append.mpr (Or.inl w))
      · exact Or.inr ⟨w.1, by omega⟩
    · rcases m2 y (Or.inr h) with w | w
      · exact Or.inl (eregs_append.mpr (Or.inr w))
      · exact Or.inr ⟨by omega, w.2⟩
  · refine its_ap4 W1.ap W2.ap fun a ha b hb y h1 h2 => ?_
    have e1 : ERegs Ed1 y ∨ ERegs Er1 y := by
      rcases List.mem_append.mp ha with ha | ha
      · exact Or.inl ⟨a, ha, h1⟩
      · exact Or.inr ⟨a, ha, h1⟩
    have e2 : ERegs Ed2 y ∨ ERegs Er2 y := by
      rcases List.mem_append.mp hb with hb | hb
      · exact Or.inl ⟨b, hb, h2⟩
      · exact Or.inr ⟨b, hb, h2⟩
    exact its_dis hp hab (m1 y e1) (m2 y e2)
  · simp only [List.mem_append] at he
    rcases he with (he | he) | (he | he)
    · exact W1.ds e (List.mem_append_left _ he)
    · exact W2.ds e (List.mem_append_left _ he)
    · exact W1.ds e (List.mem_append_right _ he)
    · exact W2.ds e (List.mem_append_right _ he)
  · simp only [List.mem_append] at he
    rcases he with (he | he) | (he | he)
    · obtain ⟨e', h1, h2⟩ := W1.lab e (List.mem_append_left _ he)
      exact ⟨e', List.mem_append_left _ h1, h2⟩
    · obtain ⟨e', h1, h2⟩ := W2.lab e (List.mem_append_left _ he)
      exact ⟨e', List.mem_append_right _ h1, h2⟩
    · obtain ⟨e', h1, h2⟩ := W1.lab e (List.mem_append_right _ he)
      exact ⟨e', List.mem_append_left _ h1, h2⟩
    · obtain ⟨e', h1, h2⟩ := W2.lab e (List.mem_append_right _ he)
      exact ⟨e', List.mem_append_right _ h1, h2⟩

/-- **Fewer entries in the halves with the same kills, the walked entries
reordered.** -/
theorem its_weak {Es Ed Er Es' Ed' Er' : List (Nat × Lazy S)} {ga gb : Comp.Gen Map} {P : Nat → List Pole}
    (W : ItsW Es Ed Er ga gb P) (hs : ∀ e, e ∈ Es ↔ e ∈ Es') (hd : ∀ e ∈ Ed', e ∈ Ed) (hr : ∀ e ∈ Er', e ∈ Er)
    (hkd : ∀ k y, itsK Ed k y → itsK Ed' k y) (hkr : ∀ k y, itsK Er k y → itsK Er' k y)
    (hap : NeedsApart (Ed' ++ Er')) : ItsW Es' Ed' Er' ga gb P := by
  have hes : ∀ y, ERegs Es y ↔ ERegs Es' y := fun y =>
    ⟨fun ⟨e, he, hm⟩ => ⟨e, (hs e).mp he, hm⟩, fun ⟨e, he, hm⟩ => ⟨e, (hs e).mpr he, hm⟩⟩
  have hsub : ∀ e ∈ Ed' ++ Er', e ∈ Ed ++ Er := fun e he => by
    rcases List.mem_append.mp he with he | he
    · exact List.mem_append_left _ (hd e he)
    · exact List.mem_append_right _ (hr e he)
  refine ⟨W.prep, W.st, W.cnd, fun k y hy => ?_, fun e he y hy => ?_, fun k y hy => ?_, W.rg, fun y hy => ?_, hap,
    fun e he => W.ds e (hsub e he), fun e he => ?_⟩
  · rcases W.rd k y hy with h | h
    · exact Or.inl (hkd k y h)
    · exact Or.inr (hkr k y h)
  · rcases W.df e ((hs e).mpr he) y hy with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (hkd _ y h))
    · exact Or.inr (Or.inr (hkr _ y h))
  · obtain ⟨w1, w2, w3⟩ := W.wr k y hy
    refine ⟨?_, fun ⟨e, he, hm⟩ => w2 ⟨e, hd e he, hm⟩, fun ⟨e, he, hm⟩ => w3 ⟨e, hr e he, hm⟩⟩
    rcases w1 with w | w
    · exact Or.inl ((hes y).mp w)
    · exact Or.inr w
  · have : ERegs Ed y ∨ ERegs Er y := by
      rcases hy with ⟨e, he, hm⟩ | ⟨e, he, hm⟩
      · exact Or.inl ⟨e, hd e he, hm⟩
      · exact Or.inr ⟨e, hr e he, hm⟩
    rcases W.mem y this with w | w
    · exact Or.inl ((hes y).mp w)
    · exact Or.inr w
  · obtain ⟨e', h1, h2⟩ := W.lab e (hsub e he)
    exact ⟨e', (hs e').mp h1, h2⟩

/-! ## `+lazy-prune` -/

theorem its_empty {l : Lazy S} (h : lazyEmpty l = true) : l.sure.ned = Need.none ∧ entries l = [] := by
  rcases l with ⟨s, f, b⟩
  simp only [lazyEmpty, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at h
  obtain ⟨⟨⟨h1, -⟩, h2⟩, h3⟩ := h
  refine ⟨h1, ?_⟩
  subst h2 h3
  simp [entries, bondEntries, forkEntries]

theorem its_bondKeep (p : Nat × Lazy S → Bool) (hp : ∀ e, p e = false → lazyEmpty e.2 = true) :
    ∀ (b : List (Nat × Lazy S)) (e : Nat × Lazy S) (y : Nat), e ∈ bondEntries b → NMem e.2.sure.ned y →
      e ∈ bondEntries (b.filter p)
  | [], e, _, he, _ => by simp [bondEntries] at he
  | (o, l) :: rest, e, y, he, hy => by
    simp only [bondEntries, List.mem_append] at he
    rw [List.filter_cons]
    split
    · simp only [bondEntries, List.mem_append]
      rcases he with he | he
      · exact Or.inl he
      · exact Or.inr (its_bondKeep p hp rest e y he hy)
    · rename_i hpe
      rcases he with he | he
      · obtain ⟨h1, h2⟩ := its_empty (hp _ (by simpa using hpe))
        rw [h2, List.mem_singleton] at he
        subst he
        rw [h1] at hy; exact hy.elim
      · exact its_bondKeep p hp rest e y he hy

theorem its_forkKeep (p : ForkE S → Bool)
    (hp : ∀ e, p e = false → lazyEmpty e.1.2 = true ∧ lazyEmpty e.2.2 = true) :
    ∀ (f : List (ForkE S)) (e : Nat × Lazy S) (y : Nat), e ∈ forkEntries f → NMem e.2.sure.ned y →
      e ∈ forkEntries (f.filter p)
  | [], e, _, he, _ => by simp [forkEntries] at he
  | ((oy, yl), (on, nl)) :: rest, e, y, he, hy => by
    simp only [forkEntries, List.mem_append] at he
    rw [List.filter_cons]
    split
    · simp only [forkEntries, List.mem_append]
      rcases he with (he | he) | he
      · exact Or.inl (Or.inl he)
      · exact Or.inl (Or.inr he)
      · exact Or.inr (its_forkKeep p hp rest e y he hy)
    · rename_i hpe
      obtain ⟨e1, e2⟩ := hp _ (by simpa using hpe)
      obtain ⟨a1, a2⟩ := its_empty e1
      obtain ⟨b1, b2⟩ := its_empty e2
      rcases he with (he | he) | he
      · rw [a2, List.mem_singleton] at he
        subst he
        rw [a1] at hy; exact hy.elim
      · rw [b2, List.mem_singleton] at he
        subst he
        rw [b1] at hy; exact hy.elim
      · exact its_forkKeep p hp rest e y he hy

theorem its_bondSub (p : Nat × Lazy S → Bool) :
    ∀ (b : List (Nat × Lazy S)), List.Sublist (bondEntries (b.filter p)) (bondEntries b)
  | [] => by simp [bondEntries]
  | (o, l) :: rest => by
    rw [List.filter_cons]
    split
    · simp only [bondEntries]
      exact (its_bondSub p rest).append_left _
    · simp only [bondEntries]
      exact (its_bondSub p rest).trans (List.sublist_append_right _ _)

theorem its_forkSub (p : ForkE S → Bool) :
    ∀ (f : List (ForkE S)), List.Sublist (forkEntries (f.filter p)) (forkEntries f)
  | [] => by simp [forkEntries]
  | ((oy, yl), (on, nl)) :: rest => by
    rw [List.filter_cons]
    split
    · simp only [forkEntries]
      exact (its_forkSub p rest).append_left _
    · simp only [forkEntries]
      exact (its_forkSub p rest).trans (List.sublist_append_right _ _)

theorem its_pruneSub (l : Lazy S) : List.Sublist (entries (lazyPrune l)) (entries l) := by
  rcases l with ⟨s, f, b⟩
  simp only [lazyPrune, entries]
  exact (its_bondSub _ b).append (its_forkSub _ f)

theorem its_pruneKeep (l : Lazy S) {e : Nat × Lazy S} {y : Nat} (he : e ∈ entries l) (hy : NMem e.2.sure.ned y) :
    e ∈ entries (lazyPrune l) := by
  rcases l with ⟨s, f, b⟩
  simp only [lazyPrune, entries, List.mem_append] at he ⊢
  rcases he with he | he
  · exact Or.inl (its_bondKeep _ (fun e h => by simpa using h) b e y he hy)
  · exact Or.inr (its_forkKeep _ (fun e h => by simpa [Bool.and_eq_true] using h) f e y he hy)

theorem its_pruneK {x : Nat} (l : Lazy S) {k y : Nat} (h : itsK ((x, l) :: entries l) k y) :
    itsK ((x, lazyPrune l) :: entries (lazyPrune l)) k y := by
  obtain ⟨e, he, h1, h2⟩ := h
  rcases List.mem_cons.mp he with rfl | he
  · exact ⟨(x, lazyPrune l), List.mem_cons_self, h1, by rcases l with ⟨s, f, b⟩; exact h2⟩
  · exact ⟨e, List.mem_cons_of_mem _ (its_pruneKeep l he h2), h1, h2⟩

theorem its_pruneMem {x : Nat} (l : Lazy S) {e : Nat × Lazy S} (he : e ∈ (x, lazyPrune l) :: entries (lazyPrune l)) :
    e ∈ (x, l) :: entries l ∨ (e = (x, lazyPrune l)) := by
  rcases List.mem_cons.mp he with rfl | he
  · exact Or.inr rfl
  · exact Or.inl (List.mem_cons_of_mem _ ((its_pruneSub l).subset he))

/-! ## The walk of `+into` -/

theorem its_pre_sure {x : Nat} {l : Lazy S} {g : Comp.Gen Map} (hp : ItsPre ((x, l) :: entries l) g) :
    ItsPre [(x, l)] g :=
  hp.sub (List.cons_sublist_cons.mpr (List.nil_sublist _)) (Nat.le_refl _) rfl

mutual
/-- **`intoLoopL` is a walk over the entries of the tree.** -/
theorem its_loop (axe : Nat) : ∀ (l : Lazy S) (x : Nat) (ga gb : Comp.Gen Map) (res : Lazy S × Lazy S),
    intoLoopL axe l x ga = some (res, gb) → ItsPre ((x, l) :: entries l) ga →
    ∃ P, ItsW ((x, l) :: entries l) ((x, res.1) :: entries res.1) ((x, res.2) :: entries res.2) ga gb P
  | mk s f b, x, ga, gb, res, h, hp => by
    rw [intoLoopL] at h
    obtain ⟨⟨sd, sr⟩, g1, h1, h⟩ := bind_some h
    dsimp only at h
    have hp1 := its_pre_sure hp
    split at h
    · rename_i hfb
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hfb
      obtain ⟨rfl, rfl⟩ := hfb
      obtain ⟨P, W⟩ := its_one h1 hp1 (ofSure sd) (ofSure sr) rfl rfl
      refine ⟨P, ?_⟩
      have e0 : entries (mk s ([] : List (ForkE S)) []) = [] := by simp [entries, bondEntries, forkEntries]
      simp only [e0, entries_ofSure]
      exact W
    · obtain ⟨⟨fd, fr⟩, g2, h2, h⟩ := bind_some h
      dsimp only at h
      obtain ⟨⟨bd, br⟩, g3, h3, h⟩ := bind_some h
      dsimp only at h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hE : entries (mk s f b) = bondEntries b ++ forkEntries f := by simp only [entries]
      have hEd : entries (mk sd fd bd) = bondEntries bd ++ forkEntries fd := by simp only [entries]
      have hEr : entries (mk sr fr br) = bondEntries br ++ forkEntries fr := by simp only [entries]
      obtain ⟨P1, W1⟩ := its_one h1 hp1 (lazyPrune (mk sd fd bd)) (lazyPrune (mk sr fr br)) rfl rfl
      have hre1 := W1.st.2.2.2.1
      have hdr1 := W1.st.2.1
      rw [hE] at hp
      have hp' : ItsPre ((x, mk s f b) :: (forkEntries f ++ bondEntries b)) ga :=
        hp.perm (List.Perm.cons _ List.perm_append_comm)
      obtain ⟨P2, W2⟩ := its_forks axe f g1 g2 _ h2
        (hp'.sub ((List.sublist_append_left _ _).trans (List.sublist_cons_self _ _)) hre1 hdr1)
      have hre2 := W2.st.2.2.2.1
      have hdr2 := W2.st.2.1
      obtain ⟨P3, W3⟩ := its_bonds axe b g2 g3 _ h3
        (hp'.sub ((List.sublist_append_right _ _).trans (List.sublist_cons_self _ _)) (Nat.le_trans hre1 hre2)
          (hdr2.trans hdr1))
      have W := its_app W1 (its_app W2 W3 (hp'.sub (List.sublist_cons_self _ _) hre1 hdr1)) hp'
      refine ⟨_, its_weak W (fun e => ?_) (fun e he => ?_) (fun e he => ?_) (fun k y hk => ?_) (fun k y hk => ?_) ?_⟩
      · simp only [hE, List.singleton_append]
        exact (List.Perm.cons _ List.perm_append_comm).mem_iff
      · rcases List.mem_cons.mp he with rfl | he
        · exact List.mem_cons_self
        · have := (its_pruneSub (mk sd fd bd)).subset he
          rw [hEd] at this
          exact List.mem_append_right _ (List.perm_append_comm.mem_iff.mp this)
      · rcases List.mem_cons.mp he with rfl | he
        · exact List.mem_cons_self
        · have := (its_pruneSub (mk sr fr br)).subset he
          rw [hEr] at this
          exact List.mem_append_right _ (List.perm_append_comm.mem_iff.mp this)
      · obtain ⟨e, he, h1, h2⟩ := hk
        rcases List.mem_cons.mp he with rfl | he
        · exact ⟨_, List.mem_cons_self, h1, h2⟩
        · have he' : e ∈ entries (mk sd fd bd) := by
            rw [hEd]; exact List.perm_append_comm.mem_iff.mp he
          exact ⟨e, List.mem_cons_of_mem _ (its_pruneKeep _ he' h2), h1, h2⟩
      · obtain ⟨e, he, h1, h2⟩ := hk
        rcases List.mem_cons.mp he with rfl | he
        · exact ⟨_, List.mem_cons_self, h1, h2⟩
        · have he' : e ∈ entries (mk sr fr br) := by
            rw [hEr]; exact List.perm_append_comm.mem_iff.mp he
          exact ⟨e, List.mem_cons_of_mem _ (its_pruneKeep _ he' h2), h1, h2⟩
      · have hap := W.ap
        have hperm : List.Perm ((x, lazyPrune (mk sd fd bd)) :: (bondEntries bd ++ forkEntries fd) ++
            (x, lazyPrune (mk sr fr br)) :: (bondEntries br ++ forkEntries fr))
            ([(x, lazyPrune (mk sd fd bd))] ++ (forkEntries fd ++ bondEntries bd) ++
              ([(x, lazyPrune (mk sr fr br))] ++ (forkEntries fr ++ bondEntries br))) :=
          List.Perm.append (List.Perm.cons _ List.perm_append_comm) (List.Perm.cons _ List.perm_append_comm)
        have hap' := (List.Perm.pairwise_iff (fun h' => its_apart_symm h') hperm).mpr hap
        refine List.Pairwise.sublist ?_ hap'
        have s1 := its_pruneSub (mk sd fd bd)
        have s2 := its_pruneSub (mk sr fr br)
        rw [hEd] at s1
        rw [hEr] at s2
        exact (List.Sublist.cons_cons _ s1).append (List.Sublist.cons_cons _ s2)

/-- Its walk over the forks. -/
theorem its_forks (axe : Nat) : ∀ (f : List (ForkE S)) (ga gb : Comp.Gen Map)
    (res : List (ForkE S) × List (ForkE S)),
    intoForks axe f ga = some (res, gb) → ItsPre (forkEntries f) ga →
    ∃ P, ItsW (forkEntries f) (forkEntries res.1) (forkEntries res.2) ga gb P
  | [], ga, gb, res, h, _ => by
    rw [intoForks] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨fun _ => [], ?_⟩
    simp only [forkEntries]
    exact its_nil ga
  | ((oy, y), (on, n)) :: rest, ga, gb, res, h, hp => by
    rw [intoForks] at h
    obtain ⟨⟨yd, yr⟩, g1, h1, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨⟨nd, nr⟩, g2, h2, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨⟨rd, rr⟩, g3, h3, h⟩ := bind_some h
    dsimp only at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hE : forkEntries (((oy, y), (on, n)) :: rest) =
        ((oy, y) :: entries y) ++ ((on, n) :: entries n) ++ forkEntries rest := by simp only [forkEntries]
    rw [hE] at hp
    obtain ⟨P1, W1⟩ := its_loop axe y oy ga g1 _ h1
      (hp.sub ((List.sublist_append_left _ _).trans (List.sublist_append_left _ _)) (Nat.le_refl _) rfl)
    have hre1 := W1.st.2.2.2.1
    have hdr1 := W1.st.2.1
    obtain ⟨P2, W2⟩ := its_loop axe n on g1 g2 _ h2
      (hp.sub ((List.sublist_append_right _ _).trans (List.sublist_append_left _ _)) hre1 hdr1)
    have hre2 := W2.st.2.2.2.1
    have hdr2 := W2.st.2.1
    obtain ⟨P3, W3⟩ := its_forks axe rest g2 g3 _ h3
      (hp.sub (List.sublist_append_right _ _) (Nat.le_trans hre1 hre2) (hdr2.trans hdr1))
    have W := its_app (its_app W1 W2 (hp.sub (List.sublist_append_left _ _) (Nat.le_refl _) rfl)) W3 hp
    refine ⟨fun k => P3 k ++ (P2 k ++ P1 k), ?_⟩
    simp only [forkEntries]
    exact W

/-- Its walk over the bonds. -/
theorem its_bonds (axe : Nat) : ∀ (b : List (Nat × Lazy S)) (ga gb : Comp.Gen Map)
    (res : List (Nat × Lazy S) × List (Nat × Lazy S)),
    intoBonds axe b ga = some (res, gb) → ItsPre (bondEntries b) ga →
    ∃ P, ItsW (bondEntries b) (bondEntries res.1) (bondEntries res.2) ga gb P
  | [], ga, gb, res, h, _ => by
    rw [intoBonds] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨fun _ => [], ?_⟩
    simp only [bondEntries]
    exact its_nil ga
  | (o, l) :: rest, ga, gb, res, h, hp => by
    rw [intoBonds] at h
    obtain ⟨⟨ld, lr⟩, g1, h1, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨⟨rd, rr⟩, g2, h2, h⟩ := bind_some h
    dsimp only at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hE : bondEntries ((o, l) :: rest) = ((o, l) :: entries l) ++ bondEntries rest := by
      simp only [bondEntries]
    rw [hE] at hp
    obtain ⟨P1, W1⟩ := its_loop axe l o ga g1 _ h1 (hp.sub (List.sublist_append_left _ _) (Nat.le_refl _) rfl)
    obtain ⟨P2, W2⟩ := its_bonds axe rest g1 g2 _ h2
      (hp.sub (List.sublist_append_right _ _) W1.st.2.2.2.1 W1.st.2.1)
    refine ⟨fun k => P2 k ++ P1 k, ?_⟩
    simp only [bondEntries]
    exact its_app W1 W2 hp
end

/-! ## Liveness through the ops in front -/

/-- **A register live after ops in front was live before**, when the ops
read first only the new kills `Kn` and define every old kill `Ko` that is
no new one. -/
theorem its_liveK {Q : Nat → List Pole} {bl bl' : Map Blob} (hP : Prep Q bl bl') {K Kn Ko : Nat → Nat → Prop}
    (hread : ∀ k y, OpsRF (Q k) y → Kn k y) (hdef : ∀ k y, Ko k y → y ∈ defsOf (Q k) ∨ Kn k y)
    {k y : Nat} (h : LiveK bl' (fun x z => K x z ∨ Kn x z) k y) : LiveK bl (fun x z => K x z ∨ Ko x z) k y := by
  induction h with
  | here hb hr hk =>
    rw [hP] at hb
    obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp hb
    rcases blockRF_pre hr with h | ⟨hd, h⟩
    · exact absurd (Or.inr (hread _ _ h)) hk
    · refine LiveK.here h0 h fun hk' => ?_
      rcases hk' with hk' | hk'
      · exact hk (Or.inl hk')
      · rcases hdef _ _ hk' with h' | h'
        · exact hd h'
        · exact hk (Or.inr h')
  | next hb hj _ hd hk ih =>
    rw [hP] at hb
    obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp hb
    refine LiveK.next h0 hj ih (fun hm => hd (mem_blockDefs_pre.mpr (Or.inl hm))) fun hk' => ?_
    rcases hk' with hk' | hk'
    · exact hk (Or.inl hk')
    · rcases hdef _ _ hk' with h' | h'
      · exact hd (mem_blockDefs_pre.mpr (Or.inr h'))
      · exact hk (Or.inr h')

theorem its_blobIn_pre {Q : Nat → Prop} {A : List Pole} {b : Blob} (hb : BlobIn Q b) (hA : RegsIn Q A) :
    BlobIn Q (pre A b) :=
  ⟨hb.1, RegsIn.append hA hb.2.1, hb.2.2⟩

/-! ## The spec -/

/-- **The spec of `+into`.** -/
theorem intoSpecL : IntoSpecL S Map := by
  intro K laz th axe g g' dd rr o hI h
  have hd : g.drop = false := hI.ats.1
  obtain ⟨A', KP', hfr'⟩ := (ht_intoL (⟨laz, th⟩ : NextL S) axe).run g _ g' hI.ats
    (hI.goal : GoalL g (CGoalL.next laz th)).1 h
  obtain ⟨hth, hap, hent⟩ := (hI.goal : GoalL g (CGoalL.next laz th))
  obtain ⟨bt, hbt, hpt, targs⟩ := hth
  have hthere : th.there < g.bo := hI.lab hbt
  unfold intoL at h
  obtain ⟨o1, ge, he, h⟩ := bind_some h
  rw [emit_apply] at he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨⟨dd, rr⟩, g2, h2, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
  have hfr : Fresh g2 (jmp0 g.bo) := hfr'
  -- the walk
  have hES : ∀ y, ERegs ((g.bo, laz) :: entries laz) y → GRegL (CGoalL.next laz th) y := by
    rintro y ⟨e, he, hm⟩
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨(th.there, laz), List.mem_cons_self, hm⟩
    · exact ⟨e, List.mem_cons_of_mem _ he, hm⟩
  have hpre : ItsPre ((g.bo, laz) :: entries laz) (g.emitted (⟨[], [], Termin.hop th⟩ : Blob)) := by
    refine ⟨List.pairwise_cons.mpr ⟨(List.pairwise_cons.mp hap).1, (List.pairwise_cons.mp hap).2⟩,
      fun e he => ?_, fun y hy => (hI.greg_lt (hES y hy)).1, hd⟩
    rcases List.mem_cons.mp he with rfl | he
    · exact (hent _ List.mem_cons_self).2.1
    · exact (hent e (List.mem_cons_of_mem _ he)).2.1
  obtain ⟨P, W⟩ := its_loop axe laz g.bo _ g2 (dd, rr) h2 hpre
  have hge : (g.emitted (⟨[], [], Termin.hop th⟩ : Blob)).re = g.re := rfl
  have hcond : g2.cond = g.cond := W.cnd
  have hre : g.re ≤ g2.re := W.st.2.2.2.1
  have hnk : ∀ y, (ERegs ((g.bo, laz) :: entries laz) y ∨ (g.re ≤ y ∧ y < g2.re)) →
      HoonMap.get g.cond y = Option.none := by
    intro y hy
    cases c : HoonMap.get g.cond y with
    | none => rfl
    | some v =>
      obtain ⟨c1, -, c3, -, -⟩ := hI.cond y v c
      rcases hy with hy | hy
      · exact absurd (hES y hy) c3
      · omega
  have hbl : ∀ k b, HoonMap.get (g.emitted (⟨[], [], Termin.hop th⟩ : Blob)).blocks k = some b →
      BlobIn (· < g.re) b := by
    intro k b hb
    rw [em_get hd] at hb
    split at hb
    · cases hb; exact blobIn_nil_fin (jmpIn_nil targs)
    · exact hI.regs k b hb
  have hdefd : ∀ y, Defd g2.blocks y → Defd g.blocks y ∨ ∃ k, y ∈ defsOf (P k) := by
    intro y hy
    obtain ⟨k, b, hb, hm⟩ := (defd_prep W.prep).mp hy
    rcases hm with hm | hm
    · exact Or.inl ((defd_emitted_nil hI.ats (b := ⟨[], [], Termin.hop th⟩) (by simp [blockDefs])).mp
        (defd_iff.mpr ⟨k, b, hb, hm⟩))
    · exact Or.inr ⟨k, hm⟩
  -- `IL` of a half
  have hIL : ∀ l : Lazy S, List.Sublist ((g.bo, l) :: entries l)
      (((g.bo, dd) :: entries dd) ++ ((g.bo, rr) :: entries rr)) → IL K (CGoalL.next l (jmp0 g.bo)) g2 := by
    intro l hsl
    have hmem : ∀ y, ERegs ((g.bo, l) :: entries l) y →
        ERegs ((g.bo, dd) :: entries dd) y ∨ ERegs ((g.bo, rr) :: entries rr) y := by
      rintro y ⟨e, he, hm⟩
      rcases List.mem_append.mp (hsl.subset he) with he' | he'
      · exact Or.inl ⟨e, he', hm⟩
      · exact Or.inr ⟨e, he', hm⟩
    have hgreg : ∀ y, GRegL (CGoalL.next l (jmp0 g.bo)) y →
        ERegs ((g.bo, dd) :: entries dd) y ∨ ERegs ((g.bo, rr) :: entries rr) y :=
      fun y hy => hmem y hy
    refine ⟨A', fun k b hb => ?_, fun k v hk => ?_, hI.kvan.mono KP'.2.1, hfr, List.Pairwise.sublist hsl W.ap,
      fun e he => ?_⟩
    · rw [W.prep k] at hb
      obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.mp hb
      exact its_blobIn_pre ((hbl k b0 h0).mono fun z hz => by omega) (W.rg k)
    · rw [hcond] at hk
      obtain ⟨c1, c2, c3, c4, c5⟩ := hI.cond k v hk
      refine ⟨by omega, fun hdk => ?_, fun hg => ?_, by omega, by rw [hcond]; exact c5⟩
      · rcases hdefd k hdk with h' | ⟨k', h'⟩
        · exact c2 h'
        · rcases (W.wr k' k h').1 with w | w
          · exact c3 (hES k w)
          · omega
      · rcases W.mem k (hgreg k hg) with w | w
        · exact c3 (hES k w)
        · omega
    · have he' := hsl.subset he
      refine ⟨?_, W.ds e he', fun y hy => ?_⟩
      · obtain ⟨e', h1, h2⟩ := W.lab e he'
        rw [← h2]
        rcases List.mem_cons.mp h1 with rfl | h1
        · obtain ⟨b, hb, hp, -⟩ := hfr
          exact ⟨b, hb, hp⟩
        · obtain ⟨⟨b, hb, hp⟩, -⟩ := hent e' (List.mem_cons_of_mem _ h1)
          obtain ⟨b', hb', hp', -⟩ := KP'.2.2 e'.1 b hb
          exact ⟨b', hb', hp'.trans hp⟩
      · have hy' : ERegs ((g.bo, dd) :: entries dd) y ∨ ERegs ((g.bo, rr) :: entries rr) y := hmem y ⟨e, he, hy⟩
        have hw := W.mem y hy'
        refine ⟨?_, fun hdy => ?_⟩
        · rcases hw with w | w
          · have := (hI.greg_lt (hES y w)).1; omega
          · exact w.2
        · rcases hdefd y hdy with h' | ⟨k, h'⟩
          · rcases hw with w | w
            · exact (hI.greg_lt (hES y w)).2 h'
            · have := defd_lt hI.regs h'; omega
          · obtain ⟨-, w2, w3⟩ := W.wr k y h'
            rcases hy' with h'' | h''
            · exact w2 h''
            · exact w3 h''
  refine ⟨hIL dd (List.sublist_append_left _ _), hIL rr (List.sublist_append_right _ _), fun y hdy hry => ?_,
    fun y hl => ?_⟩
  · -- the halves are apart
    have hx := (List.pairwise_append.mp W.ap).2.2
    have h1 : ∃ e ∈ (g.bo, dd) :: entries dd, NMem e.2.sure.ned y := by
      rcases hdy with h' | ⟨e, he, h'⟩
      · exact ⟨(g.bo, dd), List.mem_cons_self, h'⟩
      · exact ⟨e, List.mem_cons_of_mem _ he, h'⟩
    have h2 : ∃ e ∈ (g.bo, rr) :: entries rr, NMem e.2.sure.ned y := by
      rcases hry with h' | ⟨e, he, h'⟩
      · exact ⟨(g.bo, rr), List.mem_cons_self, h'⟩
      · exact ⟨e, List.mem_cons_of_mem _ he, h'⟩
    obtain ⟨a, ha, ma⟩ := h1
    obtain ⟨b, hb, mb⟩ := h2
    exact hx a ha b hb y ma mb
  -- the liveness
  have hid : ∀ z, (ERegs ((g.bo, laz) :: entries laz) z ∨ (g.re ≤ z ∧ z < g2.re)) → unproxy g2.cond z = z :=
    fun z hz => unproxy_none (by rw [hcond]; exact hnk z hz)
  have pU := unpM_prepG W.prep (fun x _ => by rw [hcond]; rfl) hbl
  have hl0 : LiveK (unpM g2) (fun x z => K x z ∨ (lazK g.bo dd x z ∨ lazK g.bo rr x z)) g.bo y :=
    hl.mono fun x z h' => by
      rcases h' with h' | h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  have hl1 := its_liveK pU (Ko := lazK g.bo laz) (fun k z hz => ?_) (fun k z hz => ?_) hl0
  rotate_left
  · obtain ⟨x, ex, hx⟩ := opsRF_ren_back _ hz
    have hr := W.rd k x hx
    have hx' : unproxy g2.cond x = x := hid x (W.mem x (by
      rcases hr with h' | h'
      · exact Or.inl (itsK_eregs h')
      · exact Or.inr (itsK_eregs h')))
    rw [hx'] at ex
    subst ex
    exact hr
  · obtain ⟨e, he, h1, h2⟩ := hz
    subst h1
    rcases W.df e he z h2 with h' | h' | h'
    · left
      rw [defsOf_ren]
      exact List.mem_map.mpr ⟨z, h', hid z (Or.inl ⟨e, he, h2⟩)⟩
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr h')
  have hget : HoonMap.get (unpM (g.emitted (⟨[], [], Termin.hop th⟩ : Blob))) g.bo =
      some ⟨[], [], Termin.hop th⟩ := by
    have := unpM_emitted_self (g := g) hd (⟨[], [], Termin.hop th⟩ : Blob)
    simp only [renBlob, renFin, renJmp_nil _ targs, List.map_nil] at this
    exact this
  have hl2 := liveK_hop_root hget targs (fun z => hI.kvan.van g.bo z (Nat.le_refl _)) (fun e he ee => by
      obtain ⟨⟨b, hb, -⟩, -⟩ := hent e (List.mem_cons_of_mem _ he)
      have := hI.lab hb
      omega) (Nat.ne_of_lt hthere) hl1
  exact (liveK_frameP hI.downU (fun x hx => unpM_emitted_lt hd _ hx) hthere).mp hl2

end Raw
end SkaModel
end Formalization
