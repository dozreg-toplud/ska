import lemmas.Ska.CompN5

/-!
# What `+split` does

`split_ok`: the block that `+split` emits for a goal `[%next laz th]` puts
together, from the needs of the head and the tail it returns, the need
`laz` of the cell (`+split-need` adds a `%con` in front of it when `laz`
names a register for the whole), and goes on to `th`.  A cell has the shape
and the looks of `laz` exactly when its head and tail have those of the two
halves.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

theorem addOps_gen {o : Nat} {ops : List Pole} {g g' : Gen Map} {u : Unit} (h : addOps o ops g = some (u, g')) :
    g'.re = g.re ∧ g'.bo = g.bo ∧ g'.drop = g.drop ∧
      ∀ o', o' ≠ o → HoonMap.get g'.blocks o' = HoonMap.get g.blocks o' := by
  by_cases hd : g.drop = false
  · obtain ⟨b, _, rfl⟩ := addOps_spec h hd
    exact ⟨rfl, rfl, rfl, fun o' h' => by simp [HoonMap.get_put, h']⟩
  · simp only [Bool.not_eq_false] at hd
    unfold addOps at h
    simp only [hd, if_true, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

/-! ## The looks -/

/-- The step of the fold of `+split-sure`. -/
def splitStep (acc : Option (S × S)) (axe : Nat) : Option (S × S) :=
  acc.bind fun (h, t) =>
    if axe = 0 then Option.none
    else if axe = 1 ∨ axe = 2 ∨ axe = 3 then some (h, t)
    else if cap axe = 2 then some (HoonSet.put h (mas axe), t)
    else some (h, HoonSet.put t (mas axe))

theorem foldl_splitStep_none (xs : List Nat) : xs.foldl (splitStep (S := S)) Option.none = Option.none := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [List.foldl, splitStep] using ih

theorem foldl_splitStep : ∀ (xs : List Nat) (h0 t0 lh lt : S),
    xs.foldl splitStep (some (h0, t0)) = some (lh, lt) →
    (∀ x ∈ xs, x ≠ 0) ∧
    (∀ y, y ∈ HoonSet.toList lh ↔ y ∈ HoonSet.toList h0 ∨ ∃ x ∈ xs, 4 ≤ x ∧ cap x = 2 ∧ y = mas x) ∧
    (∀ y, y ∈ HoonSet.toList lt ↔ y ∈ HoonSet.toList t0 ∨ ∃ x ∈ xs, 4 ≤ x ∧ cap x ≠ 2 ∧ y = mas x) := by
  intro xs
  induction xs with
  | nil =>
    intro h0 t0 lh lt h
    simp only [List.foldl, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | cons x xs ih =>
    intro h0 t0 lh lt h
    simp only [List.foldl] at h
    by_cases h0x : x = 0
    · simp [splitStep, h0x, foldl_splitStep_none] at h
    by_cases hs : x = 1 ∨ x = 2 ∨ x = 3
    · simp only [splitStep, Option.bind_some, h0x, if_false, hs, if_true] at h
      obtain ⟨n, H, T⟩ := ih _ _ _ _ h
      refine ⟨fun y hy => ?_, fun y => ?_, fun y => ?_⟩
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact h0x
        · exact n y hy
      · rw [H]; constructor
        · rintro (a | ⟨z, hz, a⟩)
          · exact Or.inl a
          · exact Or.inr ⟨z, List.mem_cons_of_mem _ hz, a⟩
        · rintro (a | ⟨z, hz, a⟩)
          · exact Or.inl a
          · rcases List.mem_cons.mp hz with rfl | hz
            · omega
            · exact Or.inr ⟨z, hz, a⟩
      · rw [T]; constructor
        · rintro (a | ⟨z, hz, a⟩)
          · exact Or.inl a
          · exact Or.inr ⟨z, List.mem_cons_of_mem _ hz, a⟩
        · rintro (a | ⟨z, hz, a⟩)
          · exact Or.inl a
          · rcases List.mem_cons.mp hz with rfl | hz
            · omega
            · exact Or.inr ⟨z, hz, a⟩
    have h4 : 4 ≤ x := by omega
    by_cases hc : cap x = 2
    · simp only [splitStep, Option.bind_some, h0x, if_false, hs, hc, if_true] at h
      obtain ⟨n, H, T⟩ := ih _ _ _ _ h
      refine ⟨fun y hy => ?_, fun y => ?_, fun y => ?_⟩
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact h0x
        · exact n y hy
      · rw [H, HoonSet.mem_put]; constructor
        · rintro ((a | a) | ⟨z, hz, a⟩)
          · exact Or.inr ⟨x, List.mem_cons_self .., h4, hc, a⟩
          · exact Or.inl a
          · exact Or.inr ⟨z, List.mem_cons_of_mem _ hz, a⟩
        · rintro (a | ⟨z, hz, a⟩)
          · exact Or.inl (Or.inr a)
          · rcases List.mem_cons.mp hz with rfl | hz
            · exact Or.inl (Or.inl a.2.2)
            · exact Or.inr ⟨z, hz, a⟩
      · rw [T]; constructor
        · rintro (a | ⟨z, hz, a⟩)
          · exact Or.inl a
          · exact Or.inr ⟨z, List.mem_cons_of_mem _ hz, a⟩
        · rintro (a | ⟨z, hz, a⟩)
          · exact Or.inl a
          · rcases List.mem_cons.mp hz with rfl | hz
            · exact absurd hc a.2.1
            · exact Or.inr ⟨z, hz, a⟩
    · simp only [splitStep, Option.bind_some, h0x, if_false, hs, hc] at h
      obtain ⟨n, H, T⟩ := ih _ _ _ _ h
      refine ⟨fun y hy => ?_, fun y => ?_, fun y => ?_⟩
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact h0x
        · exact n y hy
      · rw [H]; constructor
        · rintro (a | ⟨z, hz, a⟩)
          · exact Or.inl a
          · exact Or.inr ⟨z, List.mem_cons_of_mem _ hz, a⟩
        · rintro (a | ⟨z, hz, a⟩)
          · exact Or.inl a
          · rcases List.mem_cons.mp hz with rfl | hz
            · exact absurd a.2.1 hc
            · exact Or.inr ⟨z, hz, a⟩
      · rw [T, HoonSet.mem_put]; constructor
        · rintro ((a | a) | ⟨z, hz, a⟩)
          · exact Or.inr ⟨x, List.mem_cons_self .., h4, hc, a⟩
          · exact Or.inl a
          · exact Or.inr ⟨z, List.mem_cons_of_mem _ hz, a⟩
        · rintro (a | ⟨z, hz, a⟩)
          · exact Or.inl (Or.inr a)
          · rcases List.mem_cons.mp hz with rfl | hz
            · exact Or.inl (Or.inl a.2.2)
            · exact Or.inr ⟨z, hz, a⟩

theorem mas_two_three {x : Nat} (h : x = 2 ∨ x = 3) : mas x = 1 := by
  rcases h with rfl | rfl <;> simp [mas]

/-- The looks of a cell are the looks of its head and tail. -/
theorem splitLok_looks {lok lh lt : S} (h : splitLok lok = some (lh, lt)) (a b : Noun) :
    Looks lok (C a b) ↔ Looks lh a ∧ Looks lt b := by
  have h' : (HoonSet.toList lok).foldl splitStep (some (HoonSet.empty, HoonSet.empty)) = some (lh, lt) := h
  obtain ⟨n0, H, T⟩ := foldl_splitStep _ _ _ _ _ h'
  -- the noun at an axis of a cell, from the axis's first step
  have st : ∀ x, 2 ≤ x → slot? x (C a b) = slot? (mas x) (if cap x = 2 then a else b) := fun x hx => by
    rw [slot?_cap hx]
  constructor
  · intro hl
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · rcases (H y).mp hy with e | ⟨x, hx, h4, hc, rfl⟩
      · exact absurd e (HoonSet.mem_empty _)
      · have := hl x hx; rw [st x (by omega), if_pos hc] at this; exact this
    · rcases (T y).mp hy with e | ⟨x, hx, h4, hc, rfl⟩
      · exact absurd e (HoonSet.mem_empty _)
      · have := hl x hx; rw [st x (by omega), if_neg hc] at this; exact this
  · intro ⟨la, lb⟩ x hx
    have x0 := n0 x hx
    by_cases x1 : x = 1
    · subst x1; simp
    have x2 : 2 ≤ x := by omega
    rw [st x x2]
    by_cases x23 : x = 2 ∨ x = 3
    · rw [mas_two_three x23]; split <;> simp
    by_cases hc : cap x = 2
    · rw [if_pos hc]; exact la _ ((H _).mpr (Or.inr ⟨x, hx, by omega, hc, rfl⟩))
    · rw [if_neg hc]; exact lb _ ((T _).mpr (Or.inr ⟨x, hx, by omega, hc, rfl⟩))

/-! ## The needs -/

theorem front_nil (o : Nat) (g : Gen Map) : Front o g g [] :=
  ⟨fun B fin hb => by simpa using hb, fun _ _ => rfl, rfl, rfl, Nat.le_refl _⟩

theorem must_spec {ned n : Need} {r : Nat} {g g' : Gen Map} (h : must ned g = some ((r, n), g')) :
    g' = { g with re := g'.re } ∧ g.re ≤ g'.re ∧
    (∀ y, NMem n y → NMem ned y ∨ (g.re ≤ y ∧ y < g'.re)) ∧
    (NMem ned r ∨ (g.re ≤ r ∧ r < g'.re)) ∧
    (∀ x, Comp.Fits n x ↔ Comp.Fits ned x) ∧
    (∀ (R : Map Noun) x, HoldsN n R x → SkaModel.read r R = some x ∧ HoldsN ned R x) ∧
    (Distinct ned → (∀ y, NMem ned y → y < g.re) → Distinct n) := by
  cases ned with
  | both x p q =>
    simp only [must, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact ⟨rfl, Nat.le_refl _, fun y hy => Or.inl hy, Or.inl (Or.inl rfl), fun _ => Iff.rfl,
      fun R x hx => ⟨(holds_both_top hx).1, hx⟩, fun d _ => d⟩
  | this x =>
    simp only [must, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact ⟨rfl, Nat.le_refl _, fun y hy => Or.inl hy, Or.inl rfl, fun _ => Iff.rfl,
      fun R x hx => ⟨hx, hx⟩, fun d _ => d⟩
  | pair p q =>
    simp only [must, bind_apply, re_apply, Option.bind_some, pure_apply, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    refine ⟨rfl, Nat.le_succ _, fun y hy => ?_, Or.inr ⟨Nat.le_refl _, Nat.lt_succ_self _⟩,
      fits_both_pair _ _ _, fun R x hx => holds_both_pair hx, fun d lo => ?_⟩
    · rcases hy with e | hy | hy
      · exact Or.inr ⟨by simp [e], by simp [e]⟩
      · exact Or.inl (Or.inl hy)
      · exact Or.inl (Or.inr hy)
    · exact ⟨d.1, d.2.1, d.2.2, fun hm => Nat.lt_irrefl _ (lo _ (Or.inl hm)),
        fun hm => Nat.lt_irrefl _ (lo _ (Or.inr hm))⟩
  | none =>
    simp only [must, bind_apply, re_apply, Option.bind_some, pure_apply, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    refine ⟨rfl, Nat.le_succ _, fun y hy => Or.inr ⟨by simp [NMem] at hy; simp [hy], by simp [NMem] at hy; simp [hy]⟩,
      Or.inr ⟨Nat.le_refl _, Nat.lt_succ_self _⟩, fun x => by simp [Comp.Fits], fun R x hx => ⟨hx, trivial⟩,
      fun _ _ => trivial⟩

theorem splitNeed_spec {ned : Need} {o : Nat} {g g' : Gen Map} {x : Need × Need}
    (h : splitNeed ned o g = some (x, g')) :
    g'.bo = g.bo ∧ g'.drop = g.drop ∧ g.re ≤ g'.re ∧
    (∀ o', o' ≠ o → HoonMap.get g'.blocks o' = HoonMap.get g.blocks o') ∧
    (∀ y, NMem x.1 y → NMem ned y ∨ (g.re ≤ y ∧ y < g'.re)) ∧
    (∀ y, NMem x.2 y → NMem ned y ∨ (g.re ≤ y ∧ y < g'.re)) ∧
    (Distinct ned → (∀ y, NMem ned y → y < g.re) →
      Distinct x.1 ∧ Distinct x.2 ∧ (∀ y, NMem x.1 y → ¬ NMem x.2 y) ∧
      (∀ a b, Comp.Fits ned (C a b) ↔ Comp.Fits x.1 a ∧ Comp.Fits x.2 b)) ∧
    (g.drop = false → ∃ A, Front o g g' A ∧ (Distinct ned → (∀ y, NMem ned y → y < g.re) →
      ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) gul st t (R : Map Noun) a b,
        HoldsN x.1 R a → HoldsN x.2 R b →
        ∃ R', Runs lib O c gul st t A R R' ∧ HoldsN ned R' (C a b) ∧
          ∀ y, ¬ NMem ned y → SkaModel.read y R' = SkaModel.read y R)) := by
  cases ned with
  | pair p q =>
    simp only [splitNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, rfl, Nat.le_refl _, fun _ _ => rfl, fun y hy => Or.inl (Or.inl hy),
      fun y hy => Or.inl (Or.inr hy), fun d _ => ⟨d.1, d.2.1, d.2.2, fun a b => Iff.rfl⟩,
      fun hd => ⟨[], front_nil o g, fun _ _ lib σ O c gul st t R a b ha hb => ⟨R, Runs.nil R, ⟨ha, hb⟩, fun _ _ => rfl⟩⟩⟩
  | none =>
    simp only [splitNeed, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, rfl, Nat.le_refl _, fun _ _ => rfl, fun y hy => hy.elim, fun y hy => hy.elim,
      fun d _ => ⟨trivial, trivial, fun _ h => h.elim, fun a b => by simp [Comp.Fits]⟩,
      fun hd => ⟨[], front_nil o g, fun _ _ lib σ O c gul st t R a b ha hb => ⟨R, Runs.nil R, trivial, fun _ _ => rfl⟩⟩⟩
  | this r =>
    simp only [splitNeed, bind_apply, re_apply, Option.bind_some] at h
    obtain ⟨⟨_, g1⟩, h1, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨e1, e2, e3, e4⟩ := addOps_gen h1
    simp only at e1 e2 e3
    refine ⟨e2, e3, by omega, e4, fun y hy => Or.inr ⟨by simp [NMem] at hy; omega, by simp [NMem] at hy; omega⟩,
      fun y hy => Or.inr ⟨by simp [NMem] at hy; omega, by simp [NMem] at hy; omega⟩,
      fun d lo => ⟨trivial, trivial, fun y a b => by simp [NMem] at a b; omega, fun a b => by simp [Comp.Fits]⟩,
      fun hd => ⟨_, front_re (front_re (front_addOps h1 hd)), fun _ lo lib σ O c gul st t R a b ha hb => ?_⟩⟩
    refine ⟨store r (C a b) R, runs_con ha hb, read_store_eq _ _ _, fun y hy => read_store_ne ?_ _ _⟩
    exact fun e => hy e
  | both r hh t =>
    simp only [splitNeed] at h
    obtain ⟨⟨r1, n1⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨⟨r2, n2⟩, g2, h2, h⟩ := bind_some h
    obtain ⟨_, g3, h3, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨G1, L1, M1, R1, F1, H1, D1⟩ := must_spec h1
    obtain ⟨G2, L2, M2, R2, F2, H2, D2⟩ := must_spec h2
    obtain ⟨e1, e2, e3, e4⟩ := addOps_gen h3
    have b1 : g1.bo = g.bo := by rw [G1]
    have b2 : g2.bo = g1.bo := by rw [G2]
    have d1 : g1.drop = g.drop := by rw [G1]
    have d2 : g2.drop = g1.drop := by rw [G2]
    have k1 : g1.blocks = g.blocks := by rw [G1]
    have k2 : g2.blocks = g1.blocks := by rw [G2]
    refine ⟨by rw [e2, b2, b1], by rw [e3, d2, d1], by omega, fun o' h' => by rw [e4 o' h', k2, k1],
      fun y hy => ?_, fun y hy => ?_, fun d lo => ?_, fun hd => ?_⟩
    · rcases M1 y hy with a | ⟨a, a'⟩
      · exact Or.inl (Or.inr (Or.inl a))
      · exact Or.inr ⟨a, by omega⟩
    · rcases M2 y hy with a | ⟨a, a'⟩
      · exact Or.inl (Or.inr (Or.inr a))
      · exact Or.inr ⟨by omega, by omega⟩
    · obtain ⟨dh, dt, dht, nh, nt⟩ := d
      refine ⟨D1 dh (fun y hy => lo y (Or.inr (Or.inl hy))),
        D2 dt (fun y hy => Nat.lt_of_lt_of_le (lo y (Or.inr (Or.inr hy))) L1), fun y a b => ?_,
        fun a b => by simp only [Comp.Fits, F1, F2]⟩
      rcases M1 y a with a | ⟨a, a'⟩ <;> rcases M2 y b with b | ⟨b, b'⟩
      · exact dht y a b
      · have := lo y (Or.inr (Or.inl a)); omega
      · have := lo y (Or.inr (Or.inr b)); omega
      · omega
    · have F0 : Front o g g2 [] := ⟨fun B fin hb => by rw [k2, k1]; simpa using hb,
        fun o' _ => by rw [k2, k1], by rw [b2, b1], by rw [d2, d1], by omega⟩
      refine ⟨_, F0.trans (front_addOps h3 (by rw [d2, d1]; exact hd)), fun d lo lib σ O c gul st tr R a b ha hb => ?_⟩
      obtain ⟨dh, dt, dht, nh, nt⟩ := d
      obtain ⟨ra, ha'⟩ := H1 R a ha
      obtain ⟨rb, hb'⟩ := H2 R b hb
      refine ⟨store r (C a b) R, by simpa using runs_con ra rb, ⟨read_store_eq _ _ _,
        HoldsN.agree hh (fun y hy => read_store_ne (fun e => by subst e; exact nh hy) _ _) ha',
        HoldsN.agree t (fun y hy => read_store_ne (fun e => by subst e; exact nt hy) _ _) hb'⟩,
        fun y hy => read_store_ne (fun e => hy (Or.inl e)) _ _⟩

end Comp
end SkaModel
end Formalization
