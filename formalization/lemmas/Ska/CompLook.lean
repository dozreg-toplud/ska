import lemmas.Ska.CompRun

/-!
# `+sure-require-look`

The need that `+sure-require-look` makes of a `sure`: the sure need with a
register for every looked-at axis it does not reach.  It holds a noun
exactly where the sure need does and the noun has the looked-at axes
(`sureRequireLook_spec`).
-/

set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

/-- What one step of `+sure-require-look` does. -/
structure LookOK (ned : Need) (axe : Nat) (g0 g1 : Gen Map) (ned' : Need) : Prop where
  gen : ∃ k, g1 = { g0 with re := k }
  le : g0.re ≤ g1.re
  holds : ∀ (regs : Map (Option Noun)) n, HoldsN ned' regs n → HoldsN ned regs n
  fits : ∀ n, Fits ned' n ↔ Fits ned n ∧ (slot? axe n).isSome
  mem : ∀ r, NMem ned' r → NMem ned r ∨ (g0.re ≤ r ∧ r < g1.re)
  dist : Distinct ned → (∀ r, NMem ned r → r < g0.re) → Distinct ned'
  shape : 2 ≤ axe → (∃ p q, ned' = Need.pair p q) ∨ (∃ r p q, ned' = Need.both r p q)
  one : axe = 1 → ned' = ned ∨ (ned = Need.none ∧ ∃ r, ned' = Need.this r)

theorem lookPath_step (ned : Need) {axe : Nat} (h2 : 2 ≤ axe) :
    lookPath ned axe = (if cap axe = 2 then do
        let x ← lookPath (split3 ned).2.1 (mas axe)
        pure (wrapN (split3 ned).1 (consNeed x (split3 ned).2.2))
      else do
        let x ← lookPath (split3 ned).2.2 (mas axe)
        pure (wrapN (split3 ned).1 (consNeed (split3 ned).2.1 x)) : CM Map Need) := by
  rw [lookPath.eq_def]
  simp only [show ¬ axe ≤ 1 by omega, dif_neg, not_false_eq_true]

theorem consNeed_holds {a b : Need} (h : ¬ (a = Need.none ∧ b = Need.none)) (regs : Map (Option Noun)) (n : Noun) :
    HoldsN (consNeed a b) regs n ↔ HoldsN (Need.pair a b) regs n := by
  simp [consNeed, h]

theorem wrap_holds (here : Option Nat) {x : Need} (hx : ∃ p q, x = Need.pair p q) (regs : Map (Option Noun)) (n : Noun) :
    HoldsN (wrapN here x) regs n ↔ (∀ r, here = some r → SkaModel.read r regs = some n) ∧ HoldsN x regs n := by
  obtain ⟨p, q, rfl⟩ := hx
  cases here with
  | none => simp [wrapN]
  | some r => cases n <;> simp [wrapN, HoldsN]

theorem wrap_fits (here : Option Nat) {x : Need} (hx : ∃ p q, x = Need.pair p q) (n : Noun) :
    Fits (wrapN here x) n ↔ Fits x n := by
  obtain ⟨p, q, rfl⟩ := hx
  cases here with
  | none => simp [wrapN]
  | some r => cases n <;> simp [wrapN, Fits]

theorem wrap_mem (here : Option Nat) {x : Need} (hx : ∃ p q, x = Need.pair p q) (r : Nat) :
    NMem (wrapN here x) r ↔ here = some r ∨ NMem x r := by
  obtain ⟨p, q, rfl⟩ := hx
  cases here with
  | none => simp [wrapN]
  | some r' => simp [wrapN, NMem, eq_comm]

theorem split3_holds : ∀ (ned : Need) (regs : Map (Option Noun)) (a b : Noun),
    (∀ r, (split3 ned).1 = some r → SkaModel.read r regs = some (C a b)) →
    HoldsN (split3 ned).2.1 regs a → HoldsN (split3 ned).2.2 regs b → HoldsN ned regs (C a b)
  | Need.none, _, _, _, _, _, _ => trivial
  | Need.this r, _, _, _, h, _, _ => h r rfl
  | Need.pair p q, _, _, _, _, ha, hb => ⟨ha, hb⟩
  | Need.both r p q, _, _, _, h, ha, hb => ⟨h r rfl, ha, hb⟩

theorem split3_fits : ∀ (ned : Need) (a b : Noun),
    Fits ned (C a b) ↔ Fits (split3 ned).2.1 a ∧ Fits (split3 ned).2.2 b
  | Need.none, _, _ => by simp [Fits, split3]
  | Need.this r, _, _ => by simp [Fits, split3]
  | Need.pair p q, _, _ => by simp [Fits, split3]
  | Need.both r p q, _, _ => by simp [Fits, split3]

theorem split3_mem : ∀ (ned : Need) (r : Nat),
    NMem ned r ↔ (split3 ned).1 = some r ∨ NMem (split3 ned).2.1 r ∨ NMem (split3 ned).2.2 r
  | Need.none, _ => by simp [NMem, split3]
  | Need.this r, _ => by simp [NMem, split3, eq_comm]
  | Need.pair p q, _ => by simp [NMem, split3]
  | Need.both r p q, _ => by simp [NMem, split3, eq_comm]

theorem split3_dist : ∀ (ned : Need), Distinct ned →
    Distinct (split3 ned).2.1 ∧ Distinct (split3 ned).2.2 ∧
    (∀ x, NMem (split3 ned).2.1 x → ¬ NMem (split3 ned).2.2 x) ∧
    ∀ r, (split3 ned).1 = some r → ¬ NMem (split3 ned).2.1 r ∧ ¬ NMem (split3 ned).2.2 r
  | Need.none, _ => by simp [split3, Distinct, NMem]
  | Need.this r, _ => by simp [split3, Distinct, NMem]
  | Need.pair p q, h => by simp only [split3, Distinct] at h ⊢; exact ⟨h.1, h.2.1, h.2.2, by simp⟩
  | Need.both r p q, h => by
    simp only [split3, Distinct] at h ⊢
    exact ⟨h.1, h.2.1, h.2.2.1, fun r' e => by cases e; exact ⟨h.2.2.2.1, h.2.2.2.2⟩⟩

theorem lookPath_ne_none : ∀ (axe : Nat), 1 ≤ axe → ∀ (ned ned' : Need) (g0 g1 : Gen Map),
    lookPath ned axe g0 = some (ned', g1) → ned' ≠ Need.none := by
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
  intro ha ned ned' g0 g1 h
  by_cases h1 : axe ≤ 1
  · rw [lookPath.eq_def] at h
    simp only [h1, dif_pos] at h
    cases ned <;> simp [bind_apply, re_apply, pure_apply] at h <;> (obtain ⟨rfl, _⟩ := h) <;> simp
  · rw [lookPath_step ned (by omega)] at h
    have ihm := ih (mas axe) (mas_lt axe (by omega)) (mas_pos axe (by omega))
    have fin : ∀ (here : Option Nat) (a b : Need), (a ≠ Need.none ∨ b ≠ Need.none) →
        wrapN here (consNeed a b) ≠ Need.none := by
      intro here a b hab
      have : consNeed a b = Need.pair a b := by
        unfold consNeed; rw [if_neg]; rintro ⟨h1, h2⟩; rcases hab with h | h <;> contradiction
      rw [this]; cases here <;> simp [wrapN]
    split at h
    · obtain ⟨x, g, h5, h6⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h6
      rw [← h6.1]; exact fin _ _ _ (Or.inl (ihm _ x g0 g h5))
    · obtain ⟨x, g, h5, h6⟩ := bind_some h
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h6
      rw [← h6.1]; exact fin _ _ _ (Or.inr (ihm _ x g0 g h5))

theorem consNeed_pair {a b : Need} (h : a ≠ Need.none ∨ b ≠ Need.none) : consNeed a b = Need.pair a b := by
  unfold consNeed; rw [if_neg]; rintro ⟨h1, h2⟩; rcases h with h | h <;> contradiction

/-- The step of the loop, from what the parts satisfy. -/
theorem lookStep_ok {ned hr tr : Need} {axe : Nat} {g0 g1 : Gen Map} (h2 : 2 ≤ axe)
    (gen : ∃ k, g1 = { g0 with re := k }) (le : g0.re ≤ g1.re)
    (nz : hr ≠ Need.none ∨ tr ≠ Need.none)
    (hh : ∀ (regs : Map (Option Noun)) a, HoldsN hr regs a → HoldsN (split3 ned).2.1 regs a)
    (ht : ∀ (regs : Map (Option Noun)) b, HoldsN tr regs b → HoldsN (split3 ned).2.2 regs b)
    (hf : ∀ a b, Fits hr a ∧ Fits tr b ↔ (Fits (split3 ned).2.1 a ∧ Fits (split3 ned).2.2 b) ∧
      (slot? axe (C a b)).isSome)
    (hm : ∀ r, NMem hr r ∨ NMem tr r → NMem (split3 ned).2.1 r ∨ NMem (split3 ned).2.2 r ∨
      (g0.re ≤ r ∧ r < g1.re))
    (hd : Distinct ned → (∀ r, NMem ned r → r < g0.re) → Distinct hr ∧ Distinct tr ∧
      (∀ x, NMem hr x → ¬ NMem tr x) ∧ ∀ r, (split3 ned).1 = some r → ¬ NMem hr r ∧ ¬ NMem tr r) :
    LookOK ned axe g0 g1 (wrapN (split3 ned).1 (consNeed hr tr)) := by
  rw [consNeed_pair nz]
  have hp : ∃ p q, Need.pair hr tr = Need.pair p q := ⟨_, _, rfl⟩
  refine ⟨gen, le, ?_, ?_, ?_, ?_, ?_, fun h => absurd h (by omega)⟩
  · intro regs n hn
    rw [wrap_holds _ hp] at hn
    obtain ⟨hr', hn⟩ := hn
    cases n with
    | atom _ => exact hn.elim
    | cell a b => exact split3_holds ned regs a b hr' (hh regs a hn.1) (ht regs b hn.2)
  · intro n
    rw [wrap_fits _ hp]
    cases n with
    | atom _ =>
      constructor
      · intro h; simp only [Fits] at h
      · intro ⟨_, h⟩; rw [slot?_cap h2] at h; simp at h
    | cell a b => simp only [Fits]; rw [hf a b, split3_fits]
  · intro r hr'
    rw [wrap_mem _ hp] at hr'
    rcases hr' with h | h
    · exact Or.inl ((split3_mem ned r).mpr (Or.inl h))
    · rcases hm r h with h' | h' | h'
      · exact Or.inl ((split3_mem ned r).mpr (Or.inr (Or.inl h')))
      · exact Or.inl ((split3_mem ned r).mpr (Or.inr (Or.inr h')))
      · exact Or.inr h'
  · intro hdn hb
    obtain ⟨d1, d2, d3, d4⟩ := hd hdn hb
    cases e : (split3 ned).1 with
    | none => simp only [wrapN]; exact ⟨d1, d2, d3⟩
    | some r =>
      have : wrapN (some r) (Need.pair hr tr) = Need.both r hr tr := by simp [wrapN]
      rw [this]; exact ⟨d1, d2, d3, (d4 r e).1, (d4 r e).2⟩
  · intro _
    cases (split3 ned).1 with
    | none => exact Or.inl ⟨_, _, rfl⟩
    | some r => exact Or.inr ⟨r, hr, tr, by simp [wrapN]⟩

theorem lookPath_spec : ∀ (axe : Nat), 1 ≤ axe → ∀ (ned ned' : Need) (g0 g1 : Gen Map),
    lookPath ned axe g0 = some (ned', g1) → LookOK ned axe g0 g1 ned' := by
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
  intro ha ned ned' g0 g1 h
  by_cases h1 : axe ≤ 1
  · have e1 : axe = 1 := by omega
    subst e1
    rw [lookPath.eq_def] at h
    simp only [show (1 : Nat) ≤ 1 from Nat.le_refl 1, dif_pos] at h
    cases ned with
    | none =>
      simp only [bind_apply, re_apply, pure_apply, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact { gen := ⟨_, rfl⟩, le := Nat.le_succ _, holds := fun _ _ _ => trivial,
              fits := fun n => by simp [Fits, slot?_one],
              mem := fun r hr => by simp only [NMem] at hr; subst hr; right; simp,
              dist := fun _ _ => trivial, shape := fun h => absurd h (by omega),
              one := fun _ => Or.inr ⟨rfl, _, rfl⟩ }
    | pair p q =>
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact { gen := ⟨g0.re, rfl⟩, le := Nat.le_refl _, holds := fun _ _ h => h,
              fits := fun n => by simp [slot?_one], mem := fun r hr => Or.inl hr,
              dist := fun h _ => h, shape := fun h => absurd h (by omega), one := fun _ => Or.inl rfl }
    | both r p q =>
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact { gen := ⟨g0.re, rfl⟩, le := Nat.le_refl _, holds := fun _ _ h => h,
              fits := fun n => by simp [slot?_one], mem := fun r hr => Or.inl hr,
              dist := fun h _ => h, shape := fun h => absurd h (by omega), one := fun _ => Or.inl rfl }
    | this r =>
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact { gen := ⟨g0.re, rfl⟩, le := Nat.le_refl _, holds := fun _ _ h => h,
              fits := fun n => by simp [slot?_one], mem := fun r hr => Or.inl hr,
              dist := fun h _ => h, shape := fun h => absurd h (by omega), one := fun _ => Or.inl rfl }
  have h2 : 2 ≤ axe := by omega
  have ihm := ih (mas axe) (mas_lt axe h2) (mas_pos axe h2)
  have hnz := lookPath_ne_none (Map := Map) (mas axe) (mas_pos axe h2)
  rw [lookPath_step ned h2] at h
  have d0 := split3_dist ned
  have m0 := split3_mem ned
  split at h
  · rename_i hc
    obtain ⟨x, g, h5, h6⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h6
    obtain ⟨rfl, rfl⟩ := h6
    have L := ihm _ x g0 g h5
    refine lookStep_ok h2 L.gen L.le (Or.inl (hnz _ _ _ _ h5)) (fun regs a h => L.holds regs a h)
      (fun _ _ h => h) (fun a b => by
        rw [L.fits, slot?_cap h2]; simp only [hc, if_true]
        exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨h1, h3⟩, h2⟩, fun ⟨⟨h1, h3⟩, h2⟩ => ⟨⟨h1, h2⟩, h3⟩⟩) ?_ ?_
    · intro r hr
      rcases hr with hr | hr
      · rcases L.mem r hr with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl hr)
    · intro hd hb
      obtain ⟨d1, d2, d3, d4⟩ := d0 hd
      have hbh : ∀ r, NMem (split3 ned).2.1 r → r < g0.re := fun r h => hb r ((m0 r).mpr (Or.inr (Or.inl h)))
      have hbt : ∀ r, NMem (split3 ned).2.2 r → r < g0.re := fun r h => hb r ((m0 r).mpr (Or.inr (Or.inr h)))
      refine ⟨L.dist d1 hbh, d2, fun y hy hy' => ?_, fun r e => ⟨fun hx => ?_, (d4 r e).2⟩⟩
      · rcases L.mem y hy with h | h
        · exact d3 y h hy'
        · have := hbt y hy'; omega
      · rcases L.mem r hx with h | h
        · exact (d4 r e).1 h
        · have := hb r ((m0 r).mpr (Or.inl e)); omega
  · rename_i hc
    have hc3 : cap axe = 3 := by rcases cap_cases axe h2 with e | e; exact absurd e hc; exact e
    obtain ⟨x, g, h5, h6⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h6
    obtain ⟨rfl, rfl⟩ := h6
    have L := ihm _ x g0 g h5
    refine lookStep_ok h2 L.gen L.le (Or.inr (hnz _ _ _ _ h5)) (fun _ _ h => h)
      (fun regs a h => L.holds regs a h) (fun a b => by
        rw [L.fits, slot?_cap h2]; simp only [hc3, show (3 : Nat) ≠ 2 by decide, if_false]
        exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩⟩) ?_ ?_
    · intro r hr
      rcases hr with hr | hr
      · exact Or.inl hr
      · rcases L.mem r hr with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
    · intro hd hb
      obtain ⟨d1, d2, d3, d4⟩ := d0 hd
      have hbh : ∀ r, NMem (split3 ned).2.1 r → r < g0.re := fun r h => hb r ((m0 r).mpr (Or.inr (Or.inl h)))
      have hbt : ∀ r, NMem (split3 ned).2.2 r → r < g0.re := fun r h => hb r ((m0 r).mpr (Or.inr (Or.inr h)))
      refine ⟨d1, L.dist d2 hbt, fun y hy hy' => ?_, fun r e => ⟨(d4 r e).1, fun hx => ?_⟩⟩
      · rcases L.mem y hy' with h | h
        · exact d3 y hy h
        · have := hbh y hy; omega
      · rcases L.mem r hx with h | h
        · exact (d4 r e).2 h
        · have := hb r ((m0 r).mpr (Or.inl e)); omega

/-- One step of the fold of `+sure-require-look`. -/
def lookStep (axe : Nat) (ned : Need) : CM Map Need :=
  if axe = 1 then pure ned else
  if axe = 0 then fun _ => Option.none else
  lookPath ned axe

theorem foldl_look (xs : List Nat) (m : CM Map Need) :
    xs.foldl (fun acc axe => acc >>= lookStep axe) m =
      m >>= fun n => xs.foldl (fun acc axe => acc >>= lookStep axe) (pure n) := by
  induction xs generalizing m with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih, bind_assoc]
    congr 1; funext n
    rw [ih (pure n >>= lookStep x), pure_bind]

theorem sureRequireLook_eq (sur : Sure S) :
    (sureRequireLook sur : CM Map Need) =
      (HoonSet.toList sur.lok).foldl (fun acc axe => acc >>= lookStep axe) (pure sur.ned) := rfl

/-- What `+sure-require-look` makes. -/
structure SureOK (ned0 : Need) (xs : List Nat) (g0 g1 : Gen Map) (ned' : Need) : Prop where
  gen : ∃ k, g1 = { g0 with re := k }
  le : g0.re ≤ g1.re
  holds : ∀ (regs : Map (Option Noun)) n, HoldsN ned' regs n → HoldsN ned0 regs n
  fits : ∀ n, Fits ned' n ↔ Fits ned0 n ∧ ∀ x ∈ xs, (slot? x n).isSome
  mem : ∀ r, NMem ned' r → NMem ned0 r ∨ (g0.re ≤ r ∧ r < g1.re)
  dist : Distinct ned0 → (∀ r, NMem ned0 r → r < g0.re) → Distinct ned'
  same : (∀ x ∈ xs, x = 1) → ned' = ned0
  big : (∃ x ∈ xs, 2 ≤ x) → (∃ p q, ned' = Need.pair p q) ∨ (∃ r p q, ned' = Need.both r p q)
  keep : ((∃ p q, ned0 = Need.pair p q) ∨ (∃ r p q, ned0 = Need.both r p q)) →
    (∃ p q, ned' = Need.pair p q) ∨ (∃ r p q, ned' = Need.both r p q)

theorem foldLook_spec : ∀ (xs : List Nat) (ned0 ned' : Need) (g0 g1 : Gen Map),
    (xs.foldl (fun acc axe => acc >>= lookStep axe) (pure ned0) : CM Map Need) g0 = some (ned', g1) →
    SureOK ned0 xs g0 g1 ned' := by
  intro xs
  induction xs with
  | nil =>
    intro ned0 ned' g0 g1 h
    simp only [List.foldl_nil, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨⟨g0.re, rfl⟩, Nat.le_refl _, fun _ _ h => h, fun n => (by simp), fun r h => Or.inl h,
      fun h _ => h, fun _ => rfl, fun h => (by obtain ⟨x, hx, _⟩ := h; simp at hx), fun h => h⟩
  | cons x xs ih =>
    intro ned0 ned' g0 g1 h
    rw [List.foldl_cons, foldl_look] at h
    obtain ⟨n1, g', h1, h2⟩ := bind_some h
    rw [pure_bind] at h1
    have I := ih n1 ned' g' g1 h2
    -- the step at x
    have S1 : (2 ≤ x ∧ LookOK ned0 x g0 g' n1) ∨ (x = 1 ∧ n1 = ned0 ∧ g' = g0) := by
      unfold lookStep at h1
      by_cases e1 : x = 1
      · simp only [e1, if_true, pure_apply, Option.some.injEq, Prod.mk.injEq] at h1
        exact Or.inr ⟨e1, h1.1.symm, h1.2.symm⟩
      · by_cases e0 : x = 0
        · simp [e1, e0] at h1
        · simp only [e1, e0, if_false] at h1
          exact Or.inl ⟨by omega, lookPath_spec x (by omega) ned0 n1 g0 g' h1⟩
    rcases S1 with ⟨hx2, L⟩ | ⟨e1, rfl, rfl⟩
    · obtain ⟨k1, rfl⟩ := L.gen
      obtain ⟨k2, rfl⟩ := I.gen
      refine ⟨⟨k2, rfl⟩, Nat.le_trans L.le I.le, fun regs n h => L.holds regs n (I.holds regs n h), ?_, ?_, ?_,
        ?_, ?_, ?_⟩
      · intro n
        rw [I.fits, L.fits]
        simp only [List.mem_cons, forall_eq_or_imp]
        exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩⟩
      · intro r hr
        rcases I.mem r hr with h | h
        · rcases L.mem r h with h' | h'
          · exact Or.inl h'
          · exact Or.inr ⟨h'.1, Nat.lt_of_lt_of_le h'.2 I.le⟩
        · exact Or.inr ⟨Nat.le_trans L.le h.1, h.2⟩
      · intro hd hb
        refine I.dist (L.dist hd hb) fun r hr => ?_
        rcases L.mem r hr with h | h
        · exact Nat.lt_of_lt_of_le (hb r h) L.le
        · exact h.2
      · intro hall
        have e1 := hall x (List.mem_cons_self ..)
        omega
      · intro _
        exact I.keep (L.shape hx2)
      · intro _
        exact I.keep (L.shape hx2)
    · refine ⟨I.gen, I.le, I.holds, ?_, I.mem, I.dist, ?_, ?_, I.keep⟩
      · intro n
        rw [I.fits]
        simp only [List.mem_cons, forall_eq_or_imp, e1, slot?_one, Option.isSome_some, true_and]
      · intro hall
        exact I.same fun y hy => hall y (List.mem_cons_of_mem _ hy)
      · intro ⟨y, hy, h2⟩
        rcases List.mem_cons.mp hy with e | e
        · omega
        · exact I.big ⟨y, e, h2⟩

theorem sureRequireLook_spec {sur : Sure S} {ned' : Need} {g0 g1 : Gen Map}
    (h : sureRequireLook sur g0 = some (ned', g1)) : SureOK sur.ned (HoonSet.toList sur.lok) g0 g1 ned' :=
  foldLook_spec _ _ _ _ _ (by rw [← sureRequireLook_eq]; exact h)

theorem holdsS_of_sure {sur : Sure S} {ned' : Need} {g0 g1 : Gen Map}
    (L : SureOK sur.ned (HoonSet.toList sur.lok) g0 g1 ned') {regs : Map (Option Noun)} {n : Noun}
    (h : HoldsN ned' regs n) : HoldsS sur regs n :=
  ⟨L.holds regs n h, ((L.fits n).mp (fits_of_holds _ h)).2⟩

theorem fits_sure {sur : Sure S} {ned' : Need} {g0 g1 : Gen Map}
    (L : SureOK sur.ned (HoonSet.toList sur.lok) g0 g1 ned') (n : Noun) : Fits ned' n ↔ FitsS sur n :=
  L.fits n

end Comp
end SkaModel
end Formalization
