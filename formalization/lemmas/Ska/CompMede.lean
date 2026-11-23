import lemmas.Ska.CompLook

/-!
# `+mede`: a constant into the registers of a need

`medeLoop_spec`: the ops `+mede` puts in front of its block either put the
constant in the registers of the need, where the constant has the need's
shape, or crash.  `run_n1_next_ok`: the case `%1` of `run` for `%next`.
-/

set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

theorem addOps_spec {o : Nat} {ops : List Pole} {g g' : Gen Map} {u : Unit}
    (h : addOps o ops g = some (u, g')) (hd : g.drop = false) :
    ∃ b, HoonMap.get g.blocks o = some b ∧
      g' = { g with blocks := HoonMap.put g.blocks o { b with body := ops ++ b.body } } := by
  unfold addOps at h
  rw [if_neg (by simp [hd])] at h
  obtain ⟨b, hb, he⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at he
  exact ⟨b, hb, he.2.symm⟩

/-- What ops put in front of a block do: the block grew by `A` in front, and
nothing else changed but registers allocated. -/
structure Front (o : Nat) (g0 g1 : Gen Map) (A : List Pole) : Prop where
  blk : ∀ B fin, HoonMap.get g0.blocks o = some ⟨[], B, fin⟩ →
    HoonMap.get g1.blocks o = some ⟨[], A ++ B, fin⟩
  other : ∀ o', o' ≠ o → HoonMap.get g1.blocks o' = HoonMap.get g0.blocks o'
  bo : g1.bo = g0.bo
  drop : g1.drop = g0.drop
  le : g0.re ≤ g1.re

theorem Front.trans {o : Nat} {g0 g1 g2 : Gen Map} {A1 A2 : List Pole} (a : Front o g0 g1 A1)
    (b : Front o g1 g2 A2) : Front o g0 g2 (A2 ++ A1) :=
  ⟨fun B fin h => by rw [List.append_assoc]; exact b.blk _ _ (a.blk B fin h),
    fun o' h => (b.other o' h).trans (a.other o' h), b.bo.trans a.bo, b.drop.trans a.drop,
    Nat.le_trans a.le b.le⟩

theorem front_addOps {o : Nat} {ops : List Pole} {g g' : Gen Map} {u : Unit}
    (h : addOps o ops g = some (u, g')) (hd : g.drop = false) : Front o g g' ops := by
  obtain ⟨b, hb, rfl⟩ := addOps_spec h hd
  exact ⟨fun B fin h' => by rw [hb] at h'; cases h'; simp [HoonMap.get_put],
    fun o' h' => by simp [HoonMap.get_put, h'], rfl, rfl, Nat.le_refl _⟩

theorem front_re {o : Nat} {g g' : Gen Map} {A : List Pole} (h : Front o { g with re := g.re + 1 } g' A) :
    Front o g g' A :=
  ⟨h.blk, h.other, h.bo, h.drop, Nat.le_trans (Nat.le_succ _) h.le⟩

section
variable {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ} {t : Trace}

theorem crashes_imm_cel (n : Nat) (r : Nat) (fill : List Pole) (regs : Map Noun) :
    Crashes lib O c gul st t (Pole.imm (A n) r :: Pole.cel r :: fill) regs := by
  have h1 : Pole.imm (A n) r :: Pole.cel r :: fill = [Pole.imm (A n) r] ++ ([Pole.cel r] ++ fill) := rfl
  rw [h1]
  exact Crashes.append_right (runs_imm _ _ _) (Crashes.append_left (crashes_cel (read_store_eq r _ _)))

end

/-- The ops of `+crash-need` with an immediate atom always crash. -/
theorem crashNeed_imm_spec {o n : Nat} {ned : Need} {g0 g1 : Gen Map} {u : Unit}
    (h : crashNeed o (Sum.inl n) ned g0 = some (u, g1)) (hd : g0.drop = false) :
    ∃ A, Front o g0 g1 A ∧ ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) gul st t regs,
      Crashes lib O c gul st t A regs := by
  simp only [crashNeed, bind_apply, re_apply, Option.bind_some] at h
  exact ⟨_, front_re (front_addOps h hd), fun _ _ _ _ _ _ _ regs => crashes_imm_cel _ _ _ regs⟩

/-- **The loop of `+mede`.** -/
theorem medeLoop_spec {o : Nat} : ∀ (som : Noun) (ned : Need) (g0 g1 : Gen Map) (u : Unit),
    medeLoop o som ned g0 = some (u, g1) → g0.drop = false →
    ∃ A, Front o g0 g1 A ∧ ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (c : Straight Map) gul st t regs,
      Distinct ned →
      (Fits ned som → ∃ regs', Runs lib O c gul st t A regs regs' ∧ HoldsN ned regs' som ∧
        ∀ r, ¬ NMem ned r → SkaModel.read r regs' = SkaModel.read r regs) ∧
      (¬ Fits ned som → Crashes lib O c gul st t A regs)
  | som, Need.none, g0, g1, u, h, _ => by
    simp only [medeLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact ⟨[], ⟨fun B fin h => h, fun _ _ => rfl, rfl, rfl, Nat.le_refl _⟩, fun _ _ _ _ _ _ _ regs _ =>
      ⟨fun _ => ⟨regs, Runs.nil regs, trivial, fun _ _ => rfl⟩, fun hn => absurd trivial hn⟩⟩
  | som, Need.this r, g0, g1, u, h, hd => by
    simp only [medeLoop] at h
    refine ⟨_, front_addOps h hd, fun _ _ _ _ _ _ _ regs _ => ⟨fun _ => ⟨_, runs_imm som r regs,
      read_store_eq r som regs, fun r' hr' => read_store_ne (by simpa [NMem] using hr') _ _⟩,
      fun hn => absurd trivial hn⟩⟩
  | Noun.atom n, Need.pair p q, g0, g1, u, h, hd => by
    simp only [medeLoop] at h
    obtain ⟨A, hF, hC⟩ := crashNeed_imm_spec h hd
    exact ⟨A, hF, fun lib σ O c gul st t regs _ => ⟨fun hf => by simp [Fits] at hf,
      fun _ => hC lib σ O c gul st t regs⟩⟩
  | Noun.atom n, Need.both r p q, g0, g1, u, h, hd => by
    simp only [medeLoop] at h
    obtain ⟨A, hF, hC⟩ := crashNeed_imm_spec h hd
    exact ⟨A, hF, fun lib σ O c gul st t regs _ => ⟨fun hf => by simp [Fits] at hf,
      fun _ => hC lib σ O c gul st t regs⟩⟩
  | Noun.cell a b, Need.pair p q, g0, g1, u, h, hd => by
    simp only [medeLoop] at h
    obtain ⟨u1, g', h1, h2⟩ := bind_some h
    obtain ⟨A1, F1, S1⟩ := medeLoop_spec a p g0 g' u1 h1 hd
    obtain ⟨A2, F2, S2⟩ := medeLoop_spec b q g' g1 u h2 (F1.drop.trans hd)
    refine ⟨A2 ++ A1, F1.trans F2, fun lib σ O c gul st t regs hdist => ?_⟩
    obtain ⟨dp, dq, dpq⟩ := hdist
    refine ⟨fun hf => ?_, fun hn => ?_⟩
    · obtain ⟨regs2, R2, H2, K2⟩ := (S2 lib σ O c gul st t regs dq).1 hf.2
      obtain ⟨regs1, R1, H1, K1⟩ := (S1 lib σ O c gul st t regs2 dp).1 hf.1
      refine ⟨regs1, R2.append R1, ⟨H1, HoldsN.agree q (fun x hx => K1 x fun hp => dpq x hp hx) H2⟩,
        fun r hr => (K1 r fun h => hr (Or.inl h)).trans (K2 r fun h => hr (Or.inr h))⟩
    · by_cases hq : Fits q b
      · obtain ⟨regs2, R2, _, _⟩ := (S2 lib σ O c gul st t regs dq).1 hq
        exact Crashes.append_right R2 ((S1 lib σ O c gul st t regs2 dp).2 fun hp => hn ⟨hp, hq⟩)
      · exact Crashes.append_left ((S2 lib σ O c gul st t regs dq).2 hq)
  | Noun.cell a b, Need.both r p q, g0, g1, u, h, hd => by
    simp only [medeLoop] at h
    obtain ⟨u0, g', h0, h'⟩ := bind_some h
    have F0 := front_addOps h0 hd
    obtain ⟨u1, g'', h1, h2⟩ := bind_some h'
    obtain ⟨A1, F1, S1⟩ := medeLoop_spec a p g' g'' u1 h1 (F0.drop.trans hd)
    obtain ⟨A2, F2, S2⟩ := medeLoop_spec b q g'' g1 u h2 (F1.drop.trans (F0.drop.trans hd))
    refine ⟨A2 ++ (A1 ++ [Pole.imm (C a b) r]), (F0.trans F1).trans F2, fun lib σ O c gul st t regs hdist => ?_⟩
    obtain ⟨dp, dq, dpq, rp, rq⟩ := hdist
    refine ⟨fun hf => ?_, fun hn => ?_⟩
    · obtain ⟨regs2, R2, H2, K2⟩ := (S2 lib σ O c gul st t regs dq).1 hf.2
      obtain ⟨regs1, R1, H1, K1⟩ := (S1 lib σ O c gul st t regs2 dp).1 hf.1
      refine ⟨_, R2.append (R1.append (runs_imm _ r regs1)), ⟨read_store_eq _ _ _, ?_, ?_⟩, ?_⟩
      · exact HoldsN.agree p (fun x hx => read_store_ne (fun e => rp (by rw [← e]; exact hx)) _ _) H1
      · exact HoldsN.agree q (fun x hx => (read_store_ne (fun e => rq (by rw [← e]; exact hx)) _ _).trans
          (K1 x fun hp => dpq x hp hx)) H2
      · intro r' hr'
        rw [read_store_ne (fun e => hr' (Or.inl e))]
        exact (K1 r' fun h => hr' (Or.inr (Or.inl h))).trans (K2 r' fun h => hr' (Or.inr (Or.inr h)))
    · by_cases hq : Fits q b
      · obtain ⟨regs2, R2, _, _⟩ := (S2 lib σ O c gul st t regs dq).1 hq
        exact Crashes.append_right R2
          (Crashes.append_left ((S1 lib σ O c gul st t regs2 dp).2 fun hp => hn ⟨hp, hq⟩))
      · exact Crashes.append_left ((S2 lib σ O c gul st t regs dq).2 hq)

end Comp
end SkaModel
end Formalization
