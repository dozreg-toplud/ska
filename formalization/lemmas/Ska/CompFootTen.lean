import lemmas.Ska.CompFootCons
import lemmas.Ska.CompInto

/-!
# Fact (i) for `run`: the case `[10 [a v] q]`, and `run_foot`

* `intoRec_wr`: the `%con` ops of the walk of `+into-need` write registers
  of the need being taken apart or registers allocated in the walk, and none
  of the donor's or the recipient's need.  The op at a step writes the top
  register of a `%this` or `%both`, which is in neither half; the deeper ops
  write the fresh registers the step made for the half on the path.
* `intoNeed_wr`, `into_wr`: the same through the loop and its one
  `+add-ops`, and through the block `+into` emits.
* `foot_n10`: the case `%10` of `run_foot_of`: `+simple-next`, `+into`,
  then the runs of the donor `v` and the recipient `q` and the `+copy`
  (`foot_copyTail` with the donor as the operand that runs first).
* `run_foot`: fact (i) of every run of `run`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **The `%con` ops of the walk of `+into-need` write registers of the need
or fresh ones, and none of the donor's or the recipient's need.** -/
theorem intoRec_wr : ∀ (axe : Nat) (ned : Need) (g g' : Gen Map) (d r : Need) (ops : List Pole),
    1 ≤ axe → intoRec axe ned g = some ((d, r, ops), g') → Distinct ned → NB g.re ned →
    OpsWr (fun y => (NMem ned y ∨ (g.re ≤ y ∧ y < g'.re)) ∧ ¬ NMem d y ∧ ¬ NMem r y) ops := by
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
  intro ned g g' d r ops ha h dn lo
  rw [intoRec] at h
  by_cases h1 : axe ≤ 1
  · rw [dif_pos h1] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
    exact opsWr_nil _
  rw [dif_neg h1] at h
  have lt := mas_lt axe (by omega)
  have m1 : 1 ≤ mas axe := mas_pos axe (by omega)
  generalize decide (cap axe = 2) = b at h
  cases ned with
  | none =>
    obtain ⟨⟨d0, r0, ops0⟩, g1, e1, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
    have W := ih _ lt _ _ _ _ _ _ m1 e1 trivial (nb_none _)
    refine W.mono fun y hy => ⟨hy.1, hy.2.1, fun e => ?_⟩
    rcases (nmem_side b _ _ y).mp e with e | e
    · exact hy.2.2 e
    · exact e.elim
  | this x0 =>
    obtain ⟨l, gl, hl, h⟩ := bind_some h
    rw [re_apply] at hl; simp only [Option.some.injEq, Prod.mk.injEq] at hl; obtain ⟨rfl, rfl⟩ := hl
    obtain ⟨l', gl', hl', h⟩ := bind_some h
    rw [re_apply] at hl'; simp only [Option.some.injEq, Prod.mk.injEq] at hl'; obtain ⟨rfl, rfl⟩ := hl'
    obtain ⟨⟨d0, r0, ops0⟩, g1, e1, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
    have I := intoRec_ok _ _ _ _ _ _ _ m1 e1
    have L : g.re + 2 ≤ g1.re := I.le
    have md : ∀ y, NMem d0 y → y = (if b then g.re else g.re + 1) ∨ (g.re + 2 ≤ y ∧ y < g1.re) := I.md
    have mr : ∀ y, NMem r0 y → y = (if b then g.re else g.re + 1) ∨ (g.re + 2 ≤ y ∧ y < g1.re) := I.mr
    have x0l : x0 < g.re := lo x0 rfl
    have nn : ∀ y, NMem (Need.this (if b then g.re + 1 else g.re)) y ↔ y = (if b then g.re + 1 else g.re) :=
      fun y => Iff.rfl
    have W := ih _ lt _ _ _ _ _ _ m1 e1 trivial (fun y hy => by
      have : y = if b then g.re else g.re + 1 := hy
      show y < g.re + 1 + 1
      cases b <;> simp at this <;> omega)
    have W' : OpsWr (fun y => (y = (if b then g.re else g.re + 1) ∨ (g.re + 2 ≤ y ∧ y < g1.re)) ∧
        ¬ NMem d0 y ∧ ¬ NMem r0 y) ops0 := W.mono fun y hy => ⟨hy.1, hy.2⟩
    refine OpsWr.append (W'.mono fun y hy => ⟨Or.inr ?fr, hy.2.1, fun e => ?nr⟩) (opsWr_one fun y hy => ?op)
    case fr =>
      rcases hy.1 with e | e
      · cases b <;> simp at e <;> omega
      · omega
    case nr =>
      rcases (nmem_side b _ _ y).mp e with e | e
      · exact hy.2.2 e
      · rw [nn] at e
        rcases hy.1 with e' | e' <;> cases b <;> simp at e e' <;> omega
    case op =>
      simp only [poleWr, List.mem_cons, List.mem_nil_iff, or_false] at hy
      subst hy
      refine ⟨Or.inl rfl, fun e => ?_, fun e => ?_⟩
      · rcases md _ e with e' | e' <;> cases b <;> (try simp at e') <;> omega
      · rcases (nmem_side b _ _ _).mp e with e | e
        · rcases mr _ e with e' | e' <;> cases b <;> (try simp at e') <;> omega
        · rw [nn] at e
          cases b <;> simp at e <;> omega
  | pair p q =>
    obtain ⟨⟨d0, r0, ops0⟩, g1, e1, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
    have sub_new : ∀ y, NMem (if b then p else q) y → NMem (Need.pair p q) y := fun y hy => by
      cases b <;> simp at hy <;> simp [NMem, hy]
    have sub_old : ∀ y, NMem (if b then q else p) y → NMem (Need.pair p q) y := fun y hy => by
      cases b <;> simp at hy <;> simp [NMem, hy]
    have dno : Distinct (if b then p else q) ∧ Distinct (if b then q else p) ∧
        ∀ y, NMem (if b then p else q) y → ¬ NMem (if b then q else p) y := by
      obtain ⟨d1, d2, d3⟩ := dn
      cases b
      · exact ⟨d2, d1, fun y a c => d3 y c a⟩
      · exact ⟨d1, d2, d3⟩
    have W := ih _ lt _ _ _ _ _ _ m1 e1 dno.1 (fun y hy => lo y (sub_new y hy))
    refine W.mono fun y hy => ⟨hy.1.imp (sub_new y) id, hy.2.1, fun e => ?_⟩
    rcases (nmem_side _ _ _ y).mp e with e | e
    · exact hy.2.2 e
    · rcases hy.1 with e' | e'
      · exact dno.2.2 y e' e
      · have := lo y (sub_old y e); omega
  | both x0 hh tt =>
    obtain ⟨⟨rl, nl⟩, g1, h1, h⟩ := bind_some h
    obtain ⟨⟨rt, nt⟩, g2, h2, h⟩ := bind_some h
    obtain ⟨⟨d0, r0, ops0⟩, g3, e1, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
    obtain ⟨G1, L1, M1, Q1, F1, H1, D1⟩ := must_spec h1
    obtain ⟨G2, L2, M2, Q2, F2, H2, D2⟩ := must_spec h2
    have I := intoRec_ok _ _ _ _ _ _ _ m1 e1
    simp only at I
    have L3 := I.le
    obtain ⟨dh, dt, dht, nh, nt'⟩ := dn
    have x0l : x0 < g.re := lo x0 (Or.inl rfl)
    have loh : ∀ y, NMem hh y → y < g.re := fun y hy => lo y (Or.inr (Or.inl hy))
    have lot : ∀ y, NMem tt y → y < g.re := fun y hy => lo y (Or.inr (Or.inr hy))
    have Dl := D1 dh loh
    have Dt := D2 dt (fun y hy => Nat.lt_of_lt_of_le (lot y hy) L1)
    -- the registers of the two halves
    have snl : ∀ y, NMem nl y → NMem (Need.both x0 hh tt) y ∨ (g.re ≤ y ∧ y < g2.re) := fun y hy => by
      rcases M1 y hy with e | e
      · exact Or.inl (Or.inr (Or.inl e))
      · exact Or.inr ⟨e.1, by omega⟩
    have snt : ∀ y, NMem nt y → NMem (Need.both x0 hh tt) y ∨ (g.re ≤ y ∧ y < g2.re) := fun y hy => by
      rcases M2 y hy with e | e
      · exact Or.inl (Or.inr (Or.inr e))
      · exact Or.inr ⟨by omega, e.2⟩
    have xnl : ¬ NMem nl x0 := fun e => by
      rcases M1 x0 e with e | e
      · exact nh e
      · omega
    have xnt : ¬ NMem nt x0 := fun e => by
      rcases M2 x0 e with e | e
      · exact nt' e
      · omega
    have k : ∀ y, NMem nl y → ¬ NMem nt y := fun y a c => by
      rcases M1 y a with e | e <;> rcases M2 y c with e' | e'
      · exact dht y e e'
      · have := loh y e; omega
      · have := lot y e'; omega
      · omega
    have lnl : ∀ y, NMem nl y → y < g2.re := fun y hy => by
      rcases M1 y hy with e | e
      · have := loh y e; omega
      · omega
    have lnt : ∀ y, NMem nt y → y < g2.re := fun y hy => by
      rcases M2 y hy with e | e
      · have := lot y e; omega
      · exact e.2
    have dnew : Distinct (if b then nl else nt) := by cases b <;> assumption
    have lonew : ∀ y, NMem (if b then nl else nt) y → y < g2.re := fun y hy => by
      cases b
      · exact lnt y hy
      · exact lnl y hy
    have W := ih _ lt _ _ _ _ _ _ m1 e1 dnew lonew
    simp only at W
    have md : ∀ y, NMem d0 y → NMem (if b then nl else nt) y ∨ (g2.re ≤ y ∧ y < g3.re) := I.md
    have mr : ∀ y, NMem r0 y → NMem (if b then nl else nt) y ∨ (g2.re ≤ y ∧ y < g3.re) := I.mr
    refine OpsWr.append (W.mono fun y hy => ⟨?fr, hy.2.1, fun e => ?nr⟩) (opsWr_one fun y hy => ?op)
    case fr =>
      rcases hy.1 with e | e
      · cases b
        · exact (snt y e).imp id fun e => ⟨e.1, by omega⟩
        · exact (snl y e).imp id fun e => ⟨e.1, by omega⟩
      · exact Or.inr ⟨by omega, e.2⟩
    case nr =>
      rcases (nmem_side _ _ _ y).mp e with e | e
      · exact hy.2.2 e
      · rcases hy.1 with e' | e'
        · cases b
          · exact k y e e'
          · exact k y e' e
        · cases b
          · have := lnl y e; omega
          · have := lnt y e; omega
    case op =>
      simp only [poleWr, List.mem_cons, List.mem_nil_iff, or_false] at hy
      subst hy
      refine ⟨Or.inl (Or.inl rfl), fun e => ?_, fun e => ?_⟩
      · rcases md _ e with e' | e'
        · cases b
          · exact xnt e'
          · exact xnl e'
        · omega
      · rcases (nmem_side _ _ _ _).mp e with e | e
        · rcases mr _ e with e' | e'
          · cases b
            · exact xnt e'
            · exact xnl e'
          · omega
        · cases b
          · exact xnl e
          · exact xnt e

/-- **`+into-need` writes registers of its need or fresh ones, and none of
the two needs it returns.** -/
theorem intoNeed_wr {axe : Nat} {ned : Need} {o : Nat} {g0 g2 : Gen Map} {x : Need × Need}
    (h : intoNeed axe ned o g0 = some (x, g2)) (dn : Distinct ned) (lo : NB g0.re ned) :
    WroteIn (fun y => (NMem ned y ∨ (g0.re ≤ y ∧ y < g2.re)) ∧ ¬ NMem x.1 y ∧ ¬ NMem x.2 y) g0 g2 := by
  simp only [intoNeed] at h
  by_cases a0 : axe = 0
  · simp [a0] at h
  rw [if_neg a0] at h
  by_cases a1 : axe = 1
  · rw [if_pos a1] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact WroteIn.refl _ _
  rw [if_neg a1] at h
  obtain ⟨d, r, ops', g1, e1, e2, rfl⟩ := intoLoop_rec _ _ _ _ _ _ _ h
  have I := intoRec_ok axe ned g0 g1 d r ops' (by omega) e1
  have W := intoRec_wr axe ned g0 g1 d r ops' (by omega) e1 dn lo
  have q1 := (addOps_gen e2).1
  rw [List.append_nil] at e2
  exact (wroteIn_of_gen I.gen).trans (wroteIn_addOps (W.mono fun y hy => ⟨by rw [q1]; exact hy.1, hy.2⟩) e2)

/-- **`+into` writes registers of the goal's need or fresh ones, and none of
the donor's or the recipient's need.** -/
theorem into_wr {laz : Sure S} {th : Jmp} {axe : Nat} {g g' : Gen Map} {don rec : Sure S} {o : Nat}
    (dn : Distinct laz.ned) (lo : NB g.re laz.ned) (h : into ⟨laz, th⟩ axe g = some ((don, rec, o), g')) :
    WroteIn (fun y => (NMem laz.ned y ∨ (g.re ≤ y ∧ y < g'.re)) ∧ ¬ NMem don.ned y ∧ ¬ NMem rec.ned y) g g' := by
  simp only [into] at h
  obtain ⟨o', g0, h0, h⟩ := bind_some h
  have W0 := wroteIn_emit (Q := fun y => (NMem laz.ned y ∨ (g.re ≤ y ∧ y < g'.re)) ∧ ¬ NMem don.ned y ∧
    ¬ NMem rec.ned y) (blobWr_fin _ _) h0
  rw [emit_apply] at h0
  simp only [Option.some.injEq, Prod.mk.injEq] at h0
  obtain ⟨rfl, rfl⟩ := h0
  obtain ⟨⟨sd, sr⟩, g1, h2, h⟩ := bind_some h
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
  simp only [intoSure] at h2
  obtain ⟨⟨ld, lr⟩, hl, h2⟩ := Option.bind_eq_some_iff.mp h2
  obtain ⟨⟨⟨nd, nr⟩, g2⟩, h3, h4⟩ := Option.map_eq_some_iff.mp h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
  exact W0.trans (intoNeed_wr h3 dn lo)

/-- **Fact (i) of `[10 [a v] q]`**, for every goal: `+simple-next` writes
nothing, `+into` the goal's need and fresh registers, and the two runs and
the `+copy` as for cons, with the donor `v` run first. -/
theorem foot_n10 (a : Nat) {v q : Nomm} (ihv : FootIH S Map v) (ihq : FootIH S Map q) :
    FootIH S Map (Nomm.n10 a v q) := by
  intro goal g g' nex hd hg hD h
  simp only [run] at h
  obtain ⟨⟨laz0, th0⟩, g2, h2, h⟩ := bind_some h
  obtain ⟨k2, n2⟩ := keeps_simpleNext hd hg h2
  have w2 := wr_simpleNext (fun x => x < g'.re ∧ (g.re ≤ x ∨ GMem goal x) ∧ ¬ NMem nex.laz.ned x) h2
  have d2 := k2.dropF hd
  have F0 : (∀ x, NMem laz0.ned x → g.re ≤ x ∨ GMem goal x) ∧ Distinct laz0.ned := by
    cases goal with
    | next laz th =>
      simp only [simpleNext, pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      exact ⟨fun x hx => Or.inr hx, hD⟩
    | done =>
      simp only [simpleNext] at h2
      obtain ⟨r, g5, h5, h2⟩ := bind_some h2
      obtain ⟨e5, _, _⟩ := keeps_re h5
      obtain ⟨o, g6, h6, h2⟩ := bind_some h2
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      exact ⟨fun x hx => Or.inl (by simp only [lazyReg, NMem] at hx; omega), trivial⟩
    | pick z o =>
      simp only [simpleNext] at h2
      obtain ⟨r, g5, h5, h2⟩ := bind_some h2
      obtain ⟨e5, _, _⟩ := keeps_re h5
      obtain ⟨o', g6, h6, h2⟩ := bind_some h2
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      exact ⟨fun x hx => Or.inl (by simp only [lazyReg, NMem] at hx; omega), trivial⟩
  obtain ⟨⟨don, rec, o⟩, g3, h3, h⟩ := bind_some h
  obtain ⟨k3, nd, nr⟩ := keeps_into d2 n2 h3
  have d3 := k3.dropF d2
  have W3 := into_wr F0.2 n2.1 h3
  obtain ⟨_, _, _, _, md, mr, _, Sm⟩ := into_ok h3
  obtain ⟨Dd, Dr, Ddr, _, _⟩ := Sm F0.2 n2.1
  simp only at h
  obtain ⟨nexR, g3', hpr, h⟩ := bind_some h
  obtain ⟨rfl, rfl⟩ := past_some hpr
  obtain ⟨nexDon, g4, h4, h⟩ := bind_some h
  obtain ⟨nexDon', g4', hpd, h⟩ := bind_some h
  obtain ⟨rfl, rfl⟩ := past_some hpd
  obtain ⟨nexRec, g5, h5, h⟩ := bind_some h
  obtain ⟨WT, sT, dT, lT, _⟩ := foot_copyTail (hs := rec) (ts := don) ihq ihv d3 nr nd Dr Dd
    (fun x e e' => Ddr x e' e) (jmpIn_jmp0 _ _) h4 h5 h
  have l2 := k2.le
  have l3 := k3.le
  have A : ∀ x, (g3.re ≤ x ∨ NMem rec.ned x ∨ NMem don.ned x) → g.re ≤ x ∨ GMem goal x := fun x hx => by
    rcases hx with e | e | e
    · exact Or.inl (by omega)
    · rcases mr x e with e' | e'
      · exact F0.1 x e'
      · exact Or.inl (by omega)
    · rcases md x e with e' | e'
      · exact F0.1 x e'
      · exact Or.inl (by omega)
  have B : ∀ x, ((NMem laz0.ned x ∨ (g2.re ≤ x ∧ x < g3.re)) ∧ ¬ NMem don.ned x ∧ ¬ NMem rec.ned x) →
      x < g'.re ∧ (g.re ≤ x ∨ GMem goal x) ∧ ¬ NMem nex.laz.ned x := fun x hx => by
    have xl : x < g3.re := by
      rcases hx.1 with e | e
      · have := n2.1 x e; omega
      · exact e.2
    refine ⟨by omega, ?_, fun e => ?_⟩
    · rcases hx.1 with e | e
      · exact F0.1 x e
      · exact Or.inl (by omega)
    · rcases sT x e with e' | e' | e'
      · omega
      · exact hx.2.2 e'
      · exact hx.2.1 e'
  exact ⟨(w2.trans (W3.mono B)).trans (WT.mono fun x hx => ⟨hx.1, A x hx.2.1, hx.2.2⟩),
    fun x hx => A x (sT x hx), dT⟩

/-- **Fact (i) of every run of `run`**: from a state that does not drop, for
a goal whose registers are below `re` and whose need is distinct, the code
writes only registers below the end that the run allocated or the goal
needs, and none of the result's sure need, which is distinct and made of
those registers. -/
theorem run_foot : ∀ nm : Nomm, FootIH S Map nm :=
  run_foot_of (fun _ _ ihp ihq => foot_cons ihp ihq) (fun _ _ ihp ihq => foot_n5 ihp ihq)
    (fun a _ _ ihv ihq => foot_n10 a ihv ihq)

end Comp
end SkaModel
end Formalization
