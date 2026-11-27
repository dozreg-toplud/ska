import lemmas.Ska.RawInvMede

/-!
# Raw `+comp` output: the run-level invariant

README Gaps 14.  **`RawIH nm`**: every run of `run nm` (the model of `+run` of
`CompModel.lean`, the first fragment) from a state with `SI` whose
definitions avoid the registers of its goal keeps `SI`, and every register
live at its entry is a register of its result's need or a register live at
its goal's continuation that the goal does not name (`GLive`).  Code is
built backwards, so this is what lets the run that comes before define a
register before every read of it.

The facts of track C that the sub-runs give are gathered by `sub_facts`
(`run_keeps`, `run_foot`, `run_down`).  `raw_tail`: a block and then the run
of an operand for a fresh register (`%3`, `%4`); `raw_binTail`: the two runs
and the `+copy` of cons, `%5` and `%10`.  The cases: `raw_n0`, `raw_n1`,
`raw_n7`, `raw_n4`, `raw_n3`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]
variable {X : Map Blob → Prop} [XOK X] {ρ : Nat → Nat} {lo : Nat}

/-- **The run-level invariant** of one nomm. -/
def RawIH (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (nm : Nomm) : Prop :=
  ∀ (goal : CGoal S) (g0 g1 : Comp.Gen Map) (nex : Next S), SI g0 → GoalIn g0.re goal → GDist goal →
    GJ g0.bo goal → GArgs goal → (∀ r, Defd g0.blocks r → ¬ GMem goal r) →
    run nm goal g0 = some (nex, g1) →
    SI g1 ∧ ∀ r, Live g1.blocks nex.th.there r → NMem nex.laz.ned r ∨ GLive g0.blocks goal r

/-- **The run-level invariant with ranks** (`SIP` in place of `SI`): what
`run_rawP` proves for every nomm, for every carried predicate `X`, rank `ρ`
and label `lo`. -/
def RawIHP (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (X : Map Blob → Prop)
    (ρ : Nat → Nat) (lo : Nat) (nm : Nomm) : Prop :=
  ∀ (goal : CGoal S) (g0 g1 : Comp.Gen Map) (nex : Next S), SIP X ρ lo g0 → GoalIn g0.re goal → GDist goal →
    GJ g0.bo goal → GArgs goal → (∀ r, Defd g0.blocks r → ¬ GMem goal r) →
    run nm goal g0 = some (nex, g1) →
    SIP X ρ lo g1 ∧ ∀ r, Live g1.blocks nex.th.there r → NMem nex.laz.ned r ∨ GLive g0.blocks goal r

/-- What track C gives of a run. -/
theorem sub_facts {nm : Nomm} {goal : CGoal S} {g0 g1 : Comp.Gen Map} {nex : Next S}
    (h : SIP X ρ lo g0) (hg : GoalIn g0.re goal) (hD : GDist goal) (hj : GJ g0.bo goal) (ha : GArgs goal)
    (hr : run nm goal g0 = some (nex, g1)) :
    g0.re ≤ g1.re ∧ g0.bo ≤ g1.bo ∧ NB g1.re nex.laz.ned ∧ Distinct nex.laz.ned ∧
    (∀ x, NMem nex.laz.ned x → g0.re ≤ x ∨ GMem goal x) ∧
    (∀ x, Defd g1.blocks x → Defd g0.blocks x ∨ (x < g1.re ∧ (g0.re ≤ x ∨ GMem goal x) ∧ ¬ NMem nex.laz.ned x)) ∧
    nex.th.args = [] ∧ 1 ≤ nex.th.there ∧ nex.th.there < g1.bo := by
  obtain ⟨K, N⟩ := run_keeps nm goal g0 g1 nex h.drop hg hr
  have F := run_foot nm goal g0 g1 nex h.drop hg hD hr
  have D := run_down nm goal g0 g1 nex hj h.bo1 h.drop hr
  refine ⟨K.le, K.bo, N.1, F.dist, F.sure, fun x d => defd_of_wroteIn F.wr d, ?_, D.lo, D.hi⟩
  rcases D.entry with ⟨b, -, -, e⟩ | e
  · exact e
  · cases goal with
    | next laz th => simp only [GoalJ] at e; rw [e]; exact ha
    | pick z o =>
      simp only [GoalJ] at e
      rcases e with e | e
      · rw [e]; exact ha.1
      · rw [e]; exact ha.2
    | done => exact e.elim

/-- The goal of the run that follows another: its result's need. -/
theorem defd_next {goal : CGoal S} {g0 g1 : Comp.Gen Map} {nex : Next S} (h : SIP X ρ lo g0)
    (hf : ∀ r, Defd g0.blocks r → ¬ GMem goal r)
    (sure : ∀ x, NMem nex.laz.ned x → g0.re ≤ x ∨ GMem goal x)
    (dd : ∀ x, Defd g1.blocks x → Defd g0.blocks x ∨ (x < g1.re ∧ (g0.re ≤ x ∨ GMem goal x) ∧ ¬ NMem nex.laz.ned x)) :
    ∀ x, Defd g1.blocks x → ¬ NMem nex.laz.ned x := fun x d hm => by
  rcases dd x d with d | d
  · rcases sure x hm with e | e
    · have := h.defd_lt d; omega
    · exact hf x d e
  · exact d.2.2 hm

/-! ## A block, then the run of an operand -/

/-- **A block, then the run of an operand for a fresh register `x`**: what
is live at the run's entry is in its result's need, or live at the block
and not `x`. -/
theorem raw_tail {p : Nomm} (ihp : RawIHP S Map X ρ lo p) {g g1 g2 : Comp.Gen Map} {b : Blob} {x o : Nat} {nex : Next S}
    (h : SIP X ρ lo g) (E : EmitOK g b) (hx : x < g.re) (hnx : ¬ Defd g.blocks x) (hxb : x ∉ blockDefs b)
    (he : (emit b : CM Map Nat) g = some (o, g1))
    (hr : run p (CGoal.next (lazyReg x) (jmp0 o)) g1 = some (nex, g2)) :
    SIP X ρ lo g2 ∧ ∀ y, Live g2.blocks nex.th.there y → NMem nex.laz.ned y ∨
      ((BlockRF b y ∨ ∃ j ∈ getJmps b.fin, Live g.blocks j.there y ∧ y ∉ blockDefs b) ∧ y ≠ x) := by
  obtain ⟨S1, rfl, e1, q1, bo1⟩ := sip_emit h E he
  have hl := h.none (Nat.le_refl g.bo)
  obtain ⟨S2, L2⟩ := ihp (CGoal.next (lazyReg x) (jmp0 g.bo)) g1 g2 nex S1 ⟨nb_this (by omega), jmpIn_jmp0 _ _⟩ trivial
    ⟨by simp [jmp0]; have := h.bo1; omega, by simp [jmp0]; omega⟩ rfl
    (fun r d hm => by
      simp only [GMem, lazyReg, NMem] at hm; subst hm
      rw [e1, defd_put hl] at d
      rcases d with d | d
      · exact hnx d
      · exact hxb d) hr
  refine ⟨S2, fun y hy => ?_⟩
  rcases L2 y hy with e | ⟨hl', hn'⟩
  · exact Or.inl e
  · have he' : ∀ k, k < g.bo → HoonMap.get g1.blocks k = HoonMap.get g.blocks k := fun k hk => by
      rw [e1, get_put_ne (by omega)]
    exact Or.inr ⟨live_unfoldP (by rw [e1]; exact get_put_self) (h.below g.bo) he' E.jd hl',
      fun e => hn' (by simp [lazyReg, NMem, e])⟩

/-! ## The leaves -/

theorem nmem_fromPath_of (ned : Need) : ∀ (axe : Nat) (r : Nat), NMem ned r → NMem (fromPath ned axe) r := by
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
  intro r hr
  rw [fromPath.eq_def]
  split
  · exact hr
  · rename_i h1
    split
    · exact Or.inl (ih _ (mas_lt axe (by omega)) r hr)
    · exact Or.inr (ih _ (mas_lt axe (by omega)) r hr)

theorem raw_n0 (ax : Nat) : RawIHP S Map X ρ lo (Nomm.n0 ax) := by
  intro goal g0 g1 nex h hg hD hj ha hf hr
  simp only [run] at hr
  by_cases h0 : ax = 0
  · rw [if_pos h0] at hr
    obtain ⟨S1, -, -, nl, -⟩ := raw_bomb h hr
    exact ⟨S1, fun r hl => absurd hl (nl r)⟩
  rw [if_neg h0] at hr
  obtain ⟨nx, g2, h2, hr⟩ := bind_some hr
  obtain ⟨S2, -, -, -, -, -, -, L2, -, -⟩ := raw_simpleNext h hj ha hg h2
  by_cases h1 : ax = 1
  · rw [if_pos h1] at hr
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨S2, L2⟩
  rw [if_neg h1] at hr
  cases ef : «from» ax nx.laz with
  | none => rw [ef] at hr; cases hr
  | some laz =>
    rw [ef] at hr
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    refine ⟨S2, fun r hl => ?_⟩
    rcases L2 r hl with e | e
    · left
      simp only [«from», fromSure] at ef
      rw [if_neg h0] at ef
      by_cases hn : nx.laz.ned = Need.none
      · rw [hn] at e; exact e.elim
      · rw [if_neg hn] at ef
        simp only [Option.some.injEq] at ef
        rw [← ef]; exact nmem_fromPath_of _ _ _ e
    · exact Or.inr e

theorem raw_n1 (k : Noun) : RawIHP S Map X ρ lo (Nomm.n1 k) := by
  intro goal g0 g1 nex h hg hD hj ha hf hr
  cases goal with
  | done =>
    simp only [run] at hr
    obtain ⟨r, g2, h2, hr⟩ := bind_some hr
    obtain ⟨S2, rfl, q2, b2, o2⟩ := sip_re h h2
    obtain ⟨o, g3, h3, hr⟩ := bind_some hr
    obtain ⟨S3, rfl, e3, -, -⟩ := sip_emit S2 (emitOK_immDon S2 (by omega)
      (fun d => by rw [b2] at d; have := h.defd_lt d; omega)) h3
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨S3, fun r hl => absurd hl (live_immDon (by rw [e3]; exact get_put_self))⟩
  | pick z o =>
    simp only [run] at hr
    by_cases e0 : k = A 0
    · rw [if_pos e0] at hr
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨h, fun r hl => Or.inr (Or.inl hl)⟩
    rw [if_neg e0] at hr
    by_cases e1 : k = A 1
    · rw [if_pos e1] at hr
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨h, fun r hl => Or.inr (Or.inr hl)⟩
    rw [if_neg e1] at hr
    obtain ⟨S1, -, -, nl, -⟩ := raw_bomb h hr
    exact ⟨S1, fun r hl => absurd hl (nl r)⟩
  | next laz th =>
    simp only [run] at hr
    obtain ⟨o, g2, h2, hr⟩ := bind_some hr
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨S2, rfl, -, -, -, L2, -⟩ := raw_mede h hD hg.1 ha hj.2 (fun y hy d => hf y d hy) h2
    exact ⟨S2, fun r hl => Or.inr (L2 r hl)⟩

/-! ## `[7 p q]` -/

theorem raw_n7 {p q : Nomm} (ihp : RawIHP S Map X ρ lo p) (ihq : RawIHP S Map X ρ lo q) : RawIHP S Map X ρ lo (Nomm.n7 p q) := by
  intro goal g0 g1 nex h hg hD hj ha hf hr
  simp only [run] at hr
  obtain ⟨nq, g2, h2, hr⟩ := bind_some hr
  obtain ⟨S2, L2⟩ := ihq goal g0 g2 nq h hg hD hj ha hf h2
  obtain ⟨l2, b2, nb2, d2, s2, dd2, a2, lo2, hi2⟩ := sub_facts h hg hD hj ha h2
  obtain ⟨S1, L1⟩ := ihp (CGoal.next nq.laz nq.th) g2 g1 nex S2 ⟨nb2, fun x hx => by rw [a2] at hx; cases hx⟩ d2
    ⟨lo2, hi2⟩ a2 (defd_next h hf s2 dd2) hr
  refine ⟨S1, fun r hl => ?_⟩
  rcases L1 r hl with e | ⟨hl', hn⟩
  · exact Or.inl e
  · rcases L2 r hl' with e | e
    · exact absurd e hn
    · exact Or.inr e

/-! ## `%4` and `%3` -/

/-- A block of one op that defines a fresh register, and an end without
arguments. -/
theorem emitOK_one {g : Comp.Gen Map} {op : Pole} {fin : Termin} {d : Nat} (h : SIP X ρ lo g)
    (hd : aliasDst op = some d) (hr : ∀ x ∈ Comp.poleRegs op, x < g.re) (hnd : ¬ Defd g.blocks d)
    (ht : trOp op = false) (ha : ∀ j ∈ getJmps fin, j.args = []) (hj : ∀ j ∈ getJmps fin, j.there < g.bo)
    (hf : FinIn (· < g.re) fin) : EmitOK g ⟨[], [op], fin⟩ :=
  emitOK_of rfl ha hj (regsIn_one hr) hf (by simp [defsOf, hd])
    (fun y hy => by simp [defsOf, hd] at hy; subst hy; exact hnd) (fun q hq => by simp at hq; subst hq; exact ht)

/-- The block of `%4`: it reads `arg` first, and defines `pro`, which its end
reads. -/
theorem blockRF_inc {arg pro y : Nat} {fin : Termin} (hf : ∀ x ∈ finRegs fin, x = pro)
    (h : BlockRF ⟨[], [Pole.inc arg pro], fin⟩ y) : y = arg := by
  obtain ⟨-, h⟩ := h
  rcases h with h | ⟨hn, h⟩
  · simp only [OpsRF, reads_inc] at h
    rcases h with h | ⟨-, h⟩
    · exact h
    · exact h.elim
  · exact absurd (by rw [hf y h]; simp [defsOf, aliasDst]) hn

theorem blockDefs_inc {arg pro y : Nat} {fin : Termin} :
    y ∈ blockDefs ⟨[], [Pole.inc arg pro], fin⟩ ↔ y = pro := by simp [blockDefs, aliasDst]

theorem raw_n4 {p : Nomm} (ihp : RawIHP S Map X ρ lo p) : RawIHP S Map X ρ lo (Nomm.n4 p) := by
  intro goal g0 g1 nex h hg hD hj ha hf hr
  cases goal with
  | done =>
    simp only [run] at hr
    obtain ⟨pro, g2, h2, hr⟩ := bind_some hr
    obtain ⟨S2, rfl, q2, b2, o2⟩ := sip_re h h2
    obtain ⟨arg, g3, h3, hr⟩ := bind_some hr
    obtain ⟨S3, rfl, q3, b3, o3⟩ := sip_re S2 h3
    obtain ⟨o, g4, h4, hr⟩ := bind_some hr
    have nd : ∀ x, g0.re ≤ x → ¬ Defd g3.blocks x := fun x hx d => by
      rw [b3, b2] at d; have := h.defd_lt d; omega
    obtain ⟨S1, L1⟩ := raw_tail ihp S3 (emitOK_one S3 rfl (fun x hx => by simp [Comp.poleRegs] at hx; omega)
      (nd _ (Nat.le_refl _)) rfl (fun j hj => by simp [getJmps] at hj) (fun j hj => by simp [getJmps] at hj)
      (by simp [FinIn]; omega)) (by omega) (nd _ (by omega)) (by rw [blockDefs_inc]; omega) h4 hr
    refine ⟨S1, fun y hy => ?_⟩
    rcases L1 y hy with e | ⟨e | ⟨j, hj', -⟩, hne⟩
    · exact Or.inl e
    · exact absurd (blockRF_inc (fun x hx => by simpa [finRegs] using hx) e) hne
    · simp [getJmps] at hj'
  | pick z o =>
    simp only [GJ] at hj
    simp only [run] at hr
    obtain ⟨pro, g2, h2, hr⟩ := bind_some hr
    obtain ⟨S2, rfl, q2, b2, o2⟩ := sip_re h h2
    obtain ⟨arg, g3, h3, hr⟩ := bind_some hr
    obtain ⟨S3, rfl, q3, b3, o3⟩ := sip_re S2 h3
    obtain ⟨o', g4, h4, hr⟩ := bind_some hr
    have nd : ∀ x, g0.re ≤ x → ¬ Defd g3.blocks x := fun x hx d => by
      rw [b3, b2] at d; have := h.defd_lt d; omega
    obtain ⟨S1, L1⟩ := raw_tail ihp S3 (emitOK_one S3 rfl (fun x hx => by simp [Comp.poleRegs] at hx; omega)
      (nd _ (Nat.le_refl _)) rfl
      (fun j hj' => by simp [getJmps] at hj'; rcases hj' with rfl | rfl; exact ha.1; exact ha.2)
      (fun j hj' => by simp [getJmps] at hj'; rcases hj' with rfl | rfl <;> omega)
      (by simp [FinIn, JmpIn, ha.1, ha.2]; omega)) (by omega) (nd _ (by omega)) (by rw [blockDefs_inc]; omega) h4 hr
    refine ⟨S1, fun y hy => ?_⟩
    rcases L1 y hy with e | ⟨e | ⟨j, hj', hl, -⟩, hne⟩
    · exact Or.inl e
    · exact absurd (blockRF_inc (fun x hx => by simpa [finRegs, jmpRegs, ha.1, ha.2] using hx) e) hne
    · rw [b3, b2] at hl
      simp [getJmps] at hj'
      rcases hj' with rfl | rfl
      · exact Or.inr (Or.inl hl)
      · exact Or.inr (Or.inr hl)
  | next laz th =>
    have hjt : th.there < g0.bo := hj.2
    simp only [run] at hr
    obtain ⟨a, g2, h2, hr⟩ := bind_some hr
    obtain ⟨S2, l2, bo2, ha2, fr2, cn, cs⟩ := raw_collapse h hg.1 hj.2 (fun y hy d => hf y d hy) h2
    obtain ⟨⟨pro, th'⟩, g3, h3, hr⟩ := bind_some hr
    have P : SIP X ρ lo g3 ∧ g2.re ≤ g3.re ∧ pro < g3.re ∧ ¬ Defd g3.blocks pro ∧ th' < g3.bo ∧ g3.blocks = g2.blocks ∧
        ∀ y, Live g3.blocks th' y → y = pro ∨ (Live g0.blocks th.there y ∧ ¬ NMem laz.ned y) := by
      cases a with
      | some x =>
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
        obtain ⟨rfl, rfl⟩ := h3
        obtain ⟨-, rl, nd, tl, -, lv⟩ := cs pro th' rfl
        exact ⟨S2, Nat.le_refl _, rl, nd, tl, rfl, lv⟩
      | none =>
        obtain ⟨hn0, rfl⟩ := cn rfl
        simp only at h3
        obtain ⟨r, g4, h4, h3⟩ := bind_some h3
        obtain ⟨S4, rfl, q4, b4, o4⟩ := sip_re S2 h4
        rw [if_pos ha2] at h3
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h3
        refine ⟨S4, by omega, by omega, fun d => by rw [b4] at d; have := h.defd_lt d; omega, by omega, b4,
          fun y hl => Or.inr ⟨by rw [b4] at hl; exact hl, by rw [hn0]; exact id⟩⟩
    obtain ⟨S3, l3, prl, pnd, tl, b3, lv3⟩ := P
    obtain ⟨arg, g4, h4, hr⟩ := bind_some hr
    obtain ⟨S4, rfl, q4, b4, o4⟩ := sip_re S3 h4
    obtain ⟨o, g5, h5, hr⟩ := bind_some hr
    obtain ⟨S1, L1⟩ := raw_tail ihp S4 (emitOK_one S4 rfl (fun x hx => by simp [Comp.poleRegs] at hx; omega)
      (by rw [b4]; exact pnd) rfl (fun j hj' => by simp [getJmps] at hj'; rw [hj']; rfl)
      (fun j hj' => by simp [getJmps] at hj'; rw [hj']; simp [jmp0]; omega) (by simp [FinIn, JmpIn, jmp0]))
      (by omega) (fun d => by rw [b4] at d; have := S3.defd_lt d; omega) (by rw [blockDefs_inc]; omega) h5 hr
    refine ⟨S1, fun y hy => ?_⟩
    rcases L1 y hy with e | ⟨e | ⟨j, hj', hl, hn'⟩, hne⟩
    · exact Or.inl e
    · exact absurd (blockRF_inc (fun x hx => by simp [finRegs, jmpRegs, jmp0] at hx) e) hne
    · simp [getJmps] at hj'; subst hj'
      rw [b4] at hl
      rcases lv3 y hl with e | e
      · exact absurd e (fun e' => hn' (by rw [blockDefs_inc]; exact e'))
      · exact Or.inr e

/-- The block of `%3`: a test of a fresh register. -/
theorem blockRF_clq {r y : Nat} {z o : Jmp} (hz : z.args = []) (ho : o.args = [])
    (h : BlockRF ⟨[], [], Termin.clq r z o⟩ y) : y = r := by
  rw [blockRF_fin] at h; simpa [finRegs, jmpRegs, hz, ho] using h

theorem emitOK_clq {g : Comp.Gen Map} {r : Nat} {z o : Jmp} (hr : r < g.re) (hz : z.args = []) (ho : o.args = [])
    (hzl : z.there < g.bo) (hol : o.there < g.bo) : EmitOK g ⟨[], [], Termin.clq r z o⟩ :=
  emitOK_of rfl (fun j hj => by simp [getJmps] at hj; rcases hj with rfl | rfl; exact hz; exact ho)
    (fun j hj => by simp [getJmps] at hj; rcases hj with rfl | rfl <;> assumption) (RegsIn.nil _)
    (by simp [FinIn, JmpIn, hz, ho]; exact hr) (by simp [defsOf]) (fun y hy => by simp [defsOf] at hy)
    (fun _ h => absurd h List.not_mem_nil)

theorem raw_n3 {p : Nomm} (ihp : RawIHP S Map X ρ lo p) : RawIHP S Map X ρ lo (Nomm.n3 p) := by
  intro goal g0 g1 nex h hg hD hj ha hf hr
  cases goal with
  | done =>
    simp only [run] at hr
    obtain ⟨⟨o0, o1⟩, g2, h2, hr⟩ := bind_some hr
    obtain ⟨S2, l2, rfl, rfl, bo2, fr2, n0, n1, dd2⟩ := raw_doneBlocks h h2
    obtain ⟨r, g3, h3, hr⟩ := bind_some hr
    obtain ⟨S3, rfl, q3, b3, o3⟩ := sip_re S2 h3
    obtain ⟨oc, g4, h4, hr⟩ := bind_some hr
    obtain ⟨S1, L1⟩ := raw_tail ihp S3 (emitOK_clq (show g2.re < g3.re by omega) rfl rfl
      (show (jmp0 g0.bo).there < g3.bo by simp [jmp0]; omega) (show (jmp0 (g0.bo + 1)).there < g3.bo by simp [jmp0]; omega))
      (show g2.re < g3.re by omega) (fun d => by rw [b3] at d; have := S2.defd_lt d; omega)
      (by simp [blockDefs, defsOf]) h4 hr
    refine ⟨S1, fun y hy => ?_⟩
    rcases L1 y hy with e | ⟨e | ⟨j, hj', hl, -⟩, hne⟩
    · exact Or.inl e
    · exact absurd (blockRF_clq rfl rfl e) hne
    · rw [b3] at hl
      simp [getJmps] at hj'
      rcases hj' with rfl | rfl
      · exact absurd hl (n0 y)
      · exact absurd hl (n1 y)
  | pick z o =>
    simp only [GJ] at hj
    simp only [run] at hr
    obtain ⟨r, g3, h3, hr⟩ := bind_some hr
    obtain ⟨S3, rfl, q3, b3, o3⟩ := sip_re h h3
    obtain ⟨oc, g4, h4, hr⟩ := bind_some hr
    obtain ⟨S1, L1⟩ := raw_tail ihp S3 (emitOK_clq (by omega) ha.1 ha.2 (by omega) (by omega))
      (by omega) (fun d => by rw [b3] at d; have := h.defd_lt d; omega) (by simp [blockDefs, defsOf]) h4 hr
    refine ⟨S1, fun y hy => ?_⟩
    rcases L1 y hy with e | ⟨e | ⟨j, hj', hl, -⟩, hne⟩
    · exact Or.inl e
    · exact absurd (blockRF_clq ha.1 ha.2 e) hne
    · rw [b3] at hl
      simp [getJmps] at hj'
      rcases hj' with rfl | rfl
      · exact Or.inr (Or.inl hl)
      · exact Or.inr (Or.inr hl)
  | next laz th =>
    simp only [run] at hr
    by_cases hne : noneEquivalent laz = true
    · rw [if_pos hne] at hr
      exact ihp _ g0 g1 nex h hg hD hj ha hf hr
    rw [if_neg hne] at hr
    obtain ⟨a, g2, h2, hr⟩ := bind_some hr
    obtain ⟨S2, l2, bo2, ha2, fr2, cn, cs⟩ := raw_collapse h hg.1 hj.2 (fun y hy d => hf y d hy) h2
    cases a with
    | none => cases hr
    | some x =>
      obtain ⟨r, o⟩ := x
      obtain ⟨-, rl, nd, tl, -, lv⟩ := cs r o rfl
      simp only at hr
      obtain ⟨⟨z, o'⟩, g3, h3, hr⟩ := bind_some hr
      obtain ⟨S3, q3, bo3, rfl, rfl, fr3, lz, lo', -⟩ := raw_forl S2 rl nd tl h3
      obtain ⟨r', g4, h4, hr⟩ := bind_some hr
      obtain ⟨S4, rfl, q4, b4, o4⟩ := sip_re S3 h4
      obtain ⟨oc, g5, h5, hr⟩ := bind_some hr
      obtain ⟨S1, L1⟩ := raw_tail ihp S4 (emitOK_clq (by omega) rfl rfl (by simp [jmp0]; omega)
        (by simp [jmp0]; omega)) (by omega) (fun d => by rw [b4] at d; have := S3.defd_lt d; omega)
        (by simp [blockDefs, defsOf]) h5 hr
      refine ⟨S1, fun y hy => ?_⟩
      rcases L1 y hy with e | ⟨e | ⟨j, hj', hl, -⟩, hne'⟩
      · exact Or.inl e
      · exact absurd (blockRF_clq rfl rfl e) hne'
      · rw [b4] at hl
        simp [getJmps] at hj'
        have hl' : y ≠ r ∧ Live g2.blocks o y := by
          rcases hj' with rfl | rfl
          · exact lz y hl
          · exact lo' y hl
        rcases lv y hl'.2 with e | e
        · exact absurd e hl'.1
        · exact Or.inr e

/-! ## The two runs and the copy -/

/-- **The two runs and the `+copy` of cons, `%5` and `%10`**: `q` for `ts`
into `j`, `p` for `hs` into `q`'s code, the copy of their needs. -/
theorem raw_binTail {p q : Nomm} (ihp : RawIHP S Map X ρ lo p) (ihq : RawIHP S Map X ρ lo q) {hs ts : Sure S} {j : Jmp}
    {g2 g3 g4 g1 : Comp.Gen Map} {nex2 nex1 nex : Next S}
    (h : SIP X ρ lo g2) (nh : NB g2.re hs.ned) (nt : NB g2.re ts.ned) (dh : Distinct hs.ned) (dt : Distinct ts.ned)
    (ap : ∀ x, NMem hs.ned x → ¬ NMem ts.ned x) (ha : j.args = []) (hj1 : 1 ≤ j.there) (hj : j.there < g2.bo)
    (hf : ∀ x, Defd g2.blocks x → ¬ NMem hs.ned x ∧ ¬ NMem ts.ned x)
    (h3 : run q (CGoal.next ts j) g2 = some (nex2, g3))
    (h4 : run p (CGoal.next hs nex2.th) g3 = some (nex1, g4))
    (h5 : copy nex1 nex2.laz g4 = some (nex, g1)) :
    SIP X ρ lo g1 ∧ ∀ x, Live g1.blocks nex.th.there x → NMem nex.laz.ned x ∨
      (Live g2.blocks j.there x ∧ ¬ NMem hs.ned x ∧ ¬ NMem ts.ned x) := by
  have gq : GoalIn g2.re (CGoal.next ts j) := ⟨nt, fun x hx => by rw [ha] at hx; cases hx⟩
  obtain ⟨S3, L3⟩ := ihq (CGoal.next ts j) g2 g3 nex2 h gq dt ⟨hj1, hj⟩ ha (fun r d hm => (hf r d).2 hm) h3
  obtain ⟨l3, b3, nb3, d3, s3, dd3, a3, lo3, hi3⟩ := sub_facts h gq dt ⟨hj1, hj⟩ ha h3
  have gp : GoalIn g3.re (CGoal.next hs nex2.th) := ⟨nh.mono l3, fun x hx => by rw [a3] at hx; cases hx⟩
  have fp : ∀ r, Defd g3.blocks r → ¬ GMem (CGoal.next hs nex2.th) r := fun r d hm => by
    rcases dd3 r d with d | ⟨_, e, _⟩
    · exact (hf r d).1 hm
    · rcases e with e | e
      · have := nh r hm; omega
      · exact ap r hm e
  obtain ⟨S4, L4⟩ := ihp (CGoal.next hs nex2.th) g3 g4 nex1 S3 gp dh ⟨lo3, hi3⟩ a3 fp h4
  obtain ⟨l4, b4, nb4, d4, s4, dd4, a4, lo4, hi4⟩ := sub_facts S3 gp dh ⟨lo3, hi3⟩ a3 h4
  have m1 : ∀ x, NMem nex1.laz.ned x → g3.re ≤ x ∨ NMem hs.ned x := s4
  have m2 : ∀ x, NMem nex2.laz.ned x → (g2.re ≤ x ∨ NMem ts.ned x) ∧ x < g3.re := fun x hx => ⟨s3 x hx, nb3 x hx⟩
  have dab : Distinct (Need.pair nex1.laz.ned nex2.laz.ned) := ⟨d4, d3, fun x h1 h2 => by
    obtain ⟨e2, lt2⟩ := m2 x h2
    rcases m1 x h1 with e1 | e1
    · omega
    · rcases e2 with e2 | e2
      · have := nh x e1; omega
      · exact ap x e1 e2⟩
  have hfc : ∀ y, NMem nex1.laz.ned y ∨ NMem nex2.laz.ned y → ¬ Defd g4.blocks y := fun y hy d => by
    rcases dd4 y d with d | ⟨_, e4, n4⟩
    · rcases dd3 y d with d | ⟨_, e3, n3⟩
      · have lt := h.defd_lt d
        obtain ⟨fh, ft⟩ := hf y d
        rcases hy with hy | hy
        · rcases m1 y hy with e | e
          · omega
          · exact fh e
        · rcases (m2 y hy).1 with e | e
          · omega
          · exact ft e
      · rcases hy with hy | hy
        · rcases m1 y hy with e | e
          · omega
          · rcases e3 with e3 | e3
            · have := nh y e; omega
            · exact ap y e e3
        · exact n3 hy
    · rcases hy with hy | hy
      · exact n4 hy
      · obtain ⟨e2, lt2⟩ := m2 y hy
        rcases e4 with e4 | e4
        · omega
        · rcases e2 with e2 | e2
          · have := nh y e4; omega
          · exact ap y e4 e2
  obtain ⟨S1, eth, -, -, -, L1, -⟩ := raw_copy S4 a4 hi4 dab nb4 (nb3.mono l4) hfc h5
  refine ⟨S1, fun x hx => ?_⟩
  simp only [eth, jmp0] at hx
  rcases L1 x hx with e | ⟨hl, n1, n2⟩
  · exact Or.inl e
  · rcases L4 x hl with e | ⟨hl', nh'⟩
    · exact absurd e n1
    · rcases L3 x hl' with e | ⟨hl'', nt'⟩
      · exact absurd e n2
      · exact Or.inr ⟨hl'', nh', nt'⟩

/-! ## Cons -/

theorem raw_consNext {p q : Nomm} (ihp : RawIHP S Map X ρ lo p) (ihq : RawIHP S Map X ρ lo q)
    {laz : Sure S} {th : Jmp} {g0 g1 : Comp.Gen Map} {nex : Next S} (h : SIP X ρ lo g0) (hn : NB g0.re laz.ned)
    (dn : Distinct laz.ned) (ha : th.args = []) (hj1 : 1 ≤ th.there) (hj : th.there < g0.bo)
    (hf : ∀ y, NMem laz.ned y → ¬ Defd g0.blocks y)
    (hr : (do
      let (hed, tel, o) ← Comp.split ⟨laz, th⟩
      let nexh ← past noCode ⟨hed, jmp0 o⟩ q
      let nex2 ← run q (CGoal.next tel nexh.th)
      let nex2 ← past noCode nex2 p
      let nex1 ← run p (CGoal.next nexh.laz nex2.th)
      copy nex1 nex2.laz : CM Map (Next S)) g0 = some (nex, g1)) :
    SIP X ρ lo g1 ∧ ∀ x, Live g1.blocks nex.th.there x → NMem nex.laz.ned x ∨
      (Live g0.blocks th.there x ∧ ¬ NMem laz.ned x) := by
  obtain ⟨⟨hed, tel, o⟩, g2, h2, hr⟩ := bind_some hr
  obtain ⟨S2, eo, bo2, l2, fr2, Ls, Ds⟩ := raw_split h dn hn ha hj hf h2
  simp only at eo; subst eo
  obtain ⟨-, nh, nt⟩ := keeps_split h.drop hn (fun x hx => by rw [ha] at hx; cases hx) h2
  obtain ⟨-, dh, dt, ap, mh, mt⟩ := split_foot h.drop dn hn (fun x hx => by rw [ha] at hx; cases hx) h2
  simp only at nh nt dh dt ap mh mt Ls Ds
  obtain ⟨nexh, g2', hph, hr⟩ := bind_some hr
  obtain ⟨rfl, rfl⟩ := past_some hph
  obtain ⟨nex2, g3, h3, hr⟩ := bind_some hr
  obtain ⟨nex2', g3', hp2, hr⟩ := bind_some hr
  obtain ⟨rfl, rfl⟩ := past_some hp2
  obtain ⟨nex1, g4, h4, hr⟩ := bind_some hr
  obtain ⟨S1, L1⟩ := raw_binTail ihp ihq S2 nh nt dh dt ap rfl (by simp [jmp0]; have := h.bo1; omega)
    (by simp [jmp0]; omega)
    (fun x d => by
      rcases Ds x d with d | ⟨_, e1, e2⟩
      · have := h.defd_lt d
        refine ⟨fun e => ?_, fun e => ?_⟩
        · rcases mh x e with e' | e'
          · exact hf x e' d
          · omega
        · rcases mt x e with e' | e'
          · exact hf x e' d
          · omega
      · exact ⟨e1, e2⟩) h3 h4 hr
  refine ⟨S1, fun x hx => ?_⟩
  rcases L1 x hx with e | ⟨hl, n1, n2⟩
  · exact Or.inl e
  · rcases Ls x hl with e | e | e
    · exact absurd e n1
    · exact absurd e n2
    · exact Or.inr e

end Raw
end SkaModel
end Formalization
