import lemmas.Ska.RawInvCollapse

/-!
# Raw `+comp` output: `+mede`

README Gaps 14.  `raw_medeLoop`: the loop of `+mede` puts in front of its
block ops that define every register of the need, each once, with fresh
ones for the atoms of `+crash-need`, and read nothing before writing it.
`raw_mede`: the block of `+mede` hops to the goal's continuation and leaves
live there only what the continuation needs beyond the goal.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]
variable {X : Map Blob → Prop} [XOK X] {ρ : Nat → Nat} {lo : Nat}
variable {K : Nat → Nat → Prop} [KVan K lo]

theorem pre_pre (A B : List Pole) (b : Blob) : pre A (pre B b) = pre (A ++ B) b := by
  cases b; simp [pre]

/-- What the loop of `+mede` leaves in front of block `o`. -/
def MedeR (X : Map Blob → Prop) (ρ : Nat → Nat) (lo : Nat) (ned : Need) (g g' : Comp.Gen Map) (o : Nat) (b : Blob) : Prop :=
  SIP X ρ lo g' ∧ g'.bo = g.bo ∧ g.re ≤ g'.re ∧ ∃ A,
    (∀ k, HoonMap.get g'.blocks k = if k = o then some (pre A b) else HoonMap.get g.blocks k) ∧
    (∀ y, ¬ OpsRF A y) ∧ (∀ y ∈ defsOf A, NMem ned y ∨ (g.re ≤ y ∧ y < g'.re)) ∧
    (∀ y, NMem ned y → y ∈ defsOf A) ∧ (∀ y, Defd g'.blocks y ↔ Defd g.blocks y ∨ y ∈ defsOf A)

theorem medeR_crash {o : Nat} {n : Nat} {ned : Need} {g g' : Comp.Gen Map} {b : Blob} {u : Unit}
    (h : SIP X ρ lo g) (hb : HoonMap.get g.blocks o = some b) (dn : Distinct ned) (hn : NB g.re ned)
    (hf : ∀ y, NMem ned y → ¬ Defd g.blocks y) (hc : crashNeed o (Sum.inl n) ned g = some (u, g')) :
    MedeR X ρ lo ned g g' o b := by
  obtain ⟨S', bo', l', A, hget, hrf, hdefs, hdd, hcov⟩ :=
    raw_crashNeed h hb dn hn (fun p e => by cases e) (fun y hy _ => hf y hy) hc
  refine ⟨S', bo', l', A, hget, fun y hy => (by have := hrf y hy; cases this), fun y hy => ?_,
    fun y hy => hcov y hy (fun p e => by cases e), hdd⟩
  rcases hdefs y hy with e | e
  · exact Or.inl e.1
  · exact Or.inr e

/-- **The loop of `+mede`.** -/
theorem raw_medeLoop {o : Nat} : ∀ (ned : Need) (som : Noun) (g g' : Comp.Gen Map) (b : Blob) (u : Unit),
    SIP X ρ lo g → HoonMap.get g.blocks o = some b → Distinct ned → NB g.re ned →
    (∀ y, NMem ned y → ¬ Defd g.blocks y) → medeLoop o som ned g = some (u, g') → MedeR X ρ lo ned g g' o b := by
  intro ned
  induction ned with
  | none =>
    intro som g g' b u h hb _ _ _ hm
    cases som <;> simp only [medeLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at hm <;>
    · obtain ⟨-, rfl⟩ := hm
      refine ⟨h, rfl, Nat.le_refl _, [], fun k => ?_, fun y hy => hy, fun y hy => by simp [defsOf] at hy,
        fun y hy => hy.elim, fun y => by simp [defsOf]⟩
      by_cases e : k = o
      · subst e; simp [hb, pre_nil]
      · simp [e]
  | this r =>
    intro som g g' b u h hb _ hn hf hm
    have hm' : addOps o [Pole.imm som r] g = some (u, g') := by cases som <;> exact hm
    have hr := hn r rfl
    have P : OpsOK g [Pole.imm som r] :=
      ⟨regsIn_one (fun y hy => by simp [Comp.poleRegs] at hy; omega), by simp [defsOf, aliasDst],
        fun y hy => by simp [defsOf, aliasDst] at hy; subst hy; exact hf _ rfl,
        fun op hop => by simp at hop; subst hop; rfl⟩
    obtain ⟨S', b', hb', e', q', o'⟩ := sip_addOps h P hm'
    rw [hb] at hb'; cases hb'
    refine ⟨S', o', by omega, [Pole.imm som r], fun k => ?_, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_,
      fun y => by rw [e', defd_prepend hb]⟩
    · rw [e']; by_cases e : k = o
      · subst e; simp [get_put_self]
      · simp [get_put_ne e, e]
    · simp only [OpsRF, reads_imm, false_or] at hy; exact hy.2
    · simp [defsOf, aliasDst] at hy; exact Or.inl hy
    · simp only [NMem] at hy; simp [defsOf, aliasDst, hy]
  | pair p q ihp ihq =>
    intro som g g' b u h hb dn hn hf hm
    cases som with
    | atom n => exact medeR_crash h hb dn hn hf hm
    | cell a c =>
      simp only [medeLoop] at hm
      obtain ⟨u1, g1, h1, hm⟩ := bind_some hm
      obtain ⟨dp, dq, ap⟩ := dn
      obtain ⟨S1, bo1, l1, A1, get1, rf1, df1, cv1, dd1⟩ :=
        ihp a g g1 b u1 h hb dp (fun y hy => hn y (Or.inl hy)) (fun y hy => hf y (Or.inl hy)) h1
      have hb1 : HoonMap.get g1.blocks o = some (pre A1 b) := by rw [get1, if_pos rfl]
      obtain ⟨S2, bo2, l2, A2, get2, rf2, df2, cv2, dd2⟩ :=
        ihq c g1 g' (pre A1 b) u S1 hb1 dq (fun y hy => Nat.lt_of_lt_of_le (hn y (Or.inr hy)) l1)
          (fun y hy d => by
            rcases (dd1 y).mp d with d | d
            · exact hf y (Or.inr hy) d
            · rcases df1 y d with e | e
              · exact ap y e hy
              · have := hn y (Or.inr hy); omega) hm
      refine ⟨S2, by omega, by omega, A2 ++ A1, fun k => ?_, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_,
        fun y => ?_⟩
      · rw [get2, get1]; by_cases e : k = o
        · subst e; simp [pre_pre]
        · simp [e]
      · rcases opsRF_append.mp hy with e | ⟨-, e⟩
        · exact rf2 y e
        · exact rf1 y e
      · rw [defsOf_append, List.mem_append] at hy
        rcases hy with e | e
        · rcases df2 y e with e' | e'
          · exact Or.inl (Or.inr e')
          · exact Or.inr ⟨by omega, e'.2⟩
        · rcases df1 y e with e' | e'
          · exact Or.inl (Or.inl e')
          · exact Or.inr ⟨e'.1, by omega⟩
      · rw [defsOf_append, List.mem_append]
        rcases hy with e | e
        · exact Or.inr (cv1 y e)
        · exact Or.inl (cv2 y e)
      · rw [dd2, dd1, defsOf_append, List.mem_append]
        constructor
        · rintro ((d | d) | d)
          · exact Or.inl d
          · exact Or.inr (Or.inr d)
          · exact Or.inr (Or.inl d)
        · rintro (d | d | d)
          · exact Or.inl (Or.inl d)
          · exact Or.inr d
          · exact Or.inl (Or.inr d)
  | both r hh tt ihh iht =>
    intro som g g' b u h hb dn hn hf hm
    cases som with
    | atom n => exact medeR_crash h hb dn hn hf hm
    | cell a c =>
      simp only [medeLoop] at hm
      obtain ⟨u0, g0, h0, hm⟩ := bind_some hm
      obtain ⟨u1, g1, h1, hm⟩ := bind_some hm
      obtain ⟨dh, dt, ap, nrh, nrt⟩ := dn
      have hr := hn r (Or.inl rfl)
      have P : OpsOK g [Pole.imm (C a c) r] :=
        ⟨regsIn_one (fun y hy => by simp [Comp.poleRegs] at hy; omega), by simp [defsOf, aliasDst],
          fun y hy => by simp [defsOf, aliasDst] at hy; subst hy; exact hf _ (Or.inl rfl),
          fun op hop => by simp at hop; subst hop; rfl⟩
      obtain ⟨S0, b0, hb0, e0, q0, o0⟩ := sip_addOps h P h0
      rw [hb] at hb0; cases hb0
      have hb0' : HoonMap.get g0.blocks o = some (pre [Pole.imm (C a c) r] b) := by rw [e0]; exact get_put_self
      have dd0 : ∀ y, Defd g0.blocks y ↔ Defd g.blocks y ∨ y = r := fun y => by
        rw [e0, defd_prepend hb]; simp [defsOf, aliasDst]
      obtain ⟨S1, bo1, l1, A1, get1, rf1, df1, cv1, dd1⟩ :=
        ihh a g0 g1 _ u1 S0 hb0' dh (fun y hy => by have := hn y (Or.inr (Or.inl hy)); omega)
          (fun y hy d => by
            rcases (dd0 y).mp d with d | d
            · exact hf y (Or.inr (Or.inl hy)) d
            · subst d; exact nrh hy) h1
      have hb1 : HoonMap.get g1.blocks o = some (pre A1 (pre [Pole.imm (C a c) r] b)) := by rw [get1, if_pos rfl]
      obtain ⟨S2, bo2, l2, A2, get2, rf2, df2, cv2, dd2⟩ :=
        iht c g1 g' _ u S1 hb1 dt (fun y hy => by have := hn y (Or.inr (Or.inr hy)); omega)
          (fun y hy d => by
            rcases (dd1 y).mp d with d | d
            · rcases (dd0 y).mp d with d | d
              · exact hf y (Or.inr (Or.inr hy)) d
              · subst d; exact nrt hy
            · rcases df1 y d with e | e
              · exact ap y e hy
              · have := hn y (Or.inr (Or.inr hy)); omega) hm
      refine ⟨S2, by omega, by omega, A2 ++ A1 ++ [Pole.imm (C a c) r], fun k => ?_, fun y hy => ?_,
        fun y hy => ?_, fun y hy => ?_, fun y => ?_⟩
      · rw [get2, get1, e0]; by_cases e : k = o
        · subst e; simp [pre_pre, get_put_self]
        · simp [e, get_put_ne e]
      · rcases opsRF_append.mp hy with e | ⟨-, e⟩
        · rcases opsRF_append.mp e with e | ⟨-, e⟩
          · exact rf2 y e
          · exact rf1 y e
        · simp only [OpsRF, reads_imm, false_or] at e; exact e.2
      · simp only [defsOf_append, List.mem_append] at hy
        rcases hy with (e | e) | e
        · rcases df2 y e with e' | e'
          · exact Or.inl (Or.inr (Or.inr e'))
          · exact Or.inr ⟨by omega, e'.2⟩
        · rcases df1 y e with e' | e'
          · exact Or.inl (Or.inr (Or.inl e'))
          · exact Or.inr ⟨by omega, by omega⟩
        · simp [defsOf, aliasDst] at e; exact Or.inl (Or.inl e)
      · simp only [defsOf_append, List.mem_append]
        rcases hy with e | e | e
        · right; simp [defsOf, aliasDst, e]
        · exact Or.inl (Or.inr (cv1 y e))
        · exact Or.inl (Or.inl (cv2 y e))
      · rw [dd2, dd1, dd0]
        simp only [defsOf_append, List.mem_append]
        have : y ∈ defsOf [Pole.imm (C a c) r] ↔ y = r := by simp [defsOf, aliasDst]
        rw [this]
        constructor
        · rintro (((d | d) | d) | d)
          · exact Or.inl d
          · exact Or.inr (Or.inr d)
          · exact Or.inr (Or.inl (Or.inr d))
          · exact Or.inr (Or.inl (Or.inl d))
        · rintro (d | ((d | d) | d))
          · exact Or.inl (Or.inl (Or.inl d))
          · exact Or.inr d
          · exact Or.inl (Or.inr d)
          · exact Or.inl (Or.inl (Or.inr d))

/-- **`+mede`**: a new block hopping to the goal's continuation, with the
constant put into every register of the goal's need. -/
theorem raw_mede {th : Jmp} {som : Noun} {laz : Sure S} {g g' : Comp.Gen Map} {o : Nat}
    (h : SIP X ρ lo g) (dn : Distinct laz.ned) (hn : NB g.re laz.ned) (ha : th.args = []) (hj : th.there < g.bo)
    (hf : ∀ y, NMem laz.ned y → ¬ Defd g.blocks y)
    (hm : mede th som laz g = some (o, g')) :
    SIP X ρ lo g' ∧ o = g.bo ∧ g'.bo = g.bo + 1 ∧ g.re ≤ g'.re ∧
      (∀ k, k < g.bo → HoonMap.get g'.blocks k = HoonMap.get g.blocks k) ∧
      (∀ y, LiveK g'.blocks K o y → LiveK g.blocks K th.there y ∧ ¬ NMem laz.ned y) ∧
      (∀ y, Defd g'.blocks y → Defd g.blocks y ∨ NMem laz.ned y ∨ (g.re ≤ y ∧ y < g'.re)) := by
  simp only [mede] at hm
  obtain ⟨o1, g1, h1, hm⟩ := bind_some hm
  obtain ⟨S1, rfl, e1, q1, bo1⟩ := sip_emit h (emitOK_hop ha hj) h1
  obtain ⟨g2, g2', h2, hm⟩ := bind_some hm
  rw [get_apply] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl⟩ := h2
  rw [S1.drop] at hm
  simp only [Bool.false_eq_true, if_false] at hm
  obtain ⟨ned, g3, h3, hm⟩ := bind_some hm
  have L3 := sureRequireLook_spec h3
  obtain ⟨k3, e3⟩ := L3.gen
  have l3 := L3.le
  have S3 : SIP X ρ lo g3 := by rw [e3]; exact sip_reg S1 (by rw [e3] at l3; exact l3)
  have b3 : g3.blocks = g1.blocks := by rw [e3]
  have bo3 : g3.bo = g1.bo := by rw [e3]
  obtain ⟨u, g4, h4, hm⟩ := bind_some hm
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl⟩ := hm
  have dd1 : ∀ y, Defd g1.blocks y ↔ Defd g.blocks y := fun y => by
    rw [e1, defd_put (h.none (Nat.le_refl _))]; simp [blockDefs, defsOf]
  have nb3 : NB g3.re ned := fun y hy => by
    rcases L3.mem y hy with e | e
    · have := hn y e; omega
    · omega
  have hb3 : HoonMap.get g3.blocks g.bo = some ⟨[], [], Termin.hop th⟩ := by rw [b3, e1]; exact get_put_self
  obtain ⟨S4, bo4, l4, A, get4, rf4, df4, cv4, dd4⟩ := raw_medeLoop ned som g3 g4 _ u S3 hb3
    (L3.dist dn fun y hy => by have := hn y hy; omega) nb3
    (fun y hy d => by
      rw [b3, dd1] at d
      rcases L3.mem y hy with e | e
      · exact hf y e d
      · have := h.defd_lt d; omega) h4
  have below : ∀ k, k < g.bo → HoonMap.get g4.blocks k = HoonMap.get g.blocks k := fun k hk => by
    rw [get4, if_neg (by omega), b3, e1, get_put_ne (by omega)]
  refine ⟨S4, rfl, by omega, by omega, below, fun y hy => ?_, fun y hy => ?_⟩
  · have hk : HoonMap.get g4.blocks g.bo = some ⟨[], A ++ [], Termin.hop th⟩ := by rw [get4, if_pos rfl]
    rcases liveK_unfoldP hk (h.below g.bo) below (fun j hj' => by simp [getJmps] at hj'; subst hj'; exact hj) hy with
      ⟨-, hr⟩ | ⟨j, hj', hl, hn'⟩
    · simp only [List.append_nil] at hr
      rcases hr with hr | ⟨-, hr⟩
      · exact absurd hr (rf4 y)
      · simp [finRegs, jmpRegs_nil ha] at hr
    · simp [getJmps] at hj'; subst hj'
      refine ⟨hl, fun e => hn' ?_⟩
      simp only [List.append_nil, blockDefs, List.nil_append]
      exact cv4 y (sureRequireLook_keeps h3 e)
  · rcases (dd4 y).mp hy with d | d
    · rw [b3, dd1] at d; exact Or.inl d
    · rcases df4 y d with e | e
      · rcases L3.mem y e with e' | e'
        · exact Or.inr (Or.inl e')
        · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
      · exact Or.inr (Or.inr ⟨by omega, e.2⟩)

end Raw
end SkaModel
end Formalization
