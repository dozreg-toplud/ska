import lemmas.Ska.RawInvGen

/-!
# Raw `+comp` output: the arms that emit blocks

README Gaps 14.  For each arm of `+comp` that the first fragment runs and
that changes blocks: it keeps `SI`, which blocks it touches, the registers
it defines (each once, none defined before) and what is live at the blocks
it makes.  `+simple-next` (`raw_simpleNext`), `+bomb` (`raw_bomb`), the
blocks of `%done` (`raw_doneBlocks`), `+forl` (`raw_forl`), `+must`,
`+split-need` and `+split` (`raw_splitNeed`, `raw_split`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

theorem get_put_put {bl : Map Blob} {o x : Nat} {b b' : Blob} :
    HoonMap.get (HoonMap.put (HoonMap.put bl o b) o b') x = HoonMap.get (HoonMap.put bl o b') x := by
  by_cases e : x = o
  · subst e; simp [HoonMap.get_put]
  · simp [HoonMap.get_put, e]

theorem pre_nil (b : Blob) : pre [] b = b := by cases b; rfl

/-- A block with no parameter and no body is live where its end reads or
where its targets are live. -/
theorem blockRF_fin {f : Termin} {r : Nat} : BlockRF ⟨[], [], f⟩ r ↔ r ∈ finRegs f := by
  simp [BlockRF, OpsRF, defsOf]

theorem not_live_bom {bl : Map Blob} {k : Nat} {m : Option Nat} (hk : HoonMap.get bl k = some ⟨[], [], Termin.bom m⟩)
    {r : Nat} : ¬ Live bl k r := by
  intro h
  obtain ⟨b, hb, hr⟩ := live_iff.mp h
  rw [hk] at hb; cases hb
  rcases hr with hr | ⟨j, hj, _⟩
  · simp [blockRF_fin, finRegs] at hr
  · simp [getJmps] at hj

theorem jmpRegs_nil {j : Jmp} (h : j.args = []) : jmpRegs j = [] := by simp [jmpRegs, h]

theorem finIn_hop {P : Nat → Prop} {j : Jmp} (h : j.args = []) : FinIn P (Termin.hop j) := by
  simp [FinIn, JmpIn, h]

/-! ## `+bomb` and the blocks of `%done` -/

theorem emitOK_bom {g : Comp.Gen Map} (m : Option Nat) : EmitOK g ⟨[], [], Termin.bom m⟩ :=
  emitOK_of rfl (fun j hj => by simp [getJmps] at hj) (fun j hj => by simp [getJmps] at hj) (RegsIn.nil _)
    (by cases m <;> trivial) (by simp [defsOf]) (fun r hr => by simp [defsOf] at hr) (fun _ h => absurd h List.not_mem_nil)

theorem raw_bomb {miss : Option Nat} {g g' : Comp.Gen Map} {nex : Next S} (h : SI g)
    (hb : (bomb miss : CM Map (Next S)) g = some (nex, g')) :
    SI g' ∧ nex.laz.ned = Need.none ∧ (∀ x, x < g.bo → HoonMap.get g'.blocks x = HoonMap.get g.blocks x) ∧
      (∀ r, ¬ Live g'.blocks nex.th.there r) ∧ (∀ r, Defd g'.blocks r ↔ Defd g.blocks r) := by
  simp only [bomb] at hb
  obtain ⟨o, g1, h1, hb⟩ := bind_some hb
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  obtain ⟨S1, rfl, e1, -, -⟩ := si_emit h (emitOK_bom miss) h1
  refine ⟨S1, rfl, fun x hx => by rw [e1, get_put_ne (Nat.ne_of_lt hx)], fun r => ?_, fun r => ?_⟩
  · exact not_live_bom (by rw [e1]; exact get_put_self)
  · rw [e1, defd_put (h.none (Nat.le_refl _))]; simp [blockDefs]

theorem emitOK_don {g : Comp.Gen Map} {r : Nat} (hr : r < g.re) : EmitOK g ⟨[], [], Termin.don r⟩ :=
  emitOK_of rfl (fun j hj => by simp [getJmps] at hj) (fun j hj => by simp [getJmps] at hj) (RegsIn.nil _)
    hr (by simp [defsOf]) (fun r hr => by simp [defsOf] at hr) (fun _ h => absurd h List.not_mem_nil)

/-- A block `imm n r, don r` for a fresh `r`. -/
theorem emitOK_immDon {g : Comp.Gen Map} {r : Nat} {n : Noun} (h : SI g) (hr : r < g.re)
    (hn : ¬ Defd g.blocks r) : EmitOK g ⟨[], [Pole.imm n r], Termin.don r⟩ :=
  emitOK_of rfl (fun j hj => by simp [getJmps] at hj) (fun j hj => by simp [getJmps] at hj)
    (regsIn_one (fun x hx => by simp [Comp.poleRegs] at hx; omega)) hr (by simp [defsOf, aliasDst])
    (fun r' hr' => by simp [defsOf, aliasDst] at hr'; subst hr'; exact hn) (fun op hop => by simp at hop; subst hop; rfl)

theorem live_immDon {bl : Map Blob} {k : Nat} {r : Nat} {n : Noun}
    (hk : HoonMap.get bl k = some ⟨[], [Pole.imm n r], Termin.don r⟩) {x : Nat} : ¬ Live bl k x := by
  intro h
  obtain ⟨b, hb, hr⟩ := live_iff.mp h
  rw [hk] at hb; cases hb
  rcases hr with ⟨_, hr⟩ | ⟨j, hj, _⟩
  · simp only [OpsRF, reads_imm, false_or, defsOf, List.filterMap_cons, aliasDst, List.filterMap_nil,
      List.mem_singleton, finRegs] at hr
    rcases hr with ⟨_, hr⟩ | ⟨hn, hr⟩
    · exact hr
    · exact hn hr
  · simp [getJmps] at hj

theorem raw_doneBlocks {g g' : Comp.Gen Map} {o0 o1 : Nat} (h : SI g)
    (hd : (doneBlocks : CM Map (Nat × Nat)) g = some ((o0, o1), g')) :
    SI g' ∧ g.re ≤ g'.re ∧ o0 = g.bo ∧ o1 = g.bo + 1 ∧ g'.bo = g.bo + 2 ∧
      (∀ x, x < g.bo → HoonMap.get g'.blocks x = HoonMap.get g.blocks x) ∧
      (∀ r, ¬ Live g'.blocks o0 r) ∧ (∀ r, ¬ Live g'.blocks o1 r) ∧
      (∀ r, Defd g'.blocks r → Defd g.blocks r ∨ (g.re ≤ r ∧ r < g'.re)) := by
  simp only [doneBlocks] at hd
  obtain ⟨r0, g1, h1, hd⟩ := bind_some hd
  obtain ⟨S1, rfl, q1, b1, o1'⟩ := si_re h h1
  obtain ⟨r1, g2, h2, hd⟩ := bind_some hd
  obtain ⟨S2, rfl, q2, b2, o2'⟩ := si_re S1 h2
  have nd1 : ¬ Defd g2.blocks g.re := fun d => by have := S2.defd_lt d; rw [b2, b1] at d; have := h.defd_lt d; omega
  obtain ⟨o0', g3, h3, hd⟩ := bind_some hd
  obtain ⟨S3, rfl, e3, q3, bo3⟩ := si_emit S2 (emitOK_immDon S2 (by omega) nd1) h3
  have nd2 : ¬ Defd g3.blocks g1.re := fun d => by
    rw [e3, defd_put (S2.none (Nat.le_refl _))] at d
    rcases d with d | d
    · rw [b2, b1] at d; have := h.defd_lt d; omega
    · simp [blockDefs, defsOf, aliasDst] at d; omega
  obtain ⟨o1'', g4, h4, hd⟩ := bind_some hd
  obtain ⟨S4, rfl, e4, q4, bo4⟩ := si_emit S3 (emitOK_immDon S3 (by omega) nd2) h4
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hd
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hd
  have l3 : g3.bo = g.bo + 1 := by omega
  refine ⟨S4, by omega, by omega, by omega, by omega, fun x hx => ?_, fun r => live_immDon (n := A 0) (r := g.re) ?_,
    fun r => live_immDon (n := A 1) (r := g1.re) ?_, fun r d => ?_⟩
  · rw [e4, get_put_ne (by omega), e3, get_put_ne (by omega), b2, b1]
  · rw [e4, get_put_ne (by omega), e3, o2', o1']; exact get_put_self
  · rw [e4, l3]; exact get_put_self
  · rw [e4, defd_put (S3.none (Nat.le_refl _)), e3, defd_put (S2.none (Nat.le_refl _)), b2, b1] at d
    rcases d with (d | d) | d
    · exact Or.inl d
    · simp [blockDefs, defsOf, aliasDst] at d; exact Or.inr (by omega)
    · simp [blockDefs, defsOf, aliasDst] at d; exact Or.inr (by omega)

/-! ## `+simple-next` -/

theorem raw_simpleNext {goal : CGoal S} {g g' : Comp.Gen Map} {nex : Next S} (h : SI g) (hj : GJ g.bo goal)
    (ha : GArgs goal) (hg : GoalIn g.re goal)
    (hs : (simpleNext goal : CM Map (Next S)) g = some (nex, g')) :
    SI g' ∧ g.re ≤ g'.re ∧ g.bo ≤ g'.bo ∧ nex.th.args = [] ∧ nex.th.there < g'.bo ∧
      (∀ x, x < g.bo → HoonMap.get g'.blocks x = HoonMap.get g.blocks x) ∧
      (∀ r, Defd g'.blocks r ↔ Defd g.blocks r) ∧
      (∀ r, Live g'.blocks nex.th.there r → NMem nex.laz.ned r ∨ GLive g.blocks goal r) ∧
      (∀ r, NMem nex.laz.ned r → GMem goal r ∨ (g.re ≤ r ∧ r < g'.re)) ∧
      (∀ r, GMem goal r → NMem nex.laz.ned r) := by
  cases goal with
  | next laz th =>
    simp only [simpleNext, pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    refine ⟨h, Nat.le_refl _, Nat.le_refl _, ha, hj.2, fun _ _ => rfl, fun _ => Iff.rfl, fun r hr => ?_,
      fun r hr => Or.inl hr, fun r hr => hr⟩
    by_cases e : NMem laz.ned r
    · exact Or.inl e
    · exact Or.inr ⟨hr, e⟩
  | done =>
    simp only [simpleNext] at hs
    obtain ⟨r, g1, h1, hs⟩ := bind_some hs
    obtain ⟨S1, rfl, q1, b1, o1⟩ := si_re h h1
    obtain ⟨o, g2, h2, hs⟩ := bind_some hs
    obtain ⟨S2, rfl, e2, q2, bo2⟩ := si_emit S1 (emitOK_don (by omega)) h2
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    refine ⟨S2, by omega, by omega, rfl, by simp [jmp0]; omega, fun x hx => ?_, fun r => ?_, fun r hr => ?_,
      fun r hr => ?_, fun r hr => hr.elim⟩
    · rw [e2, get_put_ne (by omega), b1]
    · rw [e2, defd_put (S1.none (Nat.le_refl _)), b1]; simp [blockDefs]
    · have hk : HoonMap.get g2.blocks g1.bo = some ⟨[], [], Termin.don g.re⟩ := by rw [e2]; exact get_put_self
      obtain ⟨b, hb, hr'⟩ := live_iff.mp hr
      simp only [jmp0] at hb
      rw [hk] at hb; cases hb
      rcases hr' with hr' | ⟨j, hj', _⟩
      · rw [blockRF_fin] at hr'; simp [finRegs] at hr'; exact Or.inl hr'
      · simp [getJmps] at hj'
    · simp [NMem] at hr; exact Or.inr (by omega)
  | pick z o =>
    simp only [GJ] at hj
    obtain ⟨⟨_, hz⟩, ⟨_, hoo⟩⟩ := hj
    simp only [simpleNext] at hs
    obtain ⟨r, g1, h1, hs⟩ := bind_some hs
    obtain ⟨S1, rfl, q1, b1, o1⟩ := si_re h h1
    obtain ⟨o', g2, h2, hs⟩ := bind_some hs
    have E : EmitOK g1 ⟨[], [], Termin.brn g.re z o⟩ :=
      emitOK_of rfl (fun j hj' => by simp [getJmps] at hj'; rcases hj' with rfl | rfl; exact ha.1; exact ha.2)
        (fun j hj' => by simp [getJmps] at hj'; rcases hj' with rfl | rfl <;> omega) (RegsIn.nil _)
        (by simp [FinIn, JmpIn, ha.1, ha.2]; omega) (by simp [defsOf]) (fun r hr => by simp [defsOf] at hr)
        (fun _ h => absurd h List.not_mem_nil)
    obtain ⟨S2, rfl, e2, q2, bo2⟩ := si_emit S1 E h2
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    refine ⟨S2, by omega, by omega, rfl, by simp [jmp0]; omega, fun x hx => ?_, fun r => ?_, fun r hr => ?_,
      fun r hr => ?_, fun r hr => hr.elim⟩
    · rw [e2, get_put_ne (by omega), b1]
    · rw [e2, defd_put (S1.none (Nat.le_refl _)), b1]; simp [blockDefs]
    · have he : ∀ x, x < g1.bo → HoonMap.get g2.blocks x = HoonMap.get g1.blocks x := fun x hx => by
        rw [e2, get_put_ne (by omega)]
      rcases live_unfold (by rw [e2]; exact get_put_self) (S1.below g1.bo) he
        (fun j hj' => by simp [getJmps] at hj'; rcases hj' with rfl | rfl <;> omega) hr with hr' | ⟨j, hj', hl, _⟩
      · simp [BlockRF, OpsRF, defsOf, finRegs, jmpRegs, ha.1, ha.2] at hr'; exact Or.inl hr'
      · rw [b1] at hl
        simp [getJmps] at hj'
        rcases hj' with rfl | rfl
        · exact Or.inr (Or.inl hl)
        · exact Or.inr (Or.inr hl)
    · simp [NMem] at hr; exact Or.inr (by omega)

/-! ## `+forl` -/

/-- **`+forl`**: the join `barg` with the parameter `r` hops to `o`, the two
branches put `0` and `1` into fresh registers and pass them. -/
theorem raw_forl {r o : Nat} {g g' : Comp.Gen Map} {z o' : Nat} (h : SI g) (hr : r < g.re) (hn : ¬ Defd g.blocks r)
    (ho : o < g.bo) (hf : forl r o g = some ((z, o'), g')) :
    SI g' ∧ g'.re = g.re + 2 ∧ g'.bo = g.bo + 3 ∧ z = g.bo + 1 ∧ o' = g.bo + 2 ∧
      (∀ x, x < g.bo → HoonMap.get g'.blocks x = HoonMap.get g.blocks x) ∧
      (∀ x, Live g'.blocks z x → x ≠ r ∧ Live g.blocks o x) ∧ (∀ x, Live g'.blocks o' x → x ≠ r ∧ Live g.blocks o x) ∧
      (∀ x, Defd g'.blocks x → Defd g.blocks x ∨ x = r ∨ (g.re ≤ x ∧ x < g.re + 2)) := by
  simp only [forl] at hf
  obtain ⟨r0, g1, h1, hf⟩ := bind_some hf
  obtain ⟨S1, rfl, q1, b1, o1⟩ := si_re h h1
  obtain ⟨r1, g2, h2, hf⟩ := bind_some hf
  obtain ⟨S2, rfl, q2, b2, o2⟩ := si_re S1 h2
  obtain ⟨barg, g3, h3, hf⟩ := bind_some hf
  have nb : ∀ x, Defd g2.blocks x → x < g.re := fun x d => by rw [b2, b1] at d; exact h.defd_lt d
  have E3 : EmitOK g2 ⟨[r], [], Termin.hop (jmp0 o)⟩ :=
    { jd := fun j hj => by simp [getJmps] at hj; subst hj; simp [jmp0]; omega
      regs := ⟨fun x hx => by simp at hx; omega, RegsIn.nil _, finIn_hop rfl⟩
      nd := by simp [blockDefs, defsOf]
      fresh := fun x hx => by simp [blockDefs, defsOf] at hx; subst hx; rw [b2, b1]; exact hn
      tr := fun _ h => absurd h List.not_mem_nil
      p1 := by simp
      args := fun j hj x hx => by simp [getJmps] at hj; subst hj; simp [jmp0] at hx }
  obtain ⟨S3, rfl, e3, q3, bo3⟩ := si_emit S2 E3 h3
  obtain ⟨if0, g4, h4, hf⟩ := bind_some hf
  have nd0 : ¬ Defd g3.blocks g.re := fun d => by
    rw [e3, defd_put (S2.none (Nat.le_refl _))] at d
    rcases d with d | d
    · have := nb _ d; omega
    · simp [blockDefs, defsOf] at d; omega
  have E4 : EmitOK g3 ⟨[], [Pole.imm (A 0) g.re], Termin.hop ⟨[some g.re], g2.bo⟩⟩ :=
    { jd := fun j hj => by simp [getJmps] at hj; subst hj; simp; omega
      regs := ⟨fun x hx => by simp at hx, regsIn_one (fun x hx => by simp [Comp.poleRegs] at hx; omega),
        by simp [FinIn, JmpIn]; omega⟩
      nd := by simp [blockDefs, defsOf, aliasDst]
      fresh := fun x hx => by simp [blockDefs, defsOf, aliasDst] at hx; subst hx; exact nd0
      tr := fun op hop => by simp at hop; subst hop; rfl
      p1 := by simp
      args := fun j hj x hx z bz hz hzj y hy => by
        simp [getJmps] at hj; subst hj; simp at hx hzj; subst hx
        rw [get_put_ne (by omega), e3] at hz
        rcases get_put_cases hz with ⟨rfl, rfl⟩ | ⟨-, hz⟩
        · simp at hy; omega
        · rw [b2, b1] at hz; have := (h.regs z bz hz).1 y hy; omega }
  obtain ⟨S4, rfl, e4, q4, bo4⟩ := si_emit S3 E4 h4
  obtain ⟨if1, g5, h5, hf⟩ := bind_some hf
  have nd1 : ¬ Defd g4.blocks g1.re := fun d => by
    rw [e4, defd_put (S3.none (Nat.le_refl _)), e3, defd_put (S2.none (Nat.le_refl _))] at d
    rcases d with (d | d) | d
    · have := nb _ d; omega
    · simp [blockDefs, defsOf] at d; omega
    · simp [blockDefs, defsOf, aliasDst] at d; omega
  have E5 : EmitOK g4 ⟨[], [Pole.imm (A 1) g1.re], Termin.hop ⟨[some g1.re], g2.bo⟩⟩ :=
    { jd := fun j hj => by simp [getJmps] at hj; subst hj; simp; omega
      regs := ⟨fun x hx => by simp at hx, regsIn_one (fun x hx => by simp [Comp.poleRegs] at hx; omega),
        by simp [FinIn, JmpIn]; omega⟩
      nd := by simp [blockDefs, defsOf, aliasDst]
      fresh := fun x hx => by simp [blockDefs, defsOf, aliasDst] at hx; subst hx; exact nd1
      tr := fun op hop => by simp at hop; subst hop; rfl
      p1 := by simp
      args := fun j hj x hx z bz hz hzj y hy => by
        simp [getJmps] at hj; subst hj; simp at hx hzj; subst hx
        rw [get_put_ne (by omega), e4, get_put_ne (by omega), e3] at hz
        rcases get_put_cases hz with ⟨rfl, rfl⟩ | ⟨-, hz⟩
        · simp at hy; omega
        · rw [b2, b1] at hz; have := (h.regs z bz hz).1 y hy; omega }
  obtain ⟨S5, rfl, e5, q5, bo5⟩ := si_emit S4 E5 h5
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hf
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hf
  have gbarg : HoonMap.get g5.blocks g2.bo = some ⟨[r], [], Termin.hop (jmp0 o)⟩ := by
    rw [e5, get_put_ne (by omega), e4, get_put_ne (by omega), e3]; exact get_put_self
  have below : ∀ x, x < g2.bo → HoonMap.get g5.blocks x = HoonMap.get g.blocks x := fun x hx => by
    rw [e5, get_put_ne (by omega), e4, get_put_ne (by omega), e3, get_put_ne (by omega), b2, b1]
  have liveBarg : ∀ x, Live g5.blocks g2.bo x → x ≠ r ∧ Live g.blocks o x := fun x hl => by
    rcases live_unfold gbarg (h.below (g2.bo)) below (fun j hj => by simp [getJmps] at hj; subst hj; simp [jmp0]; omega)
      hl with hr' | ⟨j, hj, hl', hn'⟩
    · simp [BlockRF, OpsRF, defsOf, finRegs, jmpRegs, jmp0] at hr'
    · simp [getJmps] at hj; subst hj
      exact ⟨fun e => hn' (by simp [blockDefs, e]), hl'⟩
  have liveIf : ∀ (k : Nat) (n : Noun) (rr : Nat), HoonMap.get g5.blocks k = some ⟨[], [Pole.imm n rr], Termin.hop ⟨[some rr], g2.bo⟩⟩ →
      g2.bo < k → ∀ x, Live g5.blocks k x → x ≠ r ∧ Live g.blocks o x := fun k n rr hk hlt x hl => by
    obtain ⟨b, hb, hr'⟩ := live_iff.mp hl
    rw [hk] at hb; cases hb
    rcases hr' with hr' | ⟨j, hj, hl', _⟩
    · simp [BlockRF, OpsRF, reads_imm, defsOf, aliasDst, finRegs, jmpRegs] at hr'
    · simp [getJmps] at hj; subst hj; exact liveBarg x hl'
  refine ⟨S5, by omega, by omega, by omega, by omega, fun x hx => below x (by omega),
    liveIf _ (A 0) g.re (by rw [e5, get_put_ne (by omega), e4]; exact get_put_self) (by omega),
    liveIf _ (A 1) g1.re (by rw [e5]; exact get_put_self) (by omega), fun x d => ?_⟩
  rw [e5, defd_put (S4.none (Nat.le_refl _)), e4, defd_put (S3.none (Nat.le_refl _)), e3,
    defd_put (S2.none (Nat.le_refl _)), b2, b1] at d
  rcases d with ((d | d) | d) | d
  · exact Or.inl d
  · simp [blockDefs, defsOf] at d; exact Or.inr (Or.inl d)
  · simp [blockDefs, defsOf, aliasDst] at d; exact Or.inr (Or.inr (by omega))
  · simp [blockDefs, defsOf, aliasDst] at d; exact Or.inr (Or.inr (by omega))

end Raw
end SkaModel
end Formalization
