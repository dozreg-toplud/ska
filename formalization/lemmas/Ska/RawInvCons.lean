import lemmas.Ska.RawInvRun

/-!
# Raw `+comp` output: cons and `%5`

README Gaps 14.  `raw_cons`: cons for every goal (`%done` makes the block
`don` and runs as `%next`, `%pick` makes a `%bom` block and runs both
operands for an empty need).  `raw_n5`: the block that compares the two
operands' registers (for `%pick`, `%done`, and for `%next` through
`+collapse-lazy-atom` and `+forl`, or an `%equ` when the goal's need is
none-equivalent), then the two runs and the copy (`raw_binTail`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]
variable {X : Map Blob → Prop} [XOK X] {ρ : Nat → Nat} {lo : Nat}
variable {K : Nat → Nat → Prop} [KVan K lo]

theorem not_liveK_don {bl : Map Blob} {k r x : Nat} (hk : HoonMap.get bl k = some ⟨[], [], Termin.don r⟩)
    (hx : LiveK bl K k x) : x = r := by
  obtain ⟨b, hb, hr⟩ := liveK_cases hx
  rw [hk] at hb; cases hb
  rcases hr with hr | ⟨j, hj, _⟩
  · rw [blockRF_fin] at hr; simpa [finRegs] using hr
  · simp [getJmps] at hj

theorem not_live_don {bl : Map Blob} {k r x : Nat} (hk : HoonMap.get bl k = some ⟨[], [], Termin.don r⟩)
    (hx : Live bl k x) : x = r := not_liveK_don (K := fun _ _ => False) hk (liveK_of_live hx)

theorem raw_cons {p q : Nomm} (ihp : RawIHPK S Map X ρ lo K p) (ihq : RawIHPK S Map X ρ lo K q) : RawIHPK S Map X ρ lo K (Nomm.cons p q) := by
  intro goal g0 g1 nex h hg hD hj ha hf hr
  cases goal with
  | done =>
    simp only [run] at hr
    obtain ⟨gl, g2, h2, hr⟩ := bind_some hr
    obtain ⟨r, g3, h3, h2⟩ := bind_some h2
    obtain ⟨S3, rfl, q3, b3, o3⟩ := sip_re h h3
    obtain ⟨o, g4, h4, h2⟩ := bind_some h2
    obtain ⟨S4, rfl, e4, q4, bo4⟩ := sip_emit S3 (emitOK_don (by omega)) h4
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    simp only at hr
    obtain ⟨S1, L1⟩ := raw_consNext (laz := lazyReg g0.re) (th := jmp0 g3.bo) ihp ihq S4 (nb_this (by omega)) trivial rfl
      (by simp [jmp0]; have := h.bo1; omega) (by simp [jmp0]; omega)
      (fun y hy d => by
        simp only [lazyReg, NMem] at hy; subst hy
        rw [e4, defd_put (S3.none (Nat.le_refl _)), b3] at d
        rcases d with d | d
        · have := h.defd_lt d; omega
        · simp [blockDefs, defsOf] at d) hr
    refine ⟨S1, fun x hx => ?_⟩
    rcases L1 x hx with e | ⟨hl, hn⟩
    · exact Or.inl e
    · exfalso
      exact hn (by simp only [lazyReg, NMem]; exact not_liveK_don (by rw [e4]; exact get_put_self) hl)
  | next laz th =>
    simp only [run, bind_apply, pure_apply, Option.bind_some] at hr
    exact raw_consNext ihp ihq h hg.1 hD ha hj.1 hj.2 (fun y hy d => hf y d hy) hr
  | pick z o =>
    simp only [run, bind_apply, pure_apply, Option.bind_some] at hr
    obtain ⟨⟨o', g2⟩, h2, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨S2, rfl, e2, q2, bo2⟩ := sip_emit h (emitOK_bom Option.none) h2
    obtain ⟨⟨nex2, g3⟩, h3, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨⟨nex2', g3'⟩, hp, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨rfl, rfl⟩ := past_some hp
    obtain ⟨⟨nex1, g4⟩, h4, hr⟩ := Option.bind_eq_some_iff.mp hr
    obtain ⟨S1, L1⟩ := raw_binTail (hs := Sure.bunt) (ts := Sure.bunt) ihp ihq S2 (nb_none _) (nb_none _) trivial
      trivial (fun _ e => e.elim) rfl (by simp [jmp0]; have := h.bo1; omega) (by simp [jmp0]; omega)
      (fun _ _ => ⟨fun e => e.elim, fun e => e.elim⟩) h3 h4 hr
    refine ⟨S1, fun x hx => ?_⟩
    rcases L1 x hx with e | ⟨hl, -⟩
    · exact Or.inl e
    · exact absurd hl (not_liveK_bom (by rw [e2]; exact get_put_self))

/-! ## `%5` -/

theorem emitOK_eqq {g : Comp.Gen Map} {a c : Nat} {z o : Jmp} (hr : a < g.re) (hc : c < g.re) (hz : z.args = [])
    (ho : o.args = []) (hzl : z.there < g.bo) (hol : o.there < g.bo) : EmitOK g ⟨[], [], Termin.eqq a c z o⟩ :=
  emitOK_of rfl (fun j hj => by simp [getJmps] at hj; rcases hj with rfl | rfl; exact hz; exact ho)
    (fun j hj => by simp [getJmps] at hj; rcases hj with rfl | rfl <;> assumption) (RegsIn.nil _)
    (by simp [FinIn, JmpIn, hz, ho]; exact ⟨hr, hc⟩) (by simp [defsOf]) (fun y hy => by simp [defsOf] at hy)
    (fun _ h => absurd h List.not_mem_nil)

theorem blockRF_eqq {a c y : Nat} {z o : Jmp} (hz : z.args = []) (ho : o.args = [])
    (h : BlockRF ⟨[], [], Termin.eqq a c z o⟩ y) : y = a ∨ y = c := by
  rw [blockRF_fin] at h; simpa [finRegs, jmpRegs, hz, ho] using h

theorem raw_n5 {p q : Nomm} (ihp : RawIHPK S Map X ρ lo K p) (ihq : RawIHPK S Map X ρ lo K q) : RawIHPK S Map X ρ lo K (Nomm.n5 p q) := by
  intro goal g0 g1 nex h hg hD hj ha hf hr
  simp only [run] at hr
  obtain ⟨rp, g2, h2, hr⟩ := bind_some hr
  obtain ⟨S2, rfl, q2, b2, o2⟩ := sip_re h h2
  obtain ⟨rq, g3, h3, hr⟩ := bind_some hr
  obtain ⟨S3, rfl, q3, b3, o3⟩ := sip_re S2 h3
  obtain ⟨o, g4, h4, hr⟩ := bind_some hr
  have b30 : g3.blocks = g0.blocks := by rw [b3, b2]
  have H : SIP X ρ lo g4 ∧ 1 ≤ o ∧ o < g4.bo ∧ g3.re ≤ g4.re ∧
      (∀ x, Defd g4.blocks x → Defd g0.blocks x ∨ g3.re ≤ x ∨ GMem goal x) ∧
      (∀ x, LiveK g4.blocks K o x → x = g0.re ∨ x = g2.re ∨ GLiveK g0.blocks K goal x) := by
    cases goal with
    | pick z o' =>
      simp only [GJ] at hj
      simp only at h4
      obtain ⟨S4, rfl, e4, q4, bo4⟩ := sip_emit S3 (emitOK_eqq (by omega) (by omega) ha.1 ha.2 (by omega) (by omega)) h4
      refine ⟨S4, by have := h.bo1; omega, by omega, by omega, fun x d => ?_, fun x hl => ?_⟩
      · rw [e4, defd_put (S3.none (Nat.le_refl _)), b30] at d
        rcases d with d | d
        · exact Or.inl d
        · simp [blockDefs, defsOf] at d
      · rcases liveK_unfoldP (by rw [e4]; exact get_put_self) (S3.below g3.bo)
          (fun k hk => by rw [e4, get_put_ne (by omega)])
          (fun j hj' => by simp [getJmps] at hj'; rcases hj' with rfl | rfl <;> omega) hl with
          e | ⟨j, hj', hl', -⟩
        · rcases blockRF_eqq ha.1 ha.2 e with e | e
          · exact Or.inl e
          · exact Or.inr (Or.inl e)
        · rw [b30] at hl'
          simp [getJmps] at hj'
          rcases hj' with rfl | rfl
          · exact Or.inr (Or.inr (Or.inl hl'))
          · exact Or.inr (Or.inr (Or.inr hl'))
    | done =>
      simp only at h4
      obtain ⟨⟨o0, o1⟩, g5, h5, h4⟩ := bind_some h4
      obtain ⟨S5, l5, rfl, rfl, bo5, fr5, n0, n1, dd5⟩ := raw_doneBlocks (K := K) S3 h5
      obtain ⟨S4, rfl, e4, q4, bo4⟩ := sip_emit S5 (emitOK_eqq (by omega) (by omega) rfl rfl
        (by simp [jmp0]; omega) (by simp [jmp0]; omega)) h4
      refine ⟨S4, by have := h.bo1; omega, by omega, by omega, fun x d => ?_, fun x hl => ?_⟩
      · rw [e4, defd_put (S5.none (Nat.le_refl _))] at d
        rcases d with d | d
        · rcases dd5 x d with d | d
          · rw [b30] at d; exact Or.inl d
          · exact Or.inr (Or.inl d.1)
        · simp [blockDefs, defsOf] at d
      · rcases liveK_unfoldP (by rw [e4]; exact get_put_self) (S5.below g5.bo)
          (fun k hk => by rw [e4, get_put_ne (by omega)])
          (fun j hj' => by simp [getJmps] at hj'; rcases hj' with rfl | rfl <;> simp [jmp0] <;> omega) hl with
          e | ⟨j, hj', hl', -⟩
        · rcases blockRF_eqq rfl rfl e with e | e
          · exact Or.inl e
          · exact Or.inr (Or.inl e)
        · simp [getJmps] at hj'
          rcases hj' with rfl | rfl
          · exact absurd hl' (n0 x)
          · exact absurd hl' (n1 x)
    | next laz th =>
      have hjt : th.there < g0.bo := hj.2
      simp only at h4
      obtain ⟨a, g5, h5, h4⟩ := bind_some h4
      obtain ⟨S5, l5, bo5, ha5, fr5, cn, cs⟩ := raw_collapse (K := K) S3 (hg.1.mono (by omega)) (by omega)
        (fun y hy d => by rw [b30] at d; exact hf y d hy) h5
      cases a with
      | none =>
        obtain ⟨hn0, e5⟩ := cn rfl
        rw [e5] at h4
        rw [if_pos ha5] at h4
        have E : EmitOK g3 ⟨[], [Pole.equ g0.re g2.re], Termin.hop (jmp0 th.there)⟩ :=
          emitOK_of rfl (fun j hj' => by simp [getJmps] at hj'; rw [hj']; rfl)
            (fun j hj' => by simp [getJmps] at hj'; rw [hj']; simp [jmp0]; omega)
            (regsIn_one (fun x hx => by simp [Comp.poleRegs] at hx; omega)) (by simp [FinIn, JmpIn, jmp0])
            (by simp [defsOf, aliasDst, List.filterMap_cons]) (fun y hy => by simp [defsOf, aliasDst] at hy)
            (fun op hop => by simp at hop; subst hop; rfl)
        obtain ⟨S4, rfl, e4, q4, bo4⟩ := sip_emit S3 E h4
        refine ⟨S4, by have := h.bo1; omega, by omega, by omega, fun x d => ?_, fun x hl => ?_⟩
        · rw [e4, defd_put (S3.none (Nat.le_refl _)), b30] at d
          rcases d with d | d
          · exact Or.inl d
          · simp [blockDefs, defsOf, aliasDst] at d
        · rcases liveK_unfoldP (by rw [e4]; exact get_put_self) (S3.below g3.bo)
            (fun k hk => by rw [e4, get_put_ne (by omega)])
            (fun j hj' => by simp [getJmps] at hj'; rw [hj']; simp [jmp0]; omega) hl with
            ⟨-, e⟩ | ⟨j, hj', hl', -⟩
          · rcases e with e | ⟨-, e⟩
            · simp only [OpsRF, reads_equ] at e
              rcases e with (e | e) | ⟨-, e⟩
              · exact Or.inl e
              · exact Or.inr (Or.inl e)
              · exact e.elim
            · simp [finRegs, jmpRegs, jmp0] at e
          · simp [getJmps] at hj'; subst hj'
            rw [b30] at hl'
            exact Or.inr (Or.inr ⟨hl', by rw [hn0]; exact id⟩)
      | some x =>
        obtain ⟨r, o'⟩ := x
        obtain ⟨rm, rl, nd, tl, dd, lv⟩ := cs r o' rfl
        simp only at h4
        obtain ⟨⟨z, o''⟩, g6, h6, h4⟩ := bind_some h4
        obtain ⟨S6, q6, bo6, rfl, rfl, fr6, lz, lo', dd6⟩ := raw_forl (K := K) S5 rl nd tl h6
        obtain ⟨S4, rfl, e4, q4, bo4⟩ := sip_emit S6 (emitOK_eqq (by omega) (by omega) rfl rfl
          (by simp [jmp0]; omega) (by simp [jmp0]; omega)) h4
        refine ⟨S4, by have := h.bo1; omega, by omega, by omega, fun x d => ?_, fun x hl => ?_⟩
        · rw [e4, defd_put (S6.none (Nat.le_refl _))] at d
          rcases d with d | d
          · rcases dd6 x d with d | rfl | d
            · rcases dd x d with d | d
              · rw [b30] at d; exact Or.inl d
              · exact Or.inr (Or.inl d.1)
            · rcases rm with e | e
              · exact Or.inr (Or.inr e)
              · exact Or.inr (Or.inl e.1)
            · exact Or.inr (Or.inl (by omega))
          · simp [blockDefs, defsOf] at d
        · rcases liveK_unfoldP (by rw [e4]; exact get_put_self) (S6.below g6.bo)
            (fun k hk => by rw [e4, get_put_ne (by omega)])
            (fun j hj' => by simp [getJmps] at hj'; rcases hj' with rfl | rfl <;> simp [jmp0] <;> omega) hl with
            e | ⟨j, hj', hl', -⟩
          · rcases blockRF_eqq rfl rfl e with e | e
            · exact Or.inl e
            · exact Or.inr (Or.inl e)
          · simp [getJmps] at hj'
            have hl'' : x ≠ r ∧ LiveK g5.blocks K o' x := by
              rcases hj' with rfl | rfl
              · exact lz x hl'
              · exact lo' x hl'
            rcases lv x hl''.2 with e | ⟨e1, e2⟩
            · exact absurd e hl''.1
            · rw [b30] at e1; exact Or.inr (Or.inr ⟨e1, e2⟩)
  obtain ⟨S4, lo4, hi4, l4, dd4, lv4⟩ := H
  obtain ⟨nexq, g5, h5, hr⟩ := bind_some hr
  obtain ⟨nexq', g5', hp, hr⟩ := bind_some hr
  obtain ⟨rfl, rfl⟩ := past_some hp
  obtain ⟨nexp, g6, h6, hr⟩ := bind_some hr
  have hgm : ∀ x, GMem goal x → x < g0.re := fun x hx => by
    cases goal with
    | next laz th => exact hg.1 x hx
    | _ => exact hx.elim
  obtain ⟨S1, L1⟩ := raw_binTail (hs := lazyReg g0.re) (ts := lazyReg g2.re) ihp ihq S4 (nb_this (by omega))
    (nb_this (by omega)) trivial trivial
    (fun x e1 e2 => by simp only [lazyReg, NMem] at e1 e2; omega) rfl (by simp [jmp0]; exact lo4)
    (by simp [jmp0]; exact hi4)
    (fun x d => by
      simp only [lazyReg, NMem]
      rcases dd4 x d with d | d | d
      · have := h.defd_lt d; omega
      · omega
      · have := hgm x d; omega) h5 h6 hr
  refine ⟨S1, fun x hx => ?_⟩
  rcases L1 x hx with e | ⟨hl, n1, n2⟩
  · exact Or.inl e
  · simp only [lazyReg, NMem] at n1 n2
    rcases lv4 x hl with e | e | e
    · exact absurd e n1
    · exact absurd e n2
    · exact Or.inr e

end Raw
end SkaModel
end Formalization
