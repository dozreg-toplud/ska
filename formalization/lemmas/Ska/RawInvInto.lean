import lemmas.Ska.RawInvCons

/-!
# Raw `+comp` output: `+into` and `[10 [a v] q]`

README Gaps 14.  `intoRec_raw`: the `%con` ops of the walk of `+into-need`
(as `intoRec` of `CompInto.lean` computes them, the deepest first) define
the registers of the need on the path and fresh ones, each once, read only
the donor's and the recipient's registers before writing, and leave every
register of the need defined or in one of the two halves.  `raw_into`: the
block of `+into`.  `raw_n10`: the case `%10`, with the donor `v` run first,
then the recipient `q`, then the copy (`raw_binTail`).  `run_rawP`, `run_raw`: the
induction over every nomm, so **`RawIH` holds of `run` on the whole first
fragment**.
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

theorem tr_con {a c d : Nat} : trOp (Pole.con a c d) = false := rfl

/-- **The ops of the walk of `+into-need`.** -/
theorem intoRec_raw : ∀ (axe : Nat) (ned : Need) (g g' : Comp.Gen Map) (d r : Need) (ops : List Pole),
    1 ≤ axe → intoRec axe ned g = some ((d, r, ops), g') → Distinct ned → NB g.re ned →
    (defsOf ops).Nodup ∧ (∀ y, OpsRF ops y → NMem d y ∨ NMem r y) ∧
    (∀ y, NMem ned y → y ∈ defsOf ops ∨ NMem d y ∨ NMem r y) ∧ (∀ op ∈ ops, trOp op = false) ∧
    RegsIn (· < g'.re) ops := by
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
  intro ned g g' d r ops ha h dn lo
  have I := intoRec_ok axe ned g g' d r ops ha h
  rw [intoRec] at h
  by_cases h1 : axe ≤ 1
  · rw [dif_pos h1] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
    exact ⟨by simp [defsOf], fun y hy => hy.elim, fun y hy => Or.inr (Or.inl hy), fun _ h => absurd h List.not_mem_nil,
      RegsIn.nil _⟩
  rw [dif_neg h1] at h
  have lt := mas_lt axe (by omega)
  have m1 : 1 ≤ mas axe := mas_pos axe (by omega)
  generalize decide (cap axe = 2) = b at h
  cases ned with
  | none =>
    obtain ⟨⟨d0, r0, ops0⟩, g1, e1, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
    obtain ⟨n1, rf1, cv1, tr1, rg1⟩ := ih _ lt _ _ _ _ _ _ m1 e1 trivial (nb_none _)
    refine ⟨n1, fun y hy => ?_, fun y hy => hy.elim, tr1, rg1⟩
    rcases rf1 y hy with e | e
    · exact Or.inl e
    · exact Or.inr ((nmem_side b _ _ y).mpr (Or.inl e))
  | this x0 =>
    obtain ⟨l, g1, e1, h⟩ := bind_some h
    rw [re_apply] at e1; simp only [Option.some.injEq, Prod.mk.injEq] at e1; obtain ⟨rfl, rfl⟩ := e1
    obtain ⟨r', g2, e2, h⟩ := bind_some h
    rw [re_apply] at e2; simp only [Option.some.injEq, Prod.mk.injEq] at e2; obtain ⟨rfl, rfl⟩ := e2
    obtain ⟨⟨d0, r0, ops0⟩, g3, e3, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
    have xl := lo x0 rfl
    have I3 := intoRec_ok _ _ _ _ _ _ _ m1 e3
    obtain ⟨n1, rf1, cv1, tr1, rg1⟩ := ih _ lt _ _ _ _ _ _ m1 e3 trivial
      (nb_this (by simp; cases b <;> simp <;> omega))
    have W := intoRec_wr _ _ _ _ _ _ _ m1 e3 trivial (nb_this (by simp; cases b <;> simp <;> omega))
    have dlow : ∀ y ∈ defsOf ops0, g.re ≤ y := fun y hy => by
      obtain ⟨op, hop, hd⟩ := mem_defsOf.mp hy
      rcases (W op hop y (aliasDst_poleWr hd)).1 with e | e
      · simp only [NMem] at e; cases b <;> simp at e <;> omega
      · simp at e; omega
    refine ⟨?_, fun y hy => ?_, fun y hy => ?_, ?_, ?_⟩
    · rw [defsOf_append, defsOf_con]
      exact List.nodup_append.mpr ⟨n1, by simp, fun a ha c hc e => by
        simp at hc; subst hc; subst e; have := dlow a ha; omega⟩
    · rcases opsRF_append.mp hy with e | ⟨hn, e⟩
      · rcases rf1 y e with e | e
        · exact Or.inl e
        · exact Or.inr ((nmem_side b _ _ y).mpr (Or.inl e))
      · rw [opsRF_con] at e
        cases b
        · rcases e with rfl | rfl
          · exact Or.inr ((nmem_side false _ _ _).mpr (Or.inr (by simp [NMem])))
          · rcases cv1 (g.re + 1) (by simp [NMem]) with e | e | e
            · exact absurd e hn
            · exact Or.inl e
            · exact Or.inr ((nmem_side false _ _ _).mpr (Or.inl e))
        · rcases e with rfl | rfl
          · rcases cv1 g.re (by simp [NMem]) with e | e | e
            · exact absurd e hn
            · exact Or.inl e
            · exact Or.inr ((nmem_side true _ _ _).mpr (Or.inl e))
          · exact Or.inr ((nmem_side true _ _ _).mpr (Or.inr (by simp [NMem])))
    · simp only [NMem] at hy; subst hy
      left; rw [defsOf_append, defsOf_con]; simp
    · intro op hop
      rcases List.mem_append.mp hop with hop | hop
      · exact tr1 op hop
      · simp at hop; subst hop; rfl
    · refine RegsIn.append rg1 (regsIn_one fun y hy => ?_)
      have : g.re + 1 + 1 ≤ g3.re := by have := I3.le; simpa using this
      simp [Comp.poleRegs] at hy; rcases hy with rfl | rfl | rfl <;> omega
  | pair p q =>
    obtain ⟨⟨d0, r0, ops0⟩, g1, e1, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
    obtain ⟨dp, dq, _⟩ := dn
    have dpath : Distinct (if b then p else q) := by cases b <;> simpa
    have lpath : NB g.re (if b then p else q) := fun y hy => by
      cases b
      · exact lo y (Or.inr (by simpa using hy))
      · exact lo y (Or.inl (by simpa using hy))
    obtain ⟨n1, rf1, cv1, tr1, rg1⟩ := ih _ lt _ _ _ _ _ _ m1 e1 dpath lpath
    refine ⟨n1, fun y hy => ?_, fun y hy => ?_, tr1, rg1⟩
    · rcases rf1 y hy with e | e
      · exact Or.inl e
      · exact Or.inr ((nmem_side b _ _ y).mpr (Or.inl e))
    · cases b
      · rcases hy with e | e
        · exact Or.inr (Or.inr ((nmem_side false _ _ y).mpr (Or.inr (by simpa using e))))
        · rcases cv1 y (by simpa using e) with e' | e' | e'
          · exact Or.inl e'
          · exact Or.inr (Or.inl e')
          · exact Or.inr (Or.inr ((nmem_side false _ _ y).mpr (Or.inl e')))
      · rcases hy with e | e
        · rcases cv1 y (by simpa using e) with e' | e' | e'
          · exact Or.inl e'
          · exact Or.inr (Or.inl e')
          · exact Or.inr (Or.inr ((nmem_side true _ _ y).mpr (Or.inl e')))
        · exact Or.inr (Or.inr ((nmem_side true _ _ y).mpr (Or.inr (by simpa using e))))
  | both x0 hh tt =>
    obtain ⟨⟨l1, l2⟩, g1, e1, h⟩ := bind_some h
    obtain ⟨⟨r1, r2⟩, g2, e2, h⟩ := bind_some h
    obtain ⟨⟨d0, r0, ops0⟩, g3, e3, h⟩ := bind_some h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
    obtain ⟨ge1, le1, m1', t1, -, -, D1⟩ := must_spec e1
    obtain ⟨ge2, le2, m2', t2, -, -, D2⟩ := must_spec e2
    obtain ⟨dh, dt, ap, nxh, nxt⟩ := dn
    have xl := lo x0 (Or.inl rfl)
    have bl1 : ∀ y, NMem l2 y → y < g1.re := fun y hy => by
      rcases m1' y hy with e | e
      · have := lo y (Or.inr (Or.inl e)); omega
      · exact e.2
    have bl2 : ∀ y, NMem r2 y → y < g2.re := fun y hy => by
      rcases m2' y hy with e | e
      · have := lo y (Or.inr (Or.inr e)); omega
      · exact e.2
    have dl : Distinct l2 := D1 dh (fun y hy => lo y (Or.inr (Or.inl hy)))
    have dr : Distinct r2 := D2 dt (fun y hy => by have := lo y (Or.inr (Or.inr hy)); omega)
    have dpath : Distinct (if b then l2 else r2) := by cases b <;> simpa
    have lpath : NB g2.re (if b then l2 else r2) := fun y hy => by
      cases b
      · exact bl2 y (by simpa using hy)
      · have := bl1 y (by simpa using hy); omega
    obtain ⟨n1, rf1, cv1, tr1, rg1⟩ := ih _ lt _ _ _ _ _ _ m1 e3 dpath lpath
    have I3 := intoRec_ok _ _ _ _ _ _ _ m1 e3
    have W := intoRec_wr _ _ _ _ _ _ _ m1 e3 dpath lpath
    simp only at n1 rf1 cv1 tr1 rg1 I3 W
    have x0n : ∀ y ∈ defsOf ops0, y ≠ x0 := fun y hy e => by
      subst e
      obtain ⟨op, hop, hd⟩ := mem_defsOf.mp hy
      rcases (W op hop _ (aliasDst_poleWr hd)).1 with e | e
      · cases b
        · rcases m2' _ (by simpa using e) with e' | e'
          · exact nxt e'
          · omega
        · rcases m1' _ (by simpa using e) with e' | e'
          · exact nxh e'
          · omega
      · omega
    refine ⟨?_, fun y hy => ?_, fun y hy => ?_, ?_, ?_⟩
    · rw [defsOf_append, defsOf_con]
      exact List.nodup_append.mpr ⟨n1, by simp, fun a ha c hc e => by
        simp at hc; subst hc; subst e; exact x0n a ha rfl⟩
    · rcases opsRF_append.mp hy with e | ⟨hn, e⟩
      · rcases rf1 y e with e | e
        · exact Or.inl e
        · exact Or.inr ((nmem_side b _ _ y).mpr (Or.inl e))
      · rw [opsRF_con] at e
        cases b
        · rcases e with rfl | rfl
          · exact Or.inr ((nmem_side false _ _ _).mpr (Or.inr (by simpa using must_top e1)))
          · rcases cv1 _ (by simpa using must_top e2) with e | e | e
            · exact absurd e hn
            · exact Or.inl e
            · exact Or.inr ((nmem_side false _ _ _).mpr (Or.inl e))
        · rcases e with rfl | rfl
          · rcases cv1 _ (by simpa using must_top e1) with e | e | e
            · exact absurd e hn
            · exact Or.inl e
            · exact Or.inr ((nmem_side true _ _ _).mpr (Or.inl e))
          · exact Or.inr ((nmem_side true _ _ _).mpr (Or.inr (by simpa using must_top e2)))
    · rcases hy with rfl | e | e
      · left; rw [defsOf_append, defsOf_con]; simp
      · have e' := must_keep e1 e
        cases b
        · exact Or.inr (Or.inr ((nmem_side false _ _ y).mpr (Or.inr (by simpa using e'))))
        · rcases cv1 y (by simpa using e') with e'' | e'' | e''
          · left; rw [defsOf_append]; exact List.mem_append_left _ e''
          · exact Or.inr (Or.inl e'')
          · exact Or.inr (Or.inr ((nmem_side true _ _ y).mpr (Or.inl e'')))
      · have e' := must_keep e2 e
        cases b
        · rcases cv1 y (by simpa using e') with e'' | e'' | e''
          · left; rw [defsOf_append]; exact List.mem_append_left _ e''
          · exact Or.inr (Or.inl e'')
          · exact Or.inr (Or.inr ((nmem_side false _ _ y).mpr (Or.inl e'')))
        · exact Or.inr (Or.inr ((nmem_side true _ _ y).mpr (Or.inr (by simpa using e'))))
    · intro op hop
      rcases List.mem_append.mp hop with hop | hop
      · exact tr1 op hop
      · simp at hop; subst hop; rfl
    · refine RegsIn.append rg1 (regsIn_one fun y hy => ?_)
      have := I3.le
      have b1 := bl1 _ (must_top e1)
      have b2 := bl2 _ (must_top e2)
      simp [Comp.poleRegs] at hy; rcases hy with rfl | rfl | rfl <;> omega

/-- **`+into`**: a new block that hops to the goal's continuation, with the
`%con` ops of the walk in front. -/
theorem raw_into {laz : Sure S} {th : Jmp} {axe : Nat} {g g' : Comp.Gen Map} {don rec : Sure S} {o : Nat}
    (h : SIP X ρ lo g) (dn : Distinct laz.ned) (hn : NB g.re laz.ned) (ha : th.args = []) (hj : th.there < g.bo)
    (hf : ∀ y, NMem laz.ned y → ¬ Defd g.blocks y)
    (hs : into ⟨laz, th⟩ axe g = some ((don, rec, o), g')) :
    SIP X ρ lo g' ∧ o = g.bo ∧ g'.bo = g.bo + 1 ∧ g.re ≤ g'.re ∧
      (∀ k, k < g.bo → HoonMap.get g'.blocks k = HoonMap.get g.blocks k) ∧
      (∀ y, LiveK g'.blocks K g.bo y → NMem don.ned y ∨ NMem rec.ned y ∨
        (LiveK g.blocks K th.there y ∧ ¬ NMem laz.ned y)) ∧
      (∀ y, Defd g'.blocks y → Defd g.blocks y ∨ ((NMem laz.ned y ∨ g.re ≤ y) ∧ ¬ NMem don.ned y ∧ ¬ NMem rec.ned y)) ∧
      Distinct don.ned ∧ Distinct rec.ned ∧ (∀ y, NMem don.ned y → ¬ NMem rec.ned y) ∧
      (∀ y, NMem don.ned y → NMem laz.ned y ∨ g.re ≤ y) ∧ (∀ y, NMem rec.ned y → NMem laz.ned y ∨ g.re ≤ y) := by
  simp only [into] at hs
  obtain ⟨o', g1, h1, hs⟩ := bind_some hs
  obtain ⟨S1, rfl, e1, q1, bo1⟩ := sip_emit h (emitOK_hop ha hj) h1
  obtain ⟨⟨sd, sr⟩, g2, h2, hs⟩ := bind_some hs
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hs
  simp only [intoSure] at h2
  obtain ⟨⟨ld, lr⟩, hl, h2⟩ := Option.bind_eq_some_iff.mp h2
  obtain ⟨⟨⟨nd, nr⟩, g3⟩, h3, h4⟩ := Option.map_eq_some_iff.mp h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
  simp only
  have dd1 : ∀ y, Defd g1.blocks y ↔ Defd g.blocks y := fun y => by
    rw [e1, defd_put (h.none (Nat.le_refl _))]; simp [blockDefs, defsOf]
  have hb1 : HoonMap.get g1.blocks g.bo = some ⟨[], [], Termin.hop th⟩ := by rw [e1]; exact get_put_self
  have below1 : ∀ k, k < g.bo → HoonMap.get g1.blocks k = HoonMap.get g.blocks k := fun k hk => by
    rw [e1, get_put_ne (by omega)]
  simp only [intoNeed] at h3
  by_cases a0 : axe = 0
  · rw [if_pos a0] at h3; cases h3
  rw [if_neg a0] at h3
  by_cases a1 : axe = 1
  · rw [if_pos a1] at h3
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h3
    refine ⟨S1, trivial, bo1, by omega, below1, fun y hy => ?_, fun y d => Or.inl ((dd1 y).mp d), dn, trivial,
      fun _ _ e => e.elim, fun y hy => Or.inl hy, fun y hy => hy.elim⟩
    rcases liveK_unfoldP hb1 (h.below g.bo) below1 (fun j hj' => by simp [getJmps] at hj'; subst hj'; exact hj) hy with
      hr | ⟨j, hj', hl', -⟩
    · rw [blockRF_fin] at hr; simp [finRegs, jmpRegs_nil ha] at hr
    · simp [getJmps] at hj'; subst hj'
      by_cases e : NMem laz.ned y
      · exact Or.inl e
      · exact Or.inr (Or.inr ⟨hl', e⟩)
  rw [if_neg a1] at h3
  obtain ⟨d, r, ops', g4, e4, e5, ex⟩ := intoLoop_rec _ _ _ _ _ _ _ h3
  simp only [List.foldl_nil, Prod.mk.injEq] at ex
  obtain ⟨rfl, rfl⟩ := ex
  have hn1 : NB g1.re laz.ned := by rw [q1]; exact hn
  obtain ⟨n4, rf4, cv4, tr4, rg4⟩ := intoRec_raw axe laz.ned g1 g4 nd nr ops' (by omega) e4 dn hn1
  have I := intoRec_ok axe laz.ned g1 g4 nd nr ops' (by omega) e4
  have W := intoRec_wr axe laz.ned g1 g4 nd nr ops' (by omega) e4 dn hn1
  have S4 : SIP X ρ lo g4 := by rw [I.gen]; exact sip_reg S1 I.le
  have b4 : g4.blocks = g1.blocks := by rw [I.gen]
  have bo4 : g4.bo = g1.bo := by rw [I.gen]
  have wd : ∀ y ∈ defsOf ops', (NMem laz.ned y ∨ (g1.re ≤ y ∧ y < g4.re)) ∧ ¬ NMem nd y ∧ ¬ NMem nr y :=
    fun y hy => by obtain ⟨op, hop, hd⟩ := mem_defsOf.mp hy; exact W op hop y (aliasDst_poleWr hd)
  rw [List.append_nil] at e5
  have P : OpsOK g4 ops' := ⟨rg4, n4, fun y hy dy => by
      rw [b4, dd1] at dy
      rcases (wd y hy).1 with e | e
      · exact hf y e dy
      · have := h.defd_lt dy; omega, tr4⟩
  obtain ⟨S3, b', hb', e3, q3, o3⟩ := sip_addOps S4 P e5
  rw [b4, hb1] at hb'; cases hb'
  obtain ⟨Dd, Dr, Ap, -, -⟩ := I.sem dn hn1
  have below : ∀ k, k < g.bo → HoonMap.get g3.blocks k = HoonMap.get g.blocks k := fun k hk => by
    rw [e3, get_put_ne (by omega), b4, below1 k hk]
  refine ⟨S3, trivial, by omega, by have := I.le; omega, below, fun y hy => ?_, fun y dy => ?_, Dd, Dr, Ap,
    fun y hy => (I.md y hy).imp id fun e => by omega, fun y hy => (I.mr y hy).imp id fun e => by omega⟩
  · have hk : HoonMap.get g3.blocks g.bo = some ⟨[], ops' ++ [], Termin.hop th⟩ := by
      rw [e3]; exact get_put_self
    rcases liveK_unfoldP hk (h.below g.bo) below (fun j hj' => by simp [getJmps] at hj'; subst hj'; exact hj) hy with
      ⟨-, hr⟩ | ⟨j, hj', hl', hn'⟩
    · simp only [List.append_nil] at hr
      rcases hr with hr | ⟨-, hr⟩
      · rcases rf4 y hr with e | e
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
      · simp [finRegs, jmpRegs_nil ha] at hr
    · simp [getJmps] at hj'; subst hj'
      have hnA : y ∉ defsOf ops' := fun e => hn' (by simp [blockDefs]; exact mem_defsOf.mp e)
      by_cases e : NMem laz.ned y
      · rcases cv4 y e with e' | e' | e'
        · exact absurd e' hnA
        · exact Or.inl e'
        · exact Or.inr (Or.inl e')
      · exact Or.inr (Or.inr ⟨hl', e⟩)
  · rw [e3, defd_prepend (by rw [b4]; exact hb1), b4, dd1] at dy
    rcases dy with d' | d'
    · exact Or.inl d'
    · obtain ⟨e, n1, n2⟩ := wd y d'
      exact Or.inr ⟨e.imp id fun e => by omega, n1, n2⟩

theorem simpleNext_dist {goal : CGoal S} {g g' : Comp.Gen Map} {nex : Next S} (hD : GDist goal)
    (hs : (simpleNext goal : CM Map (Next S)) g = some (nex, g')) : Distinct nex.laz.ned := by
  cases goal with
  | next laz th =>
    simp only [simpleNext, pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs; exact hD
  | done =>
    simp only [simpleNext] at hs
    obtain ⟨r, g1, h1, hs⟩ := bind_some hs
    obtain ⟨o, g2, h2, hs⟩ := bind_some hs
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs; trivial
  | pick z o =>
    simp only [simpleNext] at hs
    obtain ⟨r, g1, h1, hs⟩ := bind_some hs
    obtain ⟨o', g2, h2, hs⟩ := bind_some hs
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs; trivial

/-! ## `[10 [a v] q]` -/

theorem raw_n10 (a : Nat) {v q : Nomm} (ihv : RawIHPK S Map X ρ lo K v) (ihq : RawIHPK S Map X ρ lo K q) :
    RawIHPK S Map X ρ lo K (Nomm.n10 a v q) := by
  intro goal g0 g1 nex h hg hD hj ha hf hr
  simp only [run] at hr
  obtain ⟨nx, g2, h2, hr⟩ := bind_some hr
  obtain ⟨S2, l2, bo2, a2, t2, fr2, dd2, L2, m2, -⟩ := raw_simpleNext (K := K) h hj ha hg h2
  have D2 := simpleNext_dist hD h2
  have hgm : ∀ x, GMem goal x → x < g0.re := fun x hx => by
    cases goal with
    | next laz th => exact hg.1 x hx
    | _ => exact hx.elim
  have nb2 : NB g2.re nx.laz.ned := fun y hy => by
    rcases m2 y hy with e | e
    · have := hgm y e; omega
    · exact e.2
  have nf2 : ∀ y, NMem nx.laz.ned y → ¬ Defd g2.blocks y := fun y hy d => by
    rw [dd2] at d
    rcases m2 y hy with e | e
    · exact hf y d e
    · have := h.defd_lt d; omega
  obtain ⟨⟨don, rec, o⟩, g3, h3, hr⟩ := bind_some hr
  obtain ⟨S3, rfl, bo3, l3, fr3, L3, dd3, Dd, Dr, Ap, md, mr⟩ := raw_into (K := K) S2 D2 nb2 a2 t2 nf2 h3
  obtain ⟨-, nd3, nr3⟩ := keeps_into S2.drop ⟨nb2, fun x hx => by rw [a2] at hx; cases hx⟩ h3
  simp only at nd3 nr3
  obtain ⟨nexR, g3', hpr, hr⟩ := bind_some hr
  obtain ⟨rfl, rfl⟩ := past_some hpr
  obtain ⟨nexDon, g4, h4, hr⟩ := bind_some hr
  obtain ⟨nexDon', g4', hpd, hr⟩ := bind_some hr
  obtain ⟨rfl, rfl⟩ := past_some hpd
  obtain ⟨nexRec, g5, h5, hr⟩ := bind_some hr
  obtain ⟨S1, L1⟩ := raw_binTail (hs := rec) (ts := don) (j := jmp0 g2.bo) ihq ihv S3 nr3 nd3 Dr Dd
    (fun x e1 e2 => Ap x e2 e1) rfl (by simp [jmp0]; have := S2.bo1; omega) (by simp [jmp0]; omega)
    (fun x d => by
      rcases dd3 x d with d | ⟨-, n1, n2⟩
      · have lt := S2.defd_lt d
        refine ⟨fun e => ?_, fun e => ?_⟩
        · rcases mr x e with e' | e'
          · exact nf2 x e' d
          · omega
        · rcases md x e with e' | e'
          · exact nf2 x e' d
          · omega
      · exact ⟨n2, n1⟩) h4 h5 hr
  refine ⟨S1, fun x hx => ?_⟩
  rcases L1 x hx with e | ⟨hl, n1, n2⟩
  · exact Or.inl e
  · rcases L3 x hl with e | e | ⟨hl', hn'⟩
    · exact absurd e n2
    · exact absurd e n1
    · rcases L2 x hl' with e | e
      · exact absurd e hn'
      · exact Or.inr e

/-! ## The induction -/

/-- **`RawIHPK` holds of every nomm**: on the nomms where `run` returns (the
first fragment), every run from a state with `SIP` (jumps down in a rank
`ρ`, labels from `lo` on ranked `3 k`, a carried predicate `X` that the two
steps keep) keeps it and leaves live at its entry, with kills `K` that
vanish from `lo` on, only its result's need and what its goal's
continuation needs beyond the goal with the same kills.  So a run of the
first fragment after a `%6` under `%next` (fork blocks that hop up, a join
with several parameters) is covered, with `X := fun _ => True`, and so is a
run whose goal's continuation is code with lazy entries that kill. -/
theorem run_rawPK : ∀ nm : Nomm, RawIHPK S Map X ρ lo K nm := by
  intro nm
  induction nm with
  | n0 ax => exact raw_n0 ax
  | n1 k => exact raw_n1 k
  | n7 p q ihp ihq => exact raw_n7 ihp ihq
  | n4 p ih => exact raw_n4 ih
  | n3 p ih => exact raw_n3 ih
  | n5 p q ihp ihq => exact raw_n5 ihp ihq
  | cons p q ihp ihq => exact raw_cons ihp ihq
  | n10 a v q ihv ihq => exact raw_n10 a ihv ihq
  | n2 => intro goal g0 g1 nex _ _ _ _ _ _ h; simp only [run] at h; cases h
  | n6 => intro goal g0 g1 nex _ _ _ _ _ _ h; simp only [run] at h; cases h
  | n11s => intro goal g0 g1 nex _ _ _ _ _ _ h; simp only [run] at h; cases h
  | n11d => intro goal g0 g1 nex _ _ _ _ _ _ h; simp only [run] at h; cases h
  | n12 => intro goal g0 g1 nex _ _ _ _ _ _ h; simp only [run] at h; cases h
  | mean => intro goal g0 g1 nex _ _ _ _ _ _ h; simp only [run] at h; cases h

/-- **`RawIHP` holds of every nomm**: `run_rawPK` with no kills. -/
theorem run_rawP : ∀ nm : Nomm, RawIHP S Map X ρ lo nm := by
  intro nm goal g0 g1 nex h hg hD hj ha hf hr
  obtain ⟨S1, L1⟩ := run_rawPK (K := fun _ _ => False) nm goal g0 g1 nex h hg hD hj ha hf hr
  exact ⟨S1, fun r hl => (L1 r (liveK_of_live hl)).imp id gLiveK_none.mp⟩

/-- **`RawIH` holds of every nomm**: on the nomms where `run` returns (the
first fragment), every run keeps the invariant and leaves live at its entry
only its result's need and what its goal's continuation needs beyond the
goal.  `run_rawP` with `X := Xstd`, `ρ := (3 * ·)`, `lo := 0`. -/
theorem run_raw : ∀ nm : Nomm, RawIH S Map nm := by
  intro nm goal g0 g1 nex h hg hD hj ha hf hr
  obtain ⟨S1, L1⟩ := run_rawP (X := Xstd) (ρ := fun k => 3 * k) (lo := 0) nm goal g0 g1 nex (si_sip h)
    hg hD hj ha hf hr
  exact ⟨sip_si S1, L1⟩

end Raw
end SkaModel
end Formalization
