import lemmas.Ska.RawInvGenP
import lemmas.Ska.RawInvKern
import lemmas.Ska.RawInvCut

/-!
# Raw `+comp` output: `+sure-loop` and `+coerce-lazy` from a state with `SIP`

README Gaps 14, track D, the class `FragX`.  Generated from the section
`+sure-loop` of `RawInvKern.lean` and from `raw_coerce` of `RawInvCut.lean`
by text substitution: `SI g` becomes `SIP X ρ lo g`, `si_addOps` and
`si_reg` their `SIP` forms (`sip_addOps`, `sip_reg`), and the names get a
`P` (`SureRP`, `sureRP_nil`, `sureRP_mov`, `sureRP_seq`, `raw_sureLoopP`,
**`raw_coerceP`**).  The state after a `%6` under `%next` has blocks that
hop up and a join with several parameters, so `SI` is false there, while
the proofs use only the fields that `SIP` keeps.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp

variable {Map : Type → Type} [HoonMap Map]
variable {X : Map Blob → Prop} [XOK X] {ρ : Nat → Nat} {lo : Nat}

/-! ## `+sure-loop` -/

/-- What `+sure-loop` leaves in front of block `o`. -/
def SureRP (X : Map Blob → Prop) (ρ : Nat → Nat) (lo : Nat) (ned tgt : Need) (g g' : Comp.Gen Map) (o : Nat) (b : Blob) : Prop :=
  SIP X ρ lo g' ∧ g'.bo = g.bo ∧ g.re ≤ g'.re ∧ ∃ A,
    (∀ k, HoonMap.get g'.blocks k = if k = o then some (pre A b) else HoonMap.get g.blocks k) ∧
    (∀ y, OpsRF A y → NMem ned y) ∧ (∀ y, NMem tgt y → y ∈ defsOf A) ∧
    (∀ y ∈ defsOf A, NMem tgt y ∨ (g.re ≤ y ∧ y < g'.re))

theorem sureRP_nil {ned tgt : Need} {g : Comp.Gen Map} {o : Nat} {b : Blob} (h : SIP X ρ lo g)
    (hb : HoonMap.get g.blocks o = some b) (ht : ∀ y, ¬ NMem tgt y) : SureRP X ρ lo ned tgt g g o b := by
  refine ⟨h, rfl, Nat.le_refl _, [], fun k => ?_, fun y hy => hy.elim, fun y hy => absurd hy (ht y),
    fun y hy => by simp [defsOf] at hy⟩
  by_cases e : k = o
  · subst e; simp [hb, pre_nil]
  · simp [e]

/-- One move into `d` from `r`. -/
theorem sureRP_mov {r d : Nat} {ned : Need} {g g' : Comp.Gen Map} {o : Nat} {b : Blob} {u : Unit} (h : SIP X ρ lo g)
    (hb : HoonMap.get g.blocks o = some b) (hr : r < g.re) (hd : d < g.re) (hnd : ¬ Defd g.blocks d)
    (hrn : NMem ned r) (ha : addOps o [Pole.mov r d] g = some (u, g')) :
    SIP X ρ lo g' ∧ g'.bo = g.bo ∧ g.re ≤ g'.re ∧
      (∀ k, HoonMap.get g'.blocks k = if k = o then some (pre [Pole.mov r d] b) else HoonMap.get g.blocks k) := by
  have P : OpsOK g [Pole.mov r d] :=
    ⟨regsIn_one (fun y hy => by simp [Comp.poleRegs] at hy; omega), by simp [defsOf_mov],
      fun y hy => by simp [defsOf_mov] at hy; subst hy; exact hnd, fun op hop => by simp at hop; subst hop; rfl⟩
  obtain ⟨S', b', hb', e', q', o'⟩ := sip_addOps h P ha
  rw [hb] at hb'; cases hb'
  refine ⟨S', o', by omega, fun k => ?_⟩
  rw [e']; by_cases e : k = o
  · subst e; simp [get_put_self]
  · simp [get_put_ne e, e]

/-- **Two loops one after the other at the same block.** -/
theorem sureRP_seq {n2 t2 ned tgt : Need} {g g1 g2 : Comp.Gen Map} {o : Nat} {b : Blob} {A1 : List Pole}
    (l1 : g.re ≤ g1.re) (bo1 : g1.bo = g.bo)
    (get1 : ∀ k, HoonMap.get g1.blocks k = if k = o then some (pre A1 b) else HoonMap.get g.blocks k)
    (rf1 : ∀ y, OpsRF A1 y → NMem ned y) (df1 : ∀ y ∈ defsOf A1, NMem tgt y ∨ (g.re ≤ y ∧ y < g1.re))
    (R2 : SureRP X ρ lo n2 t2 g1 g2 o (pre A1 b)) (s2 : ∀ y, NMem n2 y → NMem ned y) (u2 : ∀ y, NMem t2 y → NMem tgt y)
    (cov : ∀ y, NMem tgt y → y ∈ defsOf A1 ∨ NMem t2 y) : SureRP X ρ lo ned tgt g g2 o b := by
  obtain ⟨S2, bo2, l2, A2, get2, rf2, cv2, df2⟩ := R2
  refine ⟨S2, by omega, by omega, A2 ++ A1, fun k => ?_, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · rw [get2, get1]; by_cases e : k = o
    · subst e; simp [pre_pre]
    · simp [e]
  · rcases opsRF_append.mp hy with e | ⟨-, e⟩
    · exact s2 y (rf2 y e)
    · exact rf1 y e
  · rw [defsOf_append, List.mem_append]
    rcases cov y hy with e | e
    · exact Or.inr e
    · exact Or.inl (cv2 y e)
  · rw [defsOf_append, List.mem_append] at hy
    rcases hy with e | e
    · rcases df2 y e with e' | e'
      · exact Or.inl (u2 y e')
      · exact Or.inr ⟨by omega, e'.2⟩
    · rcases df1 y e with e' | e'
      · exact Or.inl e'
      · exact Or.inr ⟨e'.1, by omega⟩

/-- **`+sure-loop`.** -/
theorem raw_sureLoopP {o : Nat} : ∀ (ned tgt : Need) (g g' : Comp.Gen Map) (b : Blob) (u : Unit),
    SIP X ρ lo g → HoonMap.get g.blocks o = some b → Distinct tgt → NB g.re tgt → NB g.re ned →
    (∀ y, NMem ned y → ¬ NMem tgt y) → (∀ y, NMem tgt y → ¬ Defd g.blocks y) →
    sureLoop o ned tgt g = some (u, g') → SureRP X ρ lo ned tgt g g' o b := by
  intro ned
  induction ned with
  | none =>
    intro tgt g g' b u h hb _ _ _ _ _ hs
    simp only [sureLoop] at hs
    by_cases e : tgt = Need.none
    · rw [if_pos e] at hs
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨-, rfl⟩ := hs
      subst e; exact sureRP_nil h hb (fun y hy => hy)
    · rw [if_neg e] at hs; cases hs
  | this r =>
    intro tgt g g' b u h hb dt nt nn ap hf hs
    simp only [sureLoop] at hs
    obtain ⟨ops, g1, h1, hs⟩ := bind_some hs
    obtain ⟨B, eB, K⟩ := kernLoop_raw tgt r [] g g1 ops h1 (nn r rfl) (fun e => ap r rfl e) nt dt
    simp only [List.append_nil] at eB
    rw [eB] at hs
    have S1 : SIP X ρ lo g1 := by rw [K.gen]; exact sip_reg h K.le
    have b1 : g1.blocks = g.blocks := by rw [K.gen]
    have P : OpsOK g1 B := ⟨K.regs, K.nd, fun y hy d => by
        rw [b1] at d
        rcases K.defs y hy with e | e
        · exact hf y e d
        · have := h.defd_lt d; omega, K.tr⟩
    obtain ⟨S2, b', hb', e2, q2, o2⟩ := sip_addOps S1 P hs
    rw [b1, hb] at hb'; cases hb'
    refine ⟨S2, by rw [o2, K.gen], by have := K.le; omega, B, fun k => ?_, fun y hy => ?_, K.cov,
      fun y hy => ?_⟩
    · rw [e2, b1]; by_cases e : k = o
      · subst e; simp [get_put_self]
      · simp [e, get_put_ne e]
    · rw [K.rf y hy]; rfl
    · rcases K.defs y hy with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e.1, by omega⟩
  | pair p q ihp ihq =>
    intro tgt g g' b u h hb dt nt nn ap hf hs
    cases tgt with
    | none =>
      simp only [sureLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨-, rfl⟩ := hs
      exact sureRP_nil h hb (fun y hy => hy)
    | pair tp tq =>
      simp only [sureLoop] at hs
      obtain ⟨u1, g1, h1, hs⟩ := bind_some hs
      obtain ⟨dp, dq, apq⟩ := dt
      obtain ⟨S1, bo1, l1, A1, get1, rf1, cv1, df1⟩ := ihp tp g g1 b u1 h hb dp (fun y hy => nt y (Or.inl hy))
        (fun y hy => nn y (Or.inl hy)) (fun y hy e => ap y (Or.inl hy) (Or.inl e)) (fun y hy => hf y (Or.inl hy)) h1
      have hb1 : HoonMap.get g1.blocks o = some (pre A1 b) := by rw [get1, if_pos rfl]
      have R2 := ihq tq g1 g' (pre A1 b) u S1 hb1 dq (fun y hy => Nat.lt_of_lt_of_le (nt y (Or.inr hy)) l1)
        (fun y hy => Nat.lt_of_lt_of_le (nn y (Or.inr hy)) l1) (fun y hy e => ap y (Or.inr hy) (Or.inr e))
        (fun y hy d => by
          rcases (defd_of_ifget hb get1).mp d with d | d
          · exact hf y (Or.inr hy) d
          · rcases df1 y d with e | e
            · exact apq y e hy
            · have := nt y (Or.inr hy); omega) hs
      exact sureRP_seq l1 bo1 get1 (fun y hy => Or.inl (rf1 y hy))
        (fun y hy => (df1 y hy).imp Or.inl id) R2 (fun y hy => Or.inr hy) (fun y hy => Or.inr hy)
        (fun y hy => hy.elim (fun e => Or.inl (cv1 y e)) Or.inr)
    | this d => simp [sureLoop, crashM] at hs
    | both d th tt => simp [sureLoop, crashM] at hs
  | both r hh tt ihh iht =>
    intro tgt g g' b u h hb dt nt nn ap hf hs
    have hr := nn r (Or.inl rfl)
    cases tgt with
    | none =>
      simp only [sureLoop, pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨-, rfl⟩ := hs
      exact sureRP_nil h hb (fun y hy => hy)
    | this d =>
      simp only [sureLoop] at hs
      by_cases e : r = d
      · rw [if_pos e] at hs; cases hs
      rw [if_neg e] at hs
      obtain ⟨S1, bo1, l1, get1⟩ := sureRP_mov (ned := Need.both r hh tt) h hb hr (nt d rfl) (hf d rfl) (Or.inl rfl) hs
      refine ⟨S1, bo1, l1, [Pole.mov r d], get1, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_⟩
      · rcases opsRF_mov_cons hy with e' | ⟨-, e'⟩
        · rw [e']; exact Or.inl rfl
        · exact e'.elim
      · simp only [NMem] at hy; simp [defsOf_mov, hy]
      · simp [defsOf_mov] at hy; exact Or.inl hy
    | pair tp tq =>
      simp only [sureLoop] at hs
      obtain ⟨u1, g1, h1, hs⟩ := bind_some hs
      obtain ⟨dp, dq, apq⟩ := dt
      obtain ⟨S1, bo1, l1, A1, get1, rf1, cv1, df1⟩ := ihh tp g g1 b u1 h hb dp (fun y hy => nt y (Or.inl hy))
        (fun y hy => nn y (Or.inr (Or.inl hy))) (fun y hy e => ap y (Or.inr (Or.inl hy)) (Or.inl e))
        (fun y hy => hf y (Or.inl hy)) h1
      have hb1 : HoonMap.get g1.blocks o = some (pre A1 b) := by rw [get1, if_pos rfl]
      have R2 := iht tq g1 g' (pre A1 b) u S1 hb1 dq (fun y hy => Nat.lt_of_lt_of_le (nt y (Or.inr hy)) l1)
        (fun y hy => Nat.lt_of_lt_of_le (nn y (Or.inr (Or.inr hy))) l1)
        (fun y hy e => ap y (Or.inr (Or.inr hy)) (Or.inr e))
        (fun y hy d => by
          rcases (defd_of_ifget hb get1).mp d with d | d
          · exact hf y (Or.inr hy) d
          · rcases df1 y d with e | e
            · exact apq y e hy
            · have := nt y (Or.inr hy); omega) hs
      exact sureRP_seq l1 bo1 get1 (fun y hy => Or.inr (Or.inl (rf1 y hy)))
        (fun y hy => (df1 y hy).imp Or.inl id) R2 (fun y hy => Or.inr (Or.inr hy)) (fun y hy => Or.inr hy)
        (fun y hy => hy.elim (fun e => Or.inl (cv1 y e)) Or.inr)
    | both d th tt' =>
      simp only [sureLoop] at hs
      by_cases e : r = d
      · rw [if_pos e] at hs; cases hs
      rw [if_neg e] at hs
      obtain ⟨u0, g0, h0, hs⟩ := bind_some hs
      obtain ⟨dth, dtt, aptt, ndh, ndt⟩ := dt
      have hd := nt d (Or.inl rfl)
      obtain ⟨S0, bo0, l0, get0⟩ := sureRP_mov (ned := Need.both r hh tt) h hb hr hd (hf d (Or.inl rfl))
        (Or.inl rfl) h0
      have hb0 : HoonMap.get g0.blocks o = some (pre [Pole.mov r d] b) := by rw [get0, if_pos rfl]
      have dd0 : ∀ y, Defd g0.blocks y → Defd g.blocks y ∨ y = d := fun y dy => by
        rcases (defd_of_ifget hb get0).mp dy with e | e
        · exact Or.inl e
        · simp [defsOf_mov] at e; exact Or.inr e
      obtain ⟨u1, g1, h1, hs⟩ := bind_some hs
      obtain ⟨S1, bo1, l1, A1, get1, rf1, cv1, df1⟩ := ihh th g0 g1 _ u1 S0 hb0 dth
        (fun y hy => Nat.lt_of_lt_of_le (nt y (Or.inr (Or.inl hy))) l0)
        (fun y hy => Nat.lt_of_lt_of_le (nn y (Or.inr (Or.inl hy))) l0)
        (fun y hy e' => ap y (Or.inr (Or.inl hy)) (Or.inr (Or.inl e')))
        (fun y hy dy => by
          rcases dd0 y dy with dy | rfl
          · exact hf y (Or.inr (Or.inl hy)) dy
          · exact ndh hy) h1
      have hb1 : HoonMap.get g1.blocks o = some (pre A1 (pre [Pole.mov r d] b)) := by rw [get1, if_pos rfl]
      obtain ⟨S2, bo2, l2, A2, get2, rf2, cv2, df2⟩ := iht tt' g1 g' _ u S1 hb1 dtt
        (fun y hy => by have := nt y (Or.inr (Or.inr hy)); omega)
        (fun y hy => by have := nn y (Or.inr (Or.inr hy)); omega)
        (fun y hy e' => ap y (Or.inr (Or.inr hy)) (Or.inr (Or.inr e')))
        (fun y hy dy => by
          rcases (defd_of_ifget hb0 get1).mp dy with dy | dy
          · rcases dd0 y dy with dy | rfl
            · exact hf y (Or.inr (Or.inr hy)) dy
            · exact ndt hy
          · rcases df1 y dy with e' | e'
            · exact aptt y e' hy
            · have := nt y (Or.inr (Or.inr hy)); omega) hs
      refine ⟨S2, by omega, by omega, A2 ++ A1 ++ [Pole.mov r d], fun k => ?_, fun y hy => ?_, fun y hy => ?_,
        fun y hy => ?_⟩
      · rw [get2, get1, get0]; by_cases e' : k = o
        · subst e'; simp [pre_pre]
        · simp [e']
      · rcases opsRF_append.mp hy with e' | ⟨-, e'⟩
        · rcases opsRF_append.mp e' with e' | ⟨-, e'⟩
          · exact Or.inr (Or.inr (rf2 y e'))
          · exact Or.inr (Or.inl (rf1 y e'))
        · rcases opsRF_mov_cons e' with e' | ⟨-, e'⟩
          · rw [e']; exact Or.inl rfl
          · exact e'.elim
      · simp only [defsOf_append, List.mem_append]
        rcases hy with e' | e' | e'
        · right; simp [defsOf_mov, e']
        · exact Or.inl (Or.inr (cv1 y e'))
        · exact Or.inl (Or.inl (cv2 y e'))
      · simp only [defsOf_append, List.mem_append] at hy
        rcases hy with (e' | e') | e'
        · rcases df2 y e' with e'' | e''
          · exact Or.inl (Or.inr (Or.inr e''))
          · exact Or.inr ⟨by omega, e''.2⟩
        · rcases df1 y e' with e'' | e''
          · exact Or.inl (Or.inr (Or.inl e''))
          · exact Or.inr ⟨by omega, by omega⟩
        · simp [defsOf_mov] at e'; exact Or.inl (Or.inl e')

/-- **`+coerce-lazy` on a fork-free need at block `o`**: ops in front of `o`
that read first only input registers and define every register of the
need, each once, and fresh ones. -/
theorem raw_coerceP {S : Type} [HoonSet S] {ned : Need} {o : Nat} {laz : Sure S} {less : Cape}
    {g g' : Comp.Gen Map} {b : Blob} {u : Unit} (h : SIP X ρ lo g) (hb : HoonMap.get g.blocks o = some b)
    (nn : NB g.re ned) (dl : Distinct laz.ned) (nl : NB g.re laz.ned)
    (ap : ∀ y, NMem ned y → ¬ NMem laz.ned y) (hf : ∀ y, NMem laz.ned y → ¬ Defd g.blocks y)
    (hc : coerceLazy ned o laz less g = some (u, g')) :
    SIP X ρ lo g' ∧ g'.bo = g.bo ∧ g.re ≤ g'.re ∧ ∃ A,
      (∀ k, HoonMap.get g'.blocks k = if k = o then some (pre A b) else HoonMap.get g.blocks k) ∧
      (∀ y, OpsRF A y → NMem ned y) ∧ (∀ y, NMem laz.ned y → y ∈ defsOf A) ∧
      (∀ y ∈ defsOf A, NMem laz.ned y ∨ (g.re ≤ y ∧ y < g'.re)) := by
  simp only [coerceLazy] at hc
  obtain ⟨lok, g1, hl, hc⟩ := bind_some hc
  obtain ⟨lk, -, el⟩ := Option.map_eq_some_iff.mp hl
  simp only [Prod.mk.injEq] at el
  obtain ⟨rfl, rfl⟩ := el
  obtain ⟨tgt, g2, ht, hc⟩ := bind_some hc
  have L := sureRequireLook_spec ht
  obtain ⟨k2, e2⟩ := L.gen
  have l2 := L.le
  have S2 : SIP X ρ lo g2 := by rw [e2]; exact sip_reg h (by rw [e2] at l2; exact l2)
  have b2 : g2.blocks = g.blocks := by rw [e2]
  have keepT : ∀ y, NMem laz.ned y → NMem tgt y := fun y hy => sureRequireLook_keeps ht hy
  have mT : ∀ y, NMem tgt y → NMem laz.ned y ∨ (g.re ≤ y ∧ y < g2.re) := L.mem
  obtain ⟨S3, bo3, l3, A, get3, rf3, cv3, df3⟩ := raw_sureLoopP ned tgt g2 g' b u S2 (by rw [b2]; exact hb)
    (L.dist dl nl)
    (fun y hy => by rcases mT y hy with e | e
                    · have := nl y e; omega
                    · exact e.2)
    (fun y hy => by have := nn y hy; omega)
    (fun y hy ht' => by
      rcases mT y ht' with e | e
      · exact ap y hy e
      · have := nn y hy; omega)
    (fun y hy d => by
      rw [b2] at d
      rcases mT y hy with e | e
      · exact hf y e d
      · have := h.defd_lt d; omega) hc
  refine ⟨S3, by rw [bo3, e2], by omega, A, fun k => by rw [get3, b2], rf3, fun y hy => cv3 y (keepT y hy),
    fun y hy => ?_⟩
  rcases df3 y hy with e | e
  · rcases mT y e with e' | e'
    · exact Or.inl e'
    · exact Or.inr ⟨e'.1, by omega⟩
  · exact Or.inr ⟨by omega, e.2⟩

end Raw
end SkaModel
end Formalization
