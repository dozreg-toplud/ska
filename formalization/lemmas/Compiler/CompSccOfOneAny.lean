import lemmas.Compiler.CompSccOfAnyK
import lemmas.Compiler.CompShapeColBake

/-!
# One-bell callees without `BakeRunO` (README Gaps 19 (g), step 4)

* `OneCalleeA`: `OneCallee` without track A's `BakeRunO` (`oneCalleeA_of`).
* **`calleeCompiled_oneKA`**: `calleeCompiled_oneKP` through `csi_gate_scc_one_f_six_B_any` and
  `tsAny_holds` (track A's one-bell top with no hypothesis on the bake).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.SccLoop

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **`OneCallee` without `BakeRunO`.** -/
def OneCalleeA (env : CallEnv) (SC0 CODE CALLS : Noun) (inl : Noun → Option Nomm) (b : Bell) : Prop :=
  ∃ (cape : Cape) (DATA FOL : Noun) (nm : Nomm) (fuel : Nat) (envb : CallEnv)
    (p : NextL CSet × Gen (TreapMap mugF)) (st : Straight (TreapMap mugF)),
    b = ⟨Sock.mk cape DATA, FOL⟩ ∧
    getF mugF (C (C cape.toNoun DATA) FOL) SC0 = some (C (A 0) (setOne (C (C cape.toNoun DATA) FOL))) ∧
    inl (C (C cape.toNoun DATA) FOL) = some nm ∧ NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS ∧
    (∃ V, getF mugF (C (C cape.toNoun DATA) FOL) CODE = some (C (A 0) V) ∧ slot? 2 V = some nm.toNoun) ∧
    SixOk nm = true ∧ Bake.NoAx0 nm ∧ FixRet envb nm cape fuel ∧ CompOne env envb cape DATA nm fuel p st b

theorem oneCalleeA_of {env : CallEnv} {SC0 CODE CALLS : Noun} {inl : Noun → Option Nomm} {b : Bell}
    (h : OneCallee env SC0 CODE CALLS inl b) : OneCalleeA env SC0 CODE CALLS inl b := by
  obtain ⟨cape, DATA, FOL, nm, fuel, envb, p, st, h1, h2, h3, h4, h5, h6, h7, h8, -, h10⟩ := h
  exact ⟨cape, DATA, FOL, nm, fuel, envb, p, st, h1, h2, h3, h4, h5, h6, h7, h8, h10⟩

/-- **`calleeCompiled_oneKP` without `BakeRunO`** (track A's `csi_gate_scc_one_f_six_B_any` with
`tsAny_holds`; a one-bell callee missing inside a member run: the bells in progress `P`, `Pf` do not hold it; the `+put:by` of the one bell keeps the bells
`Pf` missing). -/
theorem calleeCompiled_oneKA {ctx CODE JETS CALLS JH SC0 : Noun} (h7 : slot? 7 ctx = some compK)
    (hl : slot? 26 ctx = some (C CODE (C JETS CALLS))) (hj : slot? 54 ctx = some JH)
    (h107 : slot? 107 ctx = some CALLS) (env envb : CallEnv) (cape : Cape) (DATA FOL : Noun) (nm : Nomm) (fuel : Nat)
    (p : NextL CSet × Gen (TreapMap mugF)) (st : Straight (TreapMap mugF)) (inl : Noun → Option Nomm)
    (hsc : getF mugF (C (C cape.toNoun DATA) FOL) SC0 = some (C (A 0) (setOne (C (C cape.toNoun DATA) FOL))))
    (hinl : inl (C (C cape.toNoun DATA) FOL) = some nm)
    (hcalls : NoSelfCall (C (C cape.toNoun DATA) FOL) CALLS)
    (hcode : ∃ V, getF mugF (C (C cape.toNoun DATA) FOL) CODE = some (C (A 0) V) ∧ slot? 2 V = some nm.toNoun)
    (hn : SixOk nm = true) (hax : Bake.NoAx0 nm) (hfix : FixRet envb nm cape fuel)
    (hone : CompOne env envb cape DATA nm fuel p st ⟨Sock.mk cape DATA, FOL⟩) (P Pf : Noun → Prop)
    (hPb : ¬ P (C (C cape.toNoun DATA) FOL)) (hPfb : ¬ Pf (C (C cape.toNoun DATA) FOL)) :
    CalleeCompiledP env (RKP SC0 inl Pf) P ctx ⟨Sock.mk cape DATA, FOL⟩ st.need := by
  intro x NR MO SC RS hA hR hcx h0
  obtain ⟨xc, xs, xf⟩ := x
  simp only at hcx h0 ⊢
  subst hcx
  obtain ⟨hns, NR1, MO1, SC1, INL, SU, hc1, hnr, hsu, hag, hsa⟩ := hA
  obtain ⟨⟨⟨NR2, MO2, INL2, SU2, hc2, hil, hin⟩, NRc, hNRc, hcl⟩, hPf0⟩ := hR
  simp only [cacheN, Noun.cell.injEq] at hc1
  obtain ⟨e1, e2, e3, e4⟩ := hc1
  subst NR1 MO1 SC1 RS
  simp only [cacheN, Noun.cell.injEq] at hc2
  obtain ⟨e5, e6, e7, e8, e9⟩ := hc2
  subst NR2 MO2 INL2 SU2 SC
  have eNc : NRc = NR := by simpa [nock_exec] using hNRc.symm
  subst NRc
  have hsu0 : getF mugF (C (C cape.toNoun DATA) FOL) SU = some (A 0) := by
    rcases getF_cases (k := (C (C cape.toNoun DATA) FOL)) hsu with h | ⟨v, hv⟩
    · exact h
    · obtain ⟨-, u, hu⟩ := hsa ⟨Sock.mk cape DATA, FOL⟩ v hv hPb
      exact absurd (hu.symm.trans h0) (by simp)
  obtain ⟨INL', hiok, hil', hin'⟩ : ∃ INL', InlOK (C (C cape.toNoun DATA) FOL) CODE INL nm INL' ∧ IsMap mugF INL' ∧
      ∀ k nm', inl k = some nm' → getF mugF k INL' = some (A 0) ∨ getF mugF k INL' = some (C (A 0) nm'.toNoun) := by
    rcases hin (C (C cape.toNoun DATA) FOL) nm hinl with hi0 | hi1
    · obtain ⟨INL', hp, hmo, -⟩ := putF_spec mugF INL (C (C cape.toNoun DATA) FOL) nm.toNoun hil
      refine ⟨INL', Or.inr ⟨hi0, hcode, hp⟩, hmo, fun k nm' hk => ?_⟩
      by_cases e : k = (C (C cape.toNoun DATA) FOL)
      · subst e
        rw [hinl] at hk
        cases hk
        exact Or.inr (getF_put_self hil hp).2
      · rw [getF_put_other hil hp e]
        exact hin k nm' hk
    · exact ⟨INL, Or.inl ⟨hi1, rfl⟩, hil, hin⟩
  obtain ⟨hrun, hfin, hneed, hsure⟩ := hone
  have hcsi := csi_gate_scc_one_f_six_B_any (fun _ => True) tsAny_holds cape DATA FOL CODE JETS CALLS JH NR MO SC0 INL SU
    h0 hnr hsu hcalls nm INL' hiok envb hn hax (fun nex => scOrd fuel nex cape)
    (scAt_of_scRet envb nm cape fuel (scRet_of_fixRet envb hn hax cape fuel hfix)) (fun _ _ _ => trivial)
  obtain ⟨NRU, hpn, hmn, -⟩ := putF_spec mugF NR (C (C cape.toNoun DATA) FOL) st.toNoun hnr
  obtain ⟨SUU, hps, hms, -⟩ := putF_spec mugF SU (C (C cape.toNoun DATA) FOL) (sccSur p.1 cape).toNoun hsu
  rw [hrun] at hcsi
  simp only [Option.bind_some, hfin, hpn, hps, Option.map_some] at hcsi
  have hst : slot? 2 st.toNoun = some st.need.toNoun := by simp [Straight.toNoun, nock_exec]
  have hmiss := cccMiss_hit_one h7 hl hj h107 ⟨Sock.mk cape DATA, FOL⟩ st.need (RS := C INL SU) (SO := xs) (SS := xf)
    hsc hcsi hst
  have hBb : ∀ b' : Bell, b'.toNoun = C (C cape.toNoun DATA) FOL → b' = ⟨Sock.mk cape DATA, FOL⟩ := by
    intro b' e
    obtain ⟨l, f⟩ := b'
    cases l <;> simp [Bell.toNoun, Sock.toNoun] at e
    · obtain ⟨⟨h1, h2⟩, h3⟩ := e
      subst h2 h3
      have := congrArg Cape.ofNoun? h1
      simp [Cape.ofNoun?_toNoun] at this
      subst this
      rfl
  refine ⟨cacheN NRU MO SC0 INL' SUU, hmiss, ext_one hnr hsu h0 hsu0 hpn hps, ?_, ?_, ?_⟩
  · refine ⟨fun o => hns o, NRU, MO, SC0, INL', SUU, rfl, hmn, hms, fun b' u hu => ?_, fun b' v hv hP => ?_⟩
    · rcases getF_put_cases hnr hpn hu with ⟨e, rfl⟩ | ⟨-, hu'⟩
      · obtain rfl := hBb b' e
        exact ⟨⟨st.need, hneed, hst⟩, _, (getF_put_self hsu hps).2⟩
      · obtain ⟨h1, v, hv⟩ := hag b' u hu'
        exact ⟨h1, v, mapSub_put hsu hsu0 hps _ _ hv⟩
    · rcases getF_put_cases hsu hps hv with ⟨e, rfl⟩ | ⟨-, hv'⟩
      · obtain rfl := hBb b' e
        exact ⟨by rw [hsure], _, (getF_put_self hnr hpn).2⟩
      · obtain ⟨h1, u, hu⟩ := hsa b' v hv' hP
        exact ⟨h1, u, mapSub_put hnr h0 hpn _ _ hu⟩
  · refine ⟨⟨⟨NRU, MO, INL', SUU, rfl, hil', hin'⟩, NRU, by simp [cacheN, nock_exec], sccClosed_put hnr h0 hpn hsc hcl⟩,
      fun N hN k hk => ?_⟩
    have eN : N = NRU := by
      have e : slot? 2 (cacheN NRU MO SC0 INL' SUU) = some N := hN
      rw [cacheN_slot2] at e; exact (Option.some.inj e).symm
    subst eN
    have hne : k ≠ C (C cape.toNoun DATA) FOL := fun e => hPfb (e ▸ hk)
    rw [csGetF_put_ne hnr hpn hne]
    exact hPf0 NR (by simp [cacheN, nock_exec]) k hk
  · refine ⟨NRU, st.toNoun, ?_, (getF_put_self hnr hpn).2⟩
    show slot? 2 (cacheN NRU MO SC0 INL' SUU) = some NRU
    simp [cacheN, nock_exec]

end Compiler
end Formalization
