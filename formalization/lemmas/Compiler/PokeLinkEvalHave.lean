import lemmas.Compiler.PokeLinkEvalBase
import lemmas.Compiler.Axes
import lemmas.Hoon.Mink

/-!
# `+eval-finalized`: `+have`, and the cases `%0` and `%10` (track P, README Gaps 23)

* `ef_htrap`: the trap of `+have` (`efHTrap`) on `[sock axe]`, `axe ≥ 1`,
  computes `haveAx`; it reads `+cap`, `+mas` of `layer1` and `+hed`, `+tel`
  of `+so` through the context `Kc` of the gate (the `|^` core).
* `ef_hgate`: the gate (`efHGate`) is `haveO`: its assert `?<  =(0 axe)`.
* `ef_0`, `ef_10`: the cases `%0` (`+pull:so`, `+have`) and `%10`
  (`+have`, `+darn:so`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeF SkaModel.PokeM

set_option linter.unusedSimpArgs false

/-- The flag noun of a boolean (`&` is `0`). -/
def efFl (h : Bool) : Noun := A (if h then 0 else 1)

set_option maxHeartbeats 1000000 in
/-- **The trap of `+have`**. -/
theorem ef_htrap (Kc : Noun) (hlib : slot? 255 Kc = some lib) (hl1 : slot? 0x7ffff Kc = some layer1) :
    ∀ (axe : Nat) (s : Sock), 1 ≤ axe →
      nock (C efHTrap (C efHGate (C (C s.toNoun (A axe)) Kc))) efHTrap = some (efFl (haveAx s axe)) := by
  have har := cf_arith
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
    intro s ha
    by_cases a1 : axe = 1
    · subst a1
      conv => lhs; arg 2; rw [efHTrap_eq]
      rw [haveAx.eq_def]; simp [nock_exec, efFl]
    · have h2 : 2 ≤ axe := by omega
      have hcap := cap_gate layer1 har.2.2.2 axe h2
      have hmas := mas_gate layer1 har axe h2
      have hm1 : 1 ≤ masF axe := masF_pos axe h2
      have ihm := fun s => ih (masF axe) (by rw [masF_eq_mas]; exact mas_lt axe h2) s hm1
      have hhed := ihm (So.hed s)
      have htel := ihm (So.tel s)
      have hne : ¬ (1 = axe) := by omega
      have hle : ¬ axe ≤ 1 := by omega
      have hh := so_hed_gate (C so.battery lib) s
      have ht := so_tel_gate (C so.battery lib) s
      conv => lhs; arg 2; rw [efHTrap_eq]
      rw [haveAx.eq_def]
      rcases s with _ | ⟨c, d⟩
      · simp only [Sock.toNoun] at hh ht hhed htel ⊢
        rcases capF_cases axe h2 with hc | hc
        · simp [nock_exec, hne, hle, hl1, hlib, cap_arm, cap.arm_at, hcap, mas_arm, mas.arm_at, hmas, hc,
            so.lib.arm_at, so_lib_arm, so.hed.arm_at, so_hed_arm, hh, hhed, ← capF_eq_cap, ← masF_eq_mas]
        · simp [nock_exec, hne, hle, hl1, hlib, cap_arm, cap.arm_at, hcap, mas_arm, mas.arm_at, hmas, hc,
            so.lib.arm_at, so_lib_arm, so.tel.arm_at, so_tel_arm, ht, htel, ← capF_eq_cap, ← masF_eq_mas]
      · rcases c with _ | _ | ⟨ch, ct⟩
        all_goals simp only [Sock.toNoun, Cape.toNoun] at hh ht hhed htel ⊢
        all_goals first
          | (simp [nock_exec, hne, hle, Sock.toNoun, Cape.toNoun, efFl]; done)
          | skip
        all_goals rcases capF_cases axe h2 with hc | hc
        all_goals first
          | (simp [nock_exec, hne, hle, hl1, hlib, cap_arm, cap.arm_at, hcap, mas_arm, mas.arm_at, hmas, hc,
              so.lib.arm_at, so_lib_arm, so.hed.arm_at, so_hed_arm, hh, hhed, ← capF_eq_cap, ← masF_eq_mas]; done)
          | (simp [nock_exec, hne, hle, hl1, hlib, cap_arm, cap.arm_at, hcap, mas_arm, mas.arm_at, hmas, hc,
              so.lib.arm_at, so_lib_arm, so.tel.arm_at, so_tel_arm, ht, htel, ← capF_eq_cap, ← masF_eq_mas]; done)

/-- **The gate `+have`**: `haveO`, its assert `?<  =(0 axe)`. -/
theorem ef_hgate (Kc : Noun) (hlib : slot? 255 Kc = some lib) (hl1 : slot? 0x7ffff Kc = some layer1)
    (s : Sock) (axe : Nat) (h : Bool) (hh : haveO s axe = some h) :
    nock (C efHGate (C (C s.toNoun (A axe)) Kc)) efHGate = some (efFl h) := by
  unfold haveO at hh
  by_cases a0 : axe = 0
  · simp [a0] at hh
  · simp only [a0, if_false, Option.some.injEq] at hh; subst hh
    have ht := ef_htrap Kc hlib hl1 axe s (by omega)
    have hne : ¬ (0 = axe) := by omega
    conv => lhs; arg 2; rw [efHGate_eq]
    simp [nock_exec, hne, ht]

/-! ## The cases `%0` and `%10` -/

section Cases

variable (b : Bell) (M : FinMap Bell Noun)

/-- The arm `+have` builds its gate on the core. -/
theorem ef_have_arm (K : Noun) : nock K efHave = some (C efHGate (C (C (C (A 1) (A 0)) (A 0)) K)) := by
  conv => lhs; arg 2; rw [efHave_eq]
  simp [nock_exec]

theorem efK_lib (n : Nomm) (sub : Sock) : slot? 255 (efK b M n sub) = some lib := by
  simp [efK, nock_exec, ana_lib7]

theorem efK_l1 (n : Nomm) (sub : Sock) : slot? 0x7ffff (efK b M n sub) = some layer1 := by
  simp [efK, nock_exec, ana_l1]

theorem ef_0 (p : Nat) : EfLoopAt b M (Nomm.n0 p) := by
  intro sub r h
  rw [ef_disp_0, efC0_eq]
  by_cases p0 : p = 0
  · subst p0; simp [efGo] at h; subst h
    simp [efK, nock_exec, Nomm.toNoun, efRes, flagNoun, Sock.toNoun, Cape.toNoun, Sock.dunno]
  · simp only [efGo, p0, if_false] at h
    cases e : So.pull sub p with
    | none => simp [e] at h
    | some sp =>
      cases e2 : haveO sub p with
      | none => simp [e, e2] at h
      | some hv =>
        simp [e, e2] at h; subst h
        have hpl := so_pull_pill sub p
        rw [e] at hpl
        have hhv := ef_hgate (efK b M (Nomm.n0 p) sub) (efK_lib b M _ sub) (efK_l1 b M _ sub) sub p hv e2
        unfold efK at hhv ⊢
        simp only [Nomm.toNoun] at hhv ⊢
        have hne : ¬ (0 = p) := fun h => p0 h.symm
        cases hv <;> simp [nock_exec, hne, hpl, hhv, ef_have_arm, ana_lib7, so.lib.arm_at, so_lib_arm, so.pull.arm_at,
          so_pull_arm, efRes, flagNoun, efFl]

set_option maxHeartbeats 2000000 in
theorem ef_10 (a : Nat) (v q : Nomm) (ihv : EfLoopAt b M v) (ihq : EfLoopAt b M q) :
    EfLoopAt b M (Nomm.n10 a v q) := by
  intro sub r h
  simp only [efGo] at h
  cases e : efGo (accFt M) sub v with
  | none => simp [e] at h
  | some rd =>
    cases e2 : efGo (accFt M) sub q with
    | none => simp [e, e2] at h
    | some rr =>
      cases e3 : haveO rr.1 a with
      | none => simp [e, e2, e3] at h
      | some hv =>
        cases e4 : So.darn rr.1 a rd.1 with
        | none => simp [e, e2, e3, e4] at h
        | some sd =>
          simp [e, e2, e3, e4] at h; subst h
          have hd := ihv sub rd e
          have hq := ihq sub rr e2
          have hdn := so_darn_pill rr.1 a rd.1
          rw [e4] at hdn
          have hhv := ef_hgate (efK b M (Nomm.n10 a v q) sub) (efK_lib b M _ sub) (efK_l1 b M _ sub) rr.1 a hv e3
          rw [ef_disp_10, efC10_eq]
          unfold efK at hd hq hhv ⊢
          obtain ⟨s1, p1, t1⟩ := rd
          obtain ⟨s2, p2, t2⟩ := rr
          simp only [efRes, flagNoun] at hd hq ⊢
          simp only [Nomm.toNoun] at hhv ⊢
          cases p1 <;> cases t1 <;> cases p2 <;> cases t2 <;> cases hv <;>
            simp [nock_exec, hd, hq, hhv, hdn, ef_have_arm, ana_lib7, so.lib.arm_at, so_lib_arm, so.darn.arm_at,
              so_darn_arm, efFl]

end Cases

end Compiler
end Formalization
