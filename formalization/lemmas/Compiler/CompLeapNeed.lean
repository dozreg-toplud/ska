import lemmas.Compiler.CompLeapN
import lemmas.Compiler.CompInto
import lemmas.Ska.CompLeap

/-!
# `+need-from` and `+need-cut` of the door of `+comp`

The two leaves of `+lazy-leap`.  `+need-from` (door arm `14`, battery
`ndfBat` with its trap `ndfL1`) reads `+cap` and `+mas` of layer 1, behind
layer 2 at axis `524287` of the door's context (`cf_layer1`).  `+need-cut`
(door arm `16375`, `ndcBat`, a gate that slams itself) reads `+cap`, `+mas`
and `+cons-need` (arm `350` of the core `K` at axis `7` of the context,
`CompLib`).  Neither reads `gen`.

Both are linked on every input: `ndf_gate` is `needFrom`, `ndc_gate` is
`needCut`, crashes included (`+cap` of `0` where the model is `none`).
Compared with the Hoon part by part: no departure.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.Ana

set_option linter.unusedSimpArgs false

variable {ctx : Noun}

/-! ## `+need-from` -/

/-- The trap of `+need-from`: the need of the noun at `axe` as a need of the
noun that holds it. -/
theorem ndf_loop (hc : CompIn ctx) (B G : Noun) (ned : Need) :
    ∀ axe, 1 ≤ axe →
    nock (C ndfL1 (C B (C (C (A axe) ned.toNoun) (C comp.door (C G ctx))))) ndfL1
      = some (fromPath ned axe).toNoun := by
  have hl1 := cf_layer1 hc
  have har := cf_arith
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
    intro ha
    by_cases a1 : axe = 1
    · subst a1
      nock_open ndfL1
      rw [fromPath.eq_def]
      simp [nock_exec]
    · have h2 : 2 ≤ axe := by omega
      have hcap := cap_gate layer1 har.2.2.2 axe h2
      have hmas := mas_gate layer1 har axe h2
      have hm1 : 1 ≤ masF axe := masF_pos axe h2
      have ihm := ih (masF axe) (by rw [masF_eq_mas]; exact mas_lt axe h2) hm1
      have hne : ¬ (1 = axe) := by omega
      nock_open ndfL1
      rw [fromPath.eq_def]
      rcases capF_cases axe h2 with hc2 | hc3
      · simp [nock_exec, hl1, hne, cap_arm, cap.arm_at, hcap, hc2, mas_arm, mas.arm_at, hmas, ihm,
          show ¬ axe ≤ 1 by omega, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none]
      · simp [nock_exec, hl1, hne, cap_arm, cap.arm_at, hcap, hc3, mas_arm, mas.arm_at, hmas, ihm,
          show ¬ axe ≤ 1 by omega, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none]

/-- **`+need-from`** is `needFrom` on every axis and need, in every door core
whose context has layer 2. -/
theorem ndf_gate (hc : CompIn ctx) (G : Noun) (axe : Nat) (ned : Need) :
    nock (C ndfBat (C (C (A axe) ned.toNoun) (C comp.door (C G ctx)))) ndfBat
      = (needFrom axe ned).map Need.toNoun := by
  have hl1 := cf_layer1 hc
  by_cases hn : ned = Need.none
  · subst hn
    nock_open ndfBat
    simp [nock_exec, needFrom, Need.toNoun, Tag.none]
  by_cases a0 : axe = 0
  · subst a0
    have hl := cap_gate_lt layer1 0 (by decide)
    conv => lhs; arg 2; unfold ndfBat
    cases ned with
    | none => exact absurd rfl hn
    | pair p q =>
      obtain ⟨a, b, hp⟩ := cd_need_cell p
      unfold ndfL1
      simp [nock_exec, needFrom, Need.toNoun, hp, hl1, cap_arm, cap.arm_at, hl]
    | this r =>
      unfold ndfL1
      simp [nock_exec, needFrom, Need.toNoun, Tag.this, Tag.none, hl1, cap_arm, cap.arm_at, hl]
    | both r h t =>
      unfold ndfL1
      simp [nock_exec, needFrom, Need.toNoun, Tag.both, Tag.none, hl1, cap_arm, cap.arm_at, hl]
  have hlp := ndf_loop hc ndfBat G ned axe (by omega)
  conv => lhs; arg 2; unfold ndfBat
  cases ned with
  | none => exact absurd rfl hn
  | pair p q =>
    obtain ⟨a, b, hp⟩ := cd_need_cell p
    simp only [Need.toNoun, hp] at hlp
    simp [nock_exec, needFrom, Need.toNoun, hp, hlp, a0]
  | this r =>
    simp only [Need.toNoun, Tag.this] at hlp
    simp [nock_exec, needFrom, Need.toNoun, Tag.this, Tag.none, hlp, a0]
  | both r h t =>
    simp only [Need.toNoun, Tag.both] at hlp
    simp [nock_exec, needFrom, Need.toNoun, Tag.both, Tag.none, hlp, a0]

/-! ## `+need-cut` -/

/-- The noun of what `+need-cut` returns. -/
def cutNoun : Option (Need × Need) → Noun := unitNoun fun e => C e.1.toNoun e.2.toNoun

/-- **`+need-cut`** is `needCut` on every axis and need, in every door core
whose context has layer 2 and `+cons-need` in `K` (`CompLib`): `~` when a
noun that holds the part is wanted in a register, a crash on `+cap` of `0`. -/
theorem ndc_gate (hc : CompIn ctx) (hl : CompLib ctx) (G : Noun) :
    ∀ (ned : Need) (axe : Nat),
    nock (C ndcBat (C (C (A axe) ned.toNoun) (C comp.door (C G ctx)))) ndcBat
      = (needCut axe ned).map cutNoun := by
  obtain ⟨K, h7, _, hcn⟩ := hl
  have hl1 := cf_layer1 hc
  have har := cf_arith
  intro ned
  induction ned with
  | none =>
    intro axe
    nock_open ndcBat
    by_cases a1 : axe = 1
    · subst a1; simp [nock_exec, needCut, Need.toNoun, cutNoun, unitNoun, Tag.none]
    · have a1' : ¬ (1 = axe) := fun h => a1 h.symm
      simp [nock_exec, needCut, Need.toNoun, cutNoun, unitNoun, a1, a1', Tag.none]
  | this r =>
    intro axe
    nock_open ndcBat
    by_cases a1 : axe = 1
    · subst a1; simp [nock_exec, needCut, Need.toNoun, cutNoun, unitNoun, Tag.none]
    · have a1' : ¬ (1 = axe) := fun h => a1 h.symm
      simp [nock_exec, needCut, Need.toNoun, cutNoun, unitNoun, a1, a1', Tag.none, Tag.this]
  | both r h t =>
    intro axe
    nock_open ndcBat
    by_cases a1 : axe = 1
    · subst a1; simp [nock_exec, needCut, Need.toNoun, cutNoun, unitNoun, Tag.none]
    · have a1' : ¬ (1 = axe) := fun h => a1 h.symm
      simp [nock_exec, needCut, Need.toNoun, cutNoun, unitNoun, a1, a1', Tag.none, Tag.this,
        Tag.both]
  | pair p q ihp ihq =>
    intro axe
    obtain ⟨a, b, hp⟩ := cd_need_cell p
    by_cases a1 : axe = 1
    · subst a1
      nock_open ndcBat
      simp [nock_exec, needCut, Need.toNoun, cutNoun, unitNoun, Tag.none]
    have a1' : ¬ (1 = axe) := fun h => a1 h.symm
    by_cases a0 : axe = 0
    · subst a0
      have hl := cap_gate_lt layer1 0 (by decide)
      nock_open ndcBat
      simp [nock_exec, needCut, Need.toNoun, hp, hl1, cap_arm, cap.arm_at, hl]
    have h2 : 2 ≤ axe := by omega
    have hcap := cap_gate layer1 har.2.2.2 axe h2
    have hmas := mas_gate layer1 har axe h2
    have ip := ihp (masF axe)
    have iq := ihq (masF axe)
    rw [hp] at ip
    nock_open ndcBat
    rcases capF_cases axe h2 with hc2 | hc3
    · have hcm : cap axe = 2 := by rw [← capF_eq_cap]; exact hc2
      cases e : needCut (masF axe) p with
      | none =>
        rw [e] at ip
        simp [nock_exec, needCut, Need.toNoun, hp, hl1, cap_arm, cap.arm_at, hcap, hc2, hcm,
          mas_arm, mas.arm_at, hmas, ip, a0, a1, a1', ← masF_eq_mas, e]
      | some k =>
        rw [e] at ip
        cases k with
        | none =>
          simp [nock_exec, needCut, Need.toNoun, hp, hl1, cap_arm, cap.arm_at, hcap, hc2, hcm,
            mas_arm, mas.arm_at, hmas, ip, a0, a1, a1', ← masF_eq_mas, e, cutNoun, unitNoun]
        | some dr =>
          obtain ⟨d, r⟩ := dr
          simp [nock_exec, needCut, Need.toNoun, hp, hl1, cap_arm, cap.arm_at, hcap, hc2, hcm,
            mas_arm, mas.arm_at, hmas, ip, a0, a1, a1', ← masF_eq_mas, e, cutNoun, unitNoun, h7,
            hcn, cnArm, cn_gate]
    · have hcm : cap axe = 3 := by rw [← capF_eq_cap]; exact hc3
      cases e : needCut (masF axe) q with
      | none =>
        rw [e] at iq
        simp [nock_exec, needCut, Need.toNoun, hp, hl1, cap_arm, cap.arm_at, hcap, hc3, hcm,
          mas_arm, mas.arm_at, hmas, iq, a0, a1, a1', ← masF_eq_mas, e]
      | some k =>
        rw [e] at iq
        cases k with
        | none =>
          simp [nock_exec, needCut, Need.toNoun, hp, hl1, cap_arm, cap.arm_at, hcap, hc3, hcm,
            mas_arm, mas.arm_at, hmas, iq, a0, a1, a1', ← masF_eq_mas, e, cutNoun, unitNoun]
        | some dr =>
          obtain ⟨d, r⟩ := dr
          have hcg := cn_gate K p r
          rw [hp] at hcg
          simp [nock_exec, needCut, Need.toNoun, hp, hl1, cap_arm, cap.arm_at, hcap, hc3, hcm,
            mas_arm, mas.arm_at, hmas, iq, a0, a1, a1', ← masF_eq_mas, e, cutNoun, unitNoun, h7,
            hcn, cnArm, hcg]

end Compiler
end Formalization
