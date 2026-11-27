import lemmas.Compiler.CompSofNouns
import lemmas.Ska.SofModel

/-!
# `+need-ord-edit` (README Gaps 19, item (f))

K arm `5596`, the gate `+sound-far` runs on `%10`.  Its battery `noeBat`
(`CompSofNouns.lean`) tests `=(1 axe)`, then `%none`/`%this`, splits the
need, runs `(cap axe)` (`+cap` of the first layer at `0x1ffff` of its
context), recurses on `(mas axe)` and the half, and joins the rest with
`+cons-need` (arm `350` of its context, `cn_gate_ord`).

* `noe_arm`: the arm builds its gate.
* **`noe_gate`**: for every axis and need the gate is `needOrdEdit`
  (`none` is the crash of `(cap 0)`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

theorem noe_arm (d : Noun) :
    nock d noeArm = some (C noeBat (C (C (A 0) (C (A 0x656e6f6e) (A 0))) d)) := by
  unfold noeArm; simp only [nock_exec]

/-- **`+need-ord-edit` is `needOrdEdit`** on every axis and need, in every
context that holds the first layer at `0x1ffff` and `+cons-need` at `350`
(as `compK` does). -/
theorem noe_gate (KC : Noun) (hK : slot? 0x1ffff KC = some layer1) (hcn : slot? 350 KC = some cnArm) :
    ∀ (axe : Nat) (ned : NeedOrd), nock (C noeBat (C (C (A axe) ned.toNoun) KC)) noeBat
      = (needOrdEdit axe ned).map fun e => C e.1.toNoun e.2.toNoun := by
  have har := cf_arith
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
    intro ned
    rw [needOrdEdit.eq_def]
    by_cases a1 : axe = 1
    · subst a1
      conv => { lhs; arg 2; unfold noeBat }
      simp [nock_exec, NeedOrd.toNoun, Tag.none]
    have hne : ¬ (1 = axe) := fun e => a1 e.symm
    by_cases a0 : axe = 0
    · subst a0
      have hc0 := cap_gate_lt layer1 0 (by decide)
      conv => { lhs; arg 2; unfold noeBat }
      cases ned <;>
        simp [nock_exec, NeedOrd.toNoun, Tag.none, Tag.this, Tag.both, ord_eqCode, hK, cap_arm, cap.arm_at, hc0]
    have h2 : 2 ≤ axe := by omega
    have hcap := cap_gate layer1 har.2.2.2 axe h2
    have hmas := mas_gate layer1 har axe h2
    have hm := mas_lt axe h2
    have hm1 := mas_pos axe h2
    rw [masF_eq_mas] at hmas
    simp only [a1, if_false, show ¬ axe < 2 by omega, dite_false]
    cases ned with
    | none =>
      conv => { lhs; arg 2; unfold noeBat }
      simp [nock_exec, NeedOrd.toNoun, Tag.none, hne]
    | this =>
      conv => { lhs; arg 2; unfold noeBat }
      simp [nock_exec, NeedOrd.toNoun, Tag.none, Tag.this, hne]
    | pair p q =>
      obtain ⟨⟨d1, r1⟩, e1⟩ := needOrdEdit_some (mas axe) hm1 p
      obtain ⟨⟨d2, r2⟩, e2⟩ := needOrdEdit_some (mas axe) hm1 q
      have ih1 := ih (mas axe) hm p
      have ih2 := ih (mas axe) hm q
      rw [e1] at ih1; rw [e2] at ih2
      have hc1 := cn_gate_ord KC r1 q
      have hc2 := cn_gate_ord KC p r2
      simp only [Option.map_some] at ih1 ih2
      conv => { lhs; arg 2; unfold noeBat }
      rcases capF_cases axe h2 with hc | hc
      · have hc' : cap axe = 2 := by rw [← capF_eq_cap]; exact hc
        simp [nock_exec, NeedOrd.toNoun, Tag.none, Tag.this, Tag.both, ord_eqCode, hne, hK, cap_arm, cap.arm_at,
          hcap, hc, hc', mas_arm, mas.arm_at, hmas, ih1, hcn, cnArm, hc1, e1]
      · have hc' : cap axe ≠ 2 := by rw [← capF_eq_cap, hc]; omega
        simp [nock_exec, NeedOrd.toNoun, Tag.none, Tag.this, Tag.both, ord_eqCode, hne, hK, cap_arm, cap.arm_at,
          hcap, hc, hc', mas_arm, mas.arm_at, hmas, ih2, hcn, cnArm, hc2, e2]
    | both p q =>
      obtain ⟨⟨d1, r1⟩, e1⟩ := needOrdEdit_some (mas axe) hm1 p
      obtain ⟨⟨d2, r2⟩, e2⟩ := needOrdEdit_some (mas axe) hm1 q
      have ih1 := ih (mas axe) hm p
      have ih2 := ih (mas axe) hm q
      rw [e1] at ih1; rw [e2] at ih2
      have hc1 := cn_gate_ord KC r1 q
      have hc2 := cn_gate_ord KC p r2
      simp only [Option.map_some] at ih1 ih2
      conv => { lhs; arg 2; unfold noeBat }
      rcases capF_cases axe h2 with hc | hc
      · have hc' : cap axe = 2 := by rw [← capF_eq_cap]; exact hc
        simp [nock_exec, NeedOrd.toNoun, Tag.none, Tag.this, Tag.both, ord_eqCode, hne, hK, cap_arm, cap.arm_at,
          hcap, hc, hc', mas_arm, mas.arm_at, hmas, ih1, hcn, cnArm, hc1, e1, eqCode_self]
      · have hc' : cap axe ≠ 2 := by rw [← capF_eq_cap, hc]; omega
        simp [nock_exec, NeedOrd.toNoun, Tag.none, Tag.this, Tag.both, ord_eqCode, hne, hK, cap_arm, cap.arm_at,
          hcap, hc, hc', mas_arm, mas.arm_at, hmas, ih2, hcn, cnArm, hc2, e2, eqCode_self]

/-- `+need-ord-edit` in `compK`. -/
theorem noe_gateK (axe : Nat) (ned : NeedOrd) :
    nock (C noeBat (C (C (A axe) ned.toNoun) compK)) noeBat
      = (needOrdEdit axe ned).map fun e => C e.1.toNoun e.2.toNoun :=
  noe_gate compK compK_layer1 compK_cn axe ned

end Compiler
end Formalization
