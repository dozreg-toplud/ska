import lemmas.Compiler.CompStraightN

/-!
# `+coerce-lazy` on a fork-free lazy need

The arm `+coerce-lazy` (door battery axis `3580`, core axis `5628`,
`%comp-coerce-lazy`, its gate body `czBody`) on `[ned o [sure ~ ~] less]`:

1. the `+rep:in` over `lok.sure` with the gate `czGate`: an axis is kept
   unless `+axe-in-less-cape` (arm `95` of `K`, `aic_gate`) or `+axe-in-need`
   (arm `0x5dd4` of `K`, `ain_gate`) holds of it; the fold is `coerceLok`
   (`cz_lok`);
2. `+sure-require-look` of the sure need with that set
   (`comp_sure_require_look`);
3. the trap `sure-loop` (`czLoop`) over the input need and the target need:
   `+kern-need` and `+add-ops` at a `%this` (with `o` not in `soft`), the
   `%mov` of a `%both`, the recursion on the halves (`cz_loop`); it is
   `sureLoop`;
4. the test `&(?=(~ fork.laz) ?=(~ bond.laz))`, true here, so `gen`.

`cz_gate`: the gate on a fork-free `laz` is `coerceLazy`, given `x.NoSoft`
(the model has no test `(~(has by soft.gen) o)` in its `%this` case).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## `+axe-in-less-cape` and `+axe-in-need` -/

def aicTrap : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 28)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 29))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 1)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 22) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 60))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 2)) (C (A 0) (A 2)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (C (A 8) (C (C (A 9) (C (A 47) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 60))) (C (A 0) (A 2)))))))) (C (A 0) (A 58)))) (C (A 0) (A 1)))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 3)) (C (A 0) (A 2))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (C (A 8) (C (C (A 9) (C (A 47) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 60))) (C (A 0) (A 2)))))))) (C (A 0) (A 59)))) (C (A 0) (A 1)))))))))))))))))))))

def aicBody : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 12)))) (C (C (A 0) (A 0)) (C (A 8) (C (C (A 1) aicTrap) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))))

def ainTrap : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 28)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 58)))) (C (C (A 1) (A 0)) (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 58))))))) (C (C (A 1) (A 1)) (C (A 6) (C (C (A 3) (C (A 0) (A 58))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (C (A 8) (C (C (A 9) (C (A 47) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 60))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 22) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 60))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 2)) (C (A 0) (A 2)))) (C (C (A 0) (A 122)) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 3)) (C (A 0) (A 2))))) (C (A 0) (A 123))))))))))) (C (A 0) (A 1)))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 58))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (C (A 8) (C (C (A 9) (C (A 47) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 60))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 22) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 60))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 2)) (C (A 0) (A 2)))) (C (C (A 0) (A 494)) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 3)) (C (A 0) (A 2))))) (C (A 0) (A 495))))))))))) (C (A 0) (A 1)))))))))))))))))

def ainBody : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 12)))) (C (C (A 0) (A 0)) (C (A 8) (C (C (A 1) ainTrap) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))))

theorem aic_at : slot? 95 compK
    = some (C (A 8) (C (C (A 1) (C (A 0) (A 1))) (C (C (A 1) aicBody) (C (A 0) (A 1))))) := by kernel_rfl

theorem ain_at : slot? 0x5dd4 compK
    = some (C (A 8) (C (C (A 1) (C (A 0) (C (A 0x656e6f6e) (A 0)))) (C (C (A 1) ainBody) (C (A 0) (A 1))))) := by
  kernel_rfl

/-- **The trap of `+axe-in-less-cape`** from an axis `≥ 1`: `axeInCape`. -/
theorem aic_loop (B KC : Noun) (hK : slot? 0x1ffff KC = some layer1) :
    ∀ axe, 1 ≤ axe → ∀ less : Cape,
    nock (C aicTrap (C B (C (C (A axe) less.toNoun) KC))) aicTrap = some (loob (axeInCape axe less)) := by
  have har := cf_arith
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
    intro ha less
    by_cases a1 : axe = 1
    · subst a1
      rw [axeInCape.eq_def]
      conv => { lhs; arg 2; unfold aicTrap }
      simp [nock_exec, loob]
    · have h2 : 2 ≤ axe := by omega
      have hcap := cap_gate layer1 har.2.2.2 axe h2
      have hmas := mas_gate layer1 har axe h2
      have hm1 : 1 ≤ masF axe := masF_pos axe h2
      have hne : ¬ (1 = axe) := by omega
      have hna : ¬ (axe ≤ 1) := by omega
      rw [axeInCape.eq_def]
      conv => { lhs; arg 2; unfold aicTrap }
      cases less with
      | yes => simp [nock_exec, Cape.toNoun, hne, hna, loob]
      | no => simp [nock_exec, Cape.toNoun, hne, hna, loob]
      | cell h t =>
        have ihh := ih (masF axe) (by rw [masF_eq_mas]; exact mas_lt axe h2) hm1 h
        have iht := ih (masF axe) (by rw [masF_eq_mas]; exact mas_lt axe h2) hm1 t
        rcases capF_cases axe h2 with hc2 | hc3
        · simp [nock_exec, Cape.toNoun, hne, hna, hK, cap_arm, cap.arm_at, hcap, hc2, mas_arm, mas.arm_at, hmas,
            ← capF_eq_cap, ← masF_eq_mas, ihh]
        · simp [nock_exec, Cape.toNoun, hne, hna, hK, cap_arm, cap.arm_at, hcap, hc3, mas_arm, mas.arm_at, hmas,
            ← capF_eq_cap, ← masF_eq_mas, iht]

/-- **The gate of `+axe-in-less-cape`**: `axeInLessCape`, a crash at `0`. -/
theorem aic_gate (KC : Noun) (hK : slot? 0x1ffff KC = some layer1) (axe : Nat) (less : Cape) :
    nock (C aicBody (C (C (A axe) less.toNoun) KC)) aicBody = (axeInLessCape axe less).map loob := by
  unfold axeInLessCape
  by_cases a0 : axe = 0
  · subst a0
    conv => { lhs; arg 2; unfold aicBody }
    simp [nock_exec]
  · have hl := aic_loop aicBody KC hK axe (by omega) less
    have a0' : ¬ (0 = axe) := fun h => a0 h.symm
    conv => { lhs; arg 2; unfold aicBody }
    generalize aicTrap = T at hl
    simp [nock_exec, a0, a0', hl]

/-- **The trap of `+axe-in-need`** from an axis `≥ 1`: `axeInNeedL`. -/
theorem ain_loop (B KC : Noun) (hK : slot? 0x1ffff KC = some layer1) :
    ∀ axe, 1 ≤ axe → ∀ ned : Need,
    nock (C ainTrap (C B (C (C (A axe) ned.toNoun) KC))) ainTrap = some (loob (axeInNeedL axe ned)) := by
  have har := cf_arith
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
    intro ha ned
    by_cases a1 : axe = 1
    · subst a1
      rw [axeInNeedL.eq_def]
      conv => { lhs; arg 2; unfold ainTrap }
      simp [nock_exec, loob]
    · have h2 : 2 ≤ axe := by omega
      have hcap := cap_gate layer1 har.2.2.2 axe h2
      have hmas := mas_gate layer1 har axe h2
      have hm1 : 1 ≤ masF axe := masF_pos axe h2
      have hm := mas_lt axe h2
      have hne : ¬ (1 = axe) := by omega
      have hna : ¬ (axe ≤ 1) := by omega
      rw [axeInNeedL.eq_def]
      conv => { lhs; arg 2; unfold ainTrap }
      cases ned with
      | none => simp [nock_exec, Need.toNoun, Tag.none, hne, hna, loob]
      | this r => simp [nock_exec, Need.toNoun, Tag.none, Tag.this, hne, hna, loob]
      | pair p q =>
        have ihp := ih (masF axe) (by rw [masF_eq_mas]; exact hm) hm1 p
        have ihq := ih (masF axe) (by rw [masF_eq_mas]; exact hm) hm1 q
        obtain ⟨u, v, hp⟩ := cd_need_cell p
        rcases capF_cases axe h2 with hc2 | hc3
        · rw [hp] at ihp
          simp [nock_exec, Need.toNoun, hp, eqCode, hne, hna, hK, cap_arm, cap.arm_at, hcap, hc2, mas_arm,
            mas.arm_at, hmas, ← capF_eq_cap, ← masF_eq_mas, ihp]
        · simp [nock_exec, Need.toNoun, hp, eqCode, hne, hna, hK, cap_arm, cap.arm_at, hcap, hc3, mas_arm,
            mas.arm_at, hmas, ← capF_eq_cap, ← masF_eq_mas, ihq]
      | both r h t =>
        have ihh := ih (masF axe) (by rw [masF_eq_mas]; exact hm) hm1 h
        have iht := ih (masF axe) (by rw [masF_eq_mas]; exact hm) hm1 t
        rcases capF_cases axe h2 with hc2 | hc3
        · simp [nock_exec, Need.toNoun, Tag.none, Tag.this, Tag.both, hne, hna, hK, cap_arm, cap.arm_at, hcap,
            hc2, mas_arm, mas.arm_at, hmas, ← capF_eq_cap, ← masF_eq_mas, ihh]
        · simp [nock_exec, Need.toNoun, Tag.none, Tag.this, Tag.both, hne, hna, hK, cap_arm, cap.arm_at, hcap,
            hc3, mas_arm, mas.arm_at, hmas, ← capF_eq_cap, ← masF_eq_mas, iht]

/-- **The gate of `+axe-in-need`**: `axeInNeedL`, a crash at `0`. -/
theorem ain_gate (KC : Noun) (hK : slot? 0x1ffff KC = some layer1) (axe : Nat) (ned : Need) :
    nock (C ainBody (C (C (A axe) ned.toNoun) KC)) ainBody
      = if axe = 0 then Option.none else some (loob (axeInNeedL axe ned)) := by
  by_cases a0 : axe = 0
  · subst a0
    conv => { lhs; arg 2; unfold ainBody }
    simp [nock_exec]
  · have hl := ain_loop ainBody KC hK axe (by omega) ned
    have a0' : ¬ (0 = axe) := fun h => a0 h.symm
    conv => { lhs; arg 2; unfold ainBody }
    generalize ainTrap = T at hl
    simp [nock_exec, a0, a0', hl]

/-! ## The nouns of `+coerce-lazy` -/

/-- The gate of the `+rep:in` over `lok`. -/
def czGate : Noun :=
  (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 95) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 0) (A 503)))) (C (A 0) (A 2)))))))) (C (C (A 0) (A 13)) (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 0x5dd4) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 0) (A 124)))) (C (A 0) (A 2)))))))) (C (C (A 0) (A 13)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 84) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2))))))))))))))

/-- The trap `sure-loop`. -/
def czLoop : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 120)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 12)))) (C (C (A 0) (A 126)) (C (A 0) (A 0))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 120)))) (C (C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 3061) (C (A 10) (C (C (A 6) (C (A 0) (A 0x1fdfe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 250))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 9) (C (A 0x2aabe) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 250)) (C (C (A 0) (A 249)) (C (A 0) (A 14))))) (C (A 0) (A 2)))))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x555df6) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 249)) (C (A 0) (A 14)))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 9) (C (A 0x2aee) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 506)) (C (A 0) (A 6)))) (C (A 0) (A 2))))))))))))))))))) (C (A 6) (C (C (A 3) (C (A 0) (A 120))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 12)))) (C (C (A 0) (A 126)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 0) (A 0)) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 9) (C (A 2) (C (A 10) (C (C (A 60) (C (A 0) (A 120))) (C (A 10) (C (C (A 6) (C (A 0) (A 12))) (C (A 0) (A 1))))))))) (C (A 0) (A 1)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 60) (C (A 0) (A 121))) (C (A 10) (C (C (A 6) (C (A 0) (A 13))) (C (A 0) (A 1)))))))))))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 120))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 12)))) (C (C (A 0) (A 126)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 12)))) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 242)) (C (A 0) (A 13)))) (C (C (A 0) (A 0)) (C (A 8) (C (C (A 9) (C (A 0x2aee) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 250)) (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0x766f6d)) (C (C (A 0) (A 242)) (C (A 0) (A 13)))) (C (A 1) (A 0))))))) (C (A 0) (A 2))))))))))) (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 9) (C (A 2) (C (A 10) (C (C (A 60) (C (A 0) (A 486))) (C (A 10) (C (C (A 6) (C (A 0) (A 12))) (C (A 0) (A 1))))))))) (C (A 0) (A 1)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 60) (C (A 0) (A 487))) (C (A 10) (C (C (A 6) (C (A 0) (A 13))) (C (A 0) (A 1)))))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 12))))) (C (A 6) (C (C (A 5) (C (C (A 0) (A 242)) (C (A 0) (A 26)))) (C (C (A 0) (A 0)) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 8) (C (C (A 9) (C (A 0x2aee) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 250)) (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0x766f6d)) (C (C (A 0) (A 242)) (C (A 0) (A 26)))) (C (A 1) (A 0))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 9) (C (A 2) (C (A 10) (C (C (A 60) (C (A 0) (A 486))) (C (A 10) (C (C (A 6) (C (A 0) (A 54))) (C (A 0) (A 1))))))))) (C (A 0) (A 1)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 60) (C (A 0) (A 487))) (C (A 10) (C (C (A 6) (C (A 0) (A 55))) (C (A 0) (A 1)))))))))))))))))))))))))))))))))))))))

/-- The `+rep:in` over `lok.sure.laz`. -/
def czLok : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 383) (C (A 10) (C (C (A 6) (C (A 0) (A 473))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (C (A 1) czGate) (C (A 0) (A 1)))))))) (C (A 0) (A 2))))))))

/-- `+sure-require-look` of `sure.laz` with the new `lok`. -/
def czSrl : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 1399) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 10) (C (C (A 3) czLok) (C (A 0) (A 108))))))) (C (A 0) (A 2))))))))))

/-- The new `gen`: `czSrl`, then the trap `sure-loop`. -/
def czX : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C czSrl (C (A 7) (C (C (A 10) (C (C (A 62) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 1) czLoop) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))))))))

/-- The test `&(?=(~ fork.laz) ?=(~ bond.laz))` and the rolls. -/
def czTail : Noun :=
  (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 218)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 219)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 0) (A 30)) (C (A 7) (C (C (A 10) (C (C (A 30) (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 475)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (C (A 1) (A 0)) (C (A 7) (C (C (A 9) (C (A 191) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))) (C (A 0) (A 30))) (C (C (A 1) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 13))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 0) (A 7)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 124)) (C (C (A 0) (A 56)) (C (C (A 0) (A 57)) (C (A 0) (A 503)))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 474)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (C (C (A 1) (A 0)) (C (A 7) (C (C (A 9) (C (A 191) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))) (C (C (A 1) (A 0)) (C (A 7) (C (C (A 9) (C (A 191) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))) (C (A 0) (A 30))) (C (C (A 1) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 13))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 8) (C (C (A 0) (A 7)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 124)) (C (C (A 0) (A 112)) (C (C (A 0) (A 113)) (C (A 0) (A 503)))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 0) (A 7)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 124)) (C (C (A 0) (A 114)) (C (C (A 0) (A 115)) (C (A 0) (A 503)))))) (C (A 0) (A 2))))))))))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))))))))

def czBody : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 7) (C (C (A 10) (C (C (A 30) czX) (C (A 0) (A 1)))) czTail))))

/-- The bunt of the sample `[ned o laz less]`. -/
def czBunt : Noun := C (C (A 0x656e6f6e) (A 0)) (C (A 0) (C (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))) (A 1)))

def czHint : Noun :=
  (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x797a616c2d656372656f632d706d6f63) (C (C (A 0) (A 0x7ffff)) (A 0))))) (C (A 0) (A 1))))

/-- The arm `+coerce-lazy`. -/
def czArm : Noun := C (A 7) (C (C (A 8) (C (C (A 1) czBunt) (C (C (A 1) czBody) (C (A 0) (A 1))))) czHint)

/-- `+coerce-lazy` is at door axis `3580` (core axis `5628`). -/
theorem comp_cz_at : slot? 3580 comp.door = some czArm := by kernel_rfl

/-- The arm builds its gate. -/
theorem comp_cz_arm (d : Noun) : nock d czArm = some (C czBody (C czBunt d)) := by
  unfold czArm czHint; generalize czBody = B; generalize czBunt = U; simp [nock_exec]

/-- The subject of the gate: `[czBody [[ned o laz less] [door gen ctx]]]`. -/
def czOrig (NED : Noun) (o : Nat) (LAZ LESS D G ctx : Noun) : Noun :=
  C czBody (C (C NED (C (A o) (C LAZ LESS))) (C D (C G ctx)))

/-! ## The gate of the `+rep:in` over `lok` -/

/-- One step of the fold of `coerceLok`. -/
noncomputable def czStep (less : Cape) (ned : Need) (s : CSet) (axe : Nat) : Option CSet :=
  (axeInLessCape axe less).bind fun inLess => if inLess then some s else
    if axe = 0 then Option.none else if axeInNeedL axe ned then some s else some (HoonSet.put s axe)

/-- **The gate of the `+rep:in`** on an axis and an accumulator: `czStep`. -/
theorem cz_gate_step {ctx : Noun} (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) (D G LAZ : Noun) (o : Nat)
    (ned : Need) (less : Cape) (axe : Nat) (s : CSet) :
    nock (C czGate (C (C (A axe) (HoonSet.toNoun s)) (czOrig ned.toNoun o LAZ less.toNoun D G ctx))) czGate
      = (czStep less ned s axe).map HoonSet.toNoun := by
  have ha := aic_gate compK compK_layer1 axe less
  have hn := ain_gate compK compK_layer1 axe ned
  have hp := cs_put_in s axe
  have haa := aic_at
  have hna := ain_at
  unfold czStep
  unfold czOrig
  generalize czBody = BD
  generalize compK = KC at ha hn haa hna h7
  generalize aicBody = AB at ha haa
  generalize ainBody = NB at hn hna
  by_cases a0 : axe = 0
  · subst a0
    simp [axeInLessCape] at ha
    conv => { lhs; arg 2; unfold czGate }
    simp [nock_exec, h7, haa, ha, axeInLessCape]
  · simp only [axeInLessCape, a0, if_false, Option.map_some] at ha
    simp only [a0, if_false] at hn
    simp only [axeInLessCape, a0, if_false, Option.bind_some]
    conv => { lhs; arg 2; unfold czGate }
    cases e1 : axeInCape axe less
    · cases e2 : axeInNeedL axe ned
      · simp [nock_exec, h7, haa, ha, hna, hn, e1, e2, loob, hc, in_arm, in.arm_at, in.put.arm_at, put_in_arm, hp]
      · simp [nock_exec, h7, haa, ha, hna, hn, e1, e2, loob]
    · simp [nock_exec, h7, haa, ha, e1, loob]

/-! ## The fold over `lok` -/

theorem cz_foldl (less : Cape) (ned : Need) : ∀ (l : List Nat) (acc : Option CSet),
    l.foldl (fun acc axe => acc.bind fun s => (axeInLessCape axe less).bind fun inLess =>
      if inLess then some s else if axe = 0 then Option.none else
      if axeInNeedL axe ned then some s else some (HoonSet.put s axe)) acc
    = acc.bind fun s => l.foldlM (fun s axe => czStep less ned s axe) s
  | [], acc => by cases acc <;> rfl
  | a :: l, acc => by
    simp only [List.foldl_cons]
    rw [cz_foldl less ned l]
    cases acc with
    | none => rfl
    | some s =>
      simp only [Option.bind_some, List.foldlM_cons]
      rfl

/-- `coerceLok` is the fold of `czStep` in the order of `+rep:in`. -/
theorem coerceLok_eq (lok : CSet) (less : Cape) (ned : Need) :
    coerceLok lok less ned = (HoonSet.toList lok).foldlM (fun s axe => czStep less ned s axe) HoonSet.empty := by
  unfold coerceLok; rw [cz_foldl]; rfl

theorem czStep_ne0 (less : Cape) (ned : Need) (s s' : CSet) (axe : Nat) (h : czStep less ned s axe = some s')
    (hs : ∀ y ∈ HoonSet.toList s, y ≠ 0) : ∀ y ∈ HoonSet.toList s', y ≠ 0 := by
  unfold czStep axeInLessCape at h
  by_cases a0 : axe = 0
  · simp [a0] at h
  · simp only [a0, if_false, Option.bind_some] at h
    split at h
    · cases h; exact hs
    · split at h
      · cases h; exact hs
      · cases h
        intro y hy
        rcases (HoonSet.mem_put s axe y).1 hy with e | e
        · rw [e]; exact a0
        · exact hs y e

theorem cz_fold_ne0 (less : Cape) (ned : Need) : ∀ (l : List Nat) (s s' : CSet),
    l.foldlM (fun s axe => czStep less ned s axe) s = some s' →
    (∀ y ∈ HoonSet.toList s, y ≠ 0) → ∀ y ∈ HoonSet.toList s', y ≠ 0
  | [], s, s', h, hs => by cases h; exact hs
  | a :: l, s, s', h, hs => by
    simp only [List.foldlM_cons] at h
    cases e : czStep less ned s a with
    | none => rw [e] at h; cases h
    | some s1 =>
      rw [e] at h
      exact cz_fold_ne0 less ned l s1 s' h (czStep_ne0 less ned s s1 a e hs)

/-- The set that `coerceLok` returns has no `0`. -/
theorem coerceLok_ne0 {lok : CSet} {less : Cape} {ned : Need} {s : CSet} (h : coerceLok lok less ned = some s) :
    ∀ y ∈ HoonSet.toList s, y ≠ 0 := by
  rw [coerceLok_eq] at h
  exact cz_fold_ne0 less ned _ _ _ h (fun y hy => absurd hy (HoonSet.mem_empty y))

/-- **The `+rep:in` over `lok`** is `coerceLok`. -/
theorem cz_lok {ctx : Noun} (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) (D G : Noun) (o : Nat)
    (ned : Need) (s : Sure CSet) (less : Cape) :
    nock (czOrig ned.toNoun o (lazyNoun s) less.toNoun D G ctx) czLok
      = (coerceLok s.lok less ned).map HoonSet.toNoun := by
  rw [coerceLok_eq]
  have hrep := rep_gate_list A HoonSet.toNoun (fun axe acc => czStep less ned acc axe) in.battery layer2 czGate
    (A 0) (czOrig ned.toNoun o (lazyNoun s) less.toNoun D G ctx) (HoonSet.toNoun s.lok) (cs_tree _)
    (HoonSet.toList s.lok) (cs_preorder _) HoonSet.empty
    (fun p _ acc => cz_gate_step hc h7 D G (lazyNoun s) o ned less p acc)
  rw [HoonSet.toNoun_empty] at hrep
  unfold czLok
  simp only [czOrig, lazyNoun, Sure.toNoun] at hrep ⊢
  generalize czBody = BD at hrep ⊢
  generalize czGate = GT at hrep ⊢
  simp [nock_exec, hc, in_arm, in.arm_at, in.rep.arm_at, rep_arm, hrep]

/-- **`+sure-require-look` of `sure.laz` with the new `lok`.** -/
theorem cz_srl {ctx : Noun} (hc : CompIn ctx) (h7 : slot? 7 ctx = some compK) (x : GenRest)
    (g : Gen (TreapMap mugF)) (o : Nat) (ned : Need) (s : Sure CSet) (less : Cape) :
    nock (czOrig ned.toNoun o (lazyNoun s) less.toNoun comp.door (genNoun g x) ctx) czSrl
      = (coerceLok s.lok less ned).bind fun lok =>
          (sureRequireLook ⟨s.ned, lok⟩ g).map fun p => C p.1.toNoun (genNoun p.2 x) := by
  have hl := cz_lok hc h7 comp.door (genNoun g x) o ned s less
  have hD := comp_srl_at
  cases e : coerceLok s.lok less ned with
  | none =>
    rw [e] at hl
    unfold czSrl
    simp only [czOrig] at hl ⊢
    generalize czLok = LK at hl ⊢
    generalize comp.door = Dr at hD hl ⊢
    simp [nock_exec, hD, comp_srl_arm, hl]
  | some lok =>
    rw [e] at hl
    have hsrl := comp_sure_require_look (x := x) hc (comp_ctx_pill ctx h7).2.1 g ⟨s.ned, lok⟩ (coerceLok_ne0 e)
    unfold czSrl
    simp only [czOrig, compCore, Sure.toNoun, lazyNoun, Option.map_some] at hl hsrl ⊢
    generalize czLok = LK at hl ⊢
    generalize comp.door = Dr at hD hl hsrl ⊢
    simp [nock_exec, hD, comp_srl_arm, hl, lazyNoun, Sure.toNoun, hsrl]

/-! ## The trap `sure-loop` -/

/-- The subject of the trap: `[czLoop [tgt [czBody [[ned o REST] core]]]]`. -/
def czLS (TGT NED : Noun) (o : Nat) (REST CORE : Noun) : Noun :=
  C czLoop (C TGT (C czBody (C (C NED (C (A o) REST)) CORE)))

/-- `sure-loop` on `%none`: `gen` when the target is `%none`, else a crash. -/
theorem cz_loop_none {ctx : Noun} (x : GenRest) (o : Nat) (REST : Noun) (tgt : Need) (g : Gen (TreapMap mugF)) :
    nock (czLS tgt.toNoun Need.none.toNoun o REST (compCore g x ctx)) czLoop
      = (sureLoop o Need.none tgt g).map fun p => genNoun p.2 x := by
  conv => { lhs; arg 2; unfold czLoop }
  simp only [czLS, compCore]
  generalize czBody = BD
  generalize comp.door = Dr
  cases tgt with
  | none => simp [nock_exec, Need.toNoun, Tag.none, sureLoop, pure, StateT.pure]
  | this r => simp [nock_exec, Need.toNoun, Tag.none, Tag.this, sureLoop, crashM]
  | both r h t => simp [nock_exec, Need.toNoun, Tag.none, Tag.both, sureLoop, crashM]
  | pair p q =>
    obtain ⟨u, v, hp⟩ := cd_need_cell p
    simp [nock_exec, Need.toNoun, Tag.none, hp, sureLoop, crashM]

/-- `sure-loop` on `%this`, with `o` not in `soft`: `+kern-need`, then
`+add-ops`. -/
theorem cz_loop_this {ctx : Noun} (hc : CompIn ctx) (x : GenRest) (o : Nat) (hs : x.SoftOut o) (REST : Noun)
    (r : Nat) (tgt : Need) (g : Gen (TreapMap mugF)) :
    nock (czLS tgt.toNoun (Need.this r).toNoun o REST (compCore g x ctx)) czLoop
      = (sureLoop o (Need.this r) tgt g).map fun p => genNoun p.2 x := by
  have hhas := crn_has x o hs
  have hkn := comp_kern_need x ctx r tgt g
  have hD1 := comp_kn_at
  have hD2 := comp_add_ops_at
  conv => { lhs; arg 2; unfold czLoop }
  simp only [czLS, sureLoop, bind, StateT.bind]
  cases e : kernNeed r tgt g with
  | none =>
    rw [e] at hkn
    simp only [compCore] at hkn ⊢
    generalize czBody = BD
    generalize comp.door = Dr at hD1 hD2 hkn ⊢
    simp [nock_exec, Need.toNoun, Tag.none, Tag.this, hc, by_arm, by.arm_at, by.has.arm_at, has_arm, hhas,
      genNoun_soft, hD1, comp_kn_arm, hkn]
  | some p =>
    obtain ⟨ops, g1⟩ := p
    rw [e] at hkn
    have hao := comp_add_ops x hc g1 o ops
    simp only [compCore, Option.map_some] at hkn hao ⊢
    generalize czBody = BD
    generalize comp.door = Dr at hD1 hD2 hkn hao ⊢
    simp [nock_exec, Need.toNoun, Tag.none, Tag.this, hc, by_arm, by.arm_at, by.has.arm_at, has_arm, hhas,
      genNoun_soft, hD1, comp_kn_arm, hkn, hD2, comp_add_ops_arm, hao]

/-- The hypothesis of the recursion of `sure-loop` on a need. -/
def CzLoopAt (ctx : Noun) (x : GenRest) (o : Nat) (REST : Noun) (n : Need) : Prop :=
  ∀ (tgt : Need) (g : Gen (TreapMap mugF)),
    nock (czLS tgt.toNoun n.toNoun o REST (compCore g x ctx)) czLoop = (sureLoop o n tgt g).map fun r => genNoun r.2 x

/-- `sure-loop` on a cell: `gen` on a `%none` target, the halves against the
halves of a cell target, a crash otherwise. -/
theorem cz_loop_pair {ctx : Noun} (x : GenRest) (o : Nat) (REST : Noun) (p q : Need)
    (ihp : CzLoopAt ctx x o REST p) (ihq : CzLoopAt ctx x o REST q) (tgt : Need) (g : Gen (TreapMap mugF)) :
    nock (czLS tgt.toNoun (Need.pair p q).toNoun o REST (compCore g x ctx)) czLoop
      = (sureLoop o (Need.pair p q) tgt g).map fun r => genNoun r.2 x := by
  obtain ⟨a, b, hp⟩ := cd_need_cell p
  cases tgt with
  | none =>
    conv => { lhs; arg 2; unfold czLoop }
    simp only [czLS, compCore]
    generalize czBody = BD
    generalize comp.door = Dr
    simp [nock_exec, Need.toNoun, Tag.none, hp, sureLoop, pure, StateT.pure]
  | this r =>
    conv => { lhs; arg 2; unfold czLoop }
    simp only [czLS, compCore]
    generalize czBody = BD
    generalize comp.door = Dr
    simp [nock_exec, Need.toNoun, Tag.none, Tag.this, hp, sureLoop, crashM]
  | both r h t =>
    conv => { lhs; arg 2; unfold czLoop }
    simp only [czLS, compCore]
    generalize czBody = BD
    generalize comp.door = Dr
    simp [nock_exec, Need.toNoun, Tag.none, Tag.both, hp, sureLoop, crashM]
  | pair tp tq =>
    obtain ⟨a', b', htp⟩ := cd_need_cell tp
    have h1 := ihp tp g
    simp only [czLS, compCore] at h1
    rw [hp, htp] at h1
    conv => { lhs; arg 2; unfold czLoop }
    simp only [sureLoop, bind, StateT.bind]
    cases e1 : sureLoop o p tp g with
    | none =>
      rw [e1] at h1
      simp only [czLS, compCore]
      generalize czBody = BD at h1 ⊢
      generalize comp.door = Dr at h1 ⊢
      simp [nock_exec, Need.toNoun, Tag.none, hp, htp, h1]
    | some r1 =>
      obtain ⟨u, g1⟩ := r1
      rw [e1] at h1
      have h2 := ihq tq g1
      simp only [czLS, compCore] at h2
      simp only [czLS, compCore, Option.map_some] at h1 ⊢
      generalize czBody = BD at h1 h2 ⊢
      generalize comp.door = Dr at h1 h2 ⊢
      simp [nock_exec, Need.toNoun, Tag.none, hp, htp, h1, h2]

/-- `sure-loop` on `%both` against `%this`: the `%mov`. -/
theorem cz_loop_both_this {ctx : Noun} (hc : CompIn ctx) (x : GenRest) (o : Nat) (REST : Noun) (r : Nat)
    (h t : Need) (d : Nat) (g : Gen (TreapMap mugF)) :
    nock (czLS (Need.this d).toNoun (Need.both r h t).toNoun o REST (compCore g x ctx)) czLoop
      = (sureLoop o (Need.both r h t) (Need.this d) g).map fun p => genNoun p.2 x := by
  have hD2 := comp_add_ops_at
  have hao := comp_add_ops x hc g o [Pole.mov r d]
  simp only [listNoun, Pole.toNoun, Tag.mov] at hao
  conv => { lhs; arg 2; unfold czLoop }
  simp only [czLS, compCore, sureLoop] at hao ⊢
  generalize czBody = BD
  generalize comp.door = Dr at hD2 hao ⊢
  by_cases e : r = d
  · subst e
    simp [nock_exec, Need.toNoun, Tag.none, Tag.this, Tag.both, crashM]
  · have e' : ¬ (d = r) := fun h => e h.symm
    simp [nock_exec, Need.toNoun, Tag.none, Tag.this, Tag.both, e, e', hD2, comp_add_ops_arm, hao]

/-- `sure-loop` on `%both` against a cell: the halves. -/
theorem cz_loop_both_pair {ctx : Noun} (x : GenRest) (o : Nat) (REST : Noun) (r : Nat) (h t : Need)
    (ihh : CzLoopAt ctx x o REST h) (iht : CzLoopAt ctx x o REST t) (tp tq : Need) (g : Gen (TreapMap mugF)) :
    nock (czLS (Need.pair tp tq).toNoun (Need.both r h t).toNoun o REST (compCore g x ctx)) czLoop
      = (sureLoop o (Need.both r h t) (Need.pair tp tq) g).map fun p => genNoun p.2 x := by
  obtain ⟨a', b', htp⟩ := cd_need_cell tp
  have h1 := ihh tp g
  simp only [czLS, compCore] at h1
  rw [htp] at h1
  conv => { lhs; arg 2; unfold czLoop }
  simp only [sureLoop, bind, StateT.bind]
  cases e1 : sureLoop o h tp g with
  | none =>
    rw [e1] at h1
    simp only [czLS, compCore]
    generalize czBody = BD at h1 ⊢
    generalize comp.door = Dr at h1 ⊢
    simp [nock_exec, Need.toNoun, Tag.none, Tag.this, Tag.both, htp, h1]
  | some r1 =>
    obtain ⟨u, g1⟩ := r1
    rw [e1] at h1
    have h2 := iht tq g1
    simp only [czLS, compCore] at h2
    simp only [czLS, compCore, Option.map_some] at h1 ⊢
    generalize czBody = BD at h1 h2 ⊢
    generalize comp.door = Dr at h1 h2 ⊢
    simp [nock_exec, Need.toNoun, Tag.none, Tag.this, Tag.both, htp, h1, h2]

/-- `sure-loop` on `%both` against `%both`: the `%mov`, then the halves. -/
theorem cz_loop_both_both {ctx : Noun} (hc : CompIn ctx) (x : GenRest) (o : Nat) (REST : Noun) (r : Nat)
    (h t : Need) (ihh : CzLoopAt ctx x o REST h) (iht : CzLoopAt ctx x o REST t) (d : Nat) (th tt : Need)
    (g : Gen (TreapMap mugF)) :
    nock (czLS (Need.both d th tt).toNoun (Need.both r h t).toNoun o REST (compCore g x ctx)) czLoop
      = (sureLoop o (Need.both r h t) (Need.both d th tt) g).map fun p => genNoun p.2 x := by
  have hD2 := comp_add_ops_at
  have hao := comp_add_ops x hc g o [Pole.mov r d]
  simp only [listNoun, Pole.toNoun, Tag.mov] at hao
  by_cases e : r = d
  · subst e
    conv => { lhs; arg 2; unfold czLoop }
    simp only [czLS, compCore, sureLoop]
    generalize czBody = BD
    generalize comp.door = Dr
    simp [nock_exec, Need.toNoun, Tag.none, Tag.this, Tag.both, crashM]
  · have e' : ¬ (d = r) := fun h => e h.symm
    conv => { lhs; arg 2; unfold czLoop }
    simp only [sureLoop, e, if_false, bind, StateT.bind]
    cases e0 : addOps o [Pole.mov r d] g with
    | none =>
      rw [e0] at hao
      simp only [czLS, compCore] at hao ⊢
      generalize czBody = BD
      generalize comp.door = Dr at hD2 hao ⊢
      simp [nock_exec, Need.toNoun, Tag.none, Tag.this, Tag.both, e, e', hD2, comp_add_ops_arm, hao]
    | some r0 =>
      obtain ⟨u0, g0⟩ := r0
      rw [e0] at hao
      have h1 := ihh th g0
      simp only [czLS, compCore] at h1
      cases e1 : sureLoop o h th g0 with
      | none =>
        rw [e1] at h1
        simp only [czLS, compCore, Option.map_some] at hao ⊢
        generalize czBody = BD at h1 ⊢
        generalize comp.door = Dr at hD2 hao h1 ⊢
        simp [nock_exec, Need.toNoun, Tag.none, Tag.this, Tag.both, e, e', hD2, comp_add_ops_arm, hao, h1, e1]
      | some r1 =>
        obtain ⟨u1, g1⟩ := r1
        rw [e1] at h1
        have h2 := iht tt g1
        simp only [czLS, compCore] at h2
        simp only [czLS, compCore, Option.map_some] at hao h1 ⊢
        generalize czBody = BD at h1 h2 ⊢
        generalize comp.door = Dr at hD2 hao h1 h2 ⊢
        simp [nock_exec, Need.toNoun, Tag.none, Tag.this, Tag.both, e, e', hD2, comp_add_ops_arm, hao, h1, h2, e1]

/-- **The trap `sure-loop`** is `sureLoop`, with `o` not in `soft`. -/
theorem cz_loop {ctx : Noun} (hc : CompIn ctx) (x : GenRest) (o : Nat) (hs : x.SoftOut o) (REST : Noun) :
    ∀ ned : Need, CzLoopAt ctx x o REST ned
  | Need.none => fun tgt g => cz_loop_none x o REST tgt g
  | Need.this r => fun tgt g => cz_loop_this hc x o hs REST r tgt g
  | Need.pair p q => fun tgt g => cz_loop_pair x o REST p q (cz_loop hc x o hs REST p) (cz_loop hc x o hs REST q) tgt g
  | Need.both r h t => by
    have ihh := cz_loop hc x o hs REST h
    have iht := cz_loop hc x o hs REST t
    intro tgt g
    cases tgt with
    | none =>
      conv => { lhs; arg 2; unfold czLoop }
      simp only [czLS, compCore]
      generalize czBody = BD
      generalize comp.door = Dr
      simp [nock_exec, Need.toNoun, Tag.none, Tag.both, sureLoop, pure, StateT.pure]
    | this d => exact cz_loop_both_this hc x o REST r h t d g
    | pair tp tq => exact cz_loop_both_pair x o REST r h t ihh iht tp tq g
    | both d th tt => exact cz_loop_both_both hc x o REST r h t ihh iht d th tt g

/-! ## The gate -/

/-- **The gate of `+coerce-lazy`** on `[ned o [sure ~ ~] less]`, with `o`
not in `soft`: `coerceLazy`. -/
theorem cz_gate {ctx : Noun} (h7 : slot? 7 ctx = some compK) (x : GenRest) (o : Nat) (hs : x.SoftOut o)
    (ned : Need) (s : Sure CSet) (less : Cape) (g : Gen (TreapMap mugF)) :
    nock (C czBody (C (C ned.toNoun (C (A o) (C (lazyNoun s) less.toNoun))) (compCore g x ctx))) czBody
      = (coerceLazy ned o s less g).map fun p => genNoun p.2 x := by
  have hc := (comp_ctx_pill ctx h7).1
  have hsrl := cz_srl hc h7 x g o ned s less
  unfold coerceLazy
  simp only [bind, StateT.bind]
  cases e : coerceLok s.lok less ned with
  | none =>
    rw [e] at hsrl
    conv => { lhs; arg 2; unfold czBody czX }
    simp only [czOrig, compCore] at hsrl ⊢
    generalize czSrl = SR at hsrl ⊢
    generalize czTail = TL
    generalize czLoop = LP
    simp [nock_exec, hsrl]
  | some lok =>
    rw [e] at hsrl
    simp only [Option.bind_some] at hsrl
    simp only [Option.map_some, Option.bind_some]
    cases e2 : sureRequireLook ⟨s.ned, lok⟩ g with
    | none =>
      rw [e2] at hsrl
      conv => { lhs; arg 2; unfold czBody czX }
      simp only [czOrig, compCore] at hsrl ⊢
      generalize czSrl = SR at hsrl ⊢
      generalize czTail = TL
      generalize czLoop = LP
      simp [nock_exec, hsrl]
    | some r =>
      obtain ⟨tgt, g1⟩ := r
      rw [e2] at hsrl
      have hl := cz_loop hc x o hs (C (lazyNoun s) less.toNoun) ned tgt g1
      simp only [czLS, compCore] at hl
      conv => { lhs; arg 2; unfold czBody czX }
      simp only [czOrig, compCore, Option.bind_some, Option.map_some] at hsrl ⊢
      generalize czSrl = SR at hsrl ⊢
      cases e3 : sureLoop o ned tgt g1 with
      | none =>
        rw [e3] at hl
        unfold czTail
        generalize czLoop = LP at hl ⊢
        simp [nock_exec, hsrl, hl]
      | some r3 =>
        obtain ⟨u3, g3⟩ := r3
        rw [e3] at hl
        simp only [lazyNoun, Option.map_some] at hsrl hl ⊢
        unfold czTail
        generalize czLoop = LP at hl ⊢
        simp [nock_exec, hsrl, hl]

/-- `+coerce-lazy` on a fork-free lazy need is `coerceLazyL` there. -/
theorem cz_gate_L {ctx : Noun} (h7 : slot? 7 ctx = some compK) (x : GenRest) (o : Nat) (hs : x.SoftOut o)
    (ned : Need) (s : Sure CSet) (less : Cape) (g : Gen (TreapMap mugF)) :
    nock (C czBody (C (C ned.toNoun (C (A o) (C (Lazy.ofSure s).toNoun less.toNoun))) (compCore g x ctx))) czBody
      = (coerceLazyL ned less o (Lazy.ofSure s) g).map fun p => genNoun p.2 x := by
  rw [Lazy.toNoun_ofSure, coerceLazyL_ofSure]
  exact cz_gate h7 x o hs ned s less g
