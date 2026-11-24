import lemmas.Compiler.CompSet
import lemmas.Compiler.Axes
import lemmas.Hoon.Mink

/-!
# `+from-sure` and `+from` of the door of `+comp`

`+from-sure` reads of the door's context `ctx` the door `+in` of layer 2
(`+run:in`) and `+cap`, `+mas`, `+peg` of layer 1, behind layer 2 at axis
`524287` of `ctx` (`cf_layer1`).  It neither reads nor writes `gen`.

The sets are the canonical treaps of `CompSet.lean`.  The side condition: no
looked-at axis is `0`.  On a look `0` the gate `|=(x=@ (peg axe x))` of the
`+run:in` runs `(peg axe 0)`, whose last case recurs on `(div 0 2)` forever,
while the model's `setRun (pegF axe)` returns (`pegF axe 0 = 0`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.Ana

variable {ctx : Noun}

/-- Layer 1 of the library, behind layer 2, in the door's context. -/
theorem cf_layer1 (hc : CompIn ctx) : slot? 524287 ctx = some layer1 := by
  have h := slot_bit 262143 (by decide) 1 (by decide) ctx
  rw [hc] at h
  rw [show (524287 : Nat) = 2 * 262143 + 1 from rfl, h]
  exact (slot_three layer2).symm.trans layer2_layer1

theorem cf_arith : AddIn layer1 ∧ ModIn layer1 ∧ MulIn layer1 ∧ DivIn layer1 := by
  obtain ⟨ha, _, hm, _, _, _, _, _, _, _, hdv, hmd⟩ := Hoon.arith_layer1
  exact ⟨ha, hmd, hm, hdv⟩

/-- The loop of `+from-sure`, a trap on the core of the gate: the need of the
noun at `axe` as a need of the noun that holds it. -/
theorem cf_loop (hc : CompIn ctx) (B G L : Noun) (ned : Need) :
    ∀ axe, 1 ≤ axe →
    nock (C comp.from_sure.loop (C B (C (C (A axe) (C ned.toNoun L)) (C comp.door (C G ctx)))))
      comp.from_sure.loop = some (fromPath ned axe).toNoun := by
  have hl1 := cf_layer1 hc
  have har := cf_arith
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
    intro ha
    by_cases a1 : axe = 1
    · subst a1
      nock_open comp.from_sure.loop
      rw [fromPath.eq_def]
      simp [nock_exec]
    · have h2 : 2 ≤ axe := by omega
      have hcap := cap_gate layer1 har.2.2.2 axe h2
      have hmas := mas_gate layer1 har axe h2
      have hm1 : 1 ≤ masF axe := masF_pos axe h2
      have ihm := ih (masF axe) (by rw [masF_eq_mas]; exact mas_lt axe h2) hm1
      have hne : ¬ (1 = axe) := by omega
      nock_open comp.from_sure.loop
      rw [fromPath.eq_def]
      rcases capF_cases axe h2 with hc2 | hc3
      · simp [nock_exec, hl1, hne, cap_arm, cap.arm_at, hcap, hc2, mas_arm, mas.arm_at, hmas, ihm,
          show ¬ axe ≤ 1 by omega, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none]
      · simp [nock_exec, hl1, hne, cap_arm, cap.arm_at, hcap, hc3, mas_arm, mas.arm_at, hmas, ihm,
          show ¬ axe ≤ 1 by omega, ← capF_eq_cap, ← masF_eq_mas, Need.toNoun, Tag.none]

/-- The battery of the gate `|=(x=@ (peg axe x))` that `+from-sure` hands
`+run:in`. -/
def cfPegBat : Noun :=
  C (A 8) (C (C (A 9) (C (A 46) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 2) (C (A 10)
    (C (C (A 6) (C (C (A 0) (A 124)) (C (A 0) (A 14)))) (C (A 0) (A 2)))))))

theorem cf_peg_gate (hc : CompIn ctx) (B G L : Noun) (axe y : Nat) (ha : 1 ≤ axe) (hy : 1 ≤ y) :
    nock (C cfPegBat (C (A y) (C B (C (C (A axe) L) (C comp.door (C G ctx)))))) cfPegBat
      = some (A (pegF axe y)) := by
  have hl1 := cf_layer1 hc
  have hp := peg_gate layer1 cf_arith axe ha y hy
  unfold cfPegBat
  simp [nock_exec, hl1, peg_arm, peg.arm_at, hp]

/-- The noun of a singleton. -/
theorem cs_setOne (a : Nat) : HoonSet.toNoun (setOne a : CSet) = C (A a) (C (A 0) (A 0)) := by
  have h := cs_putInF (HoonSet.empty : CSet) a
  rw [HoonSet.toNoun_empty] at h
  simp only [putInF, Option.some.injEq] at h
  exact h.symm

/-- `+from-sure`, on every noun `G` of the state (it reads none of it), with
no look at axis `0`. -/
theorem comp_from_sure (hc : CompIn ctx) (G : Noun) (axe : Nat) (sur : Sure CSet)
    (h0 : ∀ y ∈ HoonSet.toList sur.lok, y ≠ 0) :
    nock (C comp.from_sure.battery (C (C (A axe) sur.toNoun) (C comp.door (C G ctx))))
      comp.from_sure.battery = (fromSure axe sur).map Sure.toNoun := by
  obtain ⟨ned, lok⟩ := sur
  simp only at h0
  have hrun : ∀ (B : Noun), 1 ≤ axe →
      nock (C in.run.battery (C (C cfPegBat (C (A 0) (C B (C (C (A axe) (C ned.toNoun
        (HoonSet.toNoun lok))) (C comp.door (C G ctx)))))) (C in.battery (C (HoonSet.toNoun lok)
        layer2)))) in.run.battery = some (HoonSet.toNoun (setRun (pegF axe) lok)) := by
    intro B ha
    refine cs_run_in_gate_on layer2 cs_inIn_layer2 _ _ _ (csLift (pegF axe)) _ (cs_tree lok)
      (fun n hn => ?_) _ (cs_runInF _ lok)
    rw [cs_preorder] at hn
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hn
    exact cf_peg_gate hc _ G _ axe y ha (Nat.pos_of_ne_zero (h0 y hy))
  have hl := cf_loop hc comp.from_sure.battery G (HoonSet.toNoun lok) ned
  simp only [Sure.toNoun]
  nock_open comp.from_sure.battery
  by_cases a0 : axe = 0
  · subst a0; simp [nock_exec, fromSure]
  have ha : 1 ≤ axe := Nat.pos_of_ne_zero a0
  have ha0 : ¬ (0 = axe) := fun h => a0 h.symm
  cases ned with
  | none =>
    by_cases a1 : axe = 1
    · subst a1; simp [nock_exec, fromSure, Need.toNoun, Tag.none]
    have ha1 : ¬ (1 = axe) := fun h => a1 h.symm
    by_cases he : HoonSet.toList lok = []
    · have hn := (cs_toNoun_nil lok).2 he
      have hi : HoonSet.isEmpty lok = true := (HoonSet.isEmpty_iff lok).2 he
      simp [nock_exec, fromSure, Need.toNoun, Tag.none, hn, ha0, ha1, a0, a1, hi, cs_setOne,
        Sure.toNoun]
    · have hn : ¬ (A 0 = HoonSet.toNoun lok) := fun h => he ((cs_toNoun_nil lok).1 h.symm)
      have hi : HoonSet.isEmpty lok = false := by
        cases e : HoonSet.isEmpty lok
        · rfl
        · exact absurd ((HoonSet.isEmpty_iff lok).1 e) he
      have hr := hrun comp.from_sure.battery ha
      simp only [Need.toNoun, Tag.none, cfPegBat] at hr
      simp [nock_exec, fromSure, Need.toNoun, Tag.none, hn, ha0, ha1, a0, a1, hi, hc, in_arm,
        in.arm_at, in.run.arm_at, cs_run_in_arm, hr, Sure.toNoun]
  | pair p q =>
    obtain ⟨a, b, hp⟩ := cd_need_cell p
    have hr := hrun comp.from_sure.battery ha
    have hl' := hl axe ha
    simp only [Need.toNoun, cfPegBat, hp] at hr hl'
    simp [nock_exec, fromSure, Need.toNoun, hp, ha0, a0, hc, in_arm, in.arm_at, in.run.arm_at,
      cs_run_in_arm, hr, hl', Sure.toNoun]
  | both r h t =>
    have hr := hrun comp.from_sure.battery ha
    have hl' := hl axe ha
    simp only [Need.toNoun, cfPegBat, Tag.both] at hr hl'
    simp [nock_exec, fromSure, Need.toNoun, Tag.both, Tag.none, ha0, a0, hc, in_arm, in.arm_at,
      in.run.arm_at, cs_run_in_arm, hr, hl', Sure.toNoun]
  | this r =>
    have hr := hrun comp.from_sure.battery ha
    have hl' := hl axe ha
    simp only [Need.toNoun, cfPegBat, Tag.this] at hr hl'
    simp [nock_exec, fromSure, Need.toNoun, Tag.this, Tag.none, ha0, a0, hc, in_arm, in.arm_at,
      in.run.arm_at, cs_run_in_arm, hr, hl', Sure.toNoun]

end Compiler
end Formalization
