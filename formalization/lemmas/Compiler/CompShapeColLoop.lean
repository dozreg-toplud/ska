import lemmas.Compiler.CompShapeColOrig

/-!
# The fixed point loop of `+inter2-collapse`

`ic_loop`: when the model's loop `fixLoop` succeeds at some fuel, the trap
of `+inter2-collapse` (arm `1406` of `K`, `icTrap` of `CompShapeCol.lean`)
returns its product: each round is `+inter2-fix-round` (`fr_gate`), the
test `=(new fix)` is the test of `fixLoop` on nouns.  `ic_gate`: when
`inter2Collapse` succeeds at some fuel, the gate body of `+inter2-collapse`
returns its product (`+inter2-orig` by `oi_gate`; the `!@  collapse-check`
takes `res`).  `fixLoop_succ`: a loop that succeeds at some fuel gives the
same at every larger fuel, so the product does not depend on the fuel.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- More fuel gives the same product. -/
theorem fixLoop_succ (less : Cape) : ∀ (fuel : Nat) (fix r : I2),
    fixLoop less fuel fix = some r → fixLoop less (fuel + 1) fix = some r
  | 0, fix, r, h => by simp [fixLoop] at h
  | k + 1, fix, r, h => by
    rw [fixLoop] at h ⊢
    by_cases e : (fixRound less fix NeedOrd.none).toNoun = fix.toNoun
    · rw [if_pos e] at h ⊢; exact h
    · rw [if_neg e] at h ⊢; exact fixLoop_succ less k _ r h

theorem fixLoop_mono (less : Cape) (fuel fuel' : Nat) (hle : fuel ≤ fuel') (fix r : I2)
    (h : fixLoop less fuel fix = some r) : fixLoop less fuel' fix = some r := by
  induction hle with
  | refl => exact h
  | step _ ih => exact fixLoop_succ less _ fix r ih

/-- **The fixed point loop of `+inter2-collapse`**, when `fixLoop` succeeds. -/
theorem ic_loop (less : Cape) (CORE : Noun) : ∀ (fuel : Nat) (fix r : I2), fixLoop less fuel fix = some r →
    nock (C icTrap (C fix.toNoun (C icBody (C (C CORE less.toNoun) compK)))) icTrap = some r.toNoun
  | 0, fix, r, h => by simp [fixLoop] at h
  | k + 1, fix, r, h => by
    have hf := fr_gate less fix
    have hfa := fr_at
    rw [fixLoop] at h
    by_cases e : (fixRound less fix NeedOrd.none).toNoun = fix.toNoun
    · rw [if_pos e] at h
      cases h
      conv => { lhs; arg 2; unfold icTrap }
      generalize icTrap = IT
      generalize icBody = IB
      generalize compK = KC at hf hfa ⊢
      simp [nock_exec, hfa, fr_arm, hf, e, eqCode_self]
    · rw [if_neg e] at h
      have ih := ic_loop less CORE k _ r h
      conv => { lhs; arg 2; unfold icTrap }
      generalize icTrap = IT at ih ⊢
      generalize icBody = IB at ih ⊢
      generalize compK = KC at hf hfa ih ⊢
      simp [nock_exec, hfa, fr_arm, hf, eqCode, e, ih]

/-- **`+inter2-collapse`**, when `inter2Collapse` succeeds at some fuel. -/
theorem ic_gate (less : Cape) (intr : I2) (fuel : Nat) (r : NeedOrd) (h : inter2Collapse fuel intr less = some r) :
    nock (C icBody (C (C intr.toNoun less.toNoun) compK)) icBody = some r.toNoun := by
  unfold inter2Collapse at h
  cases e : fixLoop less fuel intr with
  | none => rw [e] at h; cases h
  | some fix =>
    rw [e, Option.bind_some] at h
    have hl := ic_loop less intr.toNoun fuel intr fix e
    have ho := oi_gate less intr fix
    have hoa := oi_at
    rw [h, Option.map_some] at ho
    conv => { lhs; arg 2; unfold icBody }
    generalize icTrap = IT at hl ⊢
    generalize icBody = IB at hl ⊢
    generalize compK = KC at hl ho hoa ⊢
    simp [nock_exec, hl, hoa, oi_arm, ho]

end Compiler
end Formalization
