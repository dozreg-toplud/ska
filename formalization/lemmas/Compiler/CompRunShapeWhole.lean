import lemmas.Compiler.CompRunSixNext
import lemmas.Compiler.CapeSize

/-!
# `+whole` from the door of `+run-shape` (track A, 2026-11-28)

The first test of the kerf of `%6` under `[%next laz]` (`rs6Kerf`) is `&((whole q.nomm)
(whole r.nomm))`, each call `[8 [9 1372 0 0x3fff] 9 2 10 [6 0 a] 0 2]`: arm `1372` of `ana`,
which sits at axis `15` of `K` (`compK = [bat [types [0 ana]]]`), so at axis `63` of the
door's context and `255` of the door's core.  `+whole` itself is already linked on every nomm
and every context of its gate (`wh_gate`, `CompRunSixNext.lean`, battery `whBat`, `wh_at`):
this file only adds the axis facts and the calls.  No new cut: the arm is `whArm`.

* `whl_ana`: `ana` at axis `63` of a context with `K` at `7`.
* **`whl_gate`**: from the door core `[comp.door [G ctx]]`, the arm `1372` at axis `255`
  slammed on a nomm is `whole`.
* `whl_call`: the call on any subject with `ana` at `0x3fff` and the nomm at the sample axis.
* **`whl_both`**: the test `&((whole q) (whole r))` of `rs6Kerf` (sample axes `4070`, `4071`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

variable {ctx : Noun}

/-- `ana` is at axis `63` of a context with `K` at axis `7`. -/
theorem whl_ana (h7 : slot? 7 ctx = some compK) : slot? 63 ctx = some ana := by
  have h : slot? 7 ctx = slot? 1 compK := by rw [h7]; rfl
  have := slot_spine (by omega) (by omega) h 3
  simp only [show 2 ^ 3 * (7 + 1) - 1 = 63 from rfl, show 2 ^ 3 * (1 + 1) - 1 = 15 from rfl] at this
  rw [this]
  rfl

/-- **The call of `+whole` on any subject** with `ana` at axis `0x3fff` and the nomm at the
axis `a` of the core `[gate subject]`. -/
theorem whl_call (S : Noun) (n : Nomm) (a : Nat) (hk : slot? 0x3fff S = some ana)
    (hn : slot? a (C (C whBat (C whBunt ana)) S) = some n.toNoun) :
    nock S (C (A 8) (C (C (A 9) (C (A 1372) (C (A 0) (A 0x3fff)))) (C (A 9) (C (A 2) (C (A 10)
      (C (C (A 6) (C (A 0) (A a))) (C (A 0) (A 2))))))))
      = some (loob (whole n)) := by
  have hw := wh_gate ana n
  simp [nock_exec, hk, wh_at, wh_arm, hn, hw]

/-- **`+whole` from the door of `+run-shape`**: the arm `1372` of `ana` (axis `255` of the door's
core) slammed on the nomm `n` is `whole n`. -/
theorem whl_gate (h7 : slot? 7 ctx = some compK) (G : Noun) (n : Nomm) :
    nock (C comp.door (C G ctx)) (C (A 8) (C (C (A 9) (C (A 1372) (C (A 0) (A 255)))) (C (A 9)
      (C (A 2) (C (A 10) (C (C (A 6) (C (A 1) n.toNoun)) (C (A 0) (A 2))))))))
      = some (loob (whole n)) := by
  have ha := whl_ana h7
  have hw := wh_gate ana n
  simp [nock_exec, ha, wh_at, wh_arm, hw]

/-- **The first test of the kerf in `rs6Kerf`**, `&((whole q) (whole r))`, on a subject with
`ana` at `0x3fff`, `q` and `r` at axes `2022` and `2023` (the sample axes `4070`, `4071` of
`[gate subject]`). -/
theorem whl_both (S : Noun) (q r : Nomm) (hk : slot? 0x3fff S = some ana)
    (hq : slot? 2022 S = some q.toNoun) (hr : slot? 2023 S = some r.toNoun) :
    nock S (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 1372) (C (A 0) (A 0x3fff)))) (C (A 9) (C (A 2)
      (C (A 10) (C (C (A 6) (C (A 0) (A 4070))) (C (A 0) (A 2)))))))) (C (C (A 6) (C (C (A 8)
      (C (C (A 9) (C (A 1372) (C (A 0) (A 0x3fff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6)
      (C (A 0) (A 4071))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1)))))
      = some (loob (whole q && whole r)) := by
  have hw1 := wh_gate ana q
  have hw2 := wh_gate ana r
  cases e1 : whole q <;> cases e2 : whole r <;>
    simp [nock_exec, hk, wh_at, wh_arm, hq, hr, hw1, hw2, e1, e2, loob]

end Compiler
end Formalization
