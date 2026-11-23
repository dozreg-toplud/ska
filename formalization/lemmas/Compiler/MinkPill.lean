import lemmas.Compiler.Monk
import lemmas.Hoon.Layer1

/-!
`+mink`, `+monk` and `+mack` in the pill's layer 4 of `hoon.hoon`, with no assumption on the
context: layer 4 holds layer 1 with `+cap` and `+mas`.  The theorems still
take the model's `Lib` and ask only that it slams the scry gate as Nock does.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon

theorem minkIn_layer4 : MinkIn layer4 := by
  obtain ⟨ha, _, hm, _, _, _, _, _, _, _, hdv, hmd⟩ := Hoon.arith_layer1
  exact ⟨layer1, mink.layer1.arm_at, ⟨cap.arm_at, hdv⟩, ⟨mas.arm_at, ha, hmd, hm, hdv⟩⟩

/-- The pill's `+mink`, the arm at `mink.axis` of layer 4, slammed on
`[[s f] gul]`, returns `x` exactly when the model returns a tone that `x`
encodes. -/
theorem mink_pill_iff (lib : Lib) (hslam : SlamIsNock lib) (s f gul x : Noun) :
    nock (C mink.battery (C (C (C s f) gul) layer4)) mink.battery = some x ↔
      ∃ r, x = r.toNoun ∧ Mink lib gul [] s f r :=
  mink_gate_iff lib layer4 minkIn_layer4 hslam s f gul x

/-- `(mink [s f] gul)` as a caller in layer 4 compiles it: pull the arm, put
the sample in, kick. -/
theorem mink_pill_call (lib : Lib) (hslam : SlamIsNock lib) (s f gul x : Noun) :
    nock (C (C (C s f) gul) layer4)
        (C (A 8) (C (C (A 9) (C (A mink.axis) (C (A 0) (A 3))))
          (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2))))))))
      = some x ↔ ∃ r, x = r.toNoun ∧ Mink lib gul [] s f r := by
  rw [← mink_pill_iff lib hslam s f gul x]
  simp only [nock_exec, mink.arm_at, mink_arm]

theorem monkIn_layer4 : MonkIn layer4 := ⟨mink.arm_at, minkIn_layer4⟩

theorem mackIn_layer4 : MackIn layer4 := ⟨monk.arm_at, monkIn_layer4⟩

/-- The pill's `+monk`: `+mink` with the trace dropped. -/
theorem monk_pill_iff (lib : Lib) (hslam : SlamIsNock lib) (s f gul x : Noun) :
    nock (C monk.battery (C (C (C s f) gul) layer4)) monk.battery = some x ↔
      ∃ r, Mink lib gul [] s f r ∧ x = (monkToon r).toNoun :=
  monk_gate_iff lib layer4 monkIn_layer4 hslam s f gul x

/-- The pill's `+mack`: the product of `+mink` with no scry gate. -/
theorem mack_pill_iff (lib : Lib) (hslam : SlamIsNock lib) (s f x : Noun) :
    nock (C mack.battery (C (C s f) layer4)) mack.battery = some x ↔
      ∃ r, Mink lib (A 0) [] s f r ∧ x = unitN (mackUnit r) :=
  mack_gate_iff lib layer4 mackIn_layer4 hslam s f x

end Compiler
end Formalization
