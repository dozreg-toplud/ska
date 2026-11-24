module

public import lemmas.Hoon.Lists
public import lemmas.Hoon.Maps
public import lemmas.Pill.Arm.Roll
public import lemmas.Pill.Arm.By
import all lemmas.Pill.Arm.Roll
import all lemmas.Pill.Arm.By
/-!
`+roll` with a gate that may crash, and the arm `+uni:by` building its gate.

`roll_gate_M` is `roll_gate` with the gate's products as an `Option`: the
fold stops at the first crash.  With `g` the gate itself it says nothing
about the gate, so it applies to any gate: on a list of one element the
roll is the gate on that element and the first accumulator
(`roll_gate_one`).  `uni_by_arm`: the arm `uni` of a door `+by` builds the
gate whose sample is the door's map.
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

/-- The loop of `+roll` with a gate that may crash. -/
theorem roll_loop_M (c bp e bc : Noun) (g : Noun → Noun → Option Noun) : ∀ (l : List Noun) (acc : Noun),
    (∀ x ∈ l, ∀ acc, nock (C bp (C (C x acc) bc)) bp = g x acc) →
    nock (C roll.loop (C roll.battery (C (C (listN l) (C bp (C (C e acc) bc))) c))) roll.loop
      = l.foldlM (fun acc x => g x acc) acc := by
  intro l
  induction l with
  | nil =>
    intro acc _
    nock_open roll.loop
    simp [nock_exec]
  | cons x xs ih =>
    intro acc hf
    have hx := hf x (by simp)
    nock_open roll.loop
    cases e1 : g x acc with
    | none => simp [nock_exec, hx, e1]
    | some acc' =>
      have hxs := ih acc' (fun y hy => hf y (by simp [hy]))
      simp [nock_exec, hx, e1, hxs]

/-- Slamming the `+roll` gate with a gate that may crash. -/
theorem roll_gate_M (c bp e acc bc : Noun) (g : Noun → Noun → Option Noun) (l : List Noun)
    (hf : ∀ x ∈ l, ∀ acc, nock (C bp (C (C x acc) bc)) bp = g x acc) :
    nock (C roll.battery (C (C (listN l) (C bp (C (C e acc) bc))) c)) roll.battery
      = l.foldlM (fun acc x => g x acc) acc := by
  nock_open roll.battery
  simp only [nock_exec, roll_loop_M c bp e bc g l acc hf]

/-- **`+roll` over a list of one element** is the gate on that element and
the first accumulator, whatever the gate. -/
theorem roll_gate_one (c bp e acc bc x : Noun) :
    nock (C roll.battery (C (C (listN [x]) (C bp (C (C e acc) bc))) c)) roll.battery
      = nock (C bp (C (C x acc) bc)) bp := by
  rw [roll_gate_M c bp e acc bc (fun x acc => nock (C bp (C (C x acc) bc)) bp) [x] (fun _ _ _ => rfl)]
  simp [List.foldlM]

/-- The arm `uni` of a door `+by` builds its gate, whose sample bunt is the
door's map. -/
theorem uni_by_arm (a ctx : Noun) :
    nock (C by.battery (C a ctx)) by.uni.arm = some (C by.uni.battery (C a (C by.battery (C a ctx)))) := by
  nock_open by.uni.arm
  simp [nock_exec]

end Hoon
end Formalization

end
