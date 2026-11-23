import lemmas.Compiler.Anno
import lemmas.Compiler.TreapMap
import lemmas.Hoon.Layer2
import lemmas.Hoon.DelBy
import lemmas.Pill.Arm.Read
import lemmas.Pill.Arm.Store
import lemmas.Pill.Arm.Move
import lemmas.Pill.Arm.Eval_pass

/-!
The register arms of the interpreter core `interp`: `+read`, `+store`,
`+move`, on map nouns, against `getF` and `putF` of `lemmas/Hoon/`.

```hoon
++  move
  |=  [s=@uvre d=@uvre regs=(map @uvre (unit *))]
  (~(put by regs) d (~(got by regs) s))
::
++  read
  |=  [r=@uvre regs=(map @uvre (unit *))]
  ^-  *
  =/  v=(unit *)  (~(got by regs) r)
  ?>  ?=(^ v)
  u.v
::
++  store
  |=  [r=@uvre v=* regs=(map @uvre (unit *))]
  (~(put by regs) r `v)
```

The arms reach the door `+by` in layer 2, at `read.layer2.axis` of their
context; `RegsIn mug c` says what they read there, for a `+mug` computed by
`mug`.  A register holds a unit: `+read` takes a value out of `[~ v]` and
crashes on `~` (poison), `+move` copies the unit.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon

/-- What `+read` and `+store` read from their context: layer 2 at
`read.layer2.axis`, with `+by` and what `got` and `put` of `+by` read. -/
abbrev RegsIn (mug : Noun → Nat) (c : Noun) : Prop :=
  ∃ l2, slot? read.layer2.axis c = some l2 ∧ slot? by.axis l2 = some by.arm ∧
    NeedIn l2 ∧ SomeIn l2 ∧ GorIn mug l2 ∧ MorIn mug l2

@[nock_exec] theorem read_arm (c : Noun) :
    nock c read.arm = some (C read.battery (C (C (A 0) (A 0)) c)) := by
  nock_open read.arm; simp only [nock_exec]

@[nock_exec] theorem store_arm (c : Noun) :
    nock c store.arm = some (C store.battery (C (C (A 0) (C (A 0) (A 0))) c)) := by
  nock_open store.arm; simp only [nock_exec]

@[nock_exec] theorem move_arm (c : Noun) :
    nock c move.arm = some (C move.battery (C (C (A 0) (C (A 0) (A 0))) c)) := by
  nock_open move.arm; simp only [nock_exec]

/-- `+read` of a register that holds a value. -/
theorem read_gate {mug : Noun → Nat} (c : Noun) (hc : RegsIn mug c) (r : Nat) (regs x v : Noun)
    (h : getF mug (A r) regs = some (C (A 0) (C x v))) :
    nock (C read.battery (C (C (A r) regs) c)) read.battery = some v := by
  obtain ⟨l2, hl2, hby, hneed, hsome, hgor, _⟩ := hc
  nock_open read.battery
  simp [nock_exec, hl2, hby, by_arm, by.got.arm_at, got_arm,
    got_gate l2 ⟨hneed, hsome, hgor⟩ (A r) regs _ h]

/-- `+read` of a poisoned register crashes. -/
theorem read_gate_poison {mug : Noun → Nat} (c : Noun) (hc : RegsIn mug c) (r : Nat) (regs : Noun)
    (n : Nat) (h : getF mug (A r) regs = some (C (A 0) (A n))) :
    nock (C read.battery (C (C (A r) regs) c)) read.battery = none := by
  obtain ⟨l2, hl2, hby, hneed, hsome, hgor, _⟩ := hc
  nock_open read.battery
  simp [nock_exec, hl2, hby, by_arm, by.got.arm_at, got_arm,
    got_gate l2 ⟨hneed, hsome, hgor⟩ (A r) regs _ h]

/-- `+read` of a register that the map does not hold crashes. -/
theorem read_gate_nil {mug : Noun → Nat} (c : Noun) (hc : RegsIn mug c) (r : Nat) (regs : Noun)
    (h : getF mug (A r) regs = some (A 0)) :
    nock (C read.battery (C (C (A r) regs) c)) read.battery = none := by
  obtain ⟨l2, hl2, hby, hneed, hsome, hgor, _⟩ := hc
  nock_open read.battery
  simp [nock_exec, hl2, hby, by_arm, by.got.arm_at, got_arm,
    got_gate_nil l2 ⟨hneed, hsome, hgor⟩ (A r) regs h]

/-- `+store` of a value in a register: it puts `[~ v]`. -/
theorem store_gate {mug : Noun → Nat} (c : Noun) (hc : RegsIn mug c) (r : Nat) (v regs out : Noun)
    (h : putF mug (A r) (C (A 0) v) regs = some out) :
    nock (C store.battery (C (C (A r) (C v regs)) c)) store.battery = some out := by
  obtain ⟨l2, hl2, hby, _, _, hgor, hmor⟩ := hc
  nock_open store.battery
  simp [nock_exec, hl2, hby, by_arm, by.put.arm_at, put_arm,
    put_gate l2 ⟨hgor, hmor⟩ (A r) _ regs out h]

/-- What `+move` reads from its context: `+by`, as `+read` and `+store`. -/
abbrev MoveIn (mug : Noun → Nat) (c : Noun) : Prop := RegsIn mug c

/-- `+move` from a register that the map holds, a value or poison. -/
theorem move_gate {mug : Noun → Nat} (c : Noun) (hc : MoveIn mug c) (s d : Nat) (regs u out : Noun)
    (h : getF mug (A s) regs = some (C (A 0) u)) (h' : putF mug (A d) u regs = some out) :
    nock (C move.battery (C (C (A s) (C (A d) regs)) c)) move.battery = some out := by
  obtain ⟨l2, hl2, hby, hneed, hsome, hgor, hmor⟩ := hc
  nock_open move.battery
  simp [nock_exec, hl2, hby, by_arm, by.got.arm_at, got_arm, by.put.arm_at, put_arm,
    got_gate l2 ⟨hneed, hsome, hgor⟩ (A s) regs u h, put_gate l2 ⟨hgor, hmor⟩ (A d) u regs out h']

/-- `+move` from a register that the map does not hold crashes. -/
theorem move_gate_nil {mug : Noun → Nat} (c : Noun) (hc : MoveIn mug c) (s d : Nat) (regs : Noun)
    (h : getF mug (A s) regs = some (A 0)) :
    nock (C move.battery (C (C (A s) (C (A d) regs)) c)) move.battery = none := by
  obtain ⟨l2, hl2, hby, hneed, hsome, hgor, _⟩ := hc
  nock_open move.battery
  simp [nock_exec, hl2, hby, by_arm, by.got.arm_at, got_arm, by.put.arm_at, put_arm,
    got_gate_nil l2 ⟨hneed, hsome, hgor⟩ (A s) regs h]

/-! ## On the pill's interpreter core, against the model

The register maps are the treaps of `TreapMap mugF` (`TreapMap.lean`) with
units as values, whose noun `HoonMap.toNoun (unitNoun id) regs` is the map
the Hoon holds. -/

theorem regsIn_interp : RegsIn mugF interp :=
  ⟨layer2, read.layer2.arm_at, by.arm_at, need.arm_at, someIn_layer2, gorIn_morIn_layer2.1,
    gorIn_morIn_layer2.2⟩

theorem moveIn_interp : MoveIn mugF interp := regsIn_interp

/-- `+read` computes `read` of `Interp.lean`, a crash when the register is
not there or is poisoned. -/
theorem read_pill (r : Nat) (regs : TreapMap mugF (Option Noun)) :
    nock (C read.battery (C (C (A r) (HoonMap.toNoun (unitNoun id) regs)) interp)) read.battery
      = SkaModel.read r regs := by
  have h := getF_hoonMap (unitNoun id) regs r
  unfold SkaModel.read
  cases e : HoonMap.get regs r with
  | none => rw [e] at h; exact read_gate_nil _ regsIn_interp r _ h
  | some u =>
    rw [e] at h
    cases u with
    | none => exact read_gate_poison _ regsIn_interp r _ 0 h
    | some v => exact read_gate _ regsIn_interp r _ (A 0) v h

/-- `+store` computes `store` of `Interp.lean`. -/
theorem store_pill (r : Nat) (v : Noun) (regs : TreapMap mugF (Option Noun)) :
    nock (C store.battery (C (C (A r) (C v (HoonMap.toNoun (unitNoun id) regs))) interp))
      store.battery = some (HoonMap.toNoun (unitNoun id) (SkaModel.store r v regs)) :=
  store_gate _ regsIn_interp r v _ _ (putF_hoonMap (unitNoun id) regs r (some v))

/-- `+move` computes `move` of `Interp.lean`. -/
theorem move_pill (s d : Nat) (regs : TreapMap mugF (Option Noun)) :
    nock (C move.battery (C (C (A s) (C (A d) (HoonMap.toNoun (unitNoun id) regs))) interp))
      move.battery = (SkaModel.move s d regs).map (HoonMap.toNoun (unitNoun id)) := by
  have h := getF_hoonMap (unitNoun id) regs s
  unfold SkaModel.move
  cases e : HoonMap.get regs s with
  | none => rw [e] at h; simpa using move_gate_nil _ moveIn_interp s d _ h
  | some u =>
    rw [e] at h
    simpa using move_gate _ moveIn_interp s d _ (unitNoun id u) _ h
      (putF_hoonMap (unitNoun id) regs d u)

end Compiler
end Formalization
