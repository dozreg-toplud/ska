import lemmas.Compiler.Mink
import lemmas.Pill.Arm.Monk
import lemmas.Pill.Arm.Mack

/-!
`+monk` and `+mack` of `hoon.hoon`, from `+mink`.

```hoon
++  monk
  ~/  %monk
  |=  [[sub=* fol=*] gul=$@(~ $-(^ (unit (unit))))]
  ^-  toon
  =/  ton=tone  (mink [sub fol] gul)
  ?.  ?=([%2 *] ton)  ton
  [%2 ~]
::
++  mack
  |=  [sub=* fol=*]
  ^-  (unit)
  =/  ton  (monk [sub fol] ~)
  ?.(?=(%0 -.ton) ~ `p.ton)
```
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon

/-- What `+monk` makes of a tone: a trace is dropped. -/
def monkToon : Tone → Toon
  | Tone.zero p => Toon.zero p
  | Tone.one p => Toon.one p
  | Tone.two _ => Toon.two []

/-- What `+mack` makes of a tone: the product of a `%0`. -/
def mackUnit : Tone → Option Noun
  | Tone.zero p => some p
  | _ => none

/-- The context of `+monk` holds `+mink` and what it reads. -/
abbrev MonkIn (c : Noun) : Prop := slot? mink.axis c = some mink.arm ∧ MinkIn c

/-- The context of `+mack` holds `+monk` and what it reads. -/
abbrev MackIn (c : Noun) : Prop := slot? monk.axis c = some monk.arm ∧ MonkIn c

@[nock_exec] theorem monk_arm (c : Noun) :
    nock c monk.arm = some (C monk.battery (C (C (C (A 0) (A 0)) (A 0)) c)) := by
  nock_open monk.arm; simp only [nock_exec]

@[nock_exec] theorem mack_arm (c : Noun) :
    nock c mack.arm = some (C mack.battery (C (C (A 0) (A 0)) c)) := by
  nock_open mack.arm; simp only [nock_exec]

/-- Slamming `+monk` on `[[s f] gul]`: `+mink` with the trace dropped. -/
theorem monk_gate_iff (lib : Lib) (ctx : Noun) (hc : MonkIn ctx) (hslam : SlamIsNock lib)
    (s f gul x : Noun) :
    nock (C monk.battery (C (C (C s f) gul) ctx)) monk.battery = some x ↔
      ∃ r, Mink lib gul [] s f r ∧ x = (monkToon r).toNoun := by
  obtain ⟨hma, hmi⟩ := hc
  cases hm : nock (C mink.battery (C (C (C s f) gul) ctx)) mink.battery with
  | none =>
    have h0 : nock (C monk.battery (C (C (C s f) gul) ctx)) monk.battery = none := by
      nock_open monk.battery; simp [nock_exec, hma, mink_arm, hm]
    rw [h0]
    simp only [reduceCtorEq, false_iff, not_exists, not_and]
    intro r hr _
    rw [mink_gate_of_model lib ctx hmi hslam s f gul r hr] at hm
    cases hm
  | some y =>
    obtain ⟨r, rfl, hr⟩ := mink_gate_to_model lib ctx hmi hslam s f gul y hm
    have h1 : nock (C monk.battery (C (C (C s f) gul) ctx)) monk.battery
        = some (monkToon r).toNoun := by
      nock_open monk.battery
      cases r <;> simp [nock_exec, hma, mink_arm, hm, Tone.toNoun, monkToon, Toon.toNoun, listNoun]
    rw [h1]
    constructor
    · intro h; exact ⟨r, hr, (Option.some.inj h).symm⟩
    · rintro ⟨r', hr', rfl⟩
      cases Mink.det hr hr'
      rfl

/-- Slamming `+mack` on `[s f]`: the product of `+mink` with no scry gate. -/
theorem mack_gate_iff (lib : Lib) (ctx : Noun) (hc : MackIn ctx) (hslam : SlamIsNock lib)
    (s f x : Noun) :
    nock (C mack.battery (C (C s f) ctx)) mack.battery = some x ↔
      ∃ r, Mink lib (A 0) [] s f r ∧ x = unitN (mackUnit r) := by
  obtain ⟨hma, hmo⟩ := hc
  cases hm : nock (C monk.battery (C (C (C s f) (A 0)) ctx)) monk.battery with
  | none =>
    have h0 : nock (C mack.battery (C (C s f) ctx)) mack.battery = none := by
      nock_open mack.battery; simp [nock_exec, hma, monk_arm, hm]
    rw [h0]
    simp only [reduceCtorEq, false_iff, not_exists, not_and]
    intro r hr _
    rw [(monk_gate_iff lib ctx hmo hslam s f (A 0) _).mpr ⟨r, hr, rfl⟩] at hm
    cases hm
  | some y =>
    obtain ⟨r, hr, rfl⟩ := (monk_gate_iff lib ctx hmo hslam s f (A 0) y).mp hm
    have h1 : nock (C mack.battery (C (C s f) ctx)) mack.battery = some (unitN (mackUnit r)) := by
      nock_open mack.battery
      cases r <;> simp [nock_exec, hma, monk_arm, hm, monkToon, Toon.toNoun, mackUnit, unitN,
        listNoun]
    rw [h1]
    constructor
    · intro h; exact ⟨r, hr, (Option.some.inj h).symm⟩
    · rintro ⟨r', hr', rfl⟩
      cases Mink.det hr hr'
      rfl

end Compiler
end Formalization
