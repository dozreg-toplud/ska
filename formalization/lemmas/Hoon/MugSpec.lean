module

public import lemmas.Hoon.Basic
public import lemmas.Pill.Arm.Mug
import all lemmas.Pill.Arm.Mug
/-!
What the proofs of the arms that hash need from `+mug`: `MugSpec mug c`, that
slamming the `+mug` gate with context `c` on any noun ends with the atom
`mug a`.  `Mug.lean` proves it for `mugF`.
-/

@[expose] public section

namespace Formalization
namespace Hoon

open Nock Pill

/-- What the proofs need from `+mug`: slamming its gate, with context `c`, on
any noun ends with an atom, and `mug a` is that atom. -/
abbrev MugSpec (mug : Noun → Nat) (c : Noun) : Prop :=
  ∀ a : Noun, nock (C Pill.mug.battery (C a c)) Pill.mug.battery = some (A (mug a))

abbrev MugIn (mug : Noun → Nat) (c : Noun) : Prop :=
  slot? Pill.mug.axis c = some Pill.mug.arm ∧ MugSpec mug c

@[nock_exec] theorem mug_arm (c : Noun) :
    nock c Pill.mug.arm = some (C Pill.mug.battery (C (A 0) c)) := by
  nock_open Pill.mug.arm; simp only [nock_exec]

end Hoon
end Formalization

end
