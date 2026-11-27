import core.Cue
import lemmas.Spec
import lemmas.KernelRfl

/-! `cue` of `core/Cue.lean` on jams made by another implementation
(`tools/nouns.py`), with atoms, cells and references.  Checked by the kernel. -/

namespace Formalization
namespace CueSpec

open Nock

example : cue 0x2 = some (A 0) := by decide

example : cue 0xc = some (A 1) := by decide

example : cue 0xb8 = some (A 5) := by decide

example : cue 0x1231 = some (C (A 1) (A 2)) := by decide

example : cue 0x344871 = some (C (A 1) (C (A 2) (A 3))) := by decide

example : cue 0x2a5 = some (C (C (A 0) (A 0)) (A 0)) := by decide

example : cue 0x127241936c66f07ade68adc05 = some (C (C (A 123456789) (C (A 77) (C (A 1) (A 0)))) (C (C (A 123456789) (C (A 77) (C (A 1) (A 0)))) (C (A 9) (C (A 123456789) (C (A 77) (C (A 1) (A 0))))))) := by decide

example : cue 0x26726fd0707d0a05 = some (C (C (A 1000) (A 2000)) (C (C (A 1000) (A 2000)) (A 1000))) := by decide

example : cue 0x24e4d8000000000000000063c01 = some (C (A 1180591620717411303427) (C (A 1180591620717411303427) (A 1180591620717411303427))) := by decide

/-- No noun: the atom ends inside a length. -/
example : cue 0 = none := by decide

/-- No noun: a reference to a bit where nothing starts. -/
example : cue 0x3b = none := by decide


end CueSpec
end Formalization
