import lemmas.Ska.CompHintCheck

/-!
# A kept hint's result is not flat in general (README Gaps 24.12)

`+lazy-bound` (`lazyBound`, the cases `%bout`/`%xray`, the dynamic hints
and `%mean` of `runLCH`) puts the formula's whole lazy need in a bond:
`mk bunt [] [(o, laz)]`.  When `laz` has a bond itself (the formula is a
cons whose head is hinted, `+past` parks the tail's need), the result is a
bond inside a bond, which is not `Flat`.  Every relation of the call
classes (`LOKS`, `LOKSF`, `LOKSM`, `LOKSH`, `DoneOK`) asks a flat result,
so a kept hint around such a formula is outside all of them; a kept hint
around a formula whose result has no bond keeps the result flat.

The witnesses, on the model (`envH`, `sndH` of `CompHintCheck.lean`):

* `boutCons`: `[11 %bout [[11 %bout [0 2]] [4 [0 3]]]]` under `%done`: the
  result's bond holds a lazy need with a bond (`nested = some true`);
* `boutLeaf`: `[11 %bout [4 [0 3]]]`: flat (`nested = some false`).
-/

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

/-- Whether the result of the run under `%done` has a bond whose lazy need
is not `ofSure` (a fork or a bond inside). -/
def nested (nm : Nomm) : Option Bool :=
  (runLCH (S := LS) (Map := FM) envH sndH true Option.none nm CGoalL.done [] gen0).map fun r =>
    !r.1.laz.fork.isEmpty || r.1.laz.bond.any fun e => !e.2.fork.isEmpty || !e.2.bond.isEmpty

def boutCons : Nomm :=
  Nomm.n11s HintTag.bout (Nomm.cons (Nomm.n11s HintTag.bout (Nomm.n0 2) (A 0)) (Nomm.n4 (Nomm.n0 3))) (A 0)

def boutLeaf : Nomm := Nomm.n11s HintTag.bout (Nomm.n4 (Nomm.n0 3)) (A 0)

#guard nested boutCons == some true
#guard nested boutLeaf == some false
-- The same cons without the outer hint is flat (the cons parks its need
-- in a bond of its own, at the top level).
#guard nested (Nomm.cons (Nomm.n11s HintTag.bout (Nomm.n0 2) (A 0)) (Nomm.n4 (Nomm.n0 3))) == some false

end Comp
end SkaModel
end Formalization
