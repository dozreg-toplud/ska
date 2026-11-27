import lemmas.Compiler.OptLinkAlStartImms

/-!
# `+alias`: the start of a block's turn, assembled (phases 9 and 10 of the plan, README Gaps 13)

```hoon
  =^  info=(map @uvre info-reg)  gen
    ?~  pre  ...entry...
    :_  gen
    ...join, refinement...
  =/  imms=(jug * @uvre)  ...
  =.  info-local.gen  info
  =.  imms-local.gen  imms
```

* `alStartF K`: the formula of the walk from the `=^  info  gen` to the
  second `=.`, then `K`; `alWalk_start`: the walk's branch after the test of an
  unreachable block is `alStartF` of `[8 alBob X]`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The walk from `=^  info  gen` (`alInfo`) through `imms` (`alImms`) and the
two `=.` (`info-local` at axis `2014`, `imms-local` at `4030`), then `K`. -/
def alStartF (K : Noun) : Noun :=
  C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C alInfo (C (A 7) (C (C (A 10) (C (C (A 30) (C (A 0) (A 5))) (C (A 0) (A 1))))
    (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C alImms (C (A 7) (C (C (A 10) (C (C (A 2014)
    (C (A 0) (A 6))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 4030) (C (A 0) (A 2))) (C (A 0) (A 1))))
    K)))))))))))))

/-- The walk, cut at `alStartF`: after `pre` and the test of an unreachable
block, `alStartF` of the rest from `bob` on. -/
theorem alWalk_start : ∃ X, alWalk = C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 247))))
    (C (C (C (A 0) (A 895)) (C (A 0) (A 12))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C alPre
    (C (A 6) (C alUnT (C alUnB (alStartF (C (A 8) (C alBob X)))))))))))) := ⟨_, rfl⟩

end Compiler
end Formalization
