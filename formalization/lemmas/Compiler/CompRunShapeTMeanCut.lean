import lemmas.Compiler.CompRunShapeTDefs
import lemmas.Compiler.CompRunShapeMean

/-!
# The case `%mean` of `+run-shape`, cut at its pushes (track A, 2026-11-28)

`rsmArm` (`CompRunShapeMeanCut.lean`) is a chain of `=^` pushes
`7 [0 1] 8 [F 7 [10 [AX 0 5] 0 1] 7 [[0 4] 0 3] R]` (`rsmTis AX F R`): `+laze-past-if` (`rsmF1`,
`gen` at axis `510`), the run of `q` (`rsmF2`, `1022`), `+id` (`rsmF3`, `2046`), the push of
`l-fol` (`rsmF4`), then `rsmR5`: the need push (`rsmNed`, `8190`), `l-arg` (`rsmArg`) and
`rsmEnd`.  `rsmArm_eq` says so (by `rfl`).

* `MeanNeedT`: what the case reads of `+callee-need`, threading the rest (a miss compiles the
  callee and returns a bigger cache).
* `rsmS5`: the subject at `rsmR5`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **What the case reads of `+callee-need`, threading the rest**: when the key is not a konst,
`env.need b`, and the rest moves from `y` to some `y'` of `E` with `Rl y y'`. -/
def MeanNeedT (ctx : Noun) (env : ShapeEnv) (E : RsRest → Prop) (Rl : RsRest → RsRest → Prop) (b : Bell)
    (k : Option Noun) (y : RsRest) : Prop :=
  meanKonstS env b k = some false → ∃ nb, env.need b = some nb ∧ ∀ st : RSt CSet, ∃ y', Rl y y' ∧ E y' ∧
    nock (C cneBat (C b.toNoun (rsDoor st y ctx))) cneBat = some (C nb.toNoun (rsGenNoun st y'))

/-- The `=^` push: `F` returns `[x gen']`, `gen` at axis `AX` is set to `gen'`, `R` runs on
`[x subject]`. -/
def rsmTis (AX : Nat) (F R : Noun) : Noun :=
  C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C F (C (A 7) (C (C (A 10) (C (C (A AX) (C (A 0) (A 5))) (C (A 0) (A 1))))
    (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) R)))))))

/-- `+laze-past-if` of `simple` over `q`. -/
def rsmF1 : Noun :=
  C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 1406) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10)
    (C (C (A 6) (C (C (A 0) (A 13)) (C (A 0) (A 4046)))) (C (A 0) (A 2)))))))))

/-- The run of `q` on `[%next gol]`. -/
def rsmF2 : Noun :=
  C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 26) (C (C (A 1) (A 0x7478656e)) (C (A 0) (A 2))))
    (C (A 10) (C (C (A 12) (C (A 0) (A 4046))) (C (A 0) (A 31)))))))))

/-- `+id`. -/
def rsmF3 : Noun := C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0xabef) (C (A 0) (A 255)))))

/-- `l-fol`: `[[%none ~] ~ [[i lf] ~]]`. -/
def rsmF4 : Noun :=
  C (C (A 1) (C (C (A 0x656e6f6e) (A 0)) (A 0))) (C (C (A 1) (A 0)) (C (C (C (A 0) (A 2)) (C (A 0) (A 6))) (C (A 1) (A 0))))

/-- The need push, `l-arg` and the end. -/
def rsmR5 : Noun := rsmTis 8190 rsmNed (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C rsmArg rsmEnd))))

/-- The prefix of the case up to `l-fol`, then `R`. -/
def rsmPreF (R : Noun) : Noun := rsmTis 510 rsmF1 (rsmTis 1022 rsmF2 (rsmTis 2046 rsmF3 (C (A 8) (C rsmF4 R))))

theorem rsmArm_eq : rsmArm = rsmPreF rsmR5 := rfl

/-- The subject at `rsmR5`: `[l-fol [i [lf [gol S]]]]` over the case's subject. -/
def rsmS5 (LFOL I LF GOL SIM NOM GN SN D : Noun) : Noun := C LFOL (C I (C LF (C GOL (rsS SIM NOM GN SN D))))

/-- The noun of `[%mean p b q body k]` with `p` and `q` as nouns. -/
def meanN (P : Noun) (b : Bell) (Q BODY : Noun) (k : Option Noun) : Noun :=
  C (A Tag.mean) (C P (C b.toNoun (C Q (C BODY (unitNoun id k)))))

theorem mean_noun (p : Nomm) (b : Bell) (q : Nomm) (body : Noun) (k : Option Noun) :
    (Nomm.mean p b q body k).toNoun = meanN p.toNoun b q.toNoun body k := rfl

end Compiler
end Formalization
