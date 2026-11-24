import lemmas.Compiler.OptLinkOnceGate
import lemmas.Hoon.UnoBy
import lemmas.Ska.OptTrim

/-!
# `+trim-trace-hints`: the nouns, the keys, the gate `trace`

The arm is `23` of `optC` (`tr_at`, nouns by `tools/gen/optlink.py trim`).
Its body (`trBody`) pushes the gate `trace` (`trTraceB`), runs the outer
trap `trOTrap` over `topo` from `[unsafe=~ out=~]` (each turn: the block by
`+got:by`, `open` by the `+roll` `trORoll` over the predecessors with
`+uno:by` and `+max`, then the inner trap `trITrap` over the body, then
`trIEnd`: the `=?` of `unsafe` and the next turn), then `opened` by the
`+rep:by` of `trOGate`, then the `+run:by` of `trRnGate`, which skips the
dropped hint ops by the test `trSGate`.

* `keyN`: the noun of a key, `[%clue hint reg]`, `[%defer a v f]`,
  `[%konst n f]`; injective (`keyN_inj`, by the decoder `keyDec`).
* `tr_trace`: **the gate `trace` on the noun of an op is `traceKey`**, as
  the unit `traceN op` of `[open key]`.
* `tr_nct`: `?=(pole-not-crashing -.op)` is `notCrashing`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The nouns -/

/-- The body of the gate `trace`: the key of a trace hint op and whether it opens the hint. -/
def trTraceB : Noun :=
  (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706468)) (C (A 0) (A 12)))) (C (C (A 6) (C (C (A 3) (C (A 0) (A 13))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6e61656d)) (C (A 0) (A 26)))) (C (C (A 1) (A 0)) (C (A 5) (C (C (A 1) (A 0x746f7073)) (C (A 0) (A 26))))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (C (A 1) (A 0)) (C (C (A 1) (A 0)) (C (C (A 1) (A 0x65756c63)) (C (C (A 0) (A 26)) (C (A 0) (A 54)))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656468)) (C (A 0) (A 12)))) (C (C (A 6) (C (C (A 3) (C (A 0) (A 13))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6e61656d)) (C (A 0) (A 26)))) (C (C (A 1) (A 0)) (C (A 5) (C (C (A 1) (A 0x746f7073)) (C (A 0) (A 26))))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (C (A 1) (A 0)) (C (C (A 1) (A 1)) (C (C (A 1) (A 0x65756c63)) (C (C (A 0) (A 26)) (C (A 0) (A 54)))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 5) (C (C (A 1) (A 0x706d68)) (C (A 0) (A 12)))) (C (A 1) (A 1))))) (C (C (C (A 1) (A 0)) (C (C (A 1) (A 0)) (C (C (A 1) (A 0x7265666564)) (C (C (A 0) (A 26)) (C (C (A 0) (A 54)) (C (A 0) (A 55))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 5) (C (C (A 1) (A 0x656d68)) (C (A 0) (A 12)))) (C (A 1) (A 1))))) (C (C (C (A 1) (A 0)) (C (C (A 1) (A 1)) (C (C (A 1) (A 0x7265666564)) (C (C (A 0) (A 26)) (C (C (A 0) (A 54)) (C (A 0) (A 55))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 5) (C (C (A 1) (A 0x706368)) (C (A 0) (A 12)))) (C (A 1) (A 1))))) (C (C (C (A 1) (A 0)) (C (C (A 1) (A 0)) (C (C (A 1) (A 0x74736e6f6b)) (C (C (A 0) (A 26)) (C (A 0) (A 27)))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 5) (C (C (A 1) (A 0x656368)) (C (A 0) (A 12)))) (C (A 1) (A 1))))) (C (C (C (A 1) (A 0)) (C (C (A 1) (A 1)) (C (C (A 1) (A 0x74736e6f6b)) (C (C (A 0) (A 26)) (C (A 0) (A 27)))))) (C (A 11) (C (C (A 0x73736f74) (C (A 1) (A 0))) (C (A 1) (A 0))))))))))))))))))))))

/-- Its sample bunt. -/
def trTBunt : Noun :=
  (C (A 0x6d7363) (C (C (C (A 1) (A 0)) (C (A 0) (A 0))) (C (A 0) (C (A 0) (A 0)))))

/-- The body of the gate `|=([k=key v=@ud w=@ud] (max v w))`. -/
def trMaxG : Noun :=
  (C (A 8) (C (C (A 9) (C (A 598) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 58)) (C (A 0) (A 59)))) (C (A 0) (A 2))))))))

/-- Its sample bunt. -/
def trMaxB : Noun :=
  (C (C (A 0x74736e6f6b) (C (A 0) (A 0))) (C (A 0) (A 0)))

/-- `(~(uno by acc) (~(gut by out) p *(map key @ud)))`: the gate `|*  meg` of `+uno:by`. -/
def trUnoB : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 4) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 1531) (C (A 10) (C (C (A 6) (C (A 0) (A 253))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2))))))))

/-- The gate of the `+roll` over the predecessors. -/
def trRGate : Noun :=
  (C (A 8) (C trUnoB (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) trMaxB) (C (C (A 1) trMaxG) (C (A 0) (A 1)))))))) (C (A 0) (A 2))))))))

/-- Its sample bunt. -/
def trRBunt : Noun :=
  (C (A 0) (A 0))

/-- `(~(get ja rev) i.topo)`. -/
def trGetJa : Noun :=
  (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 761) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 10) (C (A 10) (C (C (A 6) (C (A 0) (A 1019))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 2036))) (C (A 0) (A 2))))))))))

/-- `open`: the `+roll` over the predecessors. -/
def trORoll : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C trGetJa (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) trRBunt) (C (C (A 1) trRGate) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))

/-- `(~(got by blocks) i.topo)`. -/
def trOGot : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 252))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 1012))) (C (A 0) (A 2))))))))

/-- `!?=(?(%clq %eqq %brz %hop) -.fin.b)`. -/
def trFinT : Noun :=
  (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x7a7262)) (C (A 0) (A 246)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706f68)) (C (A 0) (A 246)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x717165)) (C (A 0) (A 246)))) (C (C (A 1) (A 0)) (C (A 5) (C (C (A 1) (A 0x716c63)) (C (A 0) (A 246))))))))))))) (C (C (A 1) (A 1)) (C (A 1) (A 0)))))

/-- `(~(uni in unsafe) ~(key by open))` at the end of a block. -/
def trEUni : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 174) (C (A 10) (C (C (A 6) (C (A 0) (A 508))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 188) (C (A 10) (C (C (A 6) (C (A 0) (A 30))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2))))))))

/-- The `=?` of `unsafe` at the end of a block. -/
def trEUpd : Noun :=
  (C (A 6) (C trFinT (C trEUni (C (A 0) (A 252)))))

/-- The next turn of the outer trap: `topo` and `out` edited. -/
def trENext : Noun :=
  (C (A 9) (C (A 2) (C (A 10) (C (C (A 250) (C (A 0) (A 8181))) (C (A 10) (C (C (A 13) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 509))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 0x3ff4)) (C (A 0) (A 30)))) (C (A 0) (A 2))))))))) (C (A 0) (A 31))))))))

/-- The end of a block in the inner trap. -/
def trIEnd : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 252) trEUpd) (C (A 0) (A 1)))) trENext))

/-- `(trace op)`. -/
def trIHint : Noun :=
  (C (A 8) (C (C (A 0) (A 510)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2))))))))

/-- `?=(pole-not-crashing -.op)`. -/
def trNcT : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x766f6d)) (C (A 0) (A 12)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706d68)) (C (A 0) (A 12)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6c6174)) (C (A 0) (A 12)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x757165)) (C (A 0) (A 12)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x707368)) (C (A 0) (A 12)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706368)) (C (A 0) (A 12)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706468)) (C (A 0) (A 12)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656d68)) (C (A 0) (A 12)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6e6f63)) (C (A 0) (A 12)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x646568)) (C (A 0) (A 12)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x657368)) (C (A 0) (A 12)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6d6d69)) (C (A 0) (A 12)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656468)) (C (A 0) (A 12)))) (C (C (A 1) (A 0)) (C (A 5) (C (C (A 1) (A 0x656368)) (C (A 0) (A 12)))))))))))))))))))))))))))))))))))))))))))

/-- `$(body t.body)`. -/
def trSkipK : Noun :=
  (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 61))) (C (A 0) (A 7))))))

/-- `$(body t.body, unsafe (~(uni in unsafe) ~(key by open)))`. -/
def trWiden : Noun :=
  (C (A 9) (C (A 2) (C (A 10) (C (C (A 252) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 174) (C (A 10) (C (C (A 6) (C (A 0) (A 2044))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 188) (C (A 10) (C (C (A 6) (C (A 0) (A 126))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2))))))))) (C (A 10) (C (C (A 6) (C (A 0) (A 61))) (C (A 0) (A 7))))))))

/-- An op without key: `pole-not-crashing` or the unsafe keys widened. -/
def trINoHint : Noun :=
  (C (A 6) (C trNcT (C trSkipK trWiden)))

/-- `(~(gut by open) key.u.hint 0)`. -/
def trHGut : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 1531) (C (A 10) (C (C (A 6) (C (A 0) (A 126))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 27)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))))) (C (A 0) (A 2))))))))

/-- `$(body t.body, open (~(put by open) key.u.hint +(n)))`. -/
def trOpenK : Noun :=
  (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 254))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 59)) (C (A 7) (C (C (A 0) (A 3)) (C (A 4) (C (A 0) (A 2))))))) (C (A 0) (A 2))))))))) (C (A 10) (C (C (A 6) (C (A 0) (A 125))) (C (A 0) (A 15))))))))

/-- `(lte n 1)`. -/
def trLte : Noun :=
  (C (A 8) (C (C (A 9) (C (A 148) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 1)))))) (C (A 0) (A 2))))))))

/-- `$(body t.body, open (~(del by open) key.u.hint))`. -/
def trDelK : Noun :=
  (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 190) (C (A 10) (C (C (A 6) (C (A 0) (A 254))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2))))))))) (C (A 10) (C (C (A 6) (C (A 0) (A 125))) (C (A 0) (A 15))))))))

/-- `$(body t.body, open (~(put by open) key.u.hint (dec n)))`. -/
def trDecK : Noun :=
  (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 254))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 59)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 2398) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))) (C (A 10) (C (C (A 6) (C (A 0) (A 125))) (C (A 0) (A 15))))))))

/-- An op with a key: its count opened or closed. -/
def trIHintC : Noun :=
  (C (A 8) (C trHGut (C (A 6) (C (C (A 0) (A 26)) (C trOpenK (C (A 6) (C trLte (C trDelK trDecK))))))))

/-- A turn of the inner trap on an op. -/
def trIStep : Noun :=
  (C (A 8) (C (C (A 0) (A 12)) (C (A 8) (C trIHint (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C trINoHint trIHintC)))))))

/-- `?=(~ body)`. -/
def trITest : Noun :=
  (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 1) (A 1)) (C (A 1) (A 0)))))

/-- The inner trap over the body of a block. -/
def trITrap : Noun :=
  (C (A 6) (C trITest (C trIEnd trIStep)))

/-- The outer trap over `topo`. -/
def trOTrap : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 250)))) (C (C (A 0) (A 12)) (C (A 8) (C trOGot (C (A 8) (C trORoll (C (A 8) (C (C (A 0) (A 26)) (C (A 8) (C (C (A 1) trITrap) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))))))))))

/-- The gate of the `+roll` over the body in `opened`. -/
def trOpg : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 0) (A 126)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (A 0) (A 29)) (C (A 6) (C (C (A 0) (A 10)) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 84) (C (A 10) (C (C (A 6) (C (A 0) (A 61))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 27))) (C (A 0) (A 2)))))))) (C (A 0) (A 29))))))))))

/-- Its sample, the bunt of `pole` made by its mold. -/
def trOBuntF : Noun :=
  (C (C (A 7) (C (C (A 9) (C (A 2743) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (A 0) (A 13)))

/-- The gate of the `+rep:by` of `opened`. -/
def trOGate : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 230)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C trOBuntF (C (C (A 1) trOpg) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))

/-- Its sample bunt. -/
def trOBunt : Noun :=
  (C (C (A 0) (C (A 0) (C (A 0) (C (A 0x6d6f62) (A 0))))) (A 0))

/-- The test of the `+skip`: a hint op whose key is not unsafe and is opened. -/
def trSGate : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (A 1) (A 1)) (C (A 6) (C (C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 381) (C (A 10) (C (C (A 6) (C (A 0) (A 510))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 27))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 381) (C (A 10) (C (C (A 6) (C (A 0) (A 254))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 27))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))))))))

/-- Its sample bunt. -/
def trSBunt : Noun :=
  trTBunt

/-- The gate of the `+run:by`: the body skipped. -/
def trRnGate : Noun :=
  (C (A 10) (C (C (A 6) (C (A 8) (C (C (A 9) (C (A 0xbef7f5f) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 58)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) trSBunt) (C (C (A 1) trSGate) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 6))))

/-- Its sample bunt. -/
def trRnBunt : Noun :=
  (C (A 0) (C (A 0) (C (A 0x6d6f62) (A 0))))

/-- The gate body of `+trim-trace-hints`. -/
def trBody : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 8) (C (C (A 1) trSBunt) (C (C (A 1) trTraceB) (C (A 0) (A 1))))) (C (A 8) (C (C (A 8) (C (C (A 1) trRBunt) (C (A 8) (C (C (A 1) trOTrap) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 767) (C (A 10) (C (C (A 6) (C (A 0) (A 124))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) trOBunt) (C (C (A 1) trOGate) (C (A 0) (A 1)))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 766) (C (A 10) (C (C (A 6) (C (A 0) (A 252))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) trRnBunt) (C (C (A 1) trRnGate) (C (A 0) (A 1)))))))) (C (A 0) (A 2))))))))))))))))

/-- Its sample bunt. -/
def trBunt : Noun :=
  (C (A 0) trRBunt)

/-- Its `%fast` hint. -/
def trHint : Noun :=
  (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x73746e69682d65636172742d6d697274) (C (C (A 0) (A 0xffff)) (A 0))))) (C (A 0) (A 1))))

/-- The arm `+trim-trace-hints`. -/
def trArm : Noun := C (A 7) (C (C (A 8) (C (C (A 1) trBunt) (C (C (A 1) trBody) (C (A 0) (A 1))))) trHint)

/-- `+trim-trace-hints` is arm `23` of `optC`. -/
theorem tr_at : slot? 23 optC = some trArm := by kernel_rfl

/-- The body read from the pill by `TrimLink` is `trBody`. -/
theorem trimBody_eq : trimBody = trBody := by
  unfold trimBody trimArm
  rw [tr_at]
  rfl

/-! ## The keys -/

/-- The noun of a key: `[%clue hint reg]`, `[%defer a v f]`, `[%konst n f]`. -/
def keyN : Opt.TKey → Noun
  | .clue n p => C (A 0x65756c63) (C (A n) (A p))
  | .defer a v f => C (A 0x7265666564) (C a.toNoun (C (listNoun A v) f))
  | .konst n f => C (A 0x74736e6f6b) (C n f)

open OptDec in
/-- The key of a noun, by its tag. -/
def keyDec (n : Noun) : Opt.TKey :=
  let t := atomOf (hd n)
  let r := tl n
  if t = 0x65756c63 then .clue (atomOf (hd r)) (atomOf (tl r))
  else if t = 0x7265666564 then .defer (bellDec (hd r)) (listDec atomOf (hd (tl r))) (tl (tl r))
  else .konst (hd r) (tl r)

open OptDec in
theorem keyDec_keyN (k : Opt.TKey) : keyDec (keyN k) = k := by
  have hl := listDec_listNoun atomOf A (fun _ => rfl)
  cases k <;> simp [keyDec, keyN, hd, tl, atomOf, bellDec_toNoun, hl]

theorem keyN_inj {a b : Opt.TKey} : keyN a = keyN b ↔ a = b :=
  ⟨fun h => by rw [← keyDec_keyN a, h, keyDec_keyN], fun h => h ▸ rfl⟩

/-! ## The gate `trace` -/

/-- The unit `[open key]` that `trace` gives. -/
def traceN (op : Pole) : Noun :=
  match Opt.traceKey op with
  | none => A 0
  | some (b, k) => C (A 0) (C (flag b) (keyN k))

/-- **The gate `trace`** on the noun of an op is `traceKey`. -/
theorem tr_trace (op : Pole) (ctx : Noun) :
    nock (C trTraceB (C op.toNoun ctx)) trTraceB = some (traceN op) := by
  conv => lhs; arg 2; unfold trTraceB
  cases op with
  | hdp n p f =>
    by_cases e1 : n = Tag.spot
    · subst e1; simp [nock_exec, Pole.toNoun, traceN, Opt.traceKey, keyN, flag, Tag.hdp, Tag.spot, Tag.mean]
    · by_cases e2 : n = Tag.mean
      · subst e2; simp [nock_exec, Pole.toNoun, traceN, Opt.traceKey, keyN, flag, Tag.hdp, Tag.spot, Tag.mean]
      · simp only [Tag.spot, Tag.mean] at e1 e2
        simp [nock_exec, Pole.toNoun, traceN, Opt.traceKey, keyN, flag, Tag.hdp, Tag.spot, Tag.mean,
          Ne.symm e1, Ne.symm e2, e1, e2]
  | hde n p f =>
    by_cases e1 : n = Tag.spot
    · subst e1; simp [nock_exec, Pole.toNoun, traceN, Opt.traceKey, keyN, flag, Tag.hde, Tag.spot, Tag.mean]
    · by_cases e2 : n = Tag.mean
      · subst e2; simp [nock_exec, Pole.toNoun, traceN, Opt.traceKey, keyN, flag, Tag.hde, Tag.spot, Tag.mean]
      · simp only [Tag.spot, Tag.mean] at e1 e2
        simp [nock_exec, Pole.toNoun, traceN, Opt.traceKey, keyN, flag, Tag.hde, Tag.spot, Tag.mean,
          Ne.symm e1, Ne.symm e2, e1, e2]
  | _ =>
    simp [nock_exec, Pole.toNoun, traceN, Opt.traceKey, keyN, flag, Tag.imm, Tag.mov, Tag.inc, Tag.con,
      Tag.hed, Tag.tal, Tag.cel, Tag.lob, Tag.equ, Tag.hsp, Tag.hse, Tag.hdp, Tag.hde, Tag.hmp, Tag.hme, Tag.hcp,
      Tag.hce, Tag.spy, Tag.nok, Tag.cal, Tag.caf, Tag.cam, Tag.csl, Tag.csf, Tag.csm]

/-- **`?=(pole-not-crashing -.op)`** is `notCrashing`. -/
theorem tr_nct (op : Pole) (H Y : Noun) :
    nock (C H (C op.toNoun Y)) trNcT = some (loob (Opt.notCrashing op)) := by
  unfold trNcT
  cases op <;> simp [nock_exec, eqCode_atom, Pole.toNoun, Opt.notCrashing, loob, Tag.imm, Tag.mov, Tag.inc, Tag.con,
      Tag.hed, Tag.tal, Tag.cel, Tag.lob, Tag.equ, Tag.hsp, Tag.hse, Tag.hdp, Tag.hde, Tag.hmp, Tag.hme, Tag.hcp,
      Tag.hce, Tag.spy, Tag.nok, Tag.cal, Tag.caf, Tag.cam, Tag.csl, Tag.csf, Tag.csm]

end Compiler
end Formalization
