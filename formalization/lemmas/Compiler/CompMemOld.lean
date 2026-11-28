import lemmas.Compiler.CompSccOne

/-!
# The gate `member` when `map-local` holds the bell

On the final pass, when `map-local` already has a straight `u` of `b`
(`s-previous` is `[~ u]`, the branch `memOld` of `member`, lines 3589 to
3603 of `nock-compilation.hoon`):

```hoon
=/  need-pessimized
  (msg-need-ord-kept need-new need.u.s-previous cape.less.b)
:+  |(moved !=(need-pessimized need.u.s-previous))
  %+  ~(put by map-local)  b
  ?:  =(need-pessimized need-new)  (finish ~)
  (finish `need-pessimized)
cache
```

Linked here for the case of a fixed point reached, where the shape of `u`
is `need-new`: `+msg-need-ord-kept` (arm `178934` of `K` since 2a5b618, its
nouns cut by `tools/gen/keptarm.py`; `+msg-need-ord`, arm `20`, cut by
`tools/gen/msgneed.py`, is kept below for its other users) of two equal
shapes is that shape by its first branch (`kept_eq`), so `need-pessimized` is `need-new`, `chg` is `moved`, and
`finish ~` is called, whose straight `finishLF` gives (`mem_prod_old`,
`mem_gate_old`).  The other case (`finish` of a pessimized shape, through
`+coerce-soft`, which has no model) is not linked.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## `+msg-need-ord` -/

/-- The branches of `+msg-need-ord` after `?:  =(a b)  a`. -/
def msgRest : Noun :=
  (C (A 11) (C (C (A 0x6f6d656d) (C (A 1) (A 0))) (C (A 6) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 24)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 24)))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 52)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 52)))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 1) (C (A 0x73696874) (A 0))) (C (A 6) (C (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 27))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 24)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 24)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 52)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 52)))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))))))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 1) (C (A 0x73696874) (A 0))) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 24)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 24)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 52)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 52)))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))))))))) (C (C (A 8) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 24)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 24)))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C (C (C (A 0) (A 12)) (C (A 0) (A 26))) (C (C (A 0) (A 26)) (C (A 0) (A 12)))))) (C (A 8) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 10)))) (C (C (A 0) (A 22)) (C (A 6) (C (C (A 3) (C (A 0) (A 10))) (C (C (A 0) (A 10)) (C (A 0) (A 0)))))))) (C (A 8) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 26)))) (C (C (A 0) (A 55)) (C (A 6) (C (C (A 3) (C (A 0) (A 26))) (C (C (A 0) (A 27)) (C (A 0) (A 0)))))))) (C (A 8) (C (C (A 8) (C (C (A 0) (A 15)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (C (A 0x656e6f6e) (A 0))))) (C (C (A 0) (A 14)) (C (A 0) (A 1014))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 0) (A 31)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (C (A 0x656e6f6e) (A 0))))) (C (C (A 0) (A 14)) (C (A 0) (A 2039))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 248)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 250)))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C (C (C (A 1) (A 0x68746f62)) (C (C (A 0) (A 6)) (C (A 0) (A 2)))) (C (A 8) (C (C (A 9) (C (A 350) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 0) (A 6)) (C (A 0) (A 2)))))) (C (A 0) (A 2))))))))))) (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 75) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 1396) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 0x5dd6) (C (A 0) (A 511)))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 0x5dd6) (C (A 0) (A 511)))))))) (C (A 0) (A 2)))))))) (C (C (A 1) (C (A 0x73696874) (A 0))) (C (A 0) (A 2))))))))))))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 24)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 52)))) (C (C (C (A 1) (A 0x68746f62)) (C (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 114)) (C (C (A 0) (A 234)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 255)))) (C (A 9) (C (A 20) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2))))))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 115)) (C (C (A 0) (A 235)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 255)))) (C (A 9) (C (A 94) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2))))))))))))) (C (A 0) (A 2)))))))))) (C (C (A 1) (A 0x68746f62)) (C (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 114)) (C (C (A 0) (A 116)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 255)))) (C (A 9) (C (A 20) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2))))))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 115)) (C (C (A 0) (A 117)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 255)))) (C (A 9) (C (A 94) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2))))))))))))) (C (A 0) (A 2))))))))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 52)))) (C (C (C (A 1) (A 0x68746f62)) (C (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 56)) (C (C (A 0) (A 234)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 255)))) (C (A 9) (C (A 20) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2))))))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 57)) (C (C (A 0) (A 235)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 255)))) (C (A 9) (C (A 94) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2))))))))))))) (C (A 0) (A 2)))))))))) (C (A 8) (C (C (A 9) (C (A 350) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 56)) (C (C (A 0) (A 116)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 255)))) (C (A 9) (C (A 20) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2))))))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 57)) (C (C (A 0) (A 117)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 255)))) (C (A 9) (C (A 94) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2))))))))))))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2)))))))))))))))))))))))))

/-- The gate body of `+msg-need-ord`. -/
def msgBody : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 5) (C (C (A 0) (A 12)) (C (A 0) (A 26)))) (C (C (A 0) (A 12)) msgRest)))))

/-- Its sample bunt. -/
def msgBunt : Noun :=
  (C (C (A 0x656e6f6e) (A 0)) (C (C (A 0x656e6f6e) (A 0)) (A 1)))

/-- Its `%fast` hint. -/
def msgHint : Noun :=
  (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x64726f2d6465656e2d67736d) (C (C (A 0) (A 0x7fff)) (A 0))))) (C (A 0) (A 1))))

/-- The arm `+msg-need-ord`. -/
def msgArm : Noun := C (A 7) (C (C (A 8) (C (C (A 1) msgBunt) (C (C (A 1) msgBody) (C (A 0) (A 1))))) msgHint)

/-- `+msg-need-ord` is arm `20` of `K`. -/
theorem msg_at : slot? 20 compK = some msgArm := by kernel_rfl

theorem msg_arm (d : Noun) : nock d msgArm = some (C msgBody (C msgBunt d)) := by
  unfold msgArm msgHint; generalize msgBody = B; generalize msgBunt = U; simp [nock_exec]

/-- **`+msg-need-ord` of two equal shapes** is that shape. -/
theorem msg_eq (X LESS K : Noun) : nock (C msgBody (C (C X (C X LESS)) K)) msgBody = some X := by
  conv => { lhs; arg 2; unfold msgBody }
  generalize msgRest = R
  simp [nock_exec, eqCode_self]

/-! ## `+msg-need-ord-kept` (2a5b618: the join of `member`)

Cut by `tools/gen/keptarm.py` as `+msg-need-ord` is above: the gate has no hint. -/

/-- The branches of `+msg-need-ord-kept` after `?:  =(new old)  new`. -/
def keptRest : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 52)))) (C (C (A 0) (A 26)) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 52)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 24)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 24)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))))))))) (C (C (A 8) (C (C (A 9) (C (A 20) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (C (A 0) (A 58)) (C (A 0) (A 59))))) (C (A 0) (A 2)))))))) (C (A 11) (C (C (A 0x6f6d656d) (C (A 1) (A 0))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 24)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 52)))) (C (C (C (A 1) (A 0x68746f62)) (C (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 114)) (C (C (A 0) (A 234)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 255)))) (C (A 9) (C (A 20) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2))))))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 115)) (C (C (A 0) (A 235)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 255)))) (C (A 9) (C (A 94) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2))))))))))))) (C (A 0) (A 2)))))))))) (C (C (A 1) (A 0x68746f62)) (C (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 114)) (C (C (A 0) (A 116)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 255)))) (C (A 9) (C (A 20) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2))))))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 115)) (C (C (A 0) (A 117)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 255)))) (C (A 9) (C (A 94) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2))))))))))))) (C (A 0) (A 2))))))))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 52)))) (C (C (C (A 1) (A 0x68746f62)) (C (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 56)) (C (C (A 0) (A 234)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 255)))) (C (A 9) (C (A 20) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2))))))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 57)) (C (C (A 0) (A 235)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 255)))) (C (A 9) (C (A 94) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2))))))))))))) (C (A 0) (A 2)))))))))) (C (A 8) (C (C (A 9) (C (A 350) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 56)) (C (C (A 0) (A 116)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 255)))) (C (A 9) (C (A 20) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2))))))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 57)) (C (C (A 0) (A 117)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 255)))) (C (A 9) (C (A 94) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2))))))))))))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))))))))))))))))

/-- The gate body of `+msg-need-ord-kept`. -/
def keptBody : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 5) (C (C (A 0) (A 12)) (C (A 0) (A 26)))) (C (C (A 0) (A 12)) keptRest)))))

/-- Its sample bunt. -/
def keptBunt : Noun :=
  (C (C (A 0x656e6f6e) (A 0)) (C (C (A 0x656e6f6e) (A 0)) (A 1)))

/-- The arm `+msg-need-ord-kept`. -/
def keptArm : Noun := C (A 8) (C (C (A 1) keptBunt) (C (C (A 1) keptBody) (C (A 0) (A 1))))

/-- `+msg-need-ord-kept` is arm `178934` of `K`. -/
theorem kept_at : slot? 178934 compK = some keptArm := by kernel_rfl

theorem kept_arm (d : Noun) : nock d keptArm = some (C keptBody (C keptBunt d)) := by
  unfold keptArm; generalize keptBody = B; generalize keptBunt = U; simp [nock_exec]

/-- **`+msg-need-ord-kept` of two equal shapes** is that shape. -/
theorem kept_eq (X LESS K : Noun) : nock (C keptBody (C (C X (C X LESS)) K)) keptBody = some X := by
  conv => { lhs; arg 2; unfold keptBody }
  generalize keptRest = R
  simp [nock_exec, eqCode_self]

/-! ## The product -/

/-- **The product of `member` when `map-local` holds a straight of `b`
whose shape is `need-new`**: `need-pessimized` is `need-new`, `chg` is
`moved`, and the gate returns `[moved (~(put by map-local) b (finish ~))
cache]`, crashing when `finish` does. -/
theorem mem_prod_old (MOVED SUR' WAS NN LZ NF NEDB IMM : Noun) (o : Nat) (SUR G2 NM DCTX CAPE DATA FOL KEEP
    ML TOP CA DN KIDS ML0 CB SCC LONG JH CACHE0 REST : Noun) (hmv : MOVED = A 0 ∨ MOVED = A 1)
    (hml : IsMap mugF ML) (hprev : getF mugF (C (C CAPE DATA) FOL) ML = some (C (A 0) (C NN REST))) :
    nock (C (C finBody (C (A 0) (finCtx MOVED SUR' WAS NN LZ NF NEDB IMM o SUR G2
          (memS3 NM DCTX (memS0 (C (C CAPE DATA) FOL) KEEP ML TOP CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0))))))
        (finCtx MOVED SUR' WAS NN LZ NF NEDB IMM o SUR G2
          (memS3 NM DCTX (memS0 (C (C CAPE DATA) FOL) KEEP ML TOP CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0)))))
        memProd
      = (nock (C finBody (C (A 0) (finCtx MOVED SUR' WAS NN LZ NF NEDB IMM o SUR G2
          (memS3 NM DCTX (memS0 (C (C CAPE DATA) FOL) KEEP ML TOP CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0))))))
          finBody).bind fun ST => (putF mugF (C (C CAPE DATA) FOL) ST ML).map fun ML' => C MOVED (C ML' CA) := by
  have hL := compK_layer2
  have hma := kept_at
  have hmsg := kept_eq NN CAPE compK
  have hg := get_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ (C (C CAPE DATA) FOL) ML _ hprev
  generalize hF : finCtx MOVED SUR' WAS NN LZ NF NEDB IMM o SUR G2
    (memS3 NM DCTX (memS0 (C (C CAPE DATA) FOL) KEEP ML TOP CA (memCtx DN KIDS ML0 CB SCC LONG JH CACHE0))) = FC
  have hFC := hF
  unfold finCtx memS3 memS0 memSam memCtx at hFC
  cases e : nock (C finBody (C (A 0) FC)) finBody with
  | none =>
    subst hFC
    unfold memProd memSprev memOld
    generalize compK = KC at hL hma hmsg e ⊢
    generalize finBody = FB at e ⊢
    rcases hmv with rfl | rfl <;>
    simp [nock_exec, hL, by.arm_at, by_arm, by.get.arm_at, get_arm, hg, hma, kept_arm, hmsg, e, eqCode_self]
  | some ST =>
    obtain ⟨ML', hp, -, -⟩ := putF_spec mugF ML (C (C CAPE DATA) FOL) ST hml
    have hpg := put_gate (mug := mugF) layer2 gorIn_morIn_layer2 (C (C CAPE DATA) FOL) ST ML ML' hp
    subst hFC
    unfold memProd memSprev memOld
    generalize compK = KC at hL hma hmsg e ⊢
    generalize finBody = FB at e ⊢
    rcases hmv with rfl | rfl <;>
    simp [nock_exec, hL, by.arm_at, by_arm, by.get.arm_at, get_arm, hg, hma, kept_arm, hmsg, e, eqCode_self,
      by.put.arm_at, put_arm, hpg, hp]

/-- **The gate `member` on its final pass when `map-local` holds a straight
of `b` whose shape is the new one** (a fixed point reached): it returns
`[moved (~(put by map-local) b straight) cache]` with `straight` the noun of
`finishLF nm ord cape`, crashing when it is `none`.  The hypotheses are
those of `mem_to_finish`, with `map-local` a map (`hml`) whose value at `b`
has the shape `need-new` at its head (`hprev`). -/
theorem mem_gate_old (cape : Cape) (DATA FOL : Noun) (keep : Bool)
    (ML TOP CACHE DN KIDS ML0 CB SCC CODE LSR JH CACHE0 : Noun)
    (nm : Nomm) (C1 C2 C3 C4 SURE : Noun)
    (hinl : nock (C inlBody (C (C (C (C cape.toNoun DATA) FOL) (C (C CODE LSR) (C JH CACHE))) compK)) inlBody
      = some (C nm.toNoun (cacheN C1 C2 C3 C4 SURE)))
    (hpu : nm.pure = true) (h6 : noSix nm = true) (ht : tenOk nm = true)
    (nex : NextL CSet) (g1 : Gen (TreapMap mugF))
    (hrunL : runL nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))
    (s : Sure CSet) (hlaz : nex.laz = Lazy.ofSure s)
    (ord : NeedOrd) (hsc : nock (C scBody (C (C nex.laz.toNoun cape.toNoun) compK)) scBody = some ord.toNoun)
    (hargs : nex.th.args = []) (nedF : Need) (g2 : Gen (TreapMap mugF))
    (hnoar : needOrdAllocRegs ord g1 = some (nedF, g2))
    (hb : NoBake nedF (Sock.mk cape DATA))
    (sur : NeedOrd) (hsur : sureOf (needToOrd s.ned) s.lok cape = some sur)
    (WAS SURE' : Noun) (hwas : getF mugF (C (C cape.toNoun DATA) FOL) SURE = some WAS)
    (hw : WAS = A 0 ∨ ∃ u, WAS = C (A 0) u)
    (hput : putF mugF (C (C cape.toNoun DATA) FOL) (memSurKN keep WAS sur.toNoun) SURE = some SURE')
    (hml : IsMap mugF ML) (REST : Noun)
    (hprev : getF mugF (C (C cape.toNoun DATA) FOL) ML = some (C (A 0) (C (needToOrd nedF).toNoun REST))) :
    nock (C memBody (C (memSam (C (C cape.toNoun DATA) FOL) (A 0x656e6f64) (loob keep) ML TOP CACHE)
        (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0))) memBody
      = (finishLF (S := CSet) (Map := TreapMap mugF) nm ord cape (fun n => (n, []))).bind fun st =>
          (putF mugF (C (C cape.toNoun DATA) FOL) st.toNoun ML).map fun ML' =>
            C (memMovedN keep WAS sur.toNoun) (C ML' (cacheN C1 C2 C3 C4 SURE')) := by
  rw [mem_to_finish cape DATA FOL keep ML TOP CACHE DN KIDS ML0 CB SCC CODE LSR JH CACHE0 nm C1 C2 C3 C4 SURE
    hinl hpu h6 ht nex g1 hrunL s hlaz ord hsc hargs nedF g2 hnoar hb sur hsur WAS SURE' hwas hw hput]
  have hmv : memMovedN keep WAS sur.toNoun = A 0 ∨ memMovedN keep WAS sur.toNoun = A 1 := by
    unfold memMovedN; split <;> simp
  unfold memFC
  rw [mem_prod_old (hmv := hmv) (hml := hml) (hprev := hprev)]
  obtain ⟨hs6, hs14, hs496, hl2⟩ := mem_rest_slots nm.toNoun SCC (C CODE LSR) JH ML TOP cape.toNoun DATA FOL
    (loob keep) (cacheN C1 C2 C3 C4 SURE') DN KIDS ML0 CB CACHE0
  have hf := fin_gate_finishLF (rfl : slot? 7 (memDCtx SCC (C CODE LSR) JH ML TOP (C (C cape.toNoun DATA) FOL))
      = some compK) (memMovedN keep WAS sur.toNoun) (memSurKN keep WAS sur.toNoun) WAS (needToOrd nedF).toNoun
    sur.toNoun _ cuBunt cape hs6 hs14 hs496 hl2 (cuRest (cacheN C1 C2 C3 C4 SURE)) rfl nm ord nex g1 g2
    nedF s hrunL hargs hlaz (mem_cond_frag nm hpu h6 nex g1 hrunL) hnoar
  rw [hf]
  cases finishLF (S := CSet) (Map := TreapMap mugF) nm ord cape (fun n => (n, [])) <;> rfl

end Compiler
end Formalization
