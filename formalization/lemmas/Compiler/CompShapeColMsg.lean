import lemmas.Compiler.CompShapeColUni
import lemmas.Compiler.CompMemOld
import lemmas.Compiler.Ca
import lemmas.Compiler.Lib

/-!
# `+msg-need-ord` in full, with `+need-ord-regs`, `+hed-need-ord`, `+tel-need-ord`

The nouns are cut by `tools/gen/shapecolmsg.py`.  Linked against the model
of `Ska/ShapeCol.lean` (README Gaps 9):

* `+need-ord-regs` (arm `1396` of `K`): its trap from `acc` is `ordRegs`
  (`nor_trap`), the gate is `ordRegs max n 0` (`nor_gate`);
* `+hed-need-ord` (`374`), `+tel-need-ord` (`92`): `ordHed`, `ordTel`
  (`hon_gate`, `ton_gate`);
* `+msg-need-ord` (arm `20`, `msgBody`): `msgRest` cut into its tests
  (`msg_dispatch`), the case of one side `%this` or `%none` (`msg_one`,
  given the two calls `(msg none+~ ..)`), `(msg none+~ d less)` is `msgNone`
  (`msg_none_gate`), and the gate is `msgOrd a b less` for every `a`, `b`,
  `less` (**`msg_gate`**), given the arms it reads in `K` (`MsgK`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The nouns -/

/-- The `?-` of the trap of `+need-ord-regs`. -/
def norSw : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 120)))) (C (C (A 0) (A 6)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 120)))) (C (C (A 4) (C (A 0) (A 6))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 120)))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 60) (C (A 0) (A 243))) (C (A 10) (C (C (A 6) (C (A 9) (C (A 2) (C (A 10) (C (C (A 60) (C (A 0) (A 242))) (C (A 10) (C (C (A 6) (C (A 4) (C (A 0) (A 6)))) (C (A 0) (A 1))))))))) (C (A 0) (A 1)))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 3) (C (A 0) (A 120)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 60) (C (A 0) (A 121))) (C (A 10) (C (C (A 6) (C (A 9) (C (A 2) (C (A 10) (C (C (A 60) (C (A 0) (A 120))) (C (A 0) (A 1))))))) (C (A 0) (A 1)))))))))))))))))))

/-- The trap of `+need-ord-regs`. -/
def norTrap : Noun :=
  (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 75) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 0) (A 125)))) (C (A 0) (A 2)))))))) (C (C (A 0) (A 6)) norSw)))

/-- The gate body of `+need-ord-regs`. -/
def norBody : Noun :=
  (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 1) norTrap) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))

/-- Its sample bunt. -/
def norBunt : Noun :=
  (C (C (A 0x656e6f6e) (A 0)) (A 0))

/-- The gate body of `+hed-need-ord`. -/
def honBody : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 12)))) (C (C (A 1) (C (A 0x656e6f6e) (A 0))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 12)))) (C (C (A 1) (C (A 0x656e6f6e) (A 0))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 12)))) (C (C (A 0) (A 26)) (C (A 11) (C (C (A 0x73736f74) (C (A 3) (C (A 0) (A 12)))) (C (A 0) (A 12)))))))))))))

/-- The gate body of `+tel-need-ord`. -/
def tonBody : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 12)))) (C (C (A 1) (C (A 0x656e6f6e) (A 0))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 12)))) (C (C (A 1) (C (A 0x656e6f6e) (A 0))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 12)))) (C (C (A 0) (A 27)) (C (A 11) (C (C (A 0x73736f74) (C (A 3) (C (A 0) (A 12)))) (C (A 0) (A 13)))))))))))))

/-- `?|(?=(%this -.a) ?=(%none -.a) ?=(%this -.b) ?=(%none -.b))`. -/
def msgOr4 : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 24)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 24)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 52)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 52)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))))))))))))

/-- Both sides `%this` or `%none`. -/
def msgT1 : Noun :=
  (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 24)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 24)))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 52)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 52)))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1)))))

/-- `less` an atom and one side `%this` or `%none`. -/
def msgT2 : Noun :=
  (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 27))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 6) (C msgOr4 (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1)))))

/-- `[single double]`. -/
def msgSD : Noun :=
  (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 24)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 24)))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C (C (C (A 0) (A 12)) (C (A 0) (A 26))) (C (C (A 0) (A 26)) (C (A 0) (A 12))))))

/-- `h-double`. -/
def msgHD : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 10)))) (C (C (A 0) (A 22)) (C (A 6) (C (C (A 3) (C (A 0) (A 10))) (C (C (A 0) (A 10)) (C (A 0) (A 0))))))))

/-- `t-double`. -/
def msgTD : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 26)))) (C (C (A 0) (A 55)) (C (A 6) (C (C (A 3) (C (A 0) (A 26))) (C (C (A 0) (A 27)) (C (A 0) (A 0))))))))

/-- `l`: `(msg none+~ h-double -.less)`. -/
def msgL : Noun :=
  (C (A 8) (C (C (A 0) (A 15)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (C (A 0x656e6f6e) (A 0))))) (C (C (A 0) (A 14)) (C (A 0) (A 1014))))) (C (A 0) (A 2))))))))

/-- `r`: `(msg none+~ t-double +.less)`. -/
def msgR : Noun :=
  (C (A 8) (C (C (A 0) (A 31)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (C (A 0x656e6f6e) (A 0))))) (C (C (A 0) (A 14)) (C (A 0) (A 2039))))) (C (A 0) (A 2))))))))

/-- `res`: `[%both l r]` or `(cons-need l r)`. -/
def msgRes : Noun :=
  (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 248)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 250)))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C (C (C (A 1) (A 0x68746f62)) (C (C (A 0) (A 6)) (C (A 0) (A 2)))) (C (A 8) (C (C (A 9) (C (A 350) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 0) (A 6)) (C (A 0) (A 2)))))) (C (A 0) (A 2)))))))))))

/-- `(gth (need-ord-regs res split-max) split-max)`. -/
def msgGth : Noun :=
  (C (A 8) (C (C (A 9) (C (A 75) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 1396) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 0x5dd6) (C (A 0) (A 511)))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 0x5dd6) (C (A 0) (A 511)))))))) (C (A 0) (A 2))))))))

/-- The cap on the registers of `res`. -/
def msgFin : Noun :=
  (C (A 6) (C msgGth (C (C (A 1) (C (A 0x73696874) (A 0))) (C (A 0) (A 2)))))

/-- The case of one side `%this` or `%none` after `[single double]`. -/
def msgOneR : Noun :=
  (C (A 8) (C msgHD (C (A 8) (C msgTD (C (A 8) (C msgL (C (A 8) (C msgR (C (A 8) (C msgRes msgFin))))))))))

/-- The case of one side `%this` or `%none`, `less` a cell. -/
def msgOneN : Noun :=
  (C (A 8) (C msgSD msgOneR))

/-- Both `%both`. -/
def msgBB : Noun :=
  (C (C (A 1) (A 0x68746f62)) (C (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 114)) (C (C (A 0) (A 234)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 255)))) (C (A 9) (C (A 20) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2))))))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 115)) (C (C (A 0) (A 235)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 255)))) (C (A 9) (C (A 94) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2))))))))))))) (C (A 0) (A 2))))))))))

/-- `a` `%both`, `b` a cell. -/
def msgBP : Noun :=
  (C (C (A 1) (A 0x68746f62)) (C (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 114)) (C (C (A 0) (A 116)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 255)))) (C (A 9) (C (A 20) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2))))))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 115)) (C (C (A 0) (A 117)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 255)))) (C (A 9) (C (A 94) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2))))))))))))) (C (A 0) (A 2))))))))))

/-- `a` a cell, `b` `%both`. -/
def msgPB : Noun :=
  (C (C (A 1) (A 0x68746f62)) (C (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 56)) (C (C (A 0) (A 234)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 255)))) (C (A 9) (C (A 20) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2))))))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 57)) (C (C (A 0) (A 235)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 255)))) (C (A 9) (C (A 94) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2))))))))))))) (C (A 0) (A 2))))))))))

/-- Both cells. -/
def msgPP : Noun :=
  (C (A 8) (C (C (A 9) (C (A 350) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 56)) (C (C (A 0) (A 116)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 255)))) (C (A 9) (C (A 20) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2))))))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 57)) (C (C (A 0) (A 117)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 255)))) (C (A 9) (C (A 94) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2))))))))))))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))

/-- The case of both sides cells or `%both`. -/
def msgCells : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 24)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 52)))) (C msgBB msgBP))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 52)))) (C msgPB msgPP))))))

/-- The branches of `+msg-need-ord` after `?:  =(a b)  a`, cut. -/
def msgRestN : Noun :=
  (C (A 11) (C (C (A 0x6f6d656d) (C (A 1) (A 0))) (C (A 6) (C msgT1 (C (C (A 1) (C (A 0x73696874) (A 0))) (C (A 6) (C msgT2 (C (C (A 1) (C (A 0x73696874) (A 0))) (C (A 6) (C msgOr4 (C msgOneN msgCells)))))))))))

/-- `(msg-need-ord a b less)`. -/
def fxMsg : Noun :=
  (C (A 8) (C (C (A 9) (C (A 20) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (C (A 0) (A 58)) (C (A 0) (A 119))))) (C (A 0) (A 2))))))))

/-- `need-here`. -/
def fxHere : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 24)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 52)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 24)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 52)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))))))))))))

/-- The `+cons-need` of the two recursive calls. -/
def fxCons : Noun :=
  (C (A 8) (C (C (A 9) (C (A 350) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 374) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 60))) (C (A 0) (A 2)))))))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 374) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 122))) (C (A 0) (A 2)))))))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 374) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 246))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 511)))) (C (A 9) (C (A 20) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 247))) (C (A 0) (A 2)))))))))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 92) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 60))) (C (A 0) (A 2)))))))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 92) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 122))) (C (A 0) (A 2)))))))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 92) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 246))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 511)))) (C (A 9) (C (A 94) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 247))) (C (A 0) (A 2)))))))))))))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))

/-- The end: `%both`, `%this`, `%none` or the cell. -/
def fxEnd : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 4)))) (C (C (A 6) (C (C (A 0) (A 6)) (C (C (A 1) (C (A 0x73696874) (A 0))) (C (A 1) (C (A 0x656e6f6e) (A 0)))))) (C (A 11) (C (C (A 0x73736f74) (C (A 3) (C (A 0) (A 4)))) (C (A 6) (C (C (A 0) (A 6)) (C (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 2))) (C (A 0) (A 2))))))))))

/-- After the test on `fix`. -/
def fxRest : Noun :=
  (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 24)))) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 26)) (C (A 0) (A 54)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 0) (A 26)) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 52)))) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 12)) (C (A 0) (A 54)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 0) (A 12)) (C (A 8) (C fxHere (C (A 8) (C fxCons fxEnd))))))))))

/-- The gate body of `+msg-need-ord-fix-aware`. -/
def fxBody : Noun :=
  (C (A 11) (C (C (A 0x6f6d656d) (C (A 1) (A 0))) (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 5) (C (C (A 0) (A 12)) (C (A 0) (A 26)))) (C (C (A 0) (A 12)) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 108)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 108)))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C fxMsg fxRest))))))))))

/-- Its sample bunt. -/
def fxBunt : Noun :=
  (C (C (A 0x656e6f6e) (A 0)) (C (C (A 0x656e6f6e) (A 0)) (C (C (A 0x656e6f6e) (A 0)) (A 1))))

/-- Its `%fast` hint. -/
def fxHint : Noun :=
  (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x65726177612d7869662d64726f2d6465656e2d67736d) (C (C (A 0) (A 0x7fff)) (A 0))))) (C (A 0) (A 1))))


/-- The arm `+need-ord-regs`. -/
def norArm : Noun := C (A 8) (C (C (A 1) norBunt) (C (C (A 1) norBody) (C (A 0) (A 1))))
/-- The arm `+hed-need-ord`. -/
def honArm : Noun := C (A 8) (C (C (A 1) (C (A 0x656e6f6e) (A 0))) (C (C (A 1) honBody) (C (A 0) (A 1))))
/-- The arm `+tel-need-ord`. -/
def tonArm : Noun := C (A 8) (C (C (A 1) (C (A 0x656e6f6e) (A 0))) (C (C (A 1) tonBody) (C (A 0) (A 1))))
/-- The arm `+msg-need-ord-fix-aware`. -/
def fxArm : Noun := C (A 7) (C (C (A 8) (C (C (A 1) fxBunt) (C (C (A 1) fxBody) (C (A 0) (A 1))))) fxHint)

/-! ## The arms in the pill -/

theorem nor_at : slot? 1396 compK = some norArm := by kernel_rfl
theorem hon_at : slot? 374 compK = some honArm := by kernel_rfl
theorem ton_at : slot? 92 compK = some tonArm := by kernel_rfl
theorem fx_at : slot? 1502 compK = some fxArm := by kernel_rfl
theorem smax_at : slot? 0x5dd6 compK = some (C (A 1) (A 6)) := by kernel_rfl
theorem compK_layer1M : slot? 0x1ffff compK = some layer1 := by kernel_rfl

theorem msgRest_eq : msgRest = msgRestN := rfl

theorem nor_arm (d : Noun) : nock d norArm = some (C norBody (C norBunt d)) := by
  unfold norArm; generalize norBody = B; generalize norBunt = U; simp [nock_exec]
theorem hon_arm (d : Noun) : nock d honArm = some (C honBody (C (C (A 0x656e6f6e) (A 0)) d)) := by
  unfold honArm; generalize honBody = B; simp [nock_exec]
theorem ton_arm (d : Noun) : nock d tonArm = some (C tonBody (C (C (A 0x656e6f6e) (A 0)) d)) := by
  unfold tonArm; generalize tonBody = B; simp [nock_exec]
theorem fx_arm (d : Noun) : nock d fxArm = some (C fxBody (C fxBunt d)) := by
  unfold fxArm fxHint; generalize fxBody = B; generalize fxBunt = U; simp [nock_exec]

/-! ## `+hed-need-ord`, `+tel-need-ord` -/

/-- **`+hed-need-ord`** is `ordHed`. -/
theorem hon_gate (KC : Noun) (a : NeedOrd) : nock (C honBody (C a.toNoun KC)) honBody = some (ordHed a).toNoun := by
  conv => { lhs; arg 2; unfold honBody }
  cases a with
  | pair p q =>
    obtain ⟨u, v, e⟩ := nord_cell p
    simp [nock_exec, NeedOrd.toNoun, ordHed, e, Tag.none, Tag.this, Tag.both]
  | _ => simp [nock_exec, NeedOrd.toNoun, ordHed, Tag.none, Tag.this, Tag.both]

/-- **`+tel-need-ord`** is `ordTel`. -/
theorem ton_gate (KC : Noun) (a : NeedOrd) : nock (C tonBody (C a.toNoun KC)) tonBody = some (ordTel a).toNoun := by
  conv => { lhs; arg 2; unfold tonBody }
  cases a with
  | pair p q =>
    obtain ⟨u, v, e⟩ := nord_cell p
    simp [nock_exec, NeedOrd.toNoun, ordTel, e, Tag.none, Tag.this, Tag.both]
  | _ => simp [nock_exec, NeedOrd.toNoun, ordTel, Tag.none, Tag.this, Tag.both]

/-! ## `+need-ord-regs` -/

/-- The subject of the trap of `+need-ord-regs`: `[trap [acc gate]]`, the
gate's sample `[n max]`. -/
def norTC (acc : Nat) (n : NeedOrd) (mx : Nat) (KC : Noun) : Noun :=
  C norTrap (C (A acc) (C norBody (C (C n.toNoun (A mx)) KC)))

/-- **The trap of `+need-ord-regs`** from `acc` is `ordRegs`. -/
theorem nor_trap (KC : Noun) (hK : slot? 0x1ffff KC = some layer1) (mx : Nat) :
    ∀ (n : NeedOrd) (acc : Nat), nock (norTC acc n mx KC) norTrap = some (A (ordRegs mx n acc)) := by
  intro n
  induction n with
  | none =>
    intro acc
    have hg := gth_gate layer1 arith_layer1.2.2.2.2.1 acc mx
    rw [ordRegs.eq_def]
    unfold norTC
    conv => { lhs; arg 2; unfold norTrap norSw }
    generalize norBody = B
    by_cases h : acc > mx <;> simp [nock_exec, hK, gth.arm_at, gth_arm, hg, h, loob, NeedOrd.toNoun, Tag.none]
  | this =>
    intro acc
    have hg := gth_gate layer1 arith_layer1.2.2.2.2.1 acc mx
    rw [ordRegs.eq_def]
    unfold norTC
    conv => { lhs; arg 2; unfold norTrap norSw }
    generalize norBody = B
    by_cases h : acc > mx <;> simp [nock_exec, hK, gth.arm_at, gth_arm, hg, h, loob, NeedOrd.toNoun, Tag.none,
      Tag.this]
  | both x y ihx ihy =>
    intro acc
    have hg := gth_gate layer1 arith_layer1.2.2.2.2.1 acc mx
    have h1 := ihx (acc + 1)
    have h2 := ihy (ordRegs mx x (acc + 1))
    rw [ordRegs.eq_def]
    unfold norTC at h1 h2 ⊢
    conv => { lhs; arg 2; unfold norTrap norSw }
    rw [show norTrap = norTrap from rfl] at h1 h2
    generalize norBody = B at h1 h2 ⊢
    by_cases h : acc > mx <;> simp [nock_exec, hK, gth.arm_at, gth_arm, hg, h, loob, NeedOrd.toNoun, Tag.none,
      Tag.this, Tag.both, h1, h2]
  | pair x y ihx ihy =>
    intro acc
    have hg := gth_gate layer1 arith_layer1.2.2.2.2.1 acc mx
    have h1 := ihx acc
    have h2 := ihy (ordRegs mx x acc)
    obtain ⟨u, v, e⟩ := nord_cell x
    rw [ordRegs.eq_def]
    unfold norTC at h1 h2 ⊢
    conv => { lhs; arg 2; unfold norTrap norSw }
    generalize norBody = B at h1 h2 ⊢
    rw [e] at h1
    by_cases h : acc > mx <;> simp [nock_exec, hK, gth.arm_at, gth_arm, hg, h, loob, NeedOrd.toNoun, Tag.none,
      Tag.this, Tag.both, h1, h2, e]

/-- **`+need-ord-regs`** is `ordRegs max n 0`. -/
theorem nor_gate (KC : Noun) (hK : slot? 0x1ffff KC = some layer1) (n : NeedOrd) (mx : Nat) :
    nock (C norBody (C (C n.toNoun (A mx)) KC)) norBody = some (A (ordRegs mx n 0)) := by
  have h := nor_trap KC hK mx n 0
  unfold norTC at h
  conv => { lhs; arg 2; unfold norBody }
  generalize norTrap = T at h ⊢
  simp [nock_exec, h]

/-! ## `+msg-need-ord`: the tests -/

/-- `%this` or `%none`: a shape that is not a cell or a `%both`. -/
def ordAtm : NeedOrd → Bool
  | NeedOrd.this => true
  | NeedOrd.none => true
  | _ => false

/-- A cape that is an atom. -/
def capeAtm : Cape → Bool
  | Cape.cell _ _ => false
  | _ => true

theorem capeHed_eq (c : Cape) : capeHed c = Ca.hed c := by cases c <;> rfl
theorem capeTel_eq (c : Cape) : capeTel c = Ca.tel c := by cases c <;> rfl

/-- What `+msg-need-ord` reads in its context `K`. -/
structure MsgK (KC : Noun) : Prop where
  cn : slot? 350 KC = some cnArm
  l1 : slot? 0x1ffff KC = some layer1
  nor : slot? 1396 KC = some norArm
  smax : slot? 0x5dd6 KC = some (C (A 1) (A 6))
  lib : slot? 63 KC = some lib

theorem msgK_compK : MsgK compK := ⟨compK_cn, compK_layer1M, nor_at, smax_at, compK_lib⟩

/-- The subject of the gate body of `+msg-need-ord`. -/
def msgS (a b : NeedOrd) (less : Cape) (KC : Noun) : Noun :=
  C msgBody (C (C a.toNoun (C b.toNoun less.toNoun)) KC)

theorem msg_t1 (MB KC : Noun) (a b : NeedOrd) (less : Cape) :
    nock (C MB (C (C a.toNoun (C b.toNoun less.toNoun)) KC)) msgT1 = some (loob (ordAtm a && ordAtm b)) := by
  unfold msgT1
  cases a <;> cases b <;> simp [nock_exec, NeedOrd.toNoun, eqCode, Tag.none, Tag.this, Tag.both, ord_eqCode,
    atom_eq_nord, nord_eq_atom, loob, ordAtm]

theorem msg_or4 (MB KC : Noun) (a b : NeedOrd) (less : Cape) :
    nock (C MB (C (C a.toNoun (C b.toNoun less.toNoun)) KC)) msgOr4 = some (loob (ordAtm a || ordAtm b)) := by
  unfold msgOr4
  cases a <;> cases b <;> simp [nock_exec, NeedOrd.toNoun, eqCode, Tag.none, Tag.this, Tag.both, ord_eqCode,
    atom_eq_nord, nord_eq_atom, loob, ordAtm]

theorem msg_t2 (MB KC : Noun) (a b : NeedOrd) (less : Cape) :
    nock (C MB (C (C a.toNoun (C b.toNoun less.toNoun)) KC)) msgT2
      = some (loob (capeAtm less && (ordAtm a || ordAtm b))) := by
  have h := msg_or4 MB KC a b less
  unfold msgT2
  generalize (ordAtm a || ordAtm b) = x at h
  cases less <;> cases x <;> simp only [Cape.toNoun] at h <;> simp [nock_exec, Cape.toNoun, h, loob, capeAtm]

/-- **The tests of `+msg-need-ord`** on two different shapes. -/
theorem msg_dispatch (KC : Noun) (a b : NeedOrd) (less : Cape) (hne : a ≠ b) :
    nock (msgS a b less KC) msgBody =
      if ordAtm a && ordAtm b then some NeedOrd.this.toNoun
      else if capeAtm less && (ordAtm a || ordAtm b) then some NeedOrd.this.toNoun
      else if ordAtm a || ordAtm b then nock (msgS a b less KC) msgOneN
      else nock (msgS a b less KC) msgCells := by
  unfold msgS
  conv => { lhs; arg 2; unfold msgBody; rw [msgRest_eq]; unfold msgRestN }
  have h1 := msg_t1 msgBody KC a b less
  have h2 := msg_t2 msgBody KC a b less
  have h3 := msg_or4 msgBody KC a b less
  have hab : ¬ a.toNoun = b.toNoun := fun h => hne (nord_inj a b h)
  generalize msgBody = MB at h1 h2 h3 ⊢
  generalize msgOneN = O
  generalize msgCells = Q
  generalize (ordAtm a && ordAtm b) = x at h1 ⊢
  generalize (capeAtm less && (ordAtm a || ordAtm b)) = y at h2 ⊢
  generalize (ordAtm a || ordAtm b) = z at h3 ⊢
  cases x <;> cases y <;> cases z <;> simp [nock_exec, eqCode, hab, h1, h2, h3, loob, NeedOrd.toNoun, Tag.this]

/-- `+msg-need-ord` of two equal shapes. -/
theorem msg_self (KC : Noun) (a : NeedOrd) (less : Cape) :
    nock (msgS a a less KC) msgBody = some a.toNoun := msg_eq a.toNoun less.toNoun KC

/-! ## `+msg-need-ord`: one side `%this` or `%none` -/

/-- `[single double]`. -/
theorem msg_sd (MB KC : Noun) (a b s d : NeedOrd) (less : Cape)
    (hsd : (a = s ∧ b = d) ∨ (a = d ∧ b = s)) (hs : ordAtm s = true) (hd : ordAtm d = false) :
    nock (C MB (C (C a.toNoun (C b.toNoun less.toNoun)) KC)) msgSD = some (C s.toNoun d.toNoun) := by
  unfold msgSD
  rcases hsd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · cases a <;> cases b <;> simp_all [nock_exec, NeedOrd.toNoun, eqCode, Tag.none, Tag.this, Tag.both,
      ord_eqCode, atom_eq_nord, nord_eq_atom, loob, ordAtm]
  · cases a <;> cases b <;> simp_all [nock_exec, NeedOrd.toNoun, eqCode, Tag.none, Tag.this, Tag.both,
      ord_eqCode, atom_eq_nord, nord_eq_atom, loob, ordAtm]

/-- The simp set of the case of one side `%this` or `%none`. -/
theorem msg_one_core (MB KC : Noun) (MK : MsgK KC) (a b s d : NeedOrd) (lh lt : Cape) (X : NeedOrd)
    (hres : nock (C (msgNone (ordTel d) lt).toNoun (C (msgNone (ordHed d) lh).toNoun (C (ordTel d).toNoun
        (C (ordHed d).toNoun (C (C s.toNoun d.toNoun) (C MB (C (C a.toNoun (C b.toNoun (Cape.cell lh lt).toNoun))
        KC))))))) msgRes = some X.toNoun)
    (hrest : nock (C MB (C (C NeedOrd.none.toNoun (C (ordHed d).toNoun lh.toNoun)) KC)) MB
      = some (msgNone (ordHed d) lh).toNoun ∧
      nock (C MB (C (C NeedOrd.none.toNoun (C (ordTel d).toNoun lt.toNoun)) KC)) MB
      = some (msgNone (ordTel d) lt).toNoun)
    (hhd : nock (C (C s.toNoun d.toNoun) (C MB (C (C a.toNoun (C b.toNoun (Cape.cell lh lt).toNoun)) KC))) msgHD
      = some (ordHed d).toNoun)
    (htd : nock (C (ordHed d).toNoun (C (C s.toNoun d.toNoun) (C MB (C (C a.toNoun (C b.toNoun
      (Cape.cell lh lt).toNoun)) KC)))) msgTD = some (ordTel d).toNoun) :
    nock (C (C s.toNoun d.toNoun) (C MB (C (C a.toNoun (C b.toNoun (Cape.cell lh lt).toNoun)) KC))) msgOneR
      = some (msgCap X).toNoun := by
  have hn := nor_gate KC MK.l1 X 6
  have hg := gth_gate layer1 arith_layer1.2.2.2.2.1 (ordRegs 6 X 0) 6
  obtain ⟨hl, hr⟩ := hrest
  unfold msgOneR
  unfold msgL msgR msgFin msgGth
  generalize msgRes = RS at hres ⊢
  generalize msgHD = HD at hhd ⊢
  generalize msgTD = TD at htd ⊢
  simp only [Cape.toNoun, NeedOrd.toNoun, Tag.none] at hl hr hres hhd htd ⊢
  by_cases h6 : 6 < ordRegs 6 X 0
  · simp [nock_exec, hhd, htd, hl, hr, hres, MK.l1, MK.nor, MK.smax, nor_arm, gth.arm_at, gth_arm, hn, hg, loob,
      h6, msgCap, splitMax, NeedOrd.toNoun, Tag.this]
  · simp [nock_exec, hhd, htd, hl, hr, hres, MK.l1, MK.nor, MK.smax, nor_arm, gth.arm_at, gth_arm, hn, hg, loob,
      h6, msgCap, splitMax]

/-- A `%both`. -/
def ordIsBoth : NeedOrd → Bool
  | NeedOrd.both _ _ => true
  | _ => false

/-- `res` of the case of one side `%this` or `%none`. -/
def msgOneRes (s d l r : NeedOrd) : NeedOrd :=
  if s = NeedOrd.this || ordIsBoth d then NeedOrd.both l r else consOrd l r

theorem msgOne_cell (s d : NeedOrd) (lh lt : Cape) :
    msgOne s d (Cape.cell lh lt) = msgCap (msgOneRes s d (msgNone (ordHed d) lh) (msgNone (ordTel d) lt)) := by
  cases d <;> simp [msgOne, msgOneRes, ordIsBoth]

theorem msg_hd (L : Noun) (s d : NeedOrd) (hd : ordAtm d = false) :
    nock (C (C s.toNoun d.toNoun) L) msgHD = some (ordHed d).toNoun := by
  unfold msgHD
  cases d with
  | pair p q =>
    obtain ⟨u, v, e⟩ := nord_cell p
    simp [nock_exec, NeedOrd.toNoun, e, ordHed, eqCode, Tag.both]
  | both x y => simp [nock_exec, NeedOrd.toNoun, ordHed, eqCode, Tag.both]
  | this => simp [ordAtm] at hd
  | none => simp [ordAtm] at hd

theorem msg_td (L H : Noun) (s d : NeedOrd) (hd : ordAtm d = false) :
    nock (C H (C (C s.toNoun d.toNoun) L)) msgTD = some (ordTel d).toNoun := by
  unfold msgTD
  cases d with
  | pair p q =>
    obtain ⟨u, v, e⟩ := nord_cell p
    simp [nock_exec, NeedOrd.toNoun, e, ordTel, eqCode, Tag.both]
  | both x y => simp [nock_exec, NeedOrd.toNoun, ordTel, eqCode, Tag.both]
  | this => simp [ordAtm] at hd
  | none => simp [ordAtm] at hd

theorem msg_res (MB KC : Noun) (hcn : slot? 350 KC = some cnArm) (SAMP T H : Noun) (s d l r : NeedOrd)
    (hs : ordAtm s = true) (hd : ordAtm d = false) :
    nock (C r.toNoun (C l.toNoun (C T (C H (C (C s.toNoun d.toNoun) (C MB (C SAMP KC))))))) msgRes
      = some (msgOneRes s d l r).toNoun := by
  have hc := cn_gate_ord KC l r
  unfold msgRes
  cases s with
  | this =>
    cases d with
    | pair p q =>
      obtain ⟨u, v, e⟩ := nord_cell p
      simp [nock_exec, NeedOrd.toNoun, e, msgOneRes, ordIsBoth, eqCode, Tag.both, Tag.this]
    | both x y => simp [nock_exec, NeedOrd.toNoun, msgOneRes, ordIsBoth, eqCode, Tag.both, Tag.this]
    | this => simp [ordAtm] at hd
    | none => simp [ordAtm] at hd
  | none =>
    cases d with
    | pair p q =>
      obtain ⟨u, v, e⟩ := nord_cell p
      simp [nock_exec, NeedOrd.toNoun, e, msgOneRes, ordIsBoth, eqCode, Tag.both, Tag.this, Tag.none, hcn, cnArm, hc]
    | both x y => simp [nock_exec, NeedOrd.toNoun, msgOneRes, ordIsBoth, eqCode, Tag.both, Tag.this, Tag.none]
    | this => simp [ordAtm] at hd
    | none => simp [ordAtm] at hd
  | pair _ _ => simp [ordAtm] at hs
  | both _ _ => simp [ordAtm] at hs

/-- **The case of one side `%this` or `%none` after `[single double]`**,
given the two calls `(msg none+~ ..)`. -/
theorem msg_one_rest (MB KC : Noun) (MK : MsgK KC) (a b s d : NeedOrd) (lh lt : Cape)
    (hs : ordAtm s = true) (hd : ordAtm d = false)
    (hrest : nock (C MB (C (C NeedOrd.none.toNoun (C (ordHed d).toNoun lh.toNoun)) KC)) MB
      = some (msgNone (ordHed d) lh).toNoun ∧
      nock (C MB (C (C NeedOrd.none.toNoun (C (ordTel d).toNoun lt.toNoun)) KC)) MB
      = some (msgNone (ordTel d) lt).toNoun) :
    nock (C (C s.toNoun d.toNoun) (C MB (C (C a.toNoun (C b.toNoun (Cape.cell lh lt).toNoun)) KC))) msgOneR
      = some (msgOne s d (Cape.cell lh lt)).toNoun := by
  rw [msgOne_cell]
  exact msg_one_core MB KC MK a b s d lh lt _
    (msg_res MB KC MK.cn _ _ _ s d _ _ hs hd) hrest (msg_hd _ s d hd) (msg_td _ _ s d hd)

/-- **The case of one side `%this` or `%none`**, `less` a cell, given the
two calls `(msg none+~ ..)`. -/
theorem msg_one (KC : Noun) (MK : MsgK KC) (a b s d : NeedOrd) (lh lt : Cape)
    (hsd : (a = s ∧ b = d) ∨ (a = d ∧ b = s)) (hs : ordAtm s = true) (hd : ordAtm d = false)
    (hl : nock (msgS NeedOrd.none (ordHed d) lh KC) msgBody = some (msgNone (ordHed d) lh).toNoun)
    (hr : nock (msgS NeedOrd.none (ordTel d) lt KC) msgBody = some (msgNone (ordTel d) lt).toNoun) :
    nock (msgS a b (Cape.cell lh lt) KC) msgOneN = some (msgOne s d (Cape.cell lh lt)).toNoun := by
  unfold msgS at hl hr ⊢
  have h1 := msg_sd msgBody KC a b s d (Cape.cell lh lt) hsd hs hd
  have h2 := msg_one_rest msgBody KC MK a b s d lh lt hs hd ⟨hl, hr⟩
  unfold msgOneN
  generalize msgBody = MB at h1 h2 ⊢
  generalize msgSD = SD at h1 ⊢
  generalize msgOneR = R at h2 ⊢
  simp [nock_exec, h1, h2]

/-! ## `+msg-need-ord` with `[%none ~]` first -/

/-- **`(msg-need-ord [%none ~] d less)`** is `msgNone d less`. -/
theorem msg_none_gate (KC : Noun) (MK : MsgK KC) :
    ∀ (d : NeedOrd) (less : Cape), nock (msgS NeedOrd.none d less KC) msgBody = some (msgNone d less).toNoun := by
  intro d
  induction d with
  | none => intro less; rw [msg_self]; rfl
  | this =>
    intro less
    rw [msg_dispatch KC _ _ less (by simp)]
    simp [ordAtm, msgNone]
  | pair p q ihp ihq =>
    intro less
    rw [msg_dispatch KC _ _ less (by simp)]
    cases less with
    | yes => simp [ordAtm, capeAtm, msgNone]
    | no => simp [ordAtm, capeAtm, msgNone]
    | cell lh lt =>
      have h := msg_one KC MK NeedOrd.none (NeedOrd.pair p q) NeedOrd.none (NeedOrd.pair p q) lh lt
        (Or.inl ⟨rfl, rfl⟩) rfl rfl (ihp lh) (ihq lt)
      simp only [ordAtm, capeAtm, Bool.true_and, Bool.and_false, Bool.false_or, Bool.or_false, Bool.false_eq_true,
        if_false, Bool.true_or, if_true, h]
      simp [msgOne_cell, msgOneRes, msgNone, ordIsBoth, ordHed, ordTel]
  | both x y ihx ihy =>
    intro less
    rw [msg_dispatch KC _ _ less (by simp)]
    cases less with
    | yes => simp [ordAtm, capeAtm, msgNone]
    | no => simp [ordAtm, capeAtm, msgNone]
    | cell lh lt =>
      have h := msg_one KC MK NeedOrd.none (NeedOrd.both x y) NeedOrd.none (NeedOrd.both x y) lh lt
        (Or.inl ⟨rfl, rfl⟩) rfl rfl (ihx lh) (ihy lt)
      simp only [ordAtm, capeAtm, Bool.true_and, Bool.and_false, Bool.false_or, Bool.or_false, Bool.false_eq_true,
        if_false, Bool.true_or, if_true, h]
      simp [msgOne_cell, msgOneRes, msgNone, ordIsBoth, ordHed, ordTel]

/-! ## `+msg-need-ord`: both sides cells or `%both` -/

/-- **The case of both sides cells or `%both`**, given the two recursive
calls on the heads and the tails. -/
theorem msg_cells (MB KC : Noun) (MK : MsgK KC) (a b : NeedOrd) (less : Cape)
    (ha : ordAtm a = false) (hb : ordAtm b = false) (r1 r2 : NeedOrd)
    (h1 : nock (C MB (C (C (ordHed a).toNoun (C (ordHed b).toNoun (Ca.hed less).toNoun)) KC)) MB = some r1.toNoun)
    (h2 : nock (C MB (C (C (ordTel a).toNoun (C (ordTel b).toNoun (Ca.tel less).toNoun)) KC)) MB = some r2.toNoun) :
    nock (C MB (C (C a.toNoun (C b.toNoun less.toNoun)) KC)) msgCells
      = some (if ordIsBoth a || ordIsBoth b then NeedOrd.both r1 r2 else consOrd r1 r2).toNoun := by
  have hc := cn_gate_ord KC r1 r2
  have hlib := MK.lib
  have hcn := MK.cn
  unfold msgCells msgBB msgBP msgPB msgPP
  cases a with
  | this => simp [ordAtm] at ha
  | none => simp [ordAtm] at ha
  | pair p q =>
    obtain ⟨u, v, e⟩ := nord_cell p
    cases b with
    | this => simp [ordAtm] at hb
    | none => simp [ordAtm] at hb
    | pair p' q' =>
      obtain ⟨u', v', e'⟩ := nord_cell p'
      simp only [ordHed, ordTel, e, e'] at h1 h2
      simp [nock_exec, NeedOrd.toNoun, e, e', eqCode, Tag.both, hlib, ca.lib.arm_at, ca_lib_arm, ca.hed.arm_at,
        ca_hed_arm, ca_hed_gate, ca.tel.arm_at, ca_tel_arm, ca_tel_gate, h1, h2, hcn, cnArm, hc, ordIsBoth]
    | both x y =>
      simp only [ordHed, ordTel, e] at h1 h2
      simp [nock_exec, NeedOrd.toNoun, e, eqCode, Tag.both, hlib, ca.lib.arm_at, ca_lib_arm, ca.hed.arm_at,
        ca_hed_arm, ca_hed_gate, ca.tel.arm_at, ca_tel_arm, ca_tel_gate, h1, h2, ordIsBoth]
  | both x y =>
    cases b with
    | this => simp [ordAtm] at hb
    | none => simp [ordAtm] at hb
    | pair p' q' =>
      obtain ⟨u, v, e⟩ := nord_cell p'
      simp only [ordHed, ordTel, e] at h1 h2
      simp [nock_exec, NeedOrd.toNoun, e, eqCode, Tag.both, hlib, ca.lib.arm_at, ca_lib_arm, ca.hed.arm_at,
        ca_hed_arm, ca_hed_gate, ca.tel.arm_at, ca_tel_arm, ca_tel_gate, h1, h2, ordIsBoth]
    | both x' y' =>
      simp only [ordHed, ordTel] at h1 h2
      simp [nock_exec, NeedOrd.toNoun, eqCode, Tag.both, hlib, ca.lib.arm_at, ca_lib_arm, ca.hed.arm_at,
        ca_hed_arm, ca_hed_gate, ca.tel.arm_at, ca_tel_arm, ca_tel_gate, h1, h2, ordIsBoth]

/-! ## `+msg-need-ord` in full -/

/-- Two different shapes, both `%this` or `%none`. -/
theorem msg_gate_atm (KC : Noun) (a b : NeedOrd) (less : Cape) (hne : a ≠ b)
    (ha : ordAtm a = true) (hb : ordAtm b = true) :
    nock (msgS a b less KC) msgBody = some (msgOrd a b less).toNoun := by
  rw [msg_dispatch KC a b less hne, ha, hb, msgOrd.eq_def, if_neg hne]
  cases a <;> cases b <;> simp_all [ordAtm]

/-- One side `%this` or `%none`, the other a cell or a `%both`. -/
theorem msg_gate_one (KC : Noun) (MK : MsgK KC) (a b s d : NeedOrd) (less : Cape) (hne : a ≠ b)
    (hsd : (a = s ∧ b = d) ∨ (a = d ∧ b = s)) (hs : ordAtm s = true) (hd : ordAtm d = false) :
    nock (msgS a b less KC) msgBody = some (msgOne s d less).toNoun := by
  have hand : (ordAtm a && ordAtm b) = false := by
    rcases hsd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hs, hd]
  have hor : (ordAtm a || ordAtm b) = true := by
    rcases hsd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hs, hd]
  rw [msg_dispatch KC a b less hne, hand, hor]
  cases less with
  | yes => simp [capeAtm, msgOne]
  | no => simp [capeAtm, msgOne]
  | cell lh lt =>
    simp only [capeAtm, Bool.false_and, Bool.false_eq_true, if_false, if_true]
    exact msg_one KC MK a b s d lh lt hsd hs hd (msg_none_gate KC MK _ _) (msg_none_gate KC MK _ _)

/-- Both sides cells or `%both`, given the two recursive calls. -/
theorem msg_gate_cells (KC : Noun) (MK : MsgK KC) (a b : NeedOrd) (less : Cape) (hne : a ≠ b)
    (ha : ordAtm a = false) (hb : ordAtm b = false)
    (h1 : nock (msgS (ordHed a) (ordHed b) (capeHed less) KC) msgBody
      = some (msgOrd (ordHed a) (ordHed b) (capeHed less)).toNoun)
    (h2 : nock (msgS (ordTel a) (ordTel b) (capeTel less) KC) msgBody
      = some (msgOrd (ordTel a) (ordTel b) (capeTel less)).toNoun) :
    nock (msgS a b less KC) msgBody = some (msgOrd a b less).toNoun := by
  rw [msg_dispatch KC a b less hne, ha, hb]
  rw [capeHed_eq] at h1
  rw [capeTel_eq] at h2
  unfold msgS at h1 h2 ⊢
  have h := msg_cells msgBody KC MK a b less ha hb _ _ h1 h2
  simp only [Bool.false_and, Bool.and_false, Bool.false_or, Bool.false_eq_true, if_false]
  rw [h, msgOrd.eq_def a b less, if_neg hne]
  clear h h1 h2
  cases a <;> cases b <;> simp [ordAtm, ordIsBoth, ordHed, ordTel, capeHed_eq, capeTel_eq] at ha hb ⊢

/-- **`+msg-need-ord`** is `msgOrd`: the gate body on `[[a b less] K]` is
`msgOrd a b less` for every `a`, `b`, `less`, given the arms it reads in
`K`.  By induction on `a`: the recursive calls on the heads and tails from
the induction hypothesis, those of the one-sided case from
`msg_none_gate`. -/
theorem msg_gate (KC : Noun) (MK : MsgK KC) :
    ∀ (a b : NeedOrd) (less : Cape), nock (msgS a b less KC) msgBody = some (msgOrd a b less).toNoun := by
  intro a
  induction a with
  | this =>
    intro b less
    by_cases e : NeedOrd.this = b
    · subst e; rw [msg_self, msgOrd.eq_def, if_pos rfl]
    cases b with
    | this => exact absurd rfl e
    | none => exact msg_gate_atm KC _ _ less e rfl rfl
    | pair p q =>
      rw [msg_gate_one KC MK _ _ _ _ less e (Or.inl ⟨rfl, rfl⟩) rfl rfl, msgOrd.eq_def, if_neg e]
    | both x y =>
      rw [msg_gate_one KC MK _ _ _ _ less e (Or.inl ⟨rfl, rfl⟩) rfl rfl, msgOrd.eq_def, if_neg e]
  | none =>
    intro b less
    by_cases e : NeedOrd.none = b
    · subst e; rw [msg_self, msgOrd.eq_def, if_pos rfl]
    cases b with
    | none => exact absurd rfl e
    | this => exact msg_gate_atm KC _ _ less e rfl rfl
    | pair p q =>
      rw [msg_gate_one KC MK _ _ _ _ less e (Or.inl ⟨rfl, rfl⟩) rfl rfl, msgOrd.eq_def, if_neg e]
    | both x y =>
      rw [msg_gate_one KC MK _ _ _ _ less e (Or.inl ⟨rfl, rfl⟩) rfl rfl, msgOrd.eq_def, if_neg e]
  | pair p q ihp ihq =>
    intro b less
    by_cases e : NeedOrd.pair p q = b
    · subst e; rw [msg_self, msgOrd.eq_def, if_pos rfl]
    cases b with
    | this =>
      rw [msg_gate_one KC MK _ _ NeedOrd.this _ less e (Or.inr ⟨rfl, rfl⟩) rfl rfl, msgOrd.eq_def, if_neg e]
    | none =>
      rw [msg_gate_one KC MK _ _ NeedOrd.none _ less e (Or.inr ⟨rfl, rfl⟩) rfl rfl, msgOrd.eq_def, if_neg e]
    | pair p' q' => exact msg_gate_cells KC MK _ _ less e rfl rfl (ihp _ _) (ihq _ _)
    | both x y => exact msg_gate_cells KC MK _ _ less e rfl rfl (ihp _ _) (ihq _ _)
  | both x y ihx ihy =>
    intro b less
    by_cases e : NeedOrd.both x y = b
    · subst e; rw [msg_self, msgOrd.eq_def, if_pos rfl]
    cases b with
    | this =>
      rw [msg_gate_one KC MK _ _ NeedOrd.this _ less e (Or.inr ⟨rfl, rfl⟩) rfl rfl, msgOrd.eq_def, if_neg e]
    | none =>
      rw [msg_gate_one KC MK _ _ NeedOrd.none _ less e (Or.inr ⟨rfl, rfl⟩) rfl rfl, msgOrd.eq_def, if_neg e]
    | pair p' q' => exact msg_gate_cells KC MK _ _ less e rfl rfl (ihx _ _) (ihy _ _)
    | both x' y' => exact msg_gate_cells KC MK _ _ less e rfl rfl (ihx _ _) (ihy _ _)

/-- `+msg-need-ord` of `K` itself. -/
theorem msg_gate_K (a b : NeedOrd) (less : Cape) :
    nock (msgS a b less compK) msgBody = some (msgOrd a b less).toNoun := msg_gate compK msgK_compK a b less

end Compiler
end Formalization
