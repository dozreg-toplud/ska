import lemmas.Compiler.CompSureOf
import lemmas.Hoon.RollUni

/-!
# `+shape-collapse` on a fork-free lazy need

```hoon
++  shape-collapse
  |=  [laz=need-lazy less=cape]
  ^-  need-ordered
  (inter2-collapse (inter1-to-inter2 (lazy-to-inter1 laz) less) less)
```

`+shape-collapse` (arm `682` of `K`, `sc_at`, its body `scBody`) is the
`ord` of `finishLF`: `+collapse-shape` allocates the registers of its product
(`cs_gate` of `CompSccIn.lean` takes it as the hypothesis `hsc`).  The model
has no function for it, but on a fork-free lazy need `[[ned lok] ~ ~]` it is
`+sure-of` of `[(need-to-ordered ned) lok]`, which is `sureOf`:

1. `+lazy-to-inter1` (arm `6006`) on no fork and no bond is `[[(need-to-ordered
   ned) lok] ~]` (`l2i_gate_sure`, with `nta_gate`);
2. `+inter1-to-inter2` (`i2_gate` of `CompSureOf.lean`) gives `[X ~]` with
   `X` the noun of `sureOf (needToOrd ned) lok less`;
3. `+inter2-collapse` (arm `1406`) runs its fixed point: one round of
   `+inter2-fix-round` (arm `0x15d7bf`) on `[X ~]` is `[(uni-need-ord [%none ~]
   X) ~]`, which is `[X ~]` (`uno_none`, the first two branches of
   `+uni-need-ord`, arm `2794`), the `+turn` and the `+roll` over no fork
   doing nothing (`fr_gate_nofork`), so the loop stops at once; then
   `+inter2-orig` (arm `1367`) with no fork returns `sure.intr`, `X`
   (`oi_gate_nofork`, `ic_gate_nofork`);
4. the `!@  collapse-check` of `+inter2-collapse` takes its first expression,
   the wing being commented out (line 2822).

So `+shape-collapse` on `[[ned lok] ~ ~]` and `less` is `sureOf (needToOrd
ned) lok less` (`sc_gate_sure`), the shape that `+sure-of` gives the
member's `sur` too, and `hsc` of `mem_gate` holds with `ord := sur`
(`hsc_of_sure`).  The nouns are cut by `tools/gen/shapecol.py`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The nouns -/

/-- The branches of `+uni-need-ord` after `?:  ?=(%none -.a)  b`. -/
def unoRest : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 26)))) (C (C (A 0) (A 12)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 24)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 26)))) (C (C (A 0) (A 13)) (C (A 6) (C (C (A 3) (C (A 0) (A 26))) (C (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 13))) (C (A 0) (A 0)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 26)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 24)))) (C (C (A 0) (A 12)) (C (A 11) (C (C (A 0x73736f74) (C (A 3) (C (A 0) (A 24)))) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 12)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 24))) (C (C (A 6) (C (C (A 3) (C (A 0) (A 26))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 11) (C (C (A 0x6f6d656d) (C (A 1) (A 0))) (C (A 8) (C (C (A 9) (C (A 350) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 24)) (C (A 0) (A 26)))) (C (A 0) (A 1)))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 25)) (C (A 0) (A 27)))) (C (A 0) (A 1)))))))))) (C (A 0) (A 2)))))))))) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 24)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 26)))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C (C (A 8) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 24)))) (C (C (A 7) (C (C (A 0) (A 12)) (C (C (A 0) (A 6)) (C (A 0) (A 7))))) (C (A 11) (C (C (A 0x73736f74) (C (A 3) (C (A 0) (A 24)))) (C (A 0) (A 12))))))) (C (A 8) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 58)))) (C (C (A 7) (C (C (A 0) (A 29)) (C (C (A 0) (A 6)) (C (A 0) (A 7))))) (C (A 11) (C (C (A 0x73736f74) (C (A 3) (C (A 0) (A 58)))) (C (A 0) (A 29))))))) (C (A 8) (C (C (A 11) (C (C (A 0x6f6d656d) (C (A 1) (A 0))) (C (A 8) (C (C (A 9) (C (A 350) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 12)) (C (A 0) (A 4)))) (C (A 0) (A 7)))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 13)) (C (A 0) (A 5)))) (C (A 0) (A 7)))))))))) (C (A 0) (A 2)))))))))) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 4)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 4)))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C (C (A 1) (C (A 0x73696874) (A 0))) (C (C (A 1) (A 0x68746f62)) (C (A 6) (C (C (A 3) (C (A 0) (A 4))) (C (C (A 0) (A 2)) (C (A 7) (C (C (A 0) (A 2)) (C (C (A 0) (A 6)) (C (A 0) (A 7)))))))))))))))))) (C (A 0) (A 0)))))))))))))))))

/-- The gate body of `+uni-need-ord`. -/
def unoBody : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 0) (A 12)) (C (A 0) (A 13)))) (C (C (A 0) (A 12)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 24)))) (C (C (A 0) (A 13)) unoRest))))))

/-- Its sample bunt. -/
def unoBunt : Noun :=
  (C (C (A 0x656e6f6e) (A 0)) (C (A 0x656e6f6e) (A 0)))

/-- Its `%fast` hint. -/
def unoHint : Noun :=
  (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x64726f2d6465656e2d696e75) (C (C (A 0) (A 0x7fff)) (A 0))))) (C (A 0) (A 1))))

/-- `[[(need-to-ordered ned.sure.laz) lok.sure.laz] ~]`. -/
def l2iYes : Noun :=
  (C (C (C (A 8) (C (C (A 9) (C (A 0xaebc) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 56))) (C (A 0) (A 2)))))))) (C (A 0) (A 25))) (C (A 1) (A 0)))

/-- The `+roll` over the bonds, with forks or bonds. -/
def l2iNo : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 59)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0xaebc) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 56))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x7ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 122)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))))) (C (C (A 1) (C (C (A 8) (C (C (A 0) (A 15)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 57))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 15)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2)))))))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (C (A 0) (A 6)) (C (A 0) (A 121))) (C (A 8) (C (C (C (C (A 1) (A 0)) (C (A 7) (C (C (A 9) (C (A 191) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))) (C (C (A 0) (A 2)) (C (A 0) (A 6)))) (C (C (A 1) (C (A 8) (C (C (A 8) (C (C (A 0) (A 63)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 57))) (C (A 0) (A 2)))))))) (C (C (C (A 8) (C (C (A 9) (C (A 2794) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 24)) (C (A 0) (A 244)))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 174) (C (A 10) (C (C (A 6) (C (A 0) (A 245))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 25))) (C (A 0) (A 2))))))))) (C (A 8) (C (C (A 9) (C (A 0xbef7f4) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 13)) (C (A 0) (A 123)))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 1))))))))))))))) (C (A 0) (A 2))))))))

/-- The gate body of `+lazy-to-inter1`. -/
def l2iBody : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 26)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 27)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C l2iYes l2iNo)))))

/-- Its sample bunt. -/
def l2iBunt : Noun :=
  (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))

/-- Its `%fast` hint. -/
def l2iHint : Noun :=
  (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x317265746e692d6f742d797a616c) (C (C (A 0) (A 0x7fff)) (A 0))))) (C (A 0) (A 1))))

/-- The bunt of `need-inter2`, from the mold at arm `0x575f` of `K` (axis `63`). -/
def frBuntF : Noun :=
  (C (A 7) (C (C (A 9) (C (A 0x575f) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))

/-- The gate of the `+roll` over `kids`. -/
def frGate : Noun :=
  (C (A 8) (C (C (A 9) (C (A 2794) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 29)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 20) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 112)) (C (C (A 0) (A 114)) (C (A 0) (A 1021))))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))

/-- Its sample bunt: two bunts of `need-inter2` and `parent`. -/
def frRBunt : Noun :=
  (C (C frBuntF frBuntF) (C (A 0) (A 14)))

/-- `=.  parent  (uni-need-ord parent sure.prev)`. -/
def frUni : Noun :=
  (C (A 10) (C (C (A 6) (C (A 8) (C (C (A 9) (C (A 2794) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 0) (A 248)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1))))

/-- `kids`: the `+turn` over `fork.prev`. -/
def frTurn : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 249)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (C (A 0x656e6f6e) (A 0)) (A 0)))) (C (C (A 1) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 60) (C (A 0) (A 12))) (C (A 0) (A 7)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 60) (C (A 0) (A 13))) (C (A 0) (A 7)))))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))

/-- The `+roll` over `kids` from `parent`. -/
def frRoll : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C frRBunt (C (C (A 1) frGate) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))

/-- The trap `round` of `+inter2-fix-round`. -/
def frTrap : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 7) (C frUni (C (A 8) (C frTurn (C frRoll (C (A 0) (A 2)))))))))

/-- The gate body of `+inter2-fix-round`. -/
def frBody : Noun :=
  (C (A 8) (C (C (A 1) (C (A 0x656e6f6e) (A 0))) (C (A 8) (C (C (A 1) frTrap) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))

/-- Its sample bunt. -/
def frBunt : Noun :=
  (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (A 1))

/-- Its `%fast` hint. -/
def frHint : Noun :=
  (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x646e756f722d7869662d327265746e69) (C (C (A 0) (A 0x7fff)) (A 0))))) (C (A 0) (A 1))))

/-- The step of the loop of `+inter2-orig` on a fork. -/
def oiFork : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 0) (A 31)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 120)) (C (C (A 0) (A 56)) (C (A 0) (A 1019))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 0) (A 63)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 249)) (C (C (A 0) (A 121)) (C (A 0) (A 2043))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 1502) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (C (A 0) (A 6)) (C (C (A 0) (A 8180)) (C (A 0) (A 4091)))))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 8) (C (C (A 9) (C (A 2794) (C (A 0) (A 1023)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 510)) (C (A 0) (A 6)))) (C (A 0) (A 2))))))))) (C (A 10) (C (C (A 14) (C (A 0) (A 253))) (C (A 10) (C (C (A 6) (C (A 0) (A 125))) (C (A 0) (A 15))))))))))))))))

/-- The loop of `+inter2-orig` over `forks` and `fixes`. -/
def oiTrap : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 14)))) (C (C (A 0) (A 30)) (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C oiFork (C (A 0) (A 0))))))))

/-- The gate body of `+inter2-orig`. -/
def oiBody : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 0) (A 24)) (C (A 8) (C (C (A 0) (A 57)) (C (A 8) (C (C (A 0) (A 245)) (C (A 8) (C (C (A 1) oiTrap) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))))))))

/-- Its sample bunt. -/
def oiBunt : Noun :=
  (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) frBunt)

/-- Its `%fast` hint. -/
def oiHint : Noun :=
  (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x6769726f2d327265746e69) (C (C (A 0) (A 0x7fff)) (A 0))))) (C (A 0) (A 1))))

/-- The fixed point loop of `+inter2-collapse`. -/
def icTrap : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0x15d7bf) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 0) (A 125)))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 0) (A 2)) (C (A 0) (A 14)))) (C (C (A 0) (A 2)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 2))) (C (A 0) (A 3)))))))))))

/-- The gate body of `+inter2-collapse`. -/
def icBody : Noun :=
  (C (A 8) (C (C (A 0) (A 12)) (C (A 7) (C (C (A 10) (C (C (A 2) (C (A 8) (C (C (A 1) icTrap) (C (A 9) (C (A 2) (C (A 0) (A 1))))))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 1367) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 60)) (C (C (A 0) (A 6)) (C (A 0) (A 61))))) (C (A 0) (A 2)))))))) (C (A 0) (A 2))))))))

/-- Its sample bunt. -/
def icBunt : Noun :=
  frBunt

/-- Its `%fast` hint. -/
def icHint : Noun :=
  (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x657370616c6c6f632d327265746e69) (C (C (A 0) (A 0x7fff)) (A 0))))) (C (A 0) (A 1))))

/-- The gate body of `+shape-collapse`. -/
def scBodyN : Noun :=
  (C (A 8) (C (C (A 9) (C (A 1406) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbbbb) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 6006) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))))) (C (A 0) (A 29)))) (C (A 0) (A 2)))))))))) (C (A 0) (A 29)))) (C (A 0) (A 2))))))))

/-! ## The arms in the pill -/

def unoArm : Noun := C (A 7) (C (C (A 8) (C (C (A 1) unoBunt) (C (C (A 1) unoBody) (C (A 0) (A 1))))) unoHint)
def l2iArm : Noun := C (A 7) (C (C (A 8) (C (C (A 1) l2iBunt) (C (C (A 1) l2iBody) (C (A 0) (A 1))))) l2iHint)
def frArm : Noun := C (A 7) (C (C (A 8) (C (C (A 1) frBunt) (C (C (A 1) frBody) (C (A 0) (A 1))))) frHint)
def oiArm : Noun := C (A 7) (C (C (A 8) (C (C (A 1) oiBunt) (C (C (A 1) oiBody) (C (A 0) (A 1))))) oiHint)
def icArm : Noun := C (A 7) (C (C (A 8) (C (C (A 1) icBunt) (C (C (A 1) icBody) (C (A 0) (A 1))))) icHint)

/-- `+uni-need-ord` is arm `2794` of `K`. -/
theorem uno_at : slot? 2794 compK = some unoArm := by kernel_rfl
/-- `+lazy-to-inter1` is arm `6006` of `K`. -/
theorem l2i_at : slot? 6006 compK = some l2iArm := by kernel_rfl
/-- `+inter2-fix-round` is arm `0x15d7bf` of `K`. -/
theorem fr_at : slot? 0x15d7bf compK = some frArm := by kernel_rfl
/-- `+inter2-orig` is arm `1367` of `K`. -/
theorem oi_at : slot? 1367 compK = some oiArm := by kernel_rfl
/-- `+inter2-collapse` is arm `1406` of `K`. -/
theorem ic_at : slot? 1406 compK = some icArm := by kernel_rfl

/-- The slot `scBody` of `CompSccIn.lean` is `scBodyN`. -/
theorem scBody_eq : scBody = scBodyN := by
  have h1 := sc_at
  have h2 : slot? 682 compK = some (C (A 7) (C (C (A 8) (C (C (A 1) (C (C (C (C (A 0x656e6f6e) (A 0)) (A 0))
      (C (A 0) (A 0))) (A 1))) (C (C (A 1) scBodyN) (C (A 0) (A 1))))) (C (A 11) (C (C (A 0x74736166) (C (A 1)
      (C (A 0x657370616c6c6f632d6570616873) (C (C (A 0) (A 0x7fff)) (A 0))))) (C (A 0) (A 1)))))) := by
    kernel_rfl
  rw [h2] at h1
  simp only [Option.some.injEq, Noun.cell.injEq, true_and, and_true] at h1
  exact h1.symm

theorem uno_arm (d : Noun) : nock d unoArm = some (C unoBody (C unoBunt d)) := by
  unfold unoArm unoHint; generalize unoBody = B; generalize unoBunt = U; simp [nock_exec]
theorem l2i_arm (d : Noun) : nock d l2iArm = some (C l2iBody (C l2iBunt d)) := by
  unfold l2iArm l2iHint; generalize l2iBody = B; generalize l2iBunt = U; simp [nock_exec]
theorem fr_arm (d : Noun) : nock d frArm = some (C frBody (C frBunt d)) := by
  unfold frArm frHint; generalize frBody = B; generalize frBunt = U; simp [nock_exec]
theorem oi_arm (d : Noun) : nock d oiArm = some (C oiBody (C oiBunt d)) := by
  unfold oiArm oiHint; generalize oiBody = B; generalize oiBunt = U; simp [nock_exec]
theorem ic_arm (d : Noun) : nock d icArm = some (C icBody (C icBunt d)) := by
  unfold icArm icHint; generalize icBody = B; generalize icBunt = U; simp [nock_exec]

/-! ## The bunt of `need-inter2` -/

/-- The bunt of `need-inter2` computed from `K`: the mold at arm `0x575f`
slammed on its own sample. -/
def i2nBuntF : Noun := C (A 7) (C (C (A 9) (C (A 0x575f) (C (A 0) (A 1)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))

noncomputable def i2nBunt : Noun := (evalFuel 2000 compK i2nBuntF).getD (A 0)

theorem i2n_bunt : nock compK i2nBuntF = some i2nBunt := nock_of_evalFuel (fuel := 2000) (by kernel_rfl)

/-- `frBuntF` on a subject whose axis `63` is `K`. -/
theorem fr_bunt_at (S : Noun) (h : slot? 63 S = some compK) : nock S frBuntF = some i2nBunt := by
  have hb := i2n_bunt
  unfold i2nBuntF at hb
  unfold frBuntF
  simp only [nock_op7, nock_op9, nock_op0, h, slot?_one, Option.bind_some] at hb ⊢
  exact hb

/-- The two bunts of the sample of the gate of the `+roll`. -/
theorem fr_bunt2_at (S : Noun) (h : slot? 63 S = some compK) :
    nock S (C frBuntF frBuntF) = some (C i2nBunt i2nBunt) := by
  rw [nock_pair S frBuntF frBuntF ⟨_, _, rfl⟩, fr_bunt_at S h]
  rfl

/-! ## `+uni-need-ord` with `[%none ~]` first -/

/-- **`+uni-need-ord` of `[%none ~]` and `X`** is `X`: by its first branch
when `X` is `[%none ~]`, by its second otherwise. -/
theorem uno_none (K : Noun) (X : NeedOrd) :
    nock (C unoBody (C (C NeedOrd.none.toNoun X.toNoun) K)) unoBody = some X.toNoun := by
  conv => { lhs; arg 2; unfold unoBody }
  generalize unoRest = R
  cases X with
  | none => simp [nock_exec, NeedOrd.toNoun, eqCode_self]
  | this => simp [nock_exec, NeedOrd.toNoun, eqCode, Tag.none, Tag.this]
  | both h t => simp [nock_exec, NeedOrd.toNoun, eqCode, Tag.none, Tag.both]
  | pair p q =>
    obtain ⟨a, b, hp⟩ := nord_cell p
    simp [nock_exec, NeedOrd.toNoun, eqCode, Tag.none, hp]

/-! ## `+lazy-to-inter1` on no fork and no bond -/

/-- **`+lazy-to-inter1` on `[[ned lok] ~ ~]`** is `[[(need-to-ordered ned)
lok] ~]`. -/
theorem l2i_gate_sure (NED : Need) (LOK : Noun) :
    nock (C l2iBody (C (C (C NED.toNoun LOK) (C (A 0) (A 0))) compK)) l2iBody
      = some (C (C (needToOrd NED).toNoun LOK) (A 0)) := by
  have hn := nta_gate compK NED
  have hna := nta_at
  conv => { lhs; arg 2; unfold l2iBody }
  generalize l2iNo = NO
  generalize compK = KC at hn hna
  simp [nock_exec, l2iYes, hna, ntaHint, hn]

/-! ## `+inter2-fix-round` on no fork -/

/-- `+roll` over `~` is its first accumulator. -/
theorem roll_gate_nil (c bp e acc bc : Noun) :
    nock (C roll.battery (C (C (A 0) (C bp (C (C e acc) bc))) c)) roll.battery = some acc := by
  have h := roll_gate_M c bp e acc bc (fun _ _ => Option.none) [] (by intro x hx; cases hx)
  simpa [listN] using h

/-- **One round of `+inter2-fix-round` on `[X ~]`** is `[X ~]`: `parent`
becomes `(uni-need-ord [%none ~] X)`, which is `X`, and the `+turn` and the
`+roll` over no fork leave it. -/
theorem fr_gate_nofork (X : NeedOrd) (LESS : Noun) :
    nock (C frBody (C (C (C X.toNoun (A 0)) LESS) compK)) frBody = some (C X.toNoun (A 0)) := by
  have hL := compK_layer2
  have hua := uno_at
  have hu := uno_none compK X
  have hb := fr_bunt2_at
  have hr := roll_gate_nil layer2
  have ht := fin_turn_nil
  conv => { lhs; arg 2; unfold frBody }
  rw [show NeedOrd.none.toNoun = C (A 0x656e6f6e) (A 0) from rfl] at hu
  generalize compK = KC at hL hua hu hb ⊢
  simp [nock_exec, frTrap, frUni, frTurn, frRoll, frRBunt, hL, hua, uno_arm, hu, turn.arm_at, turn_arm, ht,
    roll.arm_at, roll_arm, hr, hb, NeedOrd.toNoun]

/-! ## `+inter2-orig` on no fork -/

/-- **`+inter2-orig` on an `intr` with no fork** returns `sure.intr`. -/
theorem oi_gate_nofork (X F1 F2 LESS : Noun) :
    nock (C oiBody (C (C (C X (A 0)) (C (C F1 F2) LESS)) compK)) oiBody = some X := by
  conv => { lhs; arg 2; unfold oiBody }
  generalize compK = KC
  simp [nock_exec, oiTrap]

/-! ## `+inter2-collapse` on no fork -/

/-- **`+inter2-collapse` on `[X ~]`** is `X`: the fixed point loop stops after
one round, and `+inter2-orig` returns the sure shape. -/
theorem ic_gate_nofork (X : NeedOrd) (LESS : Noun) :
    nock (C icBody (C (C (C X.toNoun (A 0)) LESS) compK)) icBody = some X.toNoun := by
  have hfa := fr_at
  have hf := fr_gate_nofork X LESS
  have hoa := oi_at
  have ho := oi_gate_nofork X.toNoun X.toNoun (A 0) LESS
  conv => { lhs; arg 2; unfold icBody }
  generalize compK = KC at hfa hf hoa ho ⊢
  simp [nock_exec, icTrap, hfa, fr_arm, hf, hoa, oi_arm, ho, eqCode_self]

/-! ## `+shape-collapse` on a fork-free lazy need -/

/-- **`+shape-collapse` on `[[ned lok] ~ ~]` and `less`** is `sureOf
(needToOrd ned) lok less`, the shape `+sure-of` gives; it crashes exactly
when that is `none` (an axis `0` in `lok`). -/
theorem sc_gate_sure (NED : Need) (lok : CSet) (less : Cape) :
    nock (C scBody (C (C (C (C NED.toNoun (HoonSet.toNoun lok)) (C (A 0) (A 0))) less.toNoun) compK)) scBody
      = (sureOf (needToOrd NED) lok less).map NeedOrd.toNoun := by
  have hla := l2i_at
  have hl := l2i_gate_sure NED (HoonSet.toNoun lok)
  have hia := i2_at
  have hi := i2_gate (needToOrd NED) lok less
  have hca := ic_at
  rw [scBody_eq]
  conv => { lhs; arg 2; unfold scBodyN }
  cases e : sureOf (needToOrd NED) lok less with
  | none =>
    rw [e] at hi
    generalize compK = KC at hla hl hia hi hca ⊢
    simp [nock_exec, hla, l2i_arm, hl, hia, i2_arm, hi]
  | some r =>
    rw [e] at hi
    have hc := ic_gate_nofork r less.toNoun
    simp only [Option.map_some] at hi ⊢
    generalize compK = KC at hla hl hia hi hca hc ⊢
    simp [nock_exec, hla, l2i_arm, hl, hia, i2_arm, hi, hca, ic_arm, hc]

/-- **`hsc` of `mem_gate` from the model**: on a run whose `laz` is
fork-free with sure part `s`, `+shape-collapse` returns the shape `sur` that
`+sure-of` gives. -/
theorem hsc_of_sure (nex : NextL CSet) (s : Sure CSet) (hlaz : nex.laz = Lazy.ofSure s) (cape : Cape)
    (sur : NeedOrd) (hsur : sureOf (needToOrd s.ned) s.lok cape = some sur) :
    nock (C scBody (C (C nex.laz.toNoun cape.toNoun) compK)) scBody = some sur.toNoun := by
  have h := sc_gate_sure s.ned s.lok cape
  rw [hsur, Option.map_some] at h
  rw [hlaz, Lazy.toNoun_ofSure]
  exact h

end Compiler
end Formalization
