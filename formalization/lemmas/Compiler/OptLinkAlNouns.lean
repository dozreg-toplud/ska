import lemmas.Compiler.OptLinkSwGate
import lemmas.Ska.OptAliasModel

/-!
# `+alias`: the nouns and the subjects

The arm is `725` of `optC` (`al_at_cut`, nouns by `tools/gen/optlink.py
alias`).  Its body (`alBodyCut`, equal to `aliasBody` of `OptLinkOnce.lean`:
`aliasBody_eq`) pushes the bunt of `gen` (`alGenBunt`, eight fields, `folded`
`|`), sets `rev.gen` (axis `382`) to `alRevInit`, the `+run:by` of `(bake silt
(list @uwoo))` over `rev`, and runs the arm `$` (`alWalk`, axis `95`) of the
`|^` core whose battery is `alBat`: `join-reg` (battery axis `2`, `alJRegB`),
`rn` (`6`, `alRnB`), `join-info` (`14`, `alJInfoB`), `join-imms` (`30`,
`alJImmsB`), `param-info` (`62`, `alPInfoB`) and `$` (`63`).

The walk is cut at each `=/` and `=^` of the Hoon: `alPre`, the unreachable
block (`alUnT`, `alUnB` with its `+roll` `alUnRoll`), the facts at the start
(`alInfo`: `alEntry`, or `alJoin` with the `+roll` of `join-info` `alJnRoll`
and the refinement `alJnRef`, its cases `alJnBrn`, `alJnBrz`, `alJnClq`),
`alImms`, `alBob`, the parameters (`alPars`: `alEdges` and the trap
`alParT`), the body (`alBody`, the gate `alBodyG` of its `+roll`, one noun per
case of the `?-` over the op, `alOpImm` to `alOpLast` = `%csm`), the end
(`alFin`, one noun per case, `alFinClq` to `alFinLast` = `%bom`) and the
stores with the next turn (`alTail`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The nouns -/

/-- The case `%imm` of the body. -/
def alOpImm : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 760) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 46) (C (A 10) (C (C (A 6) (C (A 0) (A 0x1ffbe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 114))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 8) (C (C (A 0) (A 115)) (C (A 8) (C (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))) (C (A 7) (C (C (A 10) (C (C (A 0x3ffde) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7ffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 10) (C (C (A 255) (C (C (A 1) (A 0)) (C (A 0) (A 498)))) (C (A 0) (A 2)))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 0x7ffbe) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 760) (C (A 0) (A 0x7fffffff)))) (C (A 9) (C (A 4) (C (A 10) (C (C (A 6) (C (A 0) (A 0xfffbe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1010)) (C (A 0) (A 14)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (C (C (C (A 1) (A 0x6d6d69)) (C (C (A 0) (A 498)) (C (A 0) (A 6)))) (C (A 0) (A 250))) (C (A 0) (A 8190))))))))))) (C (A 7) (C (C (A 10) (C (C (A 8186) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0x3ffa))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 243)) (C (A 0) (A 12)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (C (A 0) (A 58)) (C (A 0) (A 2046))))))))))

/-- The case `%mov` of the body. -/
def alOpMov : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 4090) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 8186))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 115)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 10) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 114))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (C (A 0) (A 26)) (C (A 0) (A 1022)))))

/-- The case `%inc` of the body. -/
def alOpInc : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 10) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 114))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 0x1ffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 382))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 8) (C (C (A 0) (A 243)) (C (A 7) (C (C (A 10) (C (C (A 0x3ffde) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7ffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 0x3ffde) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffffff)))) (C (A 9) (C (A 379) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7ffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 30)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))) (C (C (A 1) (C (A 10) (C (C (A 254) (C (C (A 1) (A 0)) (C (A 0) (A 14)))) (C (A 0) (A 6))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (C (C (C (A 1) (A 0x636e69)) (C (C (A 0) (A 14)) (C (A 0) (A 2)))) (C (A 0) (A 250))) (C (A 0) (A 8190))))))))) (C (A 7) (C (C (A 10) (C (C (A 0x3ffa) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7ffa))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 499)) (C (A 0) (A 1789)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (C (A 0) (A 122)) (C (A 0) (A 4094))))))))))))

/-- The case `%con` of the body. -/
def alOpCon : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 10) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 114))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 10) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 486))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 0x3ffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7ffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0xffffffff)))) (C (A 9) (C (A 85) (C (A 10) (C (C (A 6) (C (A 0) (A 118))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 110))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 8) (C (C (A 0) (A 4071)) (C (A 8) (C (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))) (C (A 7) (C (C (A 10) (C (C (A 0x3fffde) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7fffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 10) (C (C (A 126) (C (C (A 1) (A 0)) (C (A 0) (A 126)))) (C (A 10) (C (C (A 62) (C (C (A 1) (A 0)) (C (A 0) (A 254)))) (C (A 10) (C (C (A 2) (C (A 1) (A 0))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 0x3fffde) (C (A 8) (C (C (A 8) (C (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))) (C (C (A 1) (C (A 10) (C (C (A 14) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x1fffffffff)))) (C (A 9) (C (A 84) (C (A 10) (C (C (A 6) (C (A 0) (A 118))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 62))) (C (A 0) (A 2))))))))) (C (A 0) (A 6))))) (C (A 0) (A 1))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xfffffffff)))) (C (A 9) (C (A 379) (C (A 10) (C (C (A 6) (C (A 0) (A 0xffffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1022)) (C (A 0) (A 6)))) (C (A 0) (A 2))))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 0x3fffde) (C (A 8) (C (C (A 8) (C (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))) (C (C (A 1) (C (A 10) (C (C (A 30) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x1fffffffff)))) (C (A 9) (C (A 84) (C (A 10) (C (C (A 6) (C (A 0) (A 238))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 62))) (C (A 0) (A 2))))))))) (C (A 0) (A 6))))) (C (A 0) (A 1))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xfffffffff)))) (C (A 9) (C (A 379) (C (A 10) (C (C (A 6) (C (A 0) (A 0xffffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 510)) (C (A 0) (A 6)))) (C (A 0) (A 2))))))))))) (C (A 0) (A 1)))) (C (C (C (C (A 1) (A 0x6e6f63)) (C (C (A 0) (A 254)) (C (C (A 0) (A 126)) (C (A 0) (A 6))))) (C (A 0) (A 4090))) (C (A 0) (A 0x1fffe))))))))))))) (C (A 7) (C (C (A 10) (C (C (A 0x1fffa) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1ffffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0x3fffa))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 8167)) (C (A 0) (A 12)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (C (A 0) (A 1018)) (C (A 0) (A 0x7ffe))))))))))))))))))

/-- The case `%hed` of the body. -/
def alOpHed : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 10) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 114))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 0x1ffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 94))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 8) (C (C (A 0) (A 243)) (C (A 8) (C (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))) (C (A 7) (C (C (A 10) (C (C (A 0x7ffde) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0xfffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 10) (C (C (A 14) (C (C (A 0) (A 30)) (C (A 1) (C (A 0) (A 0))))) (C (A 0) (A 2)))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 0x7ffde) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffffff)))) (C (A 9) (C (A 379) (C (A 10) (C (C (A 6) (C (A 0) (A 0xfffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 62)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))) (C (C (A 1) (C (A 10) (C (C (A 62) (C (C (A 1) (A 0)) (C (A 0) (A 30)))) (C (A 0) (A 6))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (C (C (C (A 1) (A 0x646568)) (C (C (A 0) (A 30)) (C (A 0) (A 6)))) (C (A 0) (A 506))) (C (A 0) (A 0x3ffe))))))))))) (C (A 7) (C (C (A 10) (C (C (A 0x3ffa) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7ffa))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 499)) (C (A 0) (A 445)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (C (A 0) (A 122)) (C (A 0) (A 4094))))))))))))

/-- The case `%tal` of the body. -/
def alOpTal : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 10) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 114))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 0x1ffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 190))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 8) (C (C (A 0) (A 243)) (C (A 8) (C (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))) (C (A 7) (C (C (A 10) (C (C (A 0x7ffde) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0xfffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 10) (C (C (A 30) (C (C (A 0) (A 30)) (C (A 1) (C (A 0) (A 0))))) (C (A 0) (A 2)))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 0x7ffde) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffffff)))) (C (A 9) (C (A 379) (C (A 10) (C (C (A 6) (C (A 0) (A 0xfffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 62)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))) (C (C (A 1) (C (A 10) (C (C (A 126) (C (C (A 1) (A 0)) (C (A 0) (A 30)))) (C (A 0) (A 6))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (C (C (C (A 1) (A 0x6c6174)) (C (C (A 0) (A 30)) (C (A 0) (A 6)))) (C (A 0) (A 506))) (C (A 0) (A 0x3ffe))))))))))) (C (A 7) (C (C (A 10) (C (C (A 0x3ffa) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7ffa))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 499)) (C (A 0) (A 893)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (C (A 0) (A 122)) (C (A 0) (A 4094))))))))))))

/-- The case `%cel` of the body. -/
def alOpCel : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 10) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 57))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 0x1ffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 0) (A 4)) (C (C (C (A 0) (A 122)) (C (A 0) (A 4094))) (C (A 7) (C (C (A 10) (C (C (A 0x1ffde) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 379) (C (A 10) (C (C (A 6) (C (A 0) (A 0x3ffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))) (C (C (A 1) (C (A 10) (C (C (A 2) (C (A 1) (A 0))) (C (A 0) (A 6))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (C (C (C (A 1) (A 0x6c6563)) (C (A 0) (A 6))) (C (A 0) (A 122))) (C (A 0) (A 4094))))))))))))

/-- The case `%lob` of the body. -/
def alOpLob : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 10) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 57))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 0x1ffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 6) (C (C (A 0) (A 10)) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 383))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 766)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 767)))) (C (C (A 1) (A 0)) (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 767))))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C (C (C (A 0) (A 122)) (C (A 0) (A 4094))) (C (A 7) (C (C (A 10) (C (C (A 0x1ffde) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 379) (C (A 10) (C (C (A 6) (C (A 0) (A 0x3ffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))) (C (C (A 1) (C (A 10) (C (C (A 6) (C (A 1) (A 0))) (C (A 0) (A 6))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (C (C (C (A 1) (A 0x626f6c)) (C (A 0) (A 6))) (C (A 0) (A 122))) (C (A 0) (A 4094))))))))))))

/-- The case `%equ` of the body. -/
def alOpEqu : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 10) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 114))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 10) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 243))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 0) (A 6)) (C (A 0) (A 2)))) (C (C (C (A 0) (A 122)) (C (A 0) (A 4094))) (C (C (C (C (A 1) (A 0x757165)) (C (C (A 0) (A 6)) (C (A 0) (A 2)))) (C (A 0) (A 122))) (C (A 0) (A 4094))))))))))

/-- The case `%hsp` of the body. -/
def alOpHsp : Noun :=
  (C (C (C (A 0) (A 12)) (C (A 0) (A 26))) (C (A 0) (A 1022)))

/-- The case `%hse` of the body. -/
def alOpHse : Noun :=
  alOpHsp

/-- The case `%hdp` of the body. -/
def alOpHdp : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 10) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 230))) (C (A 0) (A 2)))))))) (C (C (C (C (A 1) (A 0x706468)) (C (C (A 0) (A 114)) (C (C (A 0) (A 2)) (C (A 0) (A 231))))) (C (A 0) (A 58))) (C (A 0) (A 2046)))))

/-- The case `%hde` of the body. -/
def alOpHde : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 10) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 230))) (C (A 0) (A 2)))))))) (C (C (C (C (A 1) (A 0x656468)) (C (C (A 0) (A 114)) (C (C (A 0) (A 2)) (C (A 0) (A 231))))) (C (A 0) (A 58))) (C (A 0) (A 2046)))))

/-- The case `%hmp` of the body. -/
def alOpHmp : Noun :=
  (C (C (C (C (A 1) (A 0x706d68)) (C (C (A 0) (A 50)) (C (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 230)) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 10) (C (A 0) (A 255)))))))) (C (A 0) (A 2)))))))) (C (A 0) (A 103))))) (C (A 0) (A 26))) (C (A 0) (A 1022)))

/-- The case `%hme` of the body. -/
def alOpHme : Noun :=
  (C (C (C (C (A 1) (A 0x656d68)) (C (C (A 0) (A 50)) (C (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 230)) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 10) (C (A 0) (A 255)))))))) (C (A 0) (A 2)))))))) (C (A 0) (A 103))))) (C (A 0) (A 26))) (C (A 0) (A 1022)))

/-- The case `%hcp` of the body. -/
def alOpHcp : Noun :=
  alOpHse

/-- The case `%hce` of the body. -/
def alOpHce : Noun :=
  alOpHcp

/-- The case `%spy` of the body. -/
def alOpSpy : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 10) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 114))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 10) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 486))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 487)) (C (A 7) (C (C (A 10) (C (C (A 0x3ffde) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7ffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (C (C (C (A 1) (A 0x797073)) (C (C (A 0) (A 14)) (C (C (A 0) (A 6)) (C (A 0) (A 2))))) (C (A 0) (A 250))) (C (A 0) (A 8190)))))))))))

/-- The case `%nok` of the body. -/
def alOpNok : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 10) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 114))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 10) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 486))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 487)) (C (A 7) (C (C (A 10) (C (C (A 0x3ffde) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7ffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (C (C (C (A 1) (A 0x6b6f6e)) (C (C (A 0) (A 14)) (C (C (A 0) (A 6)) (C (A 0) (A 2))))) (C (A 0) (A 250))) (C (A 0) (A 8190)))))))))))

/-- The case `%cal` of the body. -/
def alOpCal : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 230)) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 10) (C (A 0) (A 255)))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 231)) (C (A 7) (C (C (A 10) (C (C (A 0x1ffde) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0x3ffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (C (C (C (A 1) (A 0x6c6163)) (C (C (A 0) (A 242)) (C (C (A 0) (A 6)) (C (A 0) (A 2))))) (C (A 0) (A 122))) (C (A 0) (A 4094)))))))))

/-- The case `%caf` of the body. -/
def alOpCaf : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 230)) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 10) (C (A 0) (A 255)))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 462)) (C (A 7) (C (C (A 10) (C (C (A 0x1ffde) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0x3ffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (C (C (C (A 1) (A 0x666163)) (C (C (A 0) (A 242)) (C (C (A 0) (A 6)) (C (C (A 0) (A 2)) (C (A 0) (A 975)))))) (C (A 0) (A 122))) (C (A 0) (A 4094)))))))))

/-- The case `%cam` of the body. -/
def alOpCam : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 230)) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 10) (C (A 0) (A 255)))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 462)) (C (A 7) (C (C (A 10) (C (C (A 0x1ffde) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0x3ffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (C (C (C (A 1) (A 0x6d6163)) (C (C (A 0) (A 242)) (C (C (A 0) (A 6)) (C (C (A 0) (A 2)) (C (A 0) (A 975)))))) (C (A 0) (A 122))) (C (A 0) (A 4094)))))))))

/-- The case `%csl` of the body. -/
def alOpCsl : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 10) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 230))) (C (A 0) (A 2)))))))) (C (A 11) (C (C (A 0x6e61656d) (C (C (A 1) (C (A 8) (C (C (A 9) (C (A 0x27fe) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 158) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (C (A 0x6d6f7461) (C (A 0x65727675) (A 0)))) (C (A 0) (A 487)))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 0) (A 231)) (C (A 7) (C (C (A 10) (C (C (A 0x1ffde) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0x3ffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (C (C (C (A 1) (A 0x6c7363)) (C (C (A 0) (A 242)) (C (C (A 0) (A 6)) (C (A 0) (A 2))))) (C (A 0) (A 122))) (C (A 0) (A 4094)))))))))))

/-- The case `%csf` of the body. -/
def alOpCsf : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 10) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 230))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 462)) (C (A 7) (C (C (A 10) (C (C (A 0x1ffde) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0x3ffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (C (C (C (A 1) (A 0x667363)) (C (C (A 0) (A 242)) (C (C (A 0) (A 6)) (C (C (A 0) (A 2)) (C (A 0) (A 975)))))) (C (A 0) (A 122))) (C (A 0) (A 4094)))))))))

/-- The last case of the body (no test). -/
def alOpLast : Noun :=
  (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x6d7363)) (C (A 0) (A 24))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 10) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 230))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 462)) (C (A 7) (C (C (A 10) (C (C (A 0x1ffde) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0x3ffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (C (C (C (A 1) (A 0x6d7363)) (C (C (A 0) (A 242)) (C (C (A 0) (A 6)) (C (C (A 0) (A 2)) (C (A 0) (A 975)))))) (C (A 0) (A 122))) (C (A 0) (A 4094)))))))))))

/-- The case `%clq` of the end. -/
def alFinClq : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 956)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 958)))) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 10) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 494))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 0xffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 6) (C (C (A 0) (A 4)) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 383))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 766)))) (C (C (A 3) (C (A 0) (A 767))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C (C (C (C (A 1) (A 0x706f68)) (C (C (A 1) (A 0)) (C (A 0) (A 4029)))) (C (A 7) (C (C (A 10) (C (C (A 0x3ff7f) (C (A 1) (A 0))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 0x3ff7f) (C (A 1) (A 0))) (C (A 0) (A 1)))) (C (A 6) (C (C (A 5) (C (C (A 0) (A 4031)) (C (A 0) (A 4029)))) (C (C (A 0) (A 2046)) (C (A 10) (C (C (A 254) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 760) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 10) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7ff7e))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 8127)) (C (A 0) (A 0x3ffee)))) (C (A 0) (A 2))))))))) (C (A 0) (A 2046)))))))))))) (C (A 6) (C (C (A 6) (C (C (A 0) (A 10)) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 383))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 766)))) (C (C (A 6) (C (C (A 3) (C (A 0) (A 767))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C (C (C (C (A 1) (A 0x706f68)) (C (C (A 1) (A 0)) (C (A 0) (A 4031)))) (C (A 7) (C (C (A 10) (C (C (A 0x3ff7f) (C (A 1) (A 0))) (C (A 0) (A 1)))) (C (A 6) (C (C (A 5) (C (C (A 0) (A 4031)) (C (A 0) (A 4029)))) (C (C (A 0) (A 2046)) (C (A 10) (C (C (A 254) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 760) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 10) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7ff7e))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 8125)) (C (A 0) (A 0x3ffee)))) (C (A 0) (A 2))))))))) (C (A 0) (A 2046)))))))))) (C (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 251)))) (C (A 0) (A 2046))))))))))))) (C (A 0) (A 0))))) (C (A 0) (A 0)))))

/-- The case `%eqq` of the end. -/
def alFinEqq : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 1916)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 1918)))) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 10) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 494))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 10) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 2014))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 0) (A 6)) (C (A 0) (A 2)))) (C (C (C (C (A 1) (A 0x706f68)) (C (C (A 1) (A 0)) (C (A 0) (A 8061)))) (C (A 7) (C (C (A 10) (C (C (A 0x3ff7f) (C (A 1) (A 0))) (C (A 0) (A 1)))) (C (A 6) (C (C (A 5) (C (C (A 0) (A 8063)) (C (A 0) (A 8061)))) (C (C (A 0) (A 2046)) (C (A 10) (C (C (A 254) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 760) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 10) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7ff7e))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 0x3f7f)) (C (A 0) (A 0x3ffee)))) (C (A 0) (A 2))))))))) (C (A 0) (A 2046)))))))))) (C (C (A 10) (C (C (A 14) (C (A 0) (A 2))) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 251)))))) (C (A 0) (A 2046)))))))))) (C (A 0) (A 0))))) (C (A 0) (A 0)))))

/-- The case `%brn` of the end. -/
def alFinBrn : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 956)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 958)))) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 10) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 494))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 0xffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 383)))) (C (C (A 6) (C (C (A 0) (A 10)) (C (C (C (C (A 1) (A 0x7a7262)) (C (C (A 0) (A 6)) (C (C (A 0) (A 2014)) (C (A 0) (A 2015))))) (C (A 10) (C (C (A 255) (C (A 1) (A 0))) (C (A 0) (A 2046))))) (C (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 251)))) (C (A 0) (A 2046)))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 767)))) (C (C (C (C (A 1) (A 0x706f68)) (C (C (A 1) (A 0)) (C (A 0) (A 4029)))) (C (A 7) (C (C (A 10) (C (C (A 0x3ff7f) (C (A 1) (A 0))) (C (A 0) (A 1)))) (C (A 6) (C (C (A 5) (C (C (A 0) (A 4031)) (C (A 0) (A 4029)))) (C (C (A 0) (A 2046)) (C (A 10) (C (C (A 254) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 760) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 10) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7ff7e))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 8127)) (C (A 0) (A 0x3ffee)))) (C (A 0) (A 2))))))))) (C (A 0) (A 2046)))))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 767)))) (C (C (C (C (A 1) (A 0x706f68)) (C (C (A 1) (A 0)) (C (A 0) (A 4031)))) (C (A 7) (C (C (A 10) (C (C (A 0x3ff7f) (C (A 1) (A 0))) (C (A 0) (A 1)))) (C (A 6) (C (C (A 5) (C (C (A 0) (A 4031)) (C (A 0) (A 4029)))) (C (C (A 0) (A 2046)) (C (A 10) (C (C (A 254) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 760) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 10) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7ff7e))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 8125)) (C (A 0) (A 0x3ffee)))) (C (A 0) (A 2))))))))) (C (A 0) (A 2046)))))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 1) (A 0))) (C (C (A 1) (C (A 0x6d6f62) (A 0))) (C (A 7) (C (C (A 10) (C (C (A 0x3ff7e) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 760) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 10) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7ff7e))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 8127)) (C (A 0) (A 0x3ffee)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 0x3ff7e) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 760) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 10) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7ff7e))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 8125)) (C (A 0) (A 0x3ffee)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 0) (A 2046)))))))))))))))))))))) (C (A 0) (A 0))))) (C (A 0) (A 0)))))

/-- The case `%brz` of the end. -/
def alFinBrz : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 956)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 958)))) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 10) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 494))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 0xffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 383))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 6) (C (C (A 0) (A 4)) (C (C (A 1) (C (A 0) (A 1))) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 767)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 507)))) (C (A 0) (A 4094))) (C (A 8) (C (C (A 6) (C (C (A 0) (A 5)) (C (C (A 7) (C (C (A 0) (A 507)) (C (C (A 0) (A 29)) (C (A 0) (A 31))))) (C (A 7) (C (C (A 0) (A 507)) (C (C (A 0) (A 31)) (C (A 0) (A 29)))))))) (C (C (C (A 1) (A 0x706f68)) (C (C (A 1) (A 0)) (C (A 0) (A 4)))) (C (A 7) (C (C (A 10) (C (C (A 0xfff7f) (C (A 1) (A 0))) (C (A 0) (A 1)))) (C (A 6) (C (C (A 5) (C (C (A 0) (A 4)) (C (A 0) (A 5)))) (C (C (A 0) (A 8190)) (C (A 10) (C (C (A 254) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 760) (C (A 0) (A 0x7fffffff)))) (C (A 9) (C (A 10) (C (A 10) (C (C (A 6) (C (A 0) (A 0x1fff7e))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 13)) (C (A 0) (A 0xfffee)))) (C (A 0) (A 2))))))))) (C (A 0) (A 8190))))))))))))))))))))) (C (A 0) (A 0))))) (C (A 0) (A 0)))))

/-- The case `%hop` of the end. -/
def alFinHop : Noun :=
  (C (C (A 10) (C (C (A 6) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 494)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 372) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 10) (C (A 0) (A 127))))))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 59)))) (C (A 0) (A 510)))

/-- The case `%jmp` of the end. -/
def alFinJmp : Noun :=
  (C (C (A 10) (C (C (A 7) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 495)) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 10) (C (A 0) (A 127)))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 59)))) (C (A 0) (A 510)))

/-- The case `%jmf` of the end. -/
def alFinJmf : Noun :=
  (C (C (A 10) (C (C (A 14) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 990)) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 10) (C (A 0) (A 127)))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 59)))) (C (A 0) (A 510)))

/-- The case `%jsp` of the end. -/
def alFinJsp : Noun :=
  (C (C (A 10) (C (C (A 7) (C (A 8) (C (C (A 9) (C (A 10) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 495))) (C (A 0) (A 2))))))))) (C (A 0) (A 59)))) (C (A 0) (A 510)))

/-- The case `%jsf` of the end. -/
def alFinJsf : Noun :=
  (C (C (A 10) (C (C (A 14) (C (A 8) (C (C (A 9) (C (A 10) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 990))) (C (A 0) (A 2))))))))) (C (A 0) (A 59)))) (C (A 0) (A 510)))

/-- The case `%don` of the end. -/
def alFinDon : Noun :=
  (C (C (A 10) (C (C (A 3) (C (A 8) (C (C (A 9) (C (A 10) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 247))) (C (A 0) (A 2))))))))) (C (A 0) (A 59)))) (C (A 0) (A 510)))

/-- The last case of the end (no test). -/
def alFinLast : Noun :=
  (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x6d6f62)) (C (A 0) (A 118))))) (C (C (A 0) (A 59)) (C (A 0) (A 510)))))

/-- The refinement after a `%brn`. -/
def alJnBrn : Noun :=
  (C (A 8) (C (C (A 0) (A 189)) (C (A 8) (C (C (A 0) (A 447)) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 6)) (C (A 0) (A 0x3fee)))) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 2)) (C (A 0) (A 0x3fee)))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 8) (C (C (A 8) (C (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))) (C (C (A 1) (C (A 10) (C (C (A 255) (C (A 1) (C (A 0) (A 0)))) (C (A 0) (A 6))))) (C (A 0) (A 1))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 379) (C (A 10) (C (C (A 6) (C (A 0) (A 126))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1006)) (C (A 0) (A 6)))) (C (A 0) (A 2)))))))))) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 2)) (C (A 0) (A 0x3fee)))) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 6)) (C (A 0) (A 0x3fee)))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 8) (C (C (A 8) (C (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))) (C (C (A 1) (C (A 10) (C (C (A 255) (C (A 1) (C (A 0) (A 1)))) (C (A 0) (A 6))))) (C (A 0) (A 1))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 379) (C (A 10) (C (C (A 6) (C (A 0) (A 126))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1006)) (C (A 0) (A 6)))) (C (A 0) (A 2)))))))))) (C (A 11) (C (C (A 0x6e61656d) (C (A 1) (A 0x74736f6c2d726f737365636375732d6e7262))) (C (A 6) (C (C (A 5) (C (C (A 0) (A 6)) (C (A 0) (A 2)))) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 6)) (C (A 0) (A 0x3fee)))) (C (C (A 8) (C (C (A 8) (C (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))) (C (C (A 1) (C (A 10) (C (C (A 6) (C (A 1) (A 0))) (C (A 0) (A 6))))) (C (A 0) (A 1))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 379) (C (A 10) (C (C (A 6) (C (A 0) (A 126))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1006)) (C (A 0) (A 6)))) (C (A 0) (A 2)))))))))) (C (A 0) (A 0))))) (C (A 0) (A 0)))))))))))))))))

/-- The refinement after a `%brz`. -/
def alJnBrz : Noun :=
  (C (A 8) (C (C (A 0) (A 189)) (C (A 8) (C (C (A 0) (A 447)) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 6)) (C (A 0) (A 0x3fee)))) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 2)) (C (A 0) (A 0x3fee)))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 8) (C (C (A 8) (C (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))) (C (C (A 1) (C (A 10) (C (C (A 255) (C (A 1) (C (A 0) (A 0)))) (C (A 0) (A 6))))) (C (A 0) (A 1))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 379) (C (A 10) (C (C (A 6) (C (A 0) (A 126))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1006)) (C (A 0) (A 6)))) (C (A 0) (A 2)))))))))) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 2)) (C (A 0) (A 0x3fee)))) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 6)) (C (A 0) (A 0x3fee)))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 6) (C (C (A 7) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 62))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 494))) (C (A 0) (A 2)))))))) (C (A 0) (A 6)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 8) (C (C (A 8) (C (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))) (C (C (A 1) (C (A 10) (C (C (A 255) (C (A 1) (C (A 0) (A 1)))) (C (A 0) (A 6))))) (C (A 0) (A 1))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 379) (C (A 10) (C (C (A 6) (C (A 0) (A 126))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1006)) (C (A 0) (A 6)))) (C (A 0) (A 2)))))))))) (C (A 0) (A 30))))))))))))

/-- The refinement after a `%clq`. -/
def alJnClq : Noun :=
  (C (A 8) (C (C (A 0) (A 189)) (C (A 8) (C (C (A 0) (A 447)) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 6)) (C (A 0) (A 0x3fee)))) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 2)) (C (A 0) (A 0x3fee)))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 8) (C (C (A 8) (C (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))) (C (C (A 1) (C (A 10) (C (C (A 2) (C (A 1) (A 0))) (C (A 0) (A 6))))) (C (A 0) (A 1))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 379) (C (A 10) (C (C (A 6) (C (A 0) (A 126))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1006)) (C (A 0) (A 6)))) (C (A 0) (A 2)))))))))) (C (A 11) (C (C (A 0x6e61656d) (C (A 1) (A 0x74736f6c2d726f737365636375732d716c63))) (C (A 6) (C (C (A 5) (C (C (A 0) (A 2)) (C (A 0) (A 0x3fee)))) (C (C (A 0) (A 30)) (C (A 0) (A 0))))))))))))))

/-- `|(is-loob.a ?=([~ ?] has-imm.a))` in `join-reg`. -/
def alJRegLa : Noun :=
  (C (A 6) (C (C (A 0) (A 50)) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 1663))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 3326)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 3327)))) (C (C (A 1) (A 0)) (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 3327))))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))))))

/-- `|(is-loob.b ?=([~ ?] has-imm.b))` in `join-reg`. -/
def alJRegLb : Noun :=
  (C (A 6) (C (C (A 0) (A 54)) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 1791))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 3582)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 3583)))) (C (C (A 1) (A 0)) (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 3583))))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))))))

/-- Field 1 of the `info-reg` that `join-reg` makes. -/
def alJRegF1 : Noun :=
  (C (A 6) (C (C (A 0) (A 24)) (C (C (A 6) (C (C (A 0) (A 26)) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1)))))

/-- Field 2 of the `info-reg` that `join-reg` makes. -/
def alJRegF2 : Noun :=
  (C (A 6) (C alJRegLa (C (C (A 6) (C alJRegLb (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1)))))

/-- Field 3 of the `info-reg` that `join-reg` makes. -/
def alJRegF3 : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 85) (C (A 10) (C (C (A 6) (C (A 0) (A 230))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 238))) (C (A 0) (A 2))))))))

/-- Field 4 of the `info-reg` that `join-reg` makes. -/
def alJRegF4 : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 85) (C (A 10) (C (C (A 6) (C (A 0) (A 462))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 478))) (C (A 0) (A 2))))))))

/-- Field 5 of the `info-reg` that `join-reg` makes. -/
def alJRegF5 : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 0) (A 414)) (C (A 0) (A 446)))) (C (C (A 0) (A 414)) (C (A 1) (A 0)))))

/-- Field 6 of the `info-reg` that `join-reg` makes. -/
def alJRegF6 : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 0) (A 830)) (C (A 0) (A 894)))) (C (C (A 0) (A 830)) (C (A 1) (A 0)))))

/-- Field 7 of the `info-reg` that `join-reg` makes. -/
def alJRegF7 : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 0) (A 1662)) (C (A 0) (A 1790)))) (C (C (A 0) (A 1662)) (C (A 1) (A 0)))))

/-- Field 8 of the `info-reg` that `join-reg` makes. -/
def alJRegF8 : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 0) (A 1663)) (C (A 0) (A 1791)))) (C (C (A 0) (A 1663)) (C (A 1) (A 0)))))

/-- The bunt of `gen`. -/
def alGenBunt : Noun :=
  (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 1))))))))

/-- `(~(run by rev) (bake silt (list @uwoo)))`. -/
def alRevInit : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 766) (C (A 10) (C (C (A 6) (C (A 0) (A 246))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7f7) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 767) (C (A 0) (A 0xfffff)))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 1407) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0x9ddf) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x6f6f7775)))) (C (A 0) (A 14)))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 5) (C (C (A 0) (A 14)) (C (A 0) (A 2)))) (C (A 0) (A 6))))))) (C (A 0) (A 1)))))))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2))))))))

/-- The body of `rn`: `(~(gut by old.gen) r r)`. -/
def alRnB : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 1531) (C (A 10) (C (C (A 6) (C (A 0) (A 250))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 0) (A 14)))) (C (A 0) (A 2))))))))

/-- Its sample bunt. -/
def alRnBunt : Noun :=
  (A 0)

/-- The body of `join-reg`. -/
def alJRegB : Noun :=
  (C alJRegF1 (C alJRegF2 (C alJRegF3 (C alJRegF4 (C alJRegF5 (C alJRegF6 (C alJRegF7 alJRegF8)))))))

/-- Its sample bunt. -/
def alJRegBunt : Noun :=
  (C (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0)))))))) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0)))))))))

/-- The body of `join-info`. -/
def alJInfoB : Noun :=
  (C (A 8) (C (C (A 1) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 29)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 28)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 0) (A 28)) (C (A 0) (A 29)))) (C (C (A 0) (A 28)) (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 90) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 240)) (C (A 0) (A 244)))) (C (A 0) (A 2)))))))) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 116)) (C (A 0) (A 112)))) (C (C (A 10) (C (C (A 1) (C (C (C (A 0) (A 116)) (C (A 8) (C (C (A 9) (C (A 4) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 241)) (C (A 0) (A 245)))) (C (A 0) (A 2))))))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (C (A 0) (A 114)) (C (A 0) (A 118)))) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (C (A 0) (A 115)) (C (A 0) (A 119)))) (C (A 0) (A 1))))))))) (C (A 0) (A 29)))) (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 182) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 244)) (C (A 0) (A 240)))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 686) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 119) (C (A 1) (A 0))) (C (A 10) (C (C (A 28) (C (A 0) (A 114))) (C (A 0) (A 1))))))))))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 29) (C (A 0) (A 119))) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 686) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 118) (C (A 1) (A 0))) (C (A 10) (C (C (A 28) (C (A 0) (A 115))) (C (A 0) (A 1))))))))))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 29) (C (A 0) (A 118))) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))))))))) (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 182) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 240)) (C (A 0) (A 244)))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 686) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 115) (C (A 1) (A 0))) (C (A 10) (C (C (A 29) (C (A 0) (A 118))) (C (A 0) (A 1))))))))))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 28) (C (A 0) (A 115))) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 686) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 114) (C (A 1) (A 0))) (C (A 10) (C (C (A 29) (C (A 0) (A 119))) (C (A 0) (A 1))))))))))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 28) (C (A 0) (A 114))) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))))))))))))))))))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))

/-- Its sample bunt. -/
def alJInfoBunt : Noun :=
  (C (A 0) (A 0))

/-- The body of `join-imms`. -/
def alJImmsB : Noun :=
  (C (A 8) (C (C (A 1) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 29)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 28)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 0) (A 28)) (C (A 0) (A 29)))) (C (C (A 0) (A 28)) (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 90) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 240)) (C (A 0) (A 244)))) (C (A 0) (A 2)))))))) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 116)) (C (A 0) (A 112)))) (C (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 85) (C (A 10) (C (C (A 6) (C (A 0) (A 241))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 245))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (C (A 0) (A 242)) (C (A 0) (A 246)))) (C (A 0) (A 3)))))) (C (A 8) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (C (A 0) (A 499)) (C (A 0) (A 503)))) (C (A 0) (A 7)))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 14)))) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 686) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))) (C (C (C (A 0) (A 1012)) (C (A 0) (A 14))) (C (C (A 0) (A 6)) (C (A 0) (A 2))))))))))))) (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 182) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 244)) (C (A 0) (A 240)))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 686) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 119) (C (A 1) (A 0))) (C (A 10) (C (C (A 28) (C (A 0) (A 114))) (C (A 0) (A 1))))))))))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 29) (C (A 0) (A 119))) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 686) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 118) (C (A 1) (A 0))) (C (A 10) (C (C (A 28) (C (A 0) (A 115))) (C (A 0) (A 1))))))))))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 29) (C (A 0) (A 118))) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))))))))) (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 182) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 240)) (C (A 0) (A 244)))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 686) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 115) (C (A 1) (A 0))) (C (A 10) (C (C (A 29) (C (A 0) (A 118))) (C (A 0) (A 1))))))))))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 28) (C (A 0) (A 115))) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 686) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 114) (C (A 1) (A 0))) (C (A 10) (C (C (A 29) (C (A 0) (A 119))) (C (A 0) (A 1))))))))))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 28) (C (A 0) (A 114))) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))))))))))))))))))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))

/-- Its sample bunt. -/
def alJImmsBunt : Noun :=
  alJInfoBunt

/-- The body of `param-info`. -/
def alPInfoB : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0x17defea) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 0x17dae) (C (A 0) (A 0x7fffff)))))))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) alJImmsBunt))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 13)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) alJImmsBunt))))))) (C (A 0) (A 4))) (C (C (A 1) (C (A 8) (C (C (A 9) (C (A 4) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 0) (A 29)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 8) (C (C (A 9) (C (A 0x2fbd5) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 9) (C (A 0x2fbd5) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 62))) (C (A 0) (A 2)))))))))) (C (C (A 0) (A 2)) (C (A 10) (C (C (A 254) (C (A 1) (A 0))) (C (A 10) (C (C (A 126) (C (A 1) (A 0))) (C (A 10) (C (C (A 62) (C (A 1) (A 0))) (C (A 10) (C (C (A 30) (C (A 1) (A 0))) (C (A 10) (C (C (A 14) (C (A 1) (A 0))) (C (A 0) (A 2))))))))))))))))))))))

/-- Its sample bunt. -/
def alPInfoBunt : Noun :=
  (A 0)

/-- `pre`: `~(tap in (~(get ju rev.gen) o))`. -/
def alPre : Noun :=
  (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 186) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 760) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 46) (C (A 10) (C (C (A 6) (C (A 0) (A 1918))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 1006))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2))))))))

/-- The test `&(=(~ pre) !=(0w0 o))`. -/
def alUnT : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 1006)))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1)))))

/-- The `+roll` that deletes the edges of an unreachable block from `rev.gen`. -/
def alUnRoll : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 1502) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 7) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 506))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 2030))) (C (A 0) (A 2)))))))) (C (A 0) (A 7))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (A 0) (A 1918))) (C (C (A 1) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 760) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 10) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 57)) (C (A 0) (A 8174)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))

/-- The branch of an unreachable block. -/
def alUnB : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 1919) (C (A 1) (A 0))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 1918) alUnRoll) (C (A 0) (A 1)))) (C (A 9) (C (A 95) (C (A 10) (C (C (A 247) (C (A 0) (A 1007))) (C (A 0) (A 3))))))))))

/-- The facts of the entry block: `*info-reg` for `0 .. n-args - 1`. -/
def alEntry : Noun :=
  (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 1) (C (A 6) (C (C (A 5) (C (C (A 0) (A 6)) (C (A 0) (A 1020)))) (C (C (C (A 0) (A 14)) (C (A 0) (A 126))) (C (A 7) (C (C (A 10) (C (C (A 14) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 30))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) alJImmsBunt))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 4) (C (A 0) (A 6)))) (C (A 0) (A 1)))))))))))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))))

/-- The `+roll` of `join-info` over `t.pre`. -/
def alJnRoll : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 13)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (A 1) (A 0)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 246))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 12))) (C (A 0) (A 2))))))))) (C (C (A 1) (C (A 8) (C (C (A 9) (C (A 22) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 29)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 1014))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))

/-- `pre-b`: `(~(got by new.gen) i.pre)`. -/
def alJnPreB : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 124))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2))))))))

/-- The refinement after a one-predecessor `%brn`, `%brz`, `%clq`. -/
def alJnRef : Noun :=
  (C (A 8) (C alJnPreB (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6e7262)) (C (A 0) (A 22)))) (C alJnBrn (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x7a7262)) (C (A 0) (A 22)))) (C alJnBrz (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x716c63)) (C (A 0) (A 22)))) (C alJnClq (C (A 0) (A 6)))))))))))))

/-- The facts of a block with predecessors: `[info gen]`. -/
def alJoin : Noun :=
  (C (C (A 8) (C alJnRoll (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 13))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C alJnRef (C (A 0) (A 2))))))) (C (A 0) (A 14)))

/-- The `=^  info  gen` of the facts at the start. -/
def alInfo : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C alEntry alJoin)))))

/-- `imms`: `join-imms` over `pre`. -/
def alImms : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 6)))) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 29)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (A 1) (A 0)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 1006))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2))))))))) (C (C (A 1) (C (A 8) (C (C (A 9) (C (A 46) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 29)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 4078))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))))))

/-- `bob`: `(~(got by blocks) o)`. -/
def alBob : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 2042))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 8174))) (C (A 0) (A 2))))))))

/-- `edges`: the predecessors with the arguments of their jumps to `o`. -/
def alEdges : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0x17defa) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 62)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) (C (A 8) (C (C (A 9) (C (A 0x17defea) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 1502) (C (A 0) (A 8191)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 7) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 2044))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 0) (A 7))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) alJImmsBunt) (C (C (A 1) (C (A 6) (C (C (A 5) (C (C (A 0) (A 13)) (C (A 0) (A 0x1ffee)))) (C (C (C (A 1) (A 0)) (C (C (A 0) (A 30)) (C (A 0) (A 12)))) (C (A 1) (A 0)))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2))))))))

/-- The trap of the parameters. -/
def alParT : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 60)))) (C (C (C (A 8) (C (C (A 9) (C (A 0x2fbd7f) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 0) (A 1022))) (C (A 8) (C (C (A 0) (A 120)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 62)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) alJImmsBunt) (C (C (A 1) (C (A 6) (C (C (A 3) (C (A 0) (A 13))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 26)))) (C (C (A 1) (A 0)) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 0x1fff6))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 117))) (C (A 0) (A 2)))))))))))) alJImmsBunt)))) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (A 7) (C (C (A 10) (C (C (A 0x1ffde) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0x3ffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 94) (C (A 0) (A 1023)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 30) (C (C (A 0) (A 6)) (C (A 0) (A 30)))) (C (A 0) (A 1)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 60) (C (A 0) (A 505))) (C (A 10) (C (C (A 14) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 126)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) alJImmsBunt) (C (C (A 1) (C (C (A 0) (A 12)) (C (A 6) (C (C (A 3) (C (A 0) (A 13))) (C (C (A 0) (A 27)) alJImmsBunt))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 7)))))))))))))))))))

/-- The `=^  par-new  gen` of the parameters. -/
def alPars : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C alEdges (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 1) alParT) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))))))

/-- The gate of the `+roll` over `body.bob`. -/
def alBodyG : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 27))) (C (A 0) (A 1)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6d6d69)) (C (A 0) (A 24)))) (C alOpImm (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x766f6d)) (C (A 0) (A 24)))) (C alOpMov (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x636e69)) (C (A 0) (A 24)))) (C alOpInc (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6e6f63)) (C (A 0) (A 24)))) (C alOpCon (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x646568)) (C (A 0) (A 24)))) (C alOpHed (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6c6174)) (C (A 0) (A 24)))) (C alOpTal (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6c6563)) (C (A 0) (A 24)))) (C alOpCel (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x626f6c)) (C (A 0) (A 24)))) (C alOpLob (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x757165)) (C (A 0) (A 24)))) (C alOpEqu (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x707368)) (C (A 0) (A 24)))) (C alOpHce (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x657368)) (C (A 0) (A 24)))) (C alOpHce (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706468)) (C (A 0) (A 24)))) (C alOpHdp (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656468)) (C (A 0) (A 24)))) (C alOpHde (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706d68)) (C (A 0) (A 24)))) (C alOpHmp (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656d68)) (C (A 0) (A 24)))) (C alOpHme (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706368)) (C (A 0) (A 24)))) (C alOpHce (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656368)) (C (A 0) (A 24)))) (C alOpHce (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x797073)) (C (A 0) (A 24)))) (C alOpSpy (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6b6f6e)) (C (A 0) (A 24)))) (C alOpNok (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6c6163)) (C (A 0) (A 24)))) (C alOpCal (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x666163)) (C (A 0) (A 24)))) (C alOpCaf (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6d6163)) (C (A 0) (A 24)))) (C alOpCam (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6c7363)) (C (A 0) (A 24)))) (C alOpCsl (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x667363)) (C (A 0) (A 24)))) (C alOpCsf alOpLast))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- Its sample bunt. -/
def alBodyGBunt : Noun :=
  (C (C (A 7) (C (C (A 9) (C (A 2743) (C (A 0) (A 4095)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (C (A 7) (C (C (A 8) (C (C (A 9) (C (A 1407) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2743) (C (A 0) (A 4095))))))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (A 0) (A 254))))

/-- The `=^  body-new  gen` of the body. -/
def alBody : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 58)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C alBodyGBunt (C (C (A 1) alBodyG) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 9) (C (A 0x2fbd7f) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 12))) (C (A 0) (A 2)))))))) (C (A 0) (A 5)))))))

/-- The `=^  fin-new  gen` of the end. -/
def alFin : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x716c63)) (C (A 0) (A 118)))) (C alFinClq (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x717165)) (C (A 0) (A 118)))) (C alFinEqq (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6e7262)) (C (A 0) (A 118)))) (C alFinBrn (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x7a7262)) (C (A 0) (A 118)))) (C alFinBrz (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706f68)) (C (A 0) (A 118)))) (C alFinHop (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706d6a)) (C (A 0) (A 118)))) (C alFinJmp (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x666d6a)) (C (A 0) (A 118)))) (C alFinJmf (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x70736a)) (C (A 0) (A 118)))) (C alFinJsp (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x66736a)) (C (A 0) (A 118)))) (C alFinJsf (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6e6f64)) (C (A 0) (A 118)))) (C alFinDon alFinLast))))))))))))))))))))))))))))))))

/-- The stores into `new.gen`, `info.gen`, `imms.gen` and the next turn. -/
def alTail : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 10) (C (C (A 2044) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 4092))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 0x1ffee)) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 0) (A 14)) (C (C (A 0) (A 6)) (C (A 0) (A 2)))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 8182) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0x3ff6))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 0x1ffee)) (C (A 0) (A 0xffde)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 0x3fee) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7fee))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 0x1ffee)) (C (A 0) (A 0x1ffbe)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 9) (C (A 95) (C (A 10) (C (C (A 247) (C (A 0) (A 0xffef))) (C (A 0) (A 255))))))))))))))))

/-- The arm `$` of the `|^` core: the walk over `topo`. -/
def alWalk : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 247)))) (C (C (C (A 0) (A 895)) (C (A 0) (A 12))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C alPre (C (A 6) (C alUnT (C alUnB (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C alInfo (C (A 7) (C (C (A 10) (C (C (A 30) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C alImms (C (A 7) (C (C (A 10) (C (C (A 2014) (C (A 0) (A 6))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 4030) (C (A 0) (A 2))) (C (A 0) (A 1)))) (C (A 8) (C alBob (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C alPars (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C alBody (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C alFin alTail))))))))))))))))))))))))))))))))))))))))))))))

/-- The battery of the `|^` core. -/
def alBat : Noun :=
  (C (C (A 8) (C (C (A 1) alJRegBunt) (C (C (A 1) alJRegB) (C (A 0) (A 1))))) (C (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) alRnB) (C (A 0) (A 1))))) (C (C (A 8) (C (C (A 1) alJImmsBunt) (C (C (A 1) alJInfoB) (C (A 0) (A 1))))) (C (C (A 8) (C (C (A 1) alJImmsBunt) (C (C (A 1) alJImmsB) (C (A 0) (A 1))))) (C (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) alPInfoB) (C (A 0) (A 1))))) alWalk)))))

/-- The gate body of `+alias`. -/
def alBodyCut : Noun :=
  (C (A 8) (C (C (A 1) alGenBunt) (C (A 7) (C (C (A 10) (C (C (A 382) alRevInit) (C (A 0) (A 1)))) (C (A 8) (C (C (A 1) alBat) (C (A 9) (C (A 95) (C (A 0) (A 1))))))))))

/-- The arm `+alias` as cut. -/
def alArmCut : Noun :=
  C (A 7) (C (C (A 8) (C (C (A 1) (C (A 0) (C (A 0) (C (A 0) (A 0))))) (C (C (A 1) alBodyCut) (C (A 0) (A 1)))))
    ooAliasHint)

/-- `+alias` is arm `725` of `optC`. -/
theorem al_at_cut : slot? 725 optC = some alArmCut := by kernel_rfl

/-- The body read from the pill by `AliasLink` is `alBodyCut`. -/
theorem aliasBody_eq : aliasBody = alBodyCut := by
  unfold aliasBody aliasArm
  rw [al_at_cut]
  rfl

end Compiler
end Formalization
