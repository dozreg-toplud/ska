import lemmas.Compiler.OptLinkAlNouns

/-!
# `+alias`: the nouns of the start of a block's turn (phases 7 to 12)

Written by `tools/gen/optlink.py alstart` (the definitions below the header;
the equalities at the end by hand).  The gates and traps inside the nouns of
`OptLinkAlNouns.lean` that the start of a block's turn runs, named, and those
nouns cut at them (`alXC`, equal to `alX` by `rfl`): the lenses of the
refinement (`alLsZ`, `alLsO`, `alLsL`, `alLsC`), the gate of the `+roll` of an
unreachable block (`alUnG`), the trap of the entry block (`alEnT`), the gates
of the `+roll`s of `join-info` and `join-imms` (`alJnG`, `alImG`), the gates of
`edges` (`alEdT`, its `+murn` gate `alEdM`) and of the parameter trap
(`alPaIn`, `alPaTl`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The lens `+<(has-imm `&)` of the refinement. -/
def alLsZ : Noun :=
  (C (A 10) (C (C (A 255) (C (A 1) (C (A 0) (A 0)))) (C (A 0) (A 6))))

/-- The lens `+<(has-imm `|)` of the refinement. -/
def alLsO : Noun :=
  (C (A 10) (C (C (A 255) (C (A 1) (C (A 0) (A 1)))) (C (A 0) (A 6))))

/-- The lens `+<(is-loob &)` of the refinement. -/
def alLsL : Noun :=
  (C (A 10) (C (C (A 6) (C (A 1) (A 0))) (C (A 0) (A 6))))

/-- The lens `+<(is-cell &)` of the refinement. -/
def alLsC : Noun :=
  (C (A 10) (C (C (A 2) (C (A 1) (A 0))) (C (A 0) (A 6))))

/-- The gate of the `+roll` of an unreachable block: `(~(del ju acc) there.j o)`. -/
def alUnG : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 760) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 10) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 57)) (C (A 0) (A 8174)))) (C (A 0) (A 2))))))))

/-- The trap of the entry block over `r`. -/
def alEnT : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 0) (A 6)) (C (A 0) (A 1020)))) (C (C (C (A 0) (A 14)) (C (A 0) (A 126))) (C (A 7) (C (C (A 10) (C (C (A 14) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 30))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 4) (C (A 0) (A 6)))) (C (A 0) (A 1)))))))))))

/-- The gate of the `+roll` of `join-info` over `t.pre`. -/
def alJnG : Noun :=
  (C (A 8) (C (C (A 9) (C (A 22) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 29)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 1014))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))

/-- The gate of the `+roll` of `join-imms` over `t.pre`. -/
def alImG : Noun :=
  (C (A 8) (C (C (A 9) (C (A 46) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 29)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 4078))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))

/-- The gate of the `+murn` of `edges` over the jumps of a predecessor. -/
def alEdM : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 0) (A 13)) (C (A 0) (A 0x1ffee)))) (C (C (C (A 1) (A 0)) (C (C (A 0) (A 30)) (C (A 0) (A 12)))) (C (A 1) (A 0)))))

/-- The gate of the `+turn` of `edges` over `pre`. -/
def alEdT : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0x17defea) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 1502) (C (A 0) (A 8191)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 7) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 2044))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 0) (A 7))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (C (A 1) alEdM) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))

/-- The gate of the `+turn` of `ins` over `edges`. -/
def alPaIn : Noun :=
  (C (A 6) (C (C (A 3) (C (A 0) (A 13))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 26)))) (C (C (A 1) (A 0)) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 0x1fff6))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 117))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 0)))))

/-- The gate of the `+turn` that drops the first argument of each edge. -/
def alPaTl : Noun :=
  (C (C (A 0) (A 12)) (C (A 6) (C (C (A 3) (C (A 0) (A 13))) (C (C (A 0) (A 27)) (C (A 0) (A 0))))))

/-- `alUnRoll`, cut at its gates. -/
def alUnRollC : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 1502) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 7) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 506))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 2030))) (C (A 0) (A 2)))))))) (C (A 0) (A 7))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (A 0) (A 1918))) (C (C (A 1) alUnG) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))

/-- `alEntry`, cut at its gates. -/
def alEntryC : Noun :=
  (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 1) alEnT) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))))

/-- `alJnRoll`, cut at its gates. -/
def alJnRollC : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 13)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (A 1) (A 0)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 246))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 12))) (C (A 0) (A 2))))))))) (C (C (A 1) alJnG) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))

/-- `alJnBrn`, cut at its gates. -/
def alJnBrnC : Noun :=
  (C (A 8) (C (C (A 0) (A 189)) (C (A 8) (C (C (A 0) (A 447)) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 6)) (C (A 0) (A 0x3fee)))) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 2)) (C (A 0) (A 0x3fee)))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 8) (C (C (A 8) (C (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))) (C (C (A 1) alLsZ) (C (A 0) (A 1))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 379) (C (A 10) (C (C (A 6) (C (A 0) (A 126))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1006)) (C (A 0) (A 6)))) (C (A 0) (A 2)))))))))) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 2)) (C (A 0) (A 0x3fee)))) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 6)) (C (A 0) (A 0x3fee)))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 8) (C (C (A 8) (C (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))) (C (C (A 1) alLsO) (C (A 0) (A 1))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 379) (C (A 10) (C (C (A 6) (C (A 0) (A 126))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1006)) (C (A 0) (A 6)))) (C (A 0) (A 2)))))))))) (C (A 11) (C (C (A 0x6e61656d) (C (A 1) (A 0x74736f6c2d726f737365636375732d6e7262))) (C (A 6) (C (C (A 5) (C (C (A 0) (A 6)) (C (A 0) (A 2)))) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 6)) (C (A 0) (A 0x3fee)))) (C (C (A 8) (C (C (A 8) (C (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))) (C (C (A 1) alLsL) (C (A 0) (A 1))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 379) (C (A 10) (C (C (A 6) (C (A 0) (A 126))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1006)) (C (A 0) (A 6)))) (C (A 0) (A 2)))))))))) (C (A 0) (A 0))))) (C (A 0) (A 0)))))))))))))))))

/-- `alJnBrz`, cut at its gates. -/
def alJnBrzC : Noun :=
  (C (A 8) (C (C (A 0) (A 189)) (C (A 8) (C (C (A 0) (A 447)) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 6)) (C (A 0) (A 0x3fee)))) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 2)) (C (A 0) (A 0x3fee)))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 8) (C (C (A 8) (C (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))) (C (C (A 1) alLsZ) (C (A 0) (A 1))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 379) (C (A 10) (C (C (A 6) (C (A 0) (A 126))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1006)) (C (A 0) (A 6)))) (C (A 0) (A 2)))))))))) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 2)) (C (A 0) (A 0x3fee)))) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 6)) (C (A 0) (A 0x3fee)))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 6) (C (C (A 7) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 62))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 494))) (C (A 0) (A 2)))))))) (C (A 0) (A 6)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 8) (C (C (A 8) (C (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))) (C (C (A 1) alLsO) (C (A 0) (A 1))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 379) (C (A 10) (C (C (A 6) (C (A 0) (A 126))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1006)) (C (A 0) (A 6)))) (C (A 0) (A 2)))))))))) (C (A 0) (A 30))))))))))))

/-- `alJnClq`, cut at its gates. -/
def alJnClqC : Noun :=
  (C (A 8) (C (C (A 0) (A 189)) (C (A 8) (C (C (A 0) (A 447)) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 6)) (C (A 0) (A 0x3fee)))) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 2)) (C (A 0) (A 0x3fee)))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 8) (C (C (A 8) (C (C (A 1) (C (A 1) (C (A 1) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))) (C (C (A 1) alLsC) (C (A 0) (A 1))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 379) (C (A 10) (C (C (A 6) (C (A 0) (A 126))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1006)) (C (A 0) (A 6)))) (C (A 0) (A 2)))))))))) (C (A 11) (C (C (A 0x6e61656d) (C (A 1) (A 0x74736f6c2d726f737365636375732d716c63))) (C (A 6) (C (C (A 5) (C (C (A 0) (A 2)) (C (A 0) (A 0x3fee)))) (C (C (A 0) (A 30)) (C (A 0) (A 0))))))))))))))

/-- `alImms`, cut at its gates. -/
def alImmsC : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 6)))) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 29)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (A 1) (A 0)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 1006))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2))))))))) (C (C (A 1) alImG) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))))))

/-- `alEdges`, cut at its gates. -/
def alEdgesC : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0x17defa) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 62)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) alEdT) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2))))))))

/-- `alParT`, cut at its gates. -/
def alParTC : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 60)))) (C (C (C (A 8) (C (C (A 9) (C (A 0x2fbd7f) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 0) (A 1022))) (C (A 8) (C (C (A 0) (A 120)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 62)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (C (A 1) alPaIn) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (A 7) (C (C (A 10) (C (C (A 0x1ffde) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0x3ffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 94) (C (A 0) (A 1023)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 30) (C (C (A 0) (A 6)) (C (A 0) (A 30)))) (C (A 0) (A 1)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 60) (C (A 0) (A 505))) (C (A 10) (C (C (A 14) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 126)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (C (A 1) alPaTl) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 7)))))))))))))))))))

theorem alUnRoll_cut : alUnRoll = alUnRollC := rfl
theorem alEntry_cut : alEntry = alEntryC := rfl
theorem alJnRoll_cut : alJnRoll = alJnRollC := rfl
theorem alJnBrn_cut : alJnBrn = alJnBrnC := rfl
theorem alJnBrz_cut : alJnBrz = alJnBrzC := rfl
theorem alJnClq_cut : alJnClq = alJnClqC := rfl
theorem alImms_cut : alImms = alImmsC := rfl
theorem alEdges_cut : alEdges = alEdgesC := rfl
theorem alParT_cut : alParT = alParTC := rfl

end Compiler
end Formalization
