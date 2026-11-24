import lemmas.Compiler.OptLinkTrimLink
import lemmas.Ska.OptSwitch

/-!
# `+switch-chains`: the nouns and the subjects

The arm is `182` of `optC` (`sw_at`, nouns by `tools/gen/optlink.py
switch`).  Its body (`swBodyCut`, equal to `swBody` of `OptLinkOpt.lean`:
`swBody_eq`) pushes `topo` (`+bb-topo`), `rev` (`+rev-cfg` of `(sy topo)`),
`uses` (`swUses`: the `+rep:by` of `swRepG` over the blocks), then six gates,
each with the subject before as its context: `test-of` (`swTOB`), `chain-of`
(`swCHB`), `plain-of` (`swPOB`), `plains-of` (`swPSB`), `cases` (`swCSB`, its
trap `swCST`), `tree` (`swTRB`); then `out` (the blocks), `done` (`~`), `nex`
(`swNex`) and the walk `swWalk` over `topo`.

The subjects: `swS3` after `uses`, `swS4` to `swS9` after each gate, `swW`
the core of the walk, whose `topo`, `out`, `done` and `nex` change from turn
to turn.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The nouns -/

/-- The body of the gate `put` of `uses`: `(~(put by acc) r +((~(gut by acc) r 0)))`. -/
def swPutB : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 7) (C (C (A 0) (A 3)) (C (A 4) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 1531) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))))) (C (A 0) (A 2))))))))))))) (C (A 0) (A 2))))))))

/-- The gate of the `+roll` over `body.b` in `uses`. -/
def swOpG : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 84) (C (A 0) (A 4095)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 10) (C (C (A 13) (C (A 0) (A 13))) (C (A 0) (A 62)))))))) (C (A 0) (A 2))))))))

/-- The gate of the `+rep:by` that makes `uses`. -/
def swRepG : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 13) (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 114)) (C (A 7) (C (C (A 0) (A 3)) (C (A 10) (C (C (A 13) (C (A 0) (A 13))) (C (A 0) (A 14)))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 13) (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 84) (C (A 0) (A 1023)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 231))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 10) (C (C (A 13) (C (A 0) (A 13))) (C (A 0) (A 14)))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 230)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (A 7) (C (C (A 9) (C (A 2743) (C (A 0) (A 1023)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (A 0) (A 13))) (C (C (A 1) swOpG) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))))))

/-- Its sample bunt. -/
def swRepB : Noun :=
  (C (C (A 0) (C (A 0) (C (A 0) (C (A 0x6d6f62) (A 0))))) (A 0))

/-- `uses`: how many times each register is mentioned. -/
def swUses : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (C (A 1) swPutB) (C (A 0) (A 1))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 767) (C (A 10) (C (C (A 6) (C (A 0) (A 126))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) swRepB) (C (C (A 1) swRepG) (C (A 0) (A 1)))))))) (C (A 0) (A 2))))))))))

/-- `?=([%clq * [~ *] [~ *]] fin.b)` in `test-of`. -/
def swTOClq : Noun :=
  (C (A 6) (C (C (A 3) (C (A 0) (A 11))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x716c63)) (C (A 0) (A 22)))) (C (C (A 6) (C (C (A 3) (C (A 0) (A 23))) (C (C (A 6) (C (C (A 3) (C (A 0) (A 47))) (C (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 94))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 188)))) (C (A 1) (A 1))))) (C (C (A 6) (C (C (A 3) (C (A 0) (A 95))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 190)))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1)))))

/-- `?=([%eqq * * [~ *] [~ *]] fin.yb)` in `test-of`. -/
def swTOEqq : Noun :=
  (C (A 6) (C (C (A 3) (C (A 0) (A 11))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x717165)) (C (A 0) (A 22)))) (C (C (A 6) (C (C (A 3) (C (A 0) (A 23))) (C (C (A 6) (C (C (A 3) (C (A 0) (A 47))) (C (C (A 6) (C (C (A 3) (C (A 0) (A 95))) (C (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 190))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 380)))) (C (A 1) (A 1))))) (C (C (A 6) (C (C (A 3) (C (A 0) (A 191))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 382)))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1)))))

/-- The unit `h` of `test-of` when the first op is no `%hed`. -/
def swTOH1 : Noun :=
  (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 10))) (C (C (A 5) (C (C (A 1) (A 0x646568)) (C (A 0) (A 20)))) (C (A 1) (A 1))))) (C (C (C (A 1) (A 0)) (C (A 7) (C (C (A 0) (A 10)) (C (C (A 0) (A 6)) (C (A 0) (A 7)))))) (C (A 1) (A 0)))))

/-- The unit `m` of `test-of` when the first op is no `%imm`. -/
def swTOM1 : Noun :=
  (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 26))) (C (C (A 5) (C (C (A 1) (A 0x6d6d69)) (C (A 0) (A 52)))) (C (A 1) (A 1))))) (C (C (C (A 1) (A 0)) (C (A 7) (C (C (A 0) (A 26)) (C (C (A 0) (A 6)) (C (A 0) (A 7)))))) (C (A 1) (A 0)))))

/-- The unit `h` of `test-of`: the `%hed` of the two ops. -/
def swTOH : Noun :=
  (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 4))) (C (C (A 5) (C (C (A 1) (A 0x646568)) (C (A 0) (A 8)))) (C (A 1) (A 1))))) (C (C (C (A 1) (A 0)) (C (A 7) (C (C (A 0) (A 4)) (C (C (A 0) (A 6)) (C (A 0) (A 7)))))) swTOH1)))

/-- The unit `m` of `test-of`: the `%imm` of the two ops. -/
def swTOM : Noun :=
  (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 0x6d6d69)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (C (A 1) (A 0)) (C (A 7) (C (C (A 0) (A 12)) (C (C (A 0) (A 6)) (C (A 0) (A 7)))))) swTOM1)))

/-- `(lth c (bex 31))` in `test-of`. -/
def swTOLth : Noun :=
  (C (A 8) (C (C (A 9) (C (A 2399) (C (A 0) (A 0x1ffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 2676) (C (A 0) (A 0xffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 31))))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))

/-- The test of the registers of the `%eqq` in `test-of`. -/
def swTOEq : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 7) (C (C (A 0) (A 251)) (C (C (A 0) (A 6)) (C (A 0) (A 14))))) (C (C (A 0) (A 59)) (C (A 0) (A 27))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 7) (C (C (A 0) (A 251)) (C (C (A 0) (A 6)) (C (A 0) (A 14))))) (C (C (A 0) (A 27)) (C (A 0) (A 59))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))))))

/-- The test of the `uses` of `d` and `r` in `test-of`. -/
def swTOUses : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 2)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffffff)))) (C (A 9) (C (A 1531) (C (A 10) (C (C (A 6) (C (A 0) (A 8190))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 123)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))))) (C (A 0) (A 2)))))))))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 2)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffffff)))) (C (A 9) (C (A 1531) (C (A 10) (C (C (A 6) (C (A 0) (A 8190))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 59)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))))) (C (A 0) (A 2)))))))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1)))))

/-- `test-of` from `c`: its tests and the test it returns. -/
def swTOC : Noun :=
  (C (A 8) (C (C (A 0) (A 10)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 6) (C swTOLth (C (C (A 6) (C swTOEq (C (C (A 6) (C swTOUses (C (C (C (A 1) (A 0)) (C (C (A 0) (A 8174)) (C (C (A 0) (A 2)) (C (C (A 0) (A 8061)) (C (C (A 0) (A 126)) (C (C (A 0) (A 254)) (C (C (A 0) (A 59)) (C (A 0) (A 27))))))))) (C (A 1) (A 0))))) (C (A 1) (A 0))))) (C (A 1) (A 0))))) (C (A 1) (A 0)))))))

/-- `test-of` from `=(s.u.h s.fin.b)`. -/
def swTOS : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 0) (A 26)) (C (A 0) (A 4078)))) (C swTOC (C (A 1) (A 0)))))

/-- `test-of` from `h`. -/
def swTOHM : Noun :=
  (C (A 8) (C swTOH (C (A 8) (C swTOM (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 6)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) swTOS))))))))))

/-- `test-of` from `bod`. -/
def swTOBod : Noun :=
  (C (A 8) (C (C (A 0) (A 10)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 6) (C (C (A 3) (C (A 0) (A 5))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 11)))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C swTOHM (C (A 1) (A 0)))))))

/-- `test-of` from `yb`. -/
def swTOYb : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 4094))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 4)))) (C (C (A 6) (C swTOEqq (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 6)) (C (A 0) (A 383)))) (C swTOBod (C (A 1) (A 0))))) (C (A 1) (A 0))))) (C (A 1) (A 0)))))))

/-- `test-of` after the test of `fin.b`. -/
def swTOY : Noun :=
  (C (A 8) (C (C (A 0) (A 189)) (C (A 8) (C (C (A 0) (A 447)) (C (A 6) (C (C (A 5) (C (C (C (A 0) (A 62)) (C (A 1) (A 0))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 761) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 10) (C (A 10) (C (C (A 6) (C (A 0) (A 510))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))))) (C swTOYb (C (A 1) (A 0)))))))))

/-- The body of the gate `test-of`. -/
def swTOB : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 510))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 6) (C swTOClq (C swTOY (C (A 1) (A 0)))))))

/-- The body of the gate `chain-of`. -/
def swCHB : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 0) (A 14)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (C (A 0) (A 5)) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 2046))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 222))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 4)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 10)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 761) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 10) (C (A 10) (C (C (A 6) (C (A 0) (A 510))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 478))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 2)) (C (C (A 0) (A 62)) (C (C (A 0) (A 958)) (C (A 1) (A 0)))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 0) (A 2)) (C (C (A 0) (A 958)) (C (C (A 0) (A 62)) (C (A 1) (A 0)))))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C (C (A 8) (C (C (A 8) (C (C (A 0) (A 126)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 990))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 0) (A 10)) (C (A 0) (A 122)))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 990))) (C (A 0) (A 31)))))) (C (A 1) (A 0)))))))))) (C (A 1) (A 0))))))) (C (A 1) (A 0)))))))))))))

/-- The trap of `m` in `plain-of`: the first `%imm` into `l` or `r`. -/
def swPOMT : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 6)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 5) (C (C (A 1) (A 0x6d6d69)) (C (A 0) (A 24)))) (C (A 1) (A 1))))) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 51)) (C (A 0) (A 238)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 0) (A 51)) (C (A 0) (A 478)))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (C (A 1) (A 0)) (C (A 7) (C (C (A 0) (A 12)) (C (C (A 0) (A 6)) (C (A 0) (A 7)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 13))) (C (A 0) (A 1))))))))))))

/-- `plain-of` from `?~  m`. -/
def swPOC : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 0) (A 10)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 2399) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 2676) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 31))))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2)))))))) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 238)) (C (A 0) (A 478)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 2)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 1531) (C (A 10) (C (C (A 6) (C (A 0) (A 1022))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 59)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))))) (C (A 0) (A 2)))))))))) (C (C (A 8) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 27)) (C (A 0) (A 238)))) (C (C (A 0) (A 478)) (C (A 0) (A 238))))) (C (C (A 1) (A 0)) (C (C (A 0) (A 2)) (C (C (A 0) (A 6)) (C (C (A 0) (A 3965)) (C (C (A 0) (A 3967)) (C (A 0) (A 59))))))))) (C (A 1) (A 0)))))))) (C (A 1) (A 0))))) (C (A 1) (A 0))))))))))

/-- The body of the gate `plain-of`. -/
def swPOB : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 2046))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 6) (C swTOEqq (C (C (A 8) (C (C (A 8) (C (C (A 0) (A 10)) (C (A 8) (C (C (A 1) swPOMT) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))) swPOC)) (C (A 1) (A 0)))))))

/-- `?=([[%imm *] ~] body.nb)` in `plains-of`. -/
def swPSShape : Noun :=
  (C (A 6) (C (C (A 3) (C (A 0) (A 10))) (C (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 20))) (C (C (A 5) (C (C (A 1) (A 0x6d6d69)) (C (A 0) (A 40)))) (C (A 1) (A 1))))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 21)))) (C (A 1) (A 1))))) (C (A 1) (A 1)))))

/-- The body of the gate `plains-of`. -/
def swPSB : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 0) (A 14)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (C (C (A 0) (A 14)) (C (A 0) (A 5))) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 8190))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 222))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 4)))) (C (C (A 6) (C swPSShape (C (C (A 6) (C (C (A 5) (C (C (C (A 0) (A 30)) (C (A 1) (A 0))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 761) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 10) (C (A 10) (C (C (A 6) (C (A 0) (A 2046))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 478))) (C (A 0) (A 2)))))))))) (C (C (A 8) (C (C (A 8) (C (C (A 0) (A 62)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 478))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 0) (A 10)) (C (A 0) (A 58)))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 478))) (C (A 0) (A 15)))))) (C (A 1) (A 0)))))))))) (C (A 1) (A 0))))) (C (A 1) (A 0))))) (C (A 1) (A 0)))))))))))))

/-- The gate of the `+sort` in `cases`: `(lth c.a c.b)`. -/
def swCSSG : Noun :=
  (C (A 8) (C (C (A 9) (C (A 2399) (C (A 0) (A 0x1ffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 56)) (C (A 0) (A 58)))) (C (A 0) (A 2))))))))

/-- The trap of `cases`. -/
def swCST : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 30)))) (C (C (A 8) (C (C (A 9) (C (A 0x5f7bfe) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 29)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (C (A 0) (A 0)) (C (A 0) (A 0)))) (C (C (A 1) swCSSG) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 381) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 248))) (C (A 0) (A 2)))))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 61))) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 61))) (C (A 10) (C (C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 84) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 248))) (C (A 0) (A 2)))))))) (C (C (A 0) (A 60)) (C (A 0) (A 13))))) (C (A 0) (A 1))))))))))))))

/-- The body of the gate `cases`. -/
def swCSB : Noun :=
  (C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (A 8) (C (C (A 1) swCST) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))

/-- The leaf of `tree`: `[~[[%imm c r]] [%eqq d r [~ hit] [~ mis]] ids out]`. -/
def swTRLeaf : Noun :=
  (C (C (C (C (A 1) (A 0x6d6d69)) (C (C (A 0) (A 48)) (C (A 0) (A 99)))) (C (A 1) (A 0))) (C (C (C (A 1) (A 0x717165)) (C (C (A 0) (A 26)) (C (C (A 0) (A 99)) (C (C (C (A 1) (A 0)) (C (A 0) (A 98))) (C (C (A 1) (A 0)) (C (A 0) (A 54))))))) (C (C (A 0) (A 110)) (C (A 0) (A 111)))))

/-- The two recursions of `tree` and the node it returns. -/
def swTRRec : Noun :=
  (C (A 8) (C (C (C (A 0) (A 2012)) (C (A 0) (A 4026))) (C (A 8) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 110) (C (A 0) (A 8123))) (C (A 10) (C (C (A 12) (C (A 8) (C (C (A 9) (C (A 0x2fbdfd6) (C (A 0) (A 0x1ffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 30)) (C (A 0) (A 62)))) (C (A 0) (A 2))))))))) (C (A 0) (A 31)))))))) (C (A 7) (C (C (A 10) (C (C (A 23) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3ffffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 55))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0)) (C (C (A 0) (A 4)) (C (A 0) (A 10)))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 55) (C (C (A 0) (A 22)) (C (A 0) (A 23)))) (C (A 10) (C (C (A 12) (C (A 0) (A 14))) (C (A 0) (A 63)))))))) (C (A 7) (C (C (A 10) (C (C (A 23) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 55))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 61)) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0)) (C (C (A 0) (A 4)) (C (A 0) (A 10)))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (C (A 1) (A 0)) (C (C (C (A 1) (A 0x69746c)) (C (C (A 0) (A 120)) (C (C (A 0) (A 2042)) (C (C (C (A 1) (A 0)) (C (A 0) (A 28))) (C (C (A 1) (A 0)) (C (A 0) (A 29))))))) (C (C (A 0) (A 22)) (C (A 0) (A 23)))))))))))))))

/-- `tree` from `haf`. -/
def swTRSplit : Noun :=
  (C (A 8) (C (C (A 0) (A 12)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 1198) (C (A 0) (A 0x7fffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0x2fbd5) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 2)))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0xbef5e) (C (A 0) (A 0x7fffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 0) (A 14)))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 1006))) (C (C (A 3) (C (A 0) (A 2013))) (C (A 1) (A 1))))) (C swTRRec (C (A 0) (A 0))))) (C (A 0) (A 0)))))))))))

/-- The body of the gate `tree`. -/
def swTRB : Noun :=
  (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 25)))) (C swTRLeaf swTRSplit))) (C (A 0) (A 0)))))

/-- Its sample bunt. -/
def swTRBunt : Noun :=
  (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0)))))

/-- The gate of the `+roll` of `nex`. -/
def swNexG : Noun :=
  (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 38) (C (A 0) (A 0x1ffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 0) (A 29)))) (C (A 0) (A 2)))))))) (C (C (A 4) (C (A 0) (A 12))) (C (A 0) (A 13)))))

/-- `nex`: the first label that no block has. -/
def swNex : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 186) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 188) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7ffe))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (C (A 1) swNexG) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))

/-- `(~(has in done) i.topo)`. -/
def swWHas : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0xffffffff)))) (C (A 9) (C (A 381) (C (A 10) (C (C (A 6) (C (A 0) (A 30))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 0xfffc))) (C (A 0) (A 2))))))))

/-- `(chain-of i.topo)`. -/
def swWCs : Noun :=
  (C (A 8) (C (C (A 0) (A 1022)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 0xfffc))) (C (A 0) (A 2))))))))

/-- `(gte (lent cs) 4)`. -/
def swWGte : Noun :=
  (C (A 8) (C (C (A 9) (C (A 38) (C (A 0) (A 0x3ffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0x2fbd5) (C (A 0) (A 0x1ffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 4)))))) (C (A 0) (A 2))))))))

/-- The labels `ids` of a tagged chain. -/
def swWTIds : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0xbef7f4) (C (A 0) (A 0x1fffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x1fffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 253)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (C (A 0) swTRBunt))) (C (C (A 1) (C (A 0) (A 222))) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x1fffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0x17defff) (C (A 0) (A 0x1fffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 126))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (C (A 0) swTRBunt))) (C (C (A 1) (C (A 0) (A 110))) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))

/-- The gate of the `+roll` that deletes `ids` from `out` (a tagged chain). -/
def swWTDelG : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffffffff)))) (C (A 9) (C (A 190) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2))))))))

/-- `(roll ids |=([o=@uwoo acc=_out] (~(del by acc) o)))` of a tagged chain. -/
def swWTDel : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0x3fffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (A 1) (A 0)) (C (A 0) (A 2046))) (C (C (A 1) swWTDelG) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))

/-- `cas` of a tagged chain. -/
def swWTCas : Noun :=
  (C (A 8) (C (C (A 0) (A 8190)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x3fffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 254)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (C (A 0) swTRBunt))) (C (C (A 1) (C (A 7) (C (C (A 0) (A 6)) (C (C (A 0) (A 6)) (C (C (A 0) (A 14)) (C (A 0) (A 127))))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2))))))))

/-- A tagged chain from `node`: the tree, the head, the next turn. -/
def swWTFin : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 0) (A 8190)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (C (A 0) (A 126)) (C (C (A 0) (A 30)) (C (C (A 0) (A 14)) (C (A 0) (A 8190))))))) (C (A 0) (A 2)))))))) (C (A 7) (C (C (A 10) (C (C (A 8190) (C (A 0) (A 23))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 8190) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0x3ffe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 126)) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0)) (C (C (C (C (A 1) (A 0x646568)) (C (C (A 0) (A 254)) (C (A 0) (A 126)))) (C (A 0) (A 4))) (C (A 0) (A 10)))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 0x1fffffe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 0xfffffc))) (C (A 0) (A 2)))))))) (C (A 7) (C (C (A 10) (C (C (A 0x3ffe) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1ffffffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7ffe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 0x1fffffc)) (C (A 7) (C (C (A 0) (A 3)) (C (A 10) (C (C (A 7) (C (C (A 1) (A 0x716c63)) (C (C (A 0) (A 510)) (C (C (C (A 1) (A 0)) (C (A 0) (A 126))) (C (C (A 1) (A 0)) (C (A 0) (A 62))))))) (C (A 0) (A 2)))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 0x3ffe) (C (A 0) (A 0xfffffd))) (C (A 0) (A 1023))))))))))))))))

/-- A tagged chain from `done`. -/
def swWTR : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x3fffffffff)))) (C (A 9) (C (A 187) (C (A 10) (C (C (A 6) (C (A 0) (A 2046))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 2046) swWTDel) (C (A 0) (A 1)))) (C (A 8) (C swWTCas swWTFin))))))

/-- A tagged chain, after `?>  ?=(^ cs)`. -/
def swWTag : Noun :=
  (C (A 8) (C (C (A 0) (A 8)) (C (A 8) (C (C (A 0) (A 830)) (C (A 8) (C (C (A 0) (A 926)) (C (A 8) (C (C (A 7) (C (C (A 8) (C (C (A 9) (C (A 0xbef7c) (C (A 0) (A 0xfffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 62))) (C (A 0) (A 2)))))))) (C (A 0) (A 30)))) (C (A 8) (C swWTIds swWTR))))))))))

/-- The gate of the `+roll` that deletes `old` from `out` (a plain chain). -/
def swWPDelG : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffffffff)))) (C (A 9) (C (A 190) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2))))))))

/-- `(roll old |=([o=@uwoo acc=_out] (~(del by acc) o)))` of a plain chain. -/
def swWPDel : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0x1fffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (A 1) (A 0)) (C (A 0) (A 1022))) (C (C (A 1) swWPDelG) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))

/-- `cas` of a plain chain. -/
def swWPCas : Noun :=
  (C (A 8) (C (C (A 0) (A 4094)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x1fffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 62)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) swTRBunt)) (C (C (A 1) (C (A 7) (C (C (A 0) (A 13)) (C (C (A 0) (A 6)) (C (C (A 0) (A 14)) (C (A 0) (A 31))))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2))))))))

/-- `ned` of a plain chain. -/
def swWPNed : Noun :=
  (C (A 8) (C (C (A 9) (C (A 79) (C (A 0) (A 0x7fffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 8) (C (A 0) (A 0x7fffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 2)))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0x2fbd5) (C (A 0) (A 0x3fffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 2)))))) (C (A 0) (A 2))))))))

/-- The trap of `ids` of a plain chain: new labels from `nex`. -/
def swWPIdT : Noun :=
  (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 38) (C (A 0) (A 0x3ffffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0x2fbd5) (C (A 0) (A 0x1ffffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))))) (C (A 0) (A 30)))) (C (A 0) (A 2)))))))) (C (C (C (A 0) (A 6)) (C (A 0) (A 4094))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 4094) (C (A 4) (C (A 0) (A 4094)))) (C (A 10) (C (C (A 6) (C (C (A 0) (A 4094)) (C (A 0) (A 6)))) (C (A 0) (A 1)))))))))))

/-- The test of the `+skip` of a plain chain: an `%imm` into the register of the first test. -/
def swWPSkG : Noun :=
  (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 5) (C (C (A 1) (A 0x6d6d69)) (C (A 0) (A 12)))) (C (A 1) (A 1))))) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 27)) (C (A 0) (A 0x3ff9f)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1)))))

/-- A plain chain from `node`: the tree, the head, the next turn. -/
def swWPNode : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 0) (A 0x3ffe)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 30)) (C (C (A 0) (A 254)) (C (C (A 0) (A 126)) (C (C (A 0) (A 6)) (C (A 0) (A 0x3ffe))))))) (C (A 0) (A 2)))))))) (C (A 7) (C (C (A 10) (C (C (A 0x3ffe) (C (A 0) (A 23))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1ffffffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 0x3fffffe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 0x1fffffc))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0xbef7f5f) (C (A 0) (A 0x3ffffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 26)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0x6d7363) (C (C (C (A 1) (A 0)) (C (A 0) (A 0))) (C (A 0) (C (A 0) (A 0)))))) (C (C (A 1) swWPSkG) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (A 7) (C (C (A 10) (C (C (A 0xfffe) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffffffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0x1fffe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 0x7fffffc)) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 0) (A 12)) (C (C (A 8) (C (C (A 9) (C (A 0xbef7f4) (C (A 0) (A 0x7ffffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 0) (A 60)))) (C (A 0) (A 2)))))))) (C (A 0) (A 58)))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 0x3ffe) (C (A 0) (A 0x3fffffd))) (C (A 0) (A 4095))))))))))))))))

/-- A plain chain from `ids`. -/
def swWPFin : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0x2fbdfd6) (C (A 0) (A 0x7fffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 0) (A 30)))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 1) swWPIdT) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))))) (C (A 7) (C (C (A 10) (C (C (A 2046) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) swWPNode))))))))

/-- A plain chain from `done`. -/
def swWPR : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x1fffffffff)))) (C (A 9) (C (A 187) (C (A 10) (C (C (A 6) (C (A 0) (A 1022))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 1022) swWPDel) (C (A 0) (A 1)))) (C (A 8) (C swWPCas (C (A 8) (C swWPNed swWPFin))))))))

/-- A plain chain, after `?>  ?=(^ ps)`. -/
def swWPB : Noun :=
  (C (A 8) (C (C (A 0) (A 18)) (C (A 8) (C (C (A 7) (C (C (A 8) (C (C (A 9) (C (A 0xbef7c) (C (A 0) (A 0x7ffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 0) (A 62)))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0xfffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 61)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (C (A 1) (C (A 0) (A 12))) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) swWPR))))))

/-- The plain branch of the walk: `ps` and its tests. -/
def swWPlain : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 0) (A 510)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 0x1fffc))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 2399) (C (A 0) (A 0x7ffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0x2fbd5) (C (A 0) (A 0x3ffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 4)))))) (C (A 0) (A 2)))))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 0x3ffe) (C (A 0) (A 0x1fffd))) (C (A 0) (A 7)))))) (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C swWPB (C (A 0) (A 0))))))))))

/-- The walk of `+switch-chains` over `topo`. -/
def swWalk : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 0x3ffe)))) (C (C (A 0) (A 30)) (C (A 6) (C swWHas (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 0x3ffe) (C (A 0) (A 0x7ffd))) (C (A 0) (A 1)))))) (C (A 8) (C swWCs (C (A 6) (C swWGte (C (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C swWTag (C (A 0) (A 0))))) swWPlain)))))))))))

/-- The gate body of `+switch-chains`. -/
def swBodyCut : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 2942) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 732) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 30)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 42) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C swUses (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) swTOB) (C (A 0) (A 1))))) (C (A 8) (C (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) swCHB) (C (A 0) (A 1))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) swPOB) (C (A 0) (A 1))))) (C (A 8) (C (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) swPSB) (C (A 0) (A 1))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) swCSB) (C (A 0) (A 1))))) (C (A 8) (C (C (A 8) (C (C (A 1) swTRBunt) (C (C (A 1) swTRB) (C (A 0) (A 1))))) (C (A 8) (C (C (A 0) (A 4094)) (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C swNex (C (A 8) (C (C (A 1) swWalk) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))))))))))))))))))))))))))))))

/-- The arm `+switch-chains`, cut. -/
def swArmCut : Noun := C (A 7) (C (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) swBodyCut) (C (A 0) (A 1))))) optSwHint)

/-- `+switch-chains` is arm `182` of `optC`. -/
theorem sw_at_cut : slot? 182 optC = some swArmCut := by kernel_rfl

/-- The body read from the pill by `SwitchLink` is `swBodyCut`. -/
theorem swBody_eq : swBody = swBodyCut := by
  unfold swBody swArm
  rw [sw_at_cut]
  rfl

/-! ## The subjects -/

/-- The gate core of `+switch-chains` on the blocks `BL`. -/
def swG (BL : Noun) : Noun := C swBodyCut (C BL optC)

/-- After `uses`: `[uses [rev [topo gate]]]`. -/
def swS3 (BL TOPO REV USES : Noun) : Noun := C USES (C REV (C TOPO (swG BL)))

/-- After `test-of`. -/
def swS4 (BL TOPO REV USES : Noun) : Noun := C (C swTOB (C (A 0) (swS3 BL TOPO REV USES))) (swS3 BL TOPO REV USES)

/-- After `chain-of`. -/
def swS5 (BL TOPO REV USES : Noun) : Noun := C (C swCHB (C (A 0) (swS4 BL TOPO REV USES))) (swS4 BL TOPO REV USES)

/-- After `plain-of`. -/
def swS6 (BL TOPO REV USES : Noun) : Noun := C (C swPOB (C (A 0) (swS5 BL TOPO REV USES))) (swS5 BL TOPO REV USES)

/-- After `plains-of`. -/
def swS7 (BL TOPO REV USES : Noun) : Noun := C (C swPSB (C (A 0) (swS6 BL TOPO REV USES))) (swS6 BL TOPO REV USES)

/-- After `cases`. -/
def swS8 (BL TOPO REV USES : Noun) : Noun := C (C swCSB (C (A 0) (swS7 BL TOPO REV USES))) (swS7 BL TOPO REV USES)

/-- After `tree`. -/
def swS9 (BL TOPO REV USES : Noun) : Noun := C (C swTRB (C swTRBunt (swS8 BL TOPO REV USES))) (swS8 BL TOPO REV USES)

/-- The core of the walk: `[swWalk [nex [done [out after-tree]]]]`. -/
def swW (BL TOPO REV USES OUT DONE NEX : Noun) : Noun :=
  C swWalk (C NEX (C DONE (C OUT (swS9 BL TOPO REV USES))))

/-! ## The nouns of the model's values -/

open SkaModel.Opt in
/-- The noun of a `test`: `[s c hit miss y d r]`. -/
def stestN (t : STest) : Noun := C (A t.s) (C (A t.c) (C (A t.hit) (C (A t.miss) (C (A t.y) (C (A t.d) (A t.r))))))

open SkaModel.Opt in
/-- The noun of a `plain`: `[d c hit miss r]`. -/
def splainN (t : SPlain) : Noun := C (A t.d) (C (A t.c) (C (A t.hit) (C (A t.miss) (A t.r))))

open SkaModel.Opt in
/-- The noun of a plain test with its block: `[p t]`. -/
def spN (x : Nat × SPlain) : Noun := C (A x.1) (splainN x.2)

open SkaModel.Opt in
/-- The noun of a `case`: `[c hit r]`. -/
def scaseN (x : SCase) : Noun := C (A x.c) (C (A x.hit) (A x.r))

end Compiler
end Formalization
