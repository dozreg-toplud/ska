import lemmas.Compiler.CompStraightCore
import lemmas.Compiler.SkaArms

/-!
# `+map-regs` on a block: the gate `mrInner`

`(map-regs ren)` is the gate `mrInner` (slot `1901` of the arm `762` of
`compTypes`) with the context `[mrBody [ren compTypes]]` (`tsRenameG`).  Its
body is `=/  ren-jmp  ..` (the gate `mrRjBody`, built only), then
`:+  (turn par.b ren)  (turn body.b op-gate)  ?-(fin ..)` with `+turn` (arm
`0xbef7e` of `layer2`), the op gate `mrOpBody` (the 25-way `?-` on the op
tags) and the 11-way `?-` on `fin` (`mrFinSw`).

The theorems take any gate `ren = [RB [RS RC]]` whose slam on an atom `r` is
`ren r` (`hren`) and any types core `T` with `layer2` at `32767`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The bunt of the sample of the op gate, `[%csm *bell 0 0 0]`. -/
def mrOpBunt : Noun := C (A 0x6d7363) (C (C (C (A 1) (A 0)) (C (A 0) (A 0))) (C (A 0) (C (A 0) (A 0))))

/-- The body of the gate `ren-jmp`. -/
def mrRjBody : Noun :=
  (C (A 10) (C (C (A 2) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 372) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 254))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 6))))
/-- The body of the gate of the `+turn` over `body.b`: the 25-way `?-` on
the op tags (the last case under `%toss`). -/
def mrOpBody : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6d6d69)) (C (A 0) (A 12)))) (C (C (A 10) (C (C (A 7) (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2))))))))) (C (A 0) (A 6)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x766f6d)) (C (A 0) (A 12)))) (C (C (A 10) (C (C (A 3) (C (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 58))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2)))))))))) (C (A 0) (A 6)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x636e69)) (C (A 0) (A 12)))) (C (C (A 10) (C (C (A 3) (C (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 58))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2)))))))))) (C (A 0) (A 6)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6e6f63)) (C (A 0) (A 12)))) (C (C (A 10) (C (C (A 3) (C (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 58))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 118))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 119))) (C (A 0) (A 2))))))))))) (C (A 0) (A 6)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x646568)) (C (A 0) (A 12)))) (C (C (A 10) (C (C (A 3) (C (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 58))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2)))))))))) (C (A 0) (A 6)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6c6174)) (C (A 0) (A 12)))) (C (C (A 10) (C (C (A 3) (C (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 58))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2)))))))))) (C (A 0) (A 6)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6c6563)) (C (A 0) (A 12)))) (C (C (A 10) (C (C (A 3) (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2))))))))) (C (A 0) (A 6)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x626f6c)) (C (A 0) (A 12)))) (C (C (A 10) (C (C (A 3) (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2))))))))) (C (A 0) (A 6)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x757165)) (C (A 0) (A 12)))) (C (C (A 10) (C (C (A 3) (C (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 58))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2)))))))))) (C (A 0) (A 6)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x707368)) (C (A 0) (A 12)))) (C (C (A 0) (A 6)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x657368)) (C (A 0) (A 12)))) (C (C (A 0) (A 6)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706468)) (C (A 0) (A 12)))) (C (C (A 10) (C (C (A 14) (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 118))) (C (A 0) (A 2))))))))) (C (A 0) (A 6)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656468)) (C (A 0) (A 12)))) (C (C (A 10) (C (C (A 14) (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 118))) (C (A 0) (A 2))))))))) (C (A 0) (A 6)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706d68)) (C (A 0) (A 12)))) (C (C (A 10) (C (C (A 14) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 118)) (C (A 0) (A 510)))) (C (A 0) (A 2))))))))) (C (A 0) (A 6)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656d68)) (C (A 0) (A 12)))) (C (C (A 10) (C (C (A 14) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 118)) (C (A 0) (A 510)))) (C (A 0) (A 2))))))))) (C (A 0) (A 6)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706368)) (C (A 0) (A 12)))) (C (C (A 0) (A 6)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656368)) (C (A 0) (A 12)))) (C (C (A 0) (A 6)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x797073)) (C (A 0) (A 12)))) (C (C (A 10) (C (C (A 3) (C (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 58))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 118))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 119))) (C (A 0) (A 2))))))))))) (C (A 0) (A 6)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6b6f6e)) (C (A 0) (A 12)))) (C (C (A 10) (C (C (A 3) (C (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 58))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 118))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 119))) (C (A 0) (A 2))))))))))) (C (A 0) (A 6)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6c6163)) (C (A 0) (A 12)))) (C (C (A 10) (C (C (A 7) (C (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 118)) (C (A 0) (A 510)))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 119))) (C (A 0) (A 2)))))))))) (C (A 0) (A 6)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x666163)) (C (A 0) (A 12)))) (C (C (A 10) (C (C (A 30) (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 238))) (C (A 0) (A 2))))))))) (C (A 10) (C (C (A 14) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 118)) (C (A 0) (A 510)))) (C (A 0) (A 2))))))))) (C (A 0) (A 6)))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6d6163)) (C (A 0) (A 12)))) (C (C (A 10) (C (C (A 30) (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 238))) (C (A 0) (A 2))))))))) (C (A 10) (C (C (A 14) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 118)) (C (A 0) (A 510)))) (C (A 0) (A 2))))))))) (C (A 0) (A 6)))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6c7363)) (C (A 0) (A 12)))) (C (C (A 10) (C (C (A 7) (C (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 118))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 119))) (C (A 0) (A 2)))))))))) (C (A 0) (A 6)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x667363)) (C (A 0) (A 12)))) (C (C (A 10) (C (C (A 30) (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 238))) (C (A 0) (A 2))))))))) (C (A 10) (C (C (A 14) (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 118))) (C (A 0) (A 2))))))))) (C (A 0) (A 6)))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x6d7363)) (C (A 0) (A 12))))) (C (A 10) (C (C (A 30) (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 238))) (C (A 0) (A 2))))))))) (C (A 10) (C (C (A 14) (C (A 8) (C (C (A 0) (A 254)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 118))) (C (A 0) (A 2))))))))) (C (A 0) (A 6))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
/-- The 11-way `?-` on `fin` (the last case `%bom` under `%toss`). -/
def mrFinSw : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x716c63)) (C (A 0) (A 4)))) (C (C (A 10) (C (C (A 3) (C (C (A 8) (C (C (A 0) (A 126)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 26))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 0) (A 6)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 54))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 6)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 55))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x717165)) (C (A 0) (A 4)))) (C (C (A 10) (C (C (A 3) (C (C (A 8) (C (C (A 0) (A 126)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 26))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 0) (A 126)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 54))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 0) (A 6)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 110))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 6)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 111))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6e7262)) (C (A 0) (A 4)))) (C (C (A 10) (C (C (A 3) (C (C (A 8) (C (C (A 0) (A 126)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 26))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 0) (A 6)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 54))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 6)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 55))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x7a7262)) (C (A 0) (A 4)))) (C (C (A 10) (C (C (A 3) (C (C (A 8) (C (C (A 0) (A 126)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 26))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 0) (A 6)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 54))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 6)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 55))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706f68)) (C (A 0) (A 4)))) (C (C (A 10) (C (C (A 3) (C (A 8) (C (C (A 0) (A 6)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 13))) (C (A 0) (A 2))))))))) (C (A 0) (A 2)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706d6a)) (C (A 0) (A 4)))) (C (C (A 10) (C (C (A 7) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 27)) (C (A 0) (A 254)))) (C (A 0) (A 2))))))))) (C (A 0) (A 2)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x666d6a)) (C (A 0) (A 4)))) (C (C (A 10) (C (C (A 14) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 54)) (C (A 0) (A 254)))) (C (A 0) (A 2))))))))) (C (A 0) (A 2)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x70736a)) (C (A 0) (A 4)))) (C (C (A 10) (C (C (A 7) (C (A 8) (C (C (A 0) (A 126)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 27))) (C (A 0) (A 2))))))))) (C (A 0) (A 2)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x66736a)) (C (A 0) (A 4)))) (C (C (A 10) (C (C (A 14) (C (A 8) (C (C (A 0) (A 126)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 54))) (C (A 0) (A 2))))))))) (C (A 0) (A 2)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6e6f64)) (C (A 0) (A 4)))) (C (C (A 10) (C (C (A 3) (C (A 8) (C (C (A 0) (A 126)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 13))) (C (A 0) (A 2))))))))) (C (A 0) (A 2)))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x6d6f62)) (C (A 0) (A 4))))) (C (A 0) (A 2))))))))))))))))))))))))))))))))))
/-- **The gate `mrInner` of `+map-regs`** cut into its parts, a kernel fact. -/
theorem mr_inner_eq : mrInner = (C (A 8) (C (C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (C (A 1) mrRjBody) (C (A 0) (A 1))))) (C (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 60)) (C (A 0) (A 126)))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 122)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) mrOpBunt) (C (C (A 1) mrOpBody) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 59)) mrFinSw)))))) := by
  kernel_rfl

/-- `layer2` in the types core. -/
theorem mr_types_layer2 : slot? 32767 compTypes = some layer2 := by
  have h : slot? 7 compTypes = slot? 1 ana := rfl
  have := slot_spine (by omega) (by omega) h 12
  simp only [show 2 ^ 12 * (7 + 1) - 1 = 32767 from rfl,
    show 2 ^ 12 * (1 + 1) - 1 = 8191 from rfl] at this
  rw [this]
  exact ana_layer2

/-- The renaming of an atom, the identity on cells. -/
def renN (ren : Nat → Nat) : Noun → Noun
  | Noun.atom r => A (ren r)
  | x => x

/-- **`+turn` with the gate `ren`** over a list of registers. -/
theorem mr_turn_ren (RB RS RC : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r))) (v : List Nat) :
    nock (C turn.battery (C (C (listNoun A v) (C RB (C RS RC))) layer2)) turn.battery
      = some (listNoun A (v.map ren)) := by
  rw [listNoun_map_listN, listNoun_map_listN]
  rw [turn_gate layer2 homoIn_layer2 RB RS RC (renN ren) (v.map A) (by
    intro x hx
    obtain ⟨r, _, rfl⟩ := List.mem_map.1 hx
    simp [renN, hren])]
  simp [List.map_map, Function.comp_def, renN]

/-- The subject of the op gate after its sample: `ren-jmp`, the gate core of
`mrInner` with the block `bN`, `mrBody`, `ren` and the types core `T`. -/
def mrS (RJ I bN MB RB RS RC T : Noun) : Noun := C RJ (C I (C bN (C MB (C (C RB (C RS RC)) T))))

-- BEGIN mrops
theorem mr_op_imm (X RJ I bN MB RB RS RC T : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r)))
    (hT : slot? 32767 T = some layer2) (n : Noun) (d : Nat) :
    nock (C X (C (Pole.toNoun (Pole.imm n d)) (mrS RJ I bN MB RB RS RC T))) mrOpBody
      = some (Pole.toNoun (renPole ren (Pole.imm n d))) := by
  simp [nock_exec, mrS, mrOpBody, Pole.toNoun, renPole, Tag.imm, hren]

theorem mr_op_mov (X RJ I bN MB RB RS RC T : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r)))
    (hT : slot? 32767 T = some layer2) (s d : Nat) :
    nock (C X (C (Pole.toNoun (Pole.mov s d)) (mrS RJ I bN MB RB RS RC T))) mrOpBody
      = some (Pole.toNoun (renPole ren (Pole.mov s d))) := by
  simp [nock_exec, mrS, mrOpBody, Pole.toNoun, renPole, Tag.mov, hren]

theorem mr_op_inc (X RJ I bN MB RB RS RC T : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r)))
    (hT : slot? 32767 T = some layer2) (s d : Nat) :
    nock (C X (C (Pole.toNoun (Pole.inc s d)) (mrS RJ I bN MB RB RS RC T))) mrOpBody
      = some (Pole.toNoun (renPole ren (Pole.inc s d))) := by
  simp [nock_exec, mrS, mrOpBody, Pole.toNoun, renPole, Tag.inc, hren]

theorem mr_op_con (X RJ I bN MB RB RS RC T : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r)))
    (hT : slot? 32767 T = some layer2) (h t d : Nat) :
    nock (C X (C (Pole.toNoun (Pole.con h t d)) (mrS RJ I bN MB RB RS RC T))) mrOpBody
      = some (Pole.toNoun (renPole ren (Pole.con h t d))) := by
  simp [nock_exec, mrS, mrOpBody, Pole.toNoun, renPole, Tag.con, hren]

theorem mr_op_hed (X RJ I bN MB RB RS RC T : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r)))
    (hT : slot? 32767 T = some layer2) (s d : Nat) :
    nock (C X (C (Pole.toNoun (Pole.hed s d)) (mrS RJ I bN MB RB RS RC T))) mrOpBody
      = some (Pole.toNoun (renPole ren (Pole.hed s d))) := by
  simp [nock_exec, mrS, mrOpBody, Pole.toNoun, renPole, Tag.hed, hren]

theorem mr_op_tal (X RJ I bN MB RB RS RC T : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r)))
    (hT : slot? 32767 T = some layer2) (s d : Nat) :
    nock (C X (C (Pole.toNoun (Pole.tal s d)) (mrS RJ I bN MB RB RS RC T))) mrOpBody
      = some (Pole.toNoun (renPole ren (Pole.tal s d))) := by
  simp [nock_exec, mrS, mrOpBody, Pole.toNoun, renPole, Tag.tal, hren]

theorem mr_op_cel (X RJ I bN MB RB RS RC T : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r)))
    (hT : slot? 32767 T = some layer2) (p : Nat) :
    nock (C X (C (Pole.toNoun (Pole.cel p)) (mrS RJ I bN MB RB RS RC T))) mrOpBody
      = some (Pole.toNoun (renPole ren (Pole.cel p))) := by
  simp [nock_exec, mrS, mrOpBody, Pole.toNoun, renPole, Tag.cel, hren]

theorem mr_op_lob (X RJ I bN MB RB RS RC T : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r)))
    (hT : slot? 32767 T = some layer2) (p : Nat) :
    nock (C X (C (Pole.toNoun (Pole.lob p)) (mrS RJ I bN MB RB RS RC T))) mrOpBody
      = some (Pole.toNoun (renPole ren (Pole.lob p))) := by
  simp [nock_exec, mrS, mrOpBody, Pole.toNoun, renPole, Tag.lob, hren]

theorem mr_op_equ (X RJ I bN MB RB RS RC T : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r)))
    (hT : slot? 32767 T = some layer2) (l r : Nat) :
    nock (C X (C (Pole.toNoun (Pole.equ l r)) (mrS RJ I bN MB RB RS RC T))) mrOpBody
      = some (Pole.toNoun (renPole ren (Pole.equ l r))) := by
  simp [nock_exec, mrS, mrOpBody, Pole.toNoun, renPole, Tag.equ, hren]

theorem mr_op_hsp (X RJ I bN MB RB RS RC T : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r)))
    (hT : slot? 32767 T = some layer2) (n : Nat) (f : Noun) :
    nock (C X (C (Pole.toNoun (Pole.hsp n f)) (mrS RJ I bN MB RB RS RC T))) mrOpBody
      = some (Pole.toNoun (renPole ren (Pole.hsp n f))) := by
  simp [nock_exec, mrS, mrOpBody, Pole.toNoun, renPole, Tag.hsp, hren]

theorem mr_op_hse (X RJ I bN MB RB RS RC T : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r)))
    (hT : slot? 32767 T = some layer2) (n : Nat) (f : Noun) :
    nock (C X (C (Pole.toNoun (Pole.hse n f)) (mrS RJ I bN MB RB RS RC T))) mrOpBody
      = some (Pole.toNoun (renPole ren (Pole.hse n f))) := by
  simp [nock_exec, mrS, mrOpBody, Pole.toNoun, renPole, Tag.hse, hren]

theorem mr_op_hdp (X RJ I bN MB RB RS RC T : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r)))
    (hT : slot? 32767 T = some layer2) (n p : Nat) (f : Noun) :
    nock (C X (C (Pole.toNoun (Pole.hdp n p f)) (mrS RJ I bN MB RB RS RC T))) mrOpBody
      = some (Pole.toNoun (renPole ren (Pole.hdp n p f))) := by
  simp [nock_exec, mrS, mrOpBody, Pole.toNoun, renPole, Tag.hdp, hren]

theorem mr_op_hde (X RJ I bN MB RB RS RC T : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r)))
    (hT : slot? 32767 T = some layer2) (n p : Nat) (f : Noun) :
    nock (C X (C (Pole.toNoun (Pole.hde n p f)) (mrS RJ I bN MB RB RS RC T))) mrOpBody
      = some (Pole.toNoun (renPole ren (Pole.hde n p f))) := by
  simp [nock_exec, mrS, mrOpBody, Pole.toNoun, renPole, Tag.hde, hren]

theorem mr_op_hmp (X RJ I bN MB RB RS RC T : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r)))
    (hT : slot? 32767 T = some layer2) (a : Bell) (v : List Nat) (f : Noun) :
    nock (C X (C (Pole.toNoun (Pole.hmp a v f)) (mrS RJ I bN MB RB RS RC T))) mrOpBody
      = some (Pole.toNoun (renPole ren (Pole.hmp a v f))) := by
  have ht := mr_turn_ren RB RS RC ren hren v
  simp [nock_exec, mrS, mrOpBody, Pole.toNoun, renPole, Tag.hmp, hren, hT, turn.arm_at, ht]

theorem mr_op_hme (X RJ I bN MB RB RS RC T : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r)))
    (hT : slot? 32767 T = some layer2) (a : Bell) (v : List Nat) (f : Noun) :
    nock (C X (C (Pole.toNoun (Pole.hme a v f)) (mrS RJ I bN MB RB RS RC T))) mrOpBody
      = some (Pole.toNoun (renPole ren (Pole.hme a v f))) := by
  have ht := mr_turn_ren RB RS RC ren hren v
  simp [nock_exec, mrS, mrOpBody, Pole.toNoun, renPole, Tag.hme, hren, hT, turn.arm_at, ht]

theorem mr_op_hcp (X RJ I bN MB RB RS RC T : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r)))
    (hT : slot? 32767 T = some layer2) (n f : Noun) :
    nock (C X (C (Pole.toNoun (Pole.hcp n f)) (mrS RJ I bN MB RB RS RC T))) mrOpBody
      = some (Pole.toNoun (renPole ren (Pole.hcp n f))) := by
  simp [nock_exec, mrS, mrOpBody, Pole.toNoun, renPole, Tag.hcp, hren]

theorem mr_op_hce (X RJ I bN MB RB RS RC T : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r)))
    (hT : slot? 32767 T = some layer2) (n f : Noun) :
    nock (C X (C (Pole.toNoun (Pole.hce n f)) (mrS RJ I bN MB RB RS RC T))) mrOpBody
      = some (Pole.toNoun (renPole ren (Pole.hce n f))) := by
  simp [nock_exec, mrS, mrOpBody, Pole.toNoun, renPole, Tag.hce, hren]

theorem mr_op_spy (X RJ I bN MB RB RS RC T : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r)))
    (hT : slot? 32767 T = some layer2) (e p d : Nat) :
    nock (C X (C (Pole.toNoun (Pole.spy e p d)) (mrS RJ I bN MB RB RS RC T))) mrOpBody
      = some (Pole.toNoun (renPole ren (Pole.spy e p d))) := by
  simp [nock_exec, mrS, mrOpBody, Pole.toNoun, renPole, Tag.spy, hren]

theorem mr_op_nok (X RJ I bN MB RB RS RC T : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r)))
    (hT : slot? 32767 T = some layer2) (u f d : Nat) :
    nock (C X (C (Pole.toNoun (Pole.nok u f d)) (mrS RJ I bN MB RB RS RC T))) mrOpBody
      = some (Pole.toNoun (renPole ren (Pole.nok u f d))) := by
  simp [nock_exec, mrS, mrOpBody, Pole.toNoun, renPole, Tag.nok, hren]

theorem mr_op_cal (X RJ I bN MB RB RS RC T : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r)))
    (hT : slot? 32767 T = some layer2) (a : Bell) (v : List Nat) (d : Nat) :
    nock (C X (C (Pole.toNoun (Pole.cal a v d)) (mrS RJ I bN MB RB RS RC T))) mrOpBody
      = some (Pole.toNoun (renPole ren (Pole.cal a v d))) := by
  have ht := mr_turn_ren RB RS RC ren hren v
  simp [nock_exec, mrS, mrOpBody, Pole.toNoun, renPole, Tag.cal, hren, hT, turn.arm_at, ht]

theorem mr_op_caf (X RJ I bN MB RB RS RC T : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r)))
    (hT : slot? 32767 T = some layer2) (a : Bell) (v : List Nat) (d : Nat) (n : Ring) :
    nock (C X (C (Pole.toNoun (Pole.caf a v d n)) (mrS RJ I bN MB RB RS RC T))) mrOpBody
      = some (Pole.toNoun (renPole ren (Pole.caf a v d n))) := by
  have ht := mr_turn_ren RB RS RC ren hren v
  simp [nock_exec, mrS, mrOpBody, Pole.toNoun, renPole, Tag.caf, hren, hT, turn.arm_at, ht]

theorem mr_op_cam (X RJ I bN MB RB RS RC T : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r)))
    (hT : slot? 32767 T = some layer2) (a : Bell) (v : List Nat) (d : Nat) (k : Noun) :
    nock (C X (C (Pole.toNoun (Pole.cam a v d k)) (mrS RJ I bN MB RB RS RC T))) mrOpBody
      = some (Pole.toNoun (renPole ren (Pole.cam a v d k))) := by
  have ht := mr_turn_ren RB RS RC ren hren v
  simp [nock_exec, mrS, mrOpBody, Pole.toNoun, renPole, Tag.cam, hren, hT, turn.arm_at, ht]

theorem mr_op_csl (X RJ I bN MB RB RS RC T : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r)))
    (hT : slot? 32767 T = some layer2) (a : Bell) (s d : Nat) :
    nock (C X (C (Pole.toNoun (Pole.csl a s d)) (mrS RJ I bN MB RB RS RC T))) mrOpBody
      = some (Pole.toNoun (renPole ren (Pole.csl a s d))) := by
  simp [nock_exec, mrS, mrOpBody, Pole.toNoun, renPole, Tag.csl, hren]

theorem mr_op_csf (X RJ I bN MB RB RS RC T : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r)))
    (hT : slot? 32767 T = some layer2) (a : Bell) (s d : Nat) (n : Ring) :
    nock (C X (C (Pole.toNoun (Pole.csf a s d n)) (mrS RJ I bN MB RB RS RC T))) mrOpBody
      = some (Pole.toNoun (renPole ren (Pole.csf a s d n))) := by
  simp [nock_exec, mrS, mrOpBody, Pole.toNoun, renPole, Tag.csf, hren]

theorem mr_op_csm (X RJ I bN MB RB RS RC T : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r)))
    (hT : slot? 32767 T = some layer2) (a : Bell) (s d : Nat) (k : Noun) :
    nock (C X (C (Pole.toNoun (Pole.csm a s d k)) (mrS RJ I bN MB RB RS RC T))) mrOpBody
      = some (Pole.toNoun (renPole ren (Pole.csm a s d k))) := by
  simp [nock_exec, mrS, mrOpBody, Pole.toNoun, renPole, Tag.csm, hren]

/-- **The op gate of `+map-regs`** on any op: `renPole ren op`. -/
theorem mr_op (X RJ I bN MB RB RS RC T : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r)))
    (hT : slot? 32767 T = some layer2) (op : Pole) :
    nock (C X (C (Pole.toNoun op) (mrS RJ I bN MB RB RS RC T))) mrOpBody
      = some (Pole.toNoun (renPole ren op)) := by
  cases op with
  | imm n d => exact mr_op_imm X RJ I bN MB RB RS RC T ren hren hT n d
  | mov s d => exact mr_op_mov X RJ I bN MB RB RS RC T ren hren hT s d
  | inc s d => exact mr_op_inc X RJ I bN MB RB RS RC T ren hren hT s d
  | con h t d => exact mr_op_con X RJ I bN MB RB RS RC T ren hren hT h t d
  | hed s d => exact mr_op_hed X RJ I bN MB RB RS RC T ren hren hT s d
  | tal s d => exact mr_op_tal X RJ I bN MB RB RS RC T ren hren hT s d
  | cel p => exact mr_op_cel X RJ I bN MB RB RS RC T ren hren hT p
  | lob p => exact mr_op_lob X RJ I bN MB RB RS RC T ren hren hT p
  | equ l r => exact mr_op_equ X RJ I bN MB RB RS RC T ren hren hT l r
  | hsp n f => exact mr_op_hsp X RJ I bN MB RB RS RC T ren hren hT n f
  | hse n f => exact mr_op_hse X RJ I bN MB RB RS RC T ren hren hT n f
  | hdp n p f => exact mr_op_hdp X RJ I bN MB RB RS RC T ren hren hT n p f
  | hde n p f => exact mr_op_hde X RJ I bN MB RB RS RC T ren hren hT n p f
  | hmp a v f => exact mr_op_hmp X RJ I bN MB RB RS RC T ren hren hT a v f
  | hme a v f => exact mr_op_hme X RJ I bN MB RB RS RC T ren hren hT a v f
  | hcp n f => exact mr_op_hcp X RJ I bN MB RB RS RC T ren hren hT n f
  | hce n f => exact mr_op_hce X RJ I bN MB RB RS RC T ren hren hT n f
  | spy e p d => exact mr_op_spy X RJ I bN MB RB RS RC T ren hren hT e p d
  | nok u f d => exact mr_op_nok X RJ I bN MB RB RS RC T ren hren hT u f d
  | cal a v d => exact mr_op_cal X RJ I bN MB RB RS RC T ren hren hT a v d
  | caf a v d n => exact mr_op_caf X RJ I bN MB RB RS RC T ren hren hT a v d n
  | cam a v d k => exact mr_op_cam X RJ I bN MB RB RS RC T ren hren hT a v d k
  | csl a s d => exact mr_op_csl X RJ I bN MB RB RS RC T ren hren hT a s d
  | csf a s d n => exact mr_op_csf X RJ I bN MB RB RS RC T ren hren hT a s d n
  | csm a s d k => exact mr_op_csm X RJ I bN MB RB RS RC T ren hren hT a s d k
-- END mrops


/-- **`+turn` with the op gate** over the body of a block. -/
theorem mr_turn_ops (RJ I bN MB RB RS RC T : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r)))
    (hT : slot? 32767 T = some layer2) (body : List Pole) :
    nock (C turn.battery (C (C (listNoun Pole.toNoun body)
        (C mrOpBody (C mrOpBunt (C RJ (C I (C bN (C MB (C (C RB (C RS RC)) T)))))))) layer2)) turn.battery
      = some (listNoun Pole.toNoun (body.map (renPole ren))) := by
  rw [listNoun_map_listN, listNoun_map_listN,
    show C RJ (C I (C bN (C MB (C (C RB (C RS RC)) T)))) = mrS RJ I bN MB RB RS RC T from rfl]
  rw [turn_gate_mapM layer2 homoIn_layer2 mrOpBody mrOpBunt (mrS RJ I bN MB RB RS RC T)
    (fun x => nock (C mrOpBody (C x (mrS RJ I bN MB RB RS RC T))) mrOpBody) _ (fun _ _ => rfl)]
  have h : ∀ L : List Pole, (L.map Pole.toNoun).mapM
      (fun x => nock (C mrOpBody (C x (mrS RJ I bN MB RB RS RC T))) mrOpBody)
      = some ((L.map (renPole ren)).map Pole.toNoun) := by
    intro L
    induction L with
    | nil => rfl
    | cons op L ih =>
      simp only [List.map_cons, List.mapM_cons, mr_op mrOpBody RJ I bN MB RB RS RC T ren hren hT op, ih]
      rfl
  rw [h]; rfl

/-- **`(map-regs ren)` on a block with `fin` `[%bom ~]`**: the parameters
and the body renamed, `fin` kept. -/
theorem mr_inner_bom (X MB RB RS RC T : Noun) (ren : Nat → Nat)
    (hren : ∀ r, nock (C RB (C (A r) RC)) RB = some (A (ren r)))
    (hT : slot? 32767 T = some layer2) (par : List Nat) (body : List Pole) :
    nock (C X (C (Blob.toNoun ⟨par, body, Termin.bom Option.none⟩) (C MB (C (C RB (C RS RC)) T)))) mrInner
      = some (Blob.toNoun ⟨par.map ren, body.map (renPole ren), Termin.bom Option.none⟩) := by
  have hp := mr_turn_ren RB RS RC ren hren par
  have hb := fun RJ bN => mr_turn_ops RJ X bN MB RB RS RC T ren hren hT body
  rw [mr_inner_eq]
  generalize mrRjBody = RJB
  simp [nock_exec, Blob.toNoun, Termin.toNoun, unitNoun, Tag.bom, hT, turn.arm_at, hp, hb, mrFinSw]

end Compiler
end Formalization
