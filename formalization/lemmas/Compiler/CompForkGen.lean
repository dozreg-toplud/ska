import lemmas.Compiler.CompRunSixNext

/-!
# `+fork`: the cut of its battery

`+fork` (door arm `862`, hinted `%comp-fork`) is

    =^  o-0  gen  oo
    =^  o-1  gen  oo
    =;  [[laz-0 laz-1] gen1]  ..  [[%next laz-0 ~ o-0] [%next laz-1 ~ o-1]]
    =/  laz  laz.nex
    =/  o  there.then.nex
    ?>  =(~ args.then.nex)
    |-  fork-loop ..

Its battery is cut into `fkBatS` with the trap `fkLoop` named, and the trap
with the gates of its two `+spin-split` named, `fkGF` (forks) and `fkGB`
(bonds); `fk_at` checks the cut by the kernel.  The trap's subject is
`fkTS`: `[fkLoop [o [laz [o-1 [o-0 [fkBat [[nex r-cond] [door [gen
ctx]]]]]]]]]`, with `laz` at `14`, `o` at `6`, `o-0` at `62`, `o-1` at `30`,
the door core at `255` and `gen` at `510`; the recursive calls in the gates
edit those four axes of the trap core (`%=  fork-loop  ..`).  The model is
`forkL`, `forkLoop`, `forkForks`, `forkBonds` of `Ska/CompLazyRun.lean`.
`comp_fork_head`: the arm from the trap's result on (`+oo` twice, the
assert, the goals) is `forkL`, given the link of the trap.  The trap and
its gates are not linked yet (README Gaps 9).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

/-- The gate of the `+spin-split` over the forks (the trap `fork-loop` on the
yes and no needs, `+proxy`, `+emit` of the `%brz` blocks, `+insert-hop`). -/
def fkGF : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 7) (C (C (A 10) (C (C (A 8190) (C (A 0) (A 13))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 5460) (C (A 0) (A 2047)))))) (C (A 7) (C (C (A 10) (C (C (A 0x3ffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 5460) (C (A 0) (A 4095)))))) (C (A 7) (C (C (A 10) (C (C (A 0x7ffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 5460) (C (A 0) (A 8191)))))) (C (A 7) (C (C (A 10) (C (C (A 0xfffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 5460) (C (A 0) (A 0x3fff)))))) (C (A 7) (C (C (A 10) (C (C (A 0x1fffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 5460) (C (A 0) (A 0x7fff)))))) (C (A 7) (C (C (A 10) (C (C (A 0x3fffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 5460) (C (A 0) (A 0xffff)))))) (C (A 7) (C (C (A 10) (C (C (A 0x7fffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 10) (C (C (A 0x7fffe) (C (A 8) (C (C (A 9) (C (A 0x2afffc) (C (A 0) (A 0x1ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 8176)) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 0) (A 126)) (C (C (A 0) (A 62)) (C (A 1) (A 0)))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 0x7fffe) (C (A 8) (C (C (A 9) (C (A 0x2afffc) (C (A 0) (A 0x1ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 8178)) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 0) (A 30)) (C (C (A 0) (A 14)) (C (A 1) (A 0)))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 62) (C (A 0) (A 126))) (C (A 10) (C (C (A 30) (C (A 0) (A 62))) (C (A 10) (C (C (A 14) (C (A 0) (A 4081))) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 1023)))))))))))))) (C (A 7) (C (C (A 10) (C (C (A 0xffffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 62) (C (A 0) (A 62))) (C (A 10) (C (C (A 30) (C (A 0) (A 30))) (C (A 10) (C (C (A 14) (C (A 0) (A 8179))) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2047)))))))))))))) (C (A 7) (C (C (A 10) (C (C (A 0x1ffffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xabb5a) (C (A 0) (A 0x7ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 0x1ffffd)) (C (A 0) (A 0x7ff0)))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 0x3ffffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xabb5a) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 0x3ffffd)) (C (A 0) (A 0xfff2)))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 0x7ffffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0x7a7262)) (C (C (A 0) (A 6)) (C (C (C (A 1) (A 0)) (C (A 0) (A 2046))) (C (C (A 1) (A 0)) (C (A 0) (A 1022))))))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 0xfffffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0x7a7262)) (C (C (A 0) (A 6)) (C (C (C (A 1) (A 0)) (C (A 0) (A 1022))) (C (C (A 1) (A 0)) (C (A 0) (A 510))))))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 0x1fffffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 10) (C (C (A 0x1fffffe) (C (A 8) (C (C (A 9) (C (A 4) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 0x7fff0)) (C (C (A 0) (A 14)) (C (A 0) (A 1022))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 0x1fffffe) (C (A 8) (C (C (A 9) (C (A 4) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 0x7fff2)) (C (C (A 0) (A 6)) (C (A 0) (A 510))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (C (C (C (C (A 0) (A 8190)) (C (A 0) (A 252))) (C (C (A 0) (A 2046)) (C (A 0) (A 124)))) (C (C (C (A 0) (A 4094)) (C (A 0) (A 253))) (C (C (A 0) (A 1022)) (C (A 0) (A 125))))) (C (A 0) (A 0x1fffffe)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- The gate of the `+spin-split` over the bonds. -/
def fkGB : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 0x3ffe) (C (A 0) (A 13))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 5460) (C (A 0) (A 4095)))))) (C (A 7) (C (C (A 10) (C (C (A 0x7ffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 5460) (C (A 0) (A 8191)))))) (C (A 7) (C (C (A 10) (C (C (A 0xfffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 5460) (C (A 0) (A 0x3fff)))))) (C (A 7) (C (C (A 10) (C (C (A 0x1fffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 10) (C (C (A 0x1fffe) (C (A 8) (C (C (A 9) (C (A 0x2afffc) (C (A 0) (A 0x7fff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 504)) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 0) (A 14)) (C (C (A 0) (A 6)) (C (A 1) (A 0)))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 62) (C (A 0) (A 14))) (C (A 10) (C (C (A 30) (C (A 0) (A 6))) (C (A 10) (C (C (A 14) (C (A 0) (A 249))) (C (A 10) (C (C (A 6) (C (A 0) (A 2))) (C (A 0) (A 255)))))))))))))) (C (A 7) (C (C (A 10) (C (C (A 0x3fffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xabb5a) (C (A 0) (A 0xffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 0x3fffd)) (C (A 0) (A 1016)))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 0x7fffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 0x1ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0x7a7262)) (C (C (A 0) (A 2)) (C (C (C (A 1) (A 0)) (C (A 0) (A 62))) (C (C (A 1) (A 0)) (C (A 0) (A 30))))))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 0xffffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 10) (C (C (A 0xffffe) (C (A 8) (C (C (A 9) (C (A 4) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 4088)) (C (C (A 0) (A 6)) (C (A 0) (A 62))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (C (C (C (A 0) (A 126)) (C (A 0) (A 28))) (C (C (A 0) (A 62)) (C (A 0) (A 29)))) (C (A 0) (A 0xffffe)))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- The trap `fork-loop`: `+fork-sure`, the spin over the forks, the spin
over the bonds, the two needs. -/
def fkLoop : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x157ff7) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 60)) (C (C (A 0) (A 14)) (C (C (A 0) (A 126)) (C (A 0) (A 62)))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 2046) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 372) (C (A 0) (A 8191)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 250)) (C (C (A 0) (A 4094)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (C (C (A 1) (A 0)) (C (A 7) (C (C (A 9) (C (A 191) (C (A 0) (A 0x3fff)))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))) (C (C (A 1) (A 0)) (C (A 7) (C (C (A 9) (C (A 191) (C (A 0) (A 0x3fff)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))) (C (A 0) (A 2046))) (C (C (A 1) fkGF) (C (A 0) (A 1)))))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 4094) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 372) (C (A 0) (A 0x3fff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 507)) (C (C (A 0) (A 8190)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (C (A 1) (A 0)) (C (A 7) (C (C (A 9) (C (A 191) (C (A 0) (A 0x7fff)))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))) (C (A 0) (A 4094))) (C (C (A 1) fkGB) (C (A 0) (A 1)))))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 8190) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (C (A 0) (A 28)) (C (C (A 0) (A 12)) (C (A 0) (A 4)))) (C (C (A 0) (A 29)) (C (C (A 0) (A 13)) (C (A 0) (A 5))))) (C (A 0) (A 8190)))))))))))))))))))))))))))))))))

/-- The battery of `+fork` (door arm `862`) with the trap named. -/
def fkBatS : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 5460) (C (A 0) (A 7)))))) (C (A 7) (C (C (A 10) (C (C (A 62) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 5460) (C (A 0) (A 15)))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 8) (C (C (A 0) (A 242)) (C (A 8) (C (C (A 0) (A 999)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2022)))) (C (C (A 8) (C (C (A 1) fkLoop) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (A 0) (A 0))))))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (C (C (C (A 1) (A 0x7478656e)) (C (C (A 0) (A 8)) (C (C (A 1) (A 0)) (C (A 0) (A 14))))) (C (C (A 1) (A 0x7478656e)) (C (C (A 0) (A 9)) (C (C (A 1) (A 0)) (C (A 0) (A 6)))))) (C (A 0) (A 254)))))))))))))))))))))))

def fkBunt : Noun :=
  (C (C (A 0x7478656e) (C (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))) (C (A 0) (A 0)))) (A 0))

def fkArm : Noun :=
  C (A 7) (C (C (A 8) (C (C (A 1) fkBunt) (C (C (A 1) fkBatS) (C (A 0) (A 1))))) (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x6b726f662d706d6f63) (C (C (A 0) (A 0x7ffff)) (A 0))))) (C (A 0) (A 1)))))

/-- **The cut of `+fork`** is the pill's (door arm `862`). -/
theorem fk_at : slot? 862 comp.door = some fkArm := by kernel_rfl

theorem fk_arm (d : Noun) : nock d fkArm = some (C fkBatS (C fkBunt d)) := by
  unfold fkArm; simp only [nock_exec]

/-- The subject of the trap `fork-loop`. -/
def fkTS (o : Nat) (L : Noun) (o1 o0 : Nat) (NR D : Noun) : Noun :=
  C fkLoop (C (A o) (C L (C (A o1) (C (A o0) (C fkBatS (C NR D))))))

variable {ctx : Noun}

/-- **The head of `+fork`**: `+oo` twice, the assert that the goal has no
arguments, the trap `fork-loop` on `[laz.nex there.then.nex o-0 o-1]`
(given its link), the state put back, and the two goals `[%next laz-i ~
o-i]`: the model's `forkL`. -/
theorem comp_fork_head (x : GenRest) (g : Gen (TreapMap mugF)) (laz : Lazy CSet) (th : Jmp) (rc : Nat)
    (hT : nock (fkTS th.there laz.toNoun (g.bo + 1) g.bo (C (CGoalL.next laz th).toNoun (A rc))
        (compCore (ooG (ooG g)) x ctx)) fkLoop
      = (forkLoop rc laz th.there g.bo (g.bo + 1) (ooG (ooG g))).map
          fun p => C (C p.1.1.toNoun p.1.2.toNoun) (genNoun p.2 x)) :
    nock (C fkBatS (C (C (CGoalL.next laz th).toNoun (A rc)) (compCore g x ctx))) fkBatS
      = (forkL ⟨laz, th⟩ rc g).map fun p => C (C p.1.1.goal.toNoun p.1.2.goal.toNoun) (genNoun p.2 x) := by
  have hD := comp_oo_at
  have ho1 := comp_oo' (ctx := ctx) x g
  have ho2 := comp_oo' (ctx := ctx) x (ooG g)
  rw [ooG_bo] at ho2
  obtain ⟨args, there⟩ := th
  unfold forkL
  simp only [bind_apply, oo_ap, Option.bind_some, ooG_bo]
  simp only [fkTS, compCore, CGoalL.toNoun, Jmp.toNoun] at hT ⊢
  generalize comp.door = Dr at hD ho1 ho2 hT ⊢
  cases args with
  | cons a rest =>
    conv => { lhs; arg 2; unfold fkBatS }
    simp [nock_exec, hD, ho1, ho2, listNoun]
  | nil =>
    simp only [ne_eq, not_true_eq_false, if_false]
    simp only [listNoun] at hT ⊢
    cases e : forkLoop rc laz there g.bo (g.bo + 1) (ooG (ooG g)) with
    | none =>
      rw [e] at hT
      conv => { lhs; arg 2; unfold fkBatS }
      simp [nock_exec, hD, ho1, ho2, listNoun, hT, e, bind_apply]
    | some v =>
      obtain ⟨⟨l0, l1⟩, g'⟩ := v
      rw [e] at hT
      conv => { lhs; arg 2; unfold fkBatS }
      simp [nock_exec, hD, ho1, ho2, listNoun, hT, e, bind_apply, pure_apply, NextL.goal, CGoalL.toNoun,
        Jmp.toNoun, jmp0]

end Compiler
end Formalization
