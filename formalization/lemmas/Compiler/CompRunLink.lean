import lemmas.Compiler.CompClaLink
import lemmas.Compiler.TreapList
import lemmas.Ska.CompLazyAgree

/-!
# `+run` of the door of `+comp`: its frame, `+simple-next`, and the case `%0`

`+run` (door axis `2047`) is the gate `|=  [mono=? =nomm =goal region=(list
@uxid) sup=(unit nomm)]` whose body is a `|^` core: its battery is
`[simple-next $]` (`crSn`, `crDol`), pushed on the gate's core by the gate's
battery `crB` = `[8 [1 crBat] 9 5 0 1]`.  So the `$` arm runs on

    [crBat [crB [[mono nomm goal region sup] [comp.door [gen ctx]]]]]

with `mono` at `28`, `nomm` at `58`, `goal` at `118`, `region` at `238`,
`sup` at `239`, the door's core at `15` and `gen` at `62`.  A recursive
`$(nomm .., goal ..)` is `[9 5 10 [118 ..] 10 [58 ..] ..]` on that core,
with `gen` edited in place first, so `CompRunAt` (the `$` arm on a nomm and a
goal equals `runL`) is stated on this subject, for every `mono` and `sup`:
`runL` takes neither, and the cases it models (all but `%2` and `%11`) read
neither (`mono` is read in `%2` and `%mean`, `sup` in `%2` and written in
`%7`).

`crDol` is the `?-` over the nomm: a chain of twelve tests (`[^ *]`,
`%0`, `%1`, `%2`, `%3`, `%4`, `%5`, `%6`, `%7`, `%10`, `%11`, `%mean`) and
the last case `%12`.  The bodies of the cases linked here are written out;
the others are read from the pill (`(slot? k comp.door).getD (A 0)`); one
kernel fact ties the whole arm to the pill (`comp_run_at`).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false

def crSn : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x7478656e)) (C (A 0) (A 236)))) (C (C (C (A 0) (A 118)) (C (A 0) (A 62))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 15)))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 7) (C (C (A 0) (A 3)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f64)) (C (A 0) (A 492)))) (C (C (C (A 1) (A 0x6e6f64)) (C (A 0) (A 2))) (C (C (A 1) (A 0x6e7262)) (C (C (A 0) (A 2)) (C (A 7) (C (C (A 0) (A 246)) (C (C (A 0) (A 6)) (C (A 0) (A 7))))))))))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 1) (A 0x7478656e)) (C (C (C (C (C (A 1) (A 0x73696874)) (C (A 0) (A 6))) (C (A 1) (A 0))) (C (A 1) (C (A 0) (A 0)))) (C (C (A 1) (A 0)) (C (A 0) (A 2))))) (C (A 0) (A 254))))))))))))))))))))))

def crKc : Noun :=
  (C (A 7) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f64)) (C (A 0) (A 236)))) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 15)))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0x6e6f64)) (C (A 0) (A 2)))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 10) (C (C (A 118) (C (C (A 1) (A 0x7478656e)) (C (C (A 8) (C (C (A 9) (C (A 92) (C (A 0) (A 2047)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 0) (A 2)))))) (C (A 0) (A 7)))))))))))))))))))) (C (A 0) (A 1))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6b636970)) (C (A 0) (A 236)))) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (C (A 0x6d6f62) (A 0)))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 5) (C (A 10) (C (C (A 118) (C (C (A 1) (A 0x7478656e)) (C (C (A 1) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (C (A 1) (A 0)) (C (A 0) (A 2)))))) (C (A 10) (C (C (A 58) (C (A 0) (A 245))) (C (A 0) (A 3)))))))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x2bfe) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (C (A 0) (A 1012)) (C (A 0) (A 2030))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 5) (C (A 10) (C (C (A 118) (C (C (A 1) (A 0x7478656e)) (C (C (A 1) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (A 0) (A 11))))) (C (A 10) (C (C (A 58) (C (A 0) (A 1012))) (C (A 0) (A 15)))))))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 9) (C (A 0x55dae) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 0) (A 58)))) (C (A 0) (A 2)))))))))))))))))))))))))))))))))))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x7478656e)) (C (A 0) (A 236))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x2aaefa) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 246))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x2bfe) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0x7478656e)) (C (C (A 0) (A 4)) (C (C (A 1) (A 0)) (C (A 0) (A 11))))))) (C (C (A 0) (A 501)) (C (A 0) (A 1006))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 5) (C (A 10) (C (C (A 118) (C (C (A 1) (A 0x7478656e)) (C (C (A 0) (A 26)) (C (A 0) (A 11))))) (C (A 10) (C (C (A 58) (C (A 0) (A 501))) (C (A 0) (A 7)))))))))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x2bfe) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (C (A 0) (A 2036)) (C (A 0) (A 4078))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 5) (C (A 10) (C (C (A 118) (C (C (A 1) (A 0x7478656e)) (C (C (A 0) (A 58)) (C (A 0) (A 11))))) (C (A 10) (C (C (A 58) (C (A 0) (A 2036))) (C (A 0) (A 31)))))))))) (C (A 7) (C (C (A 10) (C (C (A 2046) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 9) (C (A 0x55dae) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 0) (A 58)))) (C (A 0) (A 2)))))))))))))))))))))))))))))))))))))))))))))))))))))))

def crK0 : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 117)))) (C (C (A 8) (C (C (A 9) (C (A 1364) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x7478656e)) (C (A 0) (A 236)))) (C (C (C (A 1) (A 0)) (C (A 0) (A 951))) (C (A 1) (A 0)))))))) (C (A 0) (A 2)))))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 4) (C (A 0) (A 1)))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 245)))) (C (C (C (A 0) (A 2)) (C (A 0) (A 126))) (C (C (C (A 1) (A 0x7478656e)) (C (C (A 8) (C (C (A 9) (C (A 5630) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 501)) (C (A 0) (A 26)))) (C (A 0) (A 2)))))))) (C (A 0) (A 11)))) (C (A 0) (A 126)))))))))))))))))

def crK1 : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f64)) (C (A 0) (A 236)))) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 15)))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0x6d6d69)) (C (C (A 0) (A 245)) (C (A 0) (A 2)))) (C (A 1) (A 0))))) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0x6e6f64)) (C (A 0) (A 2)))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 1) (A 0x7478656e)) (C (C (A 1) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (C (A 1) (A 0)) (C (A 0) (A 2))))) (C (A 0) (A 254))))))))))))))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6b636970)) (C (A 0) (A 236)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 117)))) (C (C (C (C (A 1) (A 0x7478656e)) (C (C (A 1) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (A 0) (A 474)))) (C (A 0) (A 62))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 117)))) (C (C (C (C (A 1) (A 0x7478656e)) (C (C (A 1) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (A 0) (A 475)))) (C (A 0) (A 62))) (C (A 11) (C (C (A 0x73736f74) (C (A 1) (A 0))) (C (A 8) (C (C (A 9) (C (A 1364) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0))))) (C (A 0) (A 2)))))))))))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x7478656e)) (C (A 0) (A 236))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaab) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 987)) (C (C (A 0) (A 245)) (C (A 0) (A 986))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 1) (A 0x7478656e)) (C (C (A 1) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (C (A 1) (A 0)) (C (A 0) (A 2))))) (C (A 0) (A 126)))))))))))))))))))

def crK2 : Noun := (slot? 8588738558 comp.door).getD (A 0)

def crK3 : Noun :=
  (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x7478656e)) (C (A 0) (A 236)))) (C (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 2811) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 986))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 9) (C (A 5) (C (A 10) (C (C (A 58) (C (A 0) (A 117))) (C (A 0) (A 1)))))) (C (A 7) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6b636970)) (C (A 0) (A 236)))) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f64)) (C (A 0) (A 236)))) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 15)))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 31)))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0x6d6d69)) (C (C (A 1) (A 0)) (C (A 0) (A 6)))) (C (A 1) (A 0))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x6e6f64)))) (C (A 0) (A 14)))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0x6d6d69)) (C (C (A 1) (A 1)) (C (A 0) (A 6)))) (C (A 1) (A 0))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x6e6f64)))) (C (A 0) (A 14)))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 10) (C (C (A 118) (C (C (A 1) (A 0x6b636970)) (C (C (C (A 1) (A 0)) (C (A 0) (A 6))) (C (C (A 1) (A 0)) (C (A 0) (A 2)))))) (C (A 0) (A 31)))))))))))))))))))))))))))))))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x7478656e)) (C (A 0) (A 236))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x55fe) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 246))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (A 0) (A 0)) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xabffa) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 26)) (C (A 0) (A 27)))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 10) (C (C (A 118) (C (C (A 1) (A 0x6b636970)) (C (C (C (A 1) (A 0)) (C (A 0) (A 4))) (C (C (A 1) (A 0)) (C (A 0) (A 5)))))) (C (A 0) (A 7))))))))))))))))))))))))))))))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 15)))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0x716c63)) (C (C (A 0) (A 2)) (C (A 7) (C (C (A 0) (A 246)) (C (C (A 0) (A 6)) (C (A 0) (A 7)))))))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 9) (C (A 5) (C (A 10) (C (C (A 118) (C (C (A 1) (A 0x7478656e)) (C (C (A 8) (C (C (A 9) (C (A 94) (C (A 0) (A 2047)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 6)))))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 0) (A 2)))))) (C (A 10) (C (C (A 58) (C (A 0) (A 501))) (C (A 0) (A 7)))))))))))))))))))))))))))))

def crK4 : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f64)) (C (A 0) (A 236)))) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 15)))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 31)))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0x636e69)) (C (C (A 0) (A 2)) (C (A 0) (A 6)))) (C (A 1) (A 0))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x6e6f64)))) (C (A 0) (A 14)))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 9) (C (A 5) (C (A 10) (C (C (A 118) (C (C (A 1) (A 0x7478656e)) (C (C (A 8) (C (C (A 9) (C (A 92) (C (A 0) (A 4095)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 0) (A 2)))))) (C (A 10) (C (C (A 58) (C (A 0) (A 1013))) (C (A 0) (A 15)))))))))))))))))))))))))))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6b636970)) (C (A 0) (A 236)))) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 15)))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 31)))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0x636e69)) (C (C (A 0) (A 2)) (C (A 0) (A 6)))) (C (A 1) (A 0))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x6e7262)))) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 7) (C (C (A 0) (A 502)) (C (C (A 0) (A 6)) (C (A 0) (A 7)))))))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 9) (C (A 5) (C (A 10) (C (C (A 118) (C (C (A 1) (A 0x7478656e)) (C (C (A 8) (C (C (A 9) (C (A 92) (C (A 0) (A 4095)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 0) (A 2)))))) (C (A 10) (C (C (A 58) (C (A 0) (A 1013))) (C (A 0) (A 15)))))))))))))))))))))))))))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x7478656e)) (C (A 0) (A 236))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x55fe) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 246))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 31)))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 4022)))) (C (C (C (C (A 0) (A 2)) (C (A 0) (A 4023))) (C (A 0) (A 254))) (C (A 0) (A 0))))))))))))) (C (C (A 0) (A 5)) (C (A 0) (A 126)))))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 63)))))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0x636e69)) (C (C (A 0) (A 2)) (C (A 0) (A 12)))) (C (A 1) (A 0))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x706f68)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 29))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 9) (C (A 5) (C (A 10) (C (C (A 118) (C (C (A 1) (A 0x7478656e)) (C (C (A 8) (C (C (A 9) (C (A 92) (C (A 0) (A 8191)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 0) (A 2)))))) (C (A 10) (C (C (A 58) (C (A 0) (A 2037))) (C (A 0) (A 31))))))))))))))))))))))))))))))))))))))))))))))))

def crK5 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 15)))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 31)))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6b636970)) (C (A 0) (A 1004)))) (C (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0x717165)) (C (C (A 0) (A 6)) (C (C (A 0) (A 2)) (C (A 7) (C (C (A 0) (A 502)) (C (C (A 0) (A 6)) (C (A 0) (A 7))))))))))))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f64)) (C (A 0) (A 1004)))) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 63)))))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 127)))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0x6d6d69)) (C (C (A 1) (A 0)) (C (A 0) (A 6)))) (C (A 1) (A 0))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x6e6f64)))) (C (A 0) (A 14)))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 2046) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0x6d6d69)) (C (C (A 1) (A 1)) (C (A 0) (A 6)))) (C (A 1) (A 0))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x6e6f64)))) (C (A 0) (A 14)))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 4094) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 1023)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0x717165)) (C (C (A 0) (A 126)) (C (C (A 0) (A 62)) (C (C (C (A 1) (A 0)) (C (A 0) (A 6))) (C (C (A 1) (A 0)) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2)))))))))))))))))))))))))))))))))))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x7478656e)) (C (A 0) (A 1004))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x55fe) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 1014))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 8118)))) (C (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0x757165)) (C (C (A 0) (A 14)) (C (A 0) (A 6)))) (C (A 1) (A 0))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x706f68)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 0x3fb7))))))) (C (A 0) (A 2)))))))) (C (A 0) (A 0))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xabffa) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 26)) (C (A 0) (A 27)))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0x717165)) (C (C (A 0) (A 30)) (C (C (A 0) (A 14)) (C (C (C (A 1) (A 0)) (C (A 0) (A 4))) (C (C (A 1) (A 0)) (C (A 0) (A 5)))))))))))) (C (A 0) (A 2))))))))))))))))))))))))))))))))))))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 5) (C (A 10) (C (C (A 118) (C (C (A 1) (A 0x7478656e)) (C (C (A 8) (C (C (A 9) (C (A 94) (C (A 0) (A 4095)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 6)))))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 0) (A 2)))))) (C (A 10) (C (C (A 58) (C (A 0) (A 2027))) (C (A 0) (A 15)))))))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x2bfe) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (C (A 0) (A 8170)) (C (A 0) (A 8174))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 2046) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 5) (C (A 10) (C (C (A 118) (C (C (A 1) (A 0x7478656e)) (C (C (A 8) (C (C (A 9) (C (A 94) (C (A 0) (A 0x3fff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 62)))))) (C (A 0) (A 2)))))))) (C (A 0) (A 11))))) (C (A 10) (C (C (A 58) (C (A 0) (A 8170))) (C (A 0) (A 63)))))))))) (C (A 7) (C (C (A 10) (C (C (A 4094) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 9) (C (A 0x55dae) (C (A 0) (A 1023)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 0) (A 58)))) (C (A 0) (A 2))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def crK6 : Noun := (slot? 35179473141758 comp.door).getD (A 0)

def crK7 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 5) (C (A 10) (C (C (A 239) (C (C (A 1) (A 0)) (C (A 0) (A 234)))) (C (A 10) (C (C (A 58) (C (A 0) (A 235))) (C (A 0) (A 1)))))))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 9) (C (A 5) (C (A 10) (C (C (A 118) (C (A 0) (A 2))) (C (A 10) (C (C (A 58) (C (A 0) (A 490))) (C (A 0) (A 3))))))))))))))))

def crK10 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 4) (C (A 0) (A 1)))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 1372) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 0) (A 2004)))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 254) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x2bfe) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0x7478656e)) (C (C (A 0) (A 10)) (C (C (A 1) (A 0)) (C (A 0) (A 11))))))) (C (C (A 0) (A 4053)) (C (A 0) (A 2030))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 5) (C (A 10) (C (C (A 118) (C (C (A 1) (A 0x7478656e)) (C (C (A 0) (A 12)) (C (A 0) (A 11))))) (C (A 10) (C (C (A 58) (C (A 0) (A 4053))) (C (A 0) (A 15)))))))))) (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x2bfe) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (C (A 0) (A 8171)) (C (A 0) (A 8174))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 2046) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 5) (C (A 10) (C (C (A 118) (C (C (A 1) (A 0x7478656e)) (C (C (A 0) (A 58)) (C (A 0) (A 11))))) (C (A 10) (C (C (A 58) (C (A 0) (A 8171))) (C (A 0) (A 63)))))))))) (C (A 7) (C (C (A 10) (C (C (A 4094) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 9) (C (A 0x55dae) (C (A 0) (A 1023)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 0) (A 58)))) (C (A 0) (A 2))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def crK11 : Noun := (slot? 18011890248581118 comp.door).getD (A 0)

def crKmean : Noun := (slot? 144095121988648958 comp.door).getD (A 0)

def crLast : Noun := (slot? 144095121988648959 comp.door).getD (A 0)

/-- The test `?=([%k *] nomm)` of the `?-` (the cell test first). -/
def crT (k : Nat) : Noun :=
  C (A 6) (C (C (A 3) (C (A 0) (A 58))) (C (C (A 5) (C (C (A 1) (A k)) (C (A 0) (A 116)))) (C (A 1) (A 1))))

/-- The test `?=([^ *] nomm)`. -/
def crTc : Noun :=
  C (A 6) (C (C (A 3) (C (A 0) (A 58))) (C (C (A 3) (C (A 0) (A 116))) (C (A 1) (A 1))))

/-- The `$` arm of the `|^` core: the `?-` over the nomm. -/
def crDol : Noun :=
  C (A 6) (C crTc (C crKc
  (C (A 6) (C (crT 0) (C crK0
  (C (A 6) (C (crT 1) (C crK1
  (C (A 6) (C (crT 2) (C crK2
  (C (A 6) (C (crT 3) (C crK3
  (C (A 6) (C (crT 4) (C crK4
  (C (A 6) (C (crT 5) (C crK5
  (C (A 6) (C (crT 6) (C crK6
  (C (A 6) (C (crT 7) (C crK7
  (C (A 6) (C (crT 10) (C crK10
  (C (A 6) (C (crT 11) (C crK11
  (C (A 6) (C (crT 0x6e61656d) (C crKmean crLast)))))))))))))))))))))))))))))))))))

/-- The battery of the `|^` core: `[simple-next $]`. -/
def crBat : Noun := C crSn crDol

/-- The battery of the gate: push the `|^` battery, run `$`. -/
def crB : Noun := C (A 8) (C (C (A 1) crBat) (C (A 9) (C (A 5) (C (A 0) (A 1)))))

/-- The bunt of the sample: `[& [0 0] [%next [[[%none ~] ~] ~ ~] ~ 0] ~ ~]`. -/
def crBunt : Noun :=
  C (A 0) (C (C (A 0) (A 0)) (C (C (A 0x7478656e) (C (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))) (C (A 0) (A 0)))) (C (A 0) (A 0))))

/-- The arm `+run`. -/
def crArm : Noun :=
  C (A 7) (C (C (A 8) (C (C (A 1) crBunt) (C (C (A 1) crB) (C (A 0) (A 1)))))
    (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x6e75722d706d6f63) (C (C (A 0) (A 0x7ffff)) (A 0))))) (C (A 0) (A 1)))))

/-- **`+run` is arm `2047` of the door.** -/
theorem comp_run_at : slot? 2047 comp.door = some crArm := by kernel_rfl

/-! ## The subject of `$` and the predicate `CompRunAt` -/

/-- The core of the `|^`: its battery on the gate's core, whose sample is
`[mono nomm goal region sup]` and whose context is the door's core `D`. -/
def crSubj (mono nomm goal region sup D : Noun) : Noun :=
  C crBat (C crB (C (C mono (C nomm (C goal (C region sup)))) D))

/-- `soft` has no key: `(~(has by soft.gen) o)` is `|` for every block, the
branch the models take (they take `soft` to be empty). -/
def GenRest.NoSoft (x : GenRest) : Prop := ∀ o, x.SoftOut o

/-- **The `$` arm of `+run` on the noun of a nomm and a goal is `runL`**, from
the state `g`, for every `mono`, `sup` and every rest `x` of the state with an
empty `soft` (kept as it is). -/
def CompRunAt (ctx : Noun) (n : Nomm) (goal : CGoalL CSet) (region : List Nat)
    (g : Gen (TreapMap mugF)) : Prop :=
  ∀ (x : GenRest) (mono sup : Noun), x.NoSoft →
    nock (crSubj mono n.toNoun goal.toNoun (listNoun A region) sup (compCore g x ctx)) crDol
      = (runL n goal region g).map fun p => C p.1.goal.toNoun (genNoun p.2 x)

/-! ## `+simple-next` -/

theorem cr_re_at : slot? 3538943 comp.door = some comp.re.arm := comp_re_at

variable {ctx : Noun}

/-- **`+simple-next`** is `simpleNextL`: the goal itself when it is `%next`,
otherwise a fresh register `r` and a block that returns it (`%done`) or
branches on it (`%pick`), with the need `[[%this r] ~] ~ ~]`. -/
theorem comp_simple_next (hc : CompIn ctx) (x : GenRest) (g : Gen (TreapMap mugF))
    (goal : CGoalL CSet) (mono nomm region sup : Noun) :
    nock (crSubj mono nomm goal.toNoun region sup (compCore g x ctx)) crSn
      = (simpleNextL goal g).map fun p => C p.1.goal.toNoun (genNoun p.2 x) := by
  have hre := comp_re' ctx x g
  have hD1 := comp_re_at
  have hD2 := comp_emit_at
  simp only [compCore] at hre ⊢
  cases goal with
  | next laz th =>
    unfold crSn
    simp [nock_exec, crSubj, CGoalL.toNoun, simpleNextL, NextL.goal, pure, StateT.pure]
  | done =>
    have he := comp_emit x hc { g with re := g.re + 1 } ⟨[], [], Termin.don g.re⟩
    simp only [compCore, Blob.toNoun, listNoun, Termin.toNoun, Tag.don] at he
    rw [cd_emit_eq] at he
    generalize comp.door = Dr at hD1 hD2 he hre ⊢
    unfold crSn
    simp [nock_exec, crSubj, CGoalL.toNoun, simpleNextL, NextL.goal, hre, hD1, hD2, comp_emit_arm, he,
      cd_emit_eq, re, bind, StateT.bind, pure, StateT.pure, Lazy.toNoun_ofSure, lazyNoun, Sure.toNoun,
      Need.toNoun, HoonSet.toNoun_empty, Jmp.toNoun, jmp0, listNoun, Tag.this]
  | pick z o =>
    have he := comp_emit x hc { g with re := g.re + 1 } ⟨[], [], Termin.brn g.re z o⟩
    simp only [compCore, Blob.toNoun, listNoun, Termin.toNoun, Tag.brn, Jmp.toNoun] at he
    rw [cd_emit_eq] at he
    generalize comp.door = Dr at hD1 hD2 he hre ⊢
    unfold crSn
    simp [nock_exec, crSubj, CGoalL.toNoun, simpleNextL, NextL.goal, hre, hD1, hD2, comp_emit_arm, he,
      cd_emit_eq, re, bind, StateT.bind, pure, StateT.pure, Lazy.toNoun_ofSure, lazyNoun, Sure.toNoun,
      Need.toNoun, HoonSet.toNoun_empty, Jmp.toNoun, jmp0, listNoun, Tag.this]

/-! ## The case `%0` -/

/-- No looked-at axis of a fork-free `%next` goal is `0` (the side condition
of `+from`); the goals `%done` and `%pick` look at nothing. -/
def crLokOk : CGoal CSet → Prop
  | CGoal.next laz _ => ∀ y ∈ HoonSet.toList laz.lok, y ≠ 0
  | _ => True

theorem comp_bomb_at : slot? 852 comp.door = some comp.bomb.arm := by kernel_rfl

/-- The arm `bomb` builds its gate. -/
theorem comp_bomb_arm (d : Noun) : nock d comp.bomb.arm = some (C comp.bomb.battery (C (A 0) d)) := by
  nock_open comp.bomb.arm; simp only [nock_exec]

theorem comp_from_at : slot? 3582 comp.door = some comp.from.arm := by kernel_rfl

/-- The arm `from` builds its gate. -/
theorem comp_from_arm (d : Noun) : nock d comp.from.arm =
    some (C comp.from.battery (C (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) d)) := by
  nock_open comp.from.arm; simp only [nock_exec]

theorem cr_bat_sn : slot? 2 crBat = some crSn := rfl
theorem cr_bat_dol : slot? 3 crBat = some crDol := rfl

/-- The `?-` sends `[%0 ax]` to the body of `%0`. -/
theorem cr_disp_n0 (ax : Nat) (mono goal region sup D : Noun) :
    nock (crSubj mono (C (A 0) (A ax)) goal region sup D) crDol
      = nock (crSubj mono (C (A 0) (A ax)) goal region sup D) crK0 := by
  nock_open crDol
  simp [nock_exec, crSubj, crTc, crT]

/-- What `+simple-next` returns on a fork-free goal: a fork-free need with no
look at `0`. -/
theorem cr_sn_shape (gl : CGoal CSet) (hlok : crLokOk gl) (g : Gen (TreapMap mugF))
    (nex : NextL CSet) (g1 : Gen (TreapMap mugF)) (e : simpleNextL (CGoal.toL gl) g = some (nex, g1)) :
    ∃ s : Sure CSet, nex.laz = Lazy.ofSure s ∧ ∀ y ∈ HoonSet.toList s.lok, y ≠ 0 := by
  cases gl with
  | next laz th =>
    simp [CGoal.toL, simpleNextL, pure, StateT.pure] at e
    exact ⟨laz, by rw [← e.1], hlok⟩
  | done =>
    simp [CGoal.toL, simpleNextL, re, bind, StateT.bind, pure, StateT.pure, cd_emit_eq] at e
    rcases e with ⟨rfl, -⟩
    exact ⟨_, rfl, fun y hy => absurd hy (HoonSet.mem_empty y)⟩
  | pick z o =>
    simp [CGoal.toL, simpleNextL, re, bind, StateT.bind, pure, StateT.pure, cd_emit_eq] at e
    rcases e with ⟨rfl, -⟩
    exact ⟨_, rfl, fun y hy => absurd hy (HoonSet.mem_empty y)⟩

/-- **The case `%0` of `+run`** on a fork-free goal with no look at `0`:
`(bomb ..)` on axis `0`, otherwise `+simple-next`, then `+from` unless the
axis is `1`. -/
theorem comp_run_n0 (h7 : slot? 7 ctx = some compK) (ax : Nat) (gl : CGoal CSet) (region : List Nat)
    (g : Gen (TreapMap mugF)) (hlok : crLokOk gl) :
    CompRunAt ctx (Nomm.n0 ax) (CGoal.toL gl) region g := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  intro x mono sup _
  simp only [Nomm.toNoun]
  rw [cr_disp_n0]
  by_cases h0 : ax = 0
  · subst h0
    have hD := comp_bomb_at
    simp only [compCore]
    cases gl with
    | next laz th =>
      have hb := comp_bomb (S := CSet) x hc g (some th.there)
      simp [compCore, bomb, cd_emit_eq, bind, StateT.bind, pure, StateT.pure, unitNoun, Next.goal,
        CGoal.toNoun, Jmp.toNoun, jmp0, lazyNoun, Sure.toNoun, Sure.bunt, Need.toNoun, HoonSet.toNoun_empty,
        listNoun] at hb
      generalize comp.door = Dr at hb hD ⊢
      nock_open crK0
      simp [nock_exec, crSubj, hD, comp_bomb_arm, CGoal.toL, CGoalL.toNoun, Jmp.toNoun, unitNoun, hb,
        runL, bombL, cd_emit_eq, NextL.goal, Next.goal, CGoal.toNoun, Lazy.toNoun_ofSure, Functor.map,
        StateT.map, jmp0, lazyNoun, Sure.toNoun, Sure.bunt, Need.toNoun, HoonSet.toNoun_empty, listNoun]
    | done =>
      have hb := comp_bomb (S := CSet) x hc g Option.none
      simp [compCore, bomb, cd_emit_eq, bind, StateT.bind, pure, StateT.pure, unitNoun, Next.goal,
        CGoal.toNoun, Jmp.toNoun, jmp0, lazyNoun, Sure.toNoun, Sure.bunt, Need.toNoun, HoonSet.toNoun_empty,
        listNoun] at hb
      generalize comp.door = Dr at hb hD ⊢
      nock_open crK0
      simp [nock_exec, crSubj, hD, comp_bomb_arm, CGoal.toL, CGoalL.toNoun, Jmp.toNoun, unitNoun, hb,
        runL, bombL, cd_emit_eq, NextL.goal, Next.goal, CGoal.toNoun, Lazy.toNoun_ofSure, Functor.map,
        StateT.map, jmp0, lazyNoun, Sure.toNoun, Sure.bunt, Need.toNoun, HoonSet.toNoun_empty, listNoun]
    | pick z o =>
      have hb := comp_bomb (S := CSet) x hc g Option.none
      simp [compCore, bomb, cd_emit_eq, bind, StateT.bind, pure, StateT.pure, unitNoun, Next.goal,
        CGoal.toNoun, Jmp.toNoun, jmp0, lazyNoun, Sure.toNoun, Sure.bunt, Need.toNoun, HoonSet.toNoun_empty,
        listNoun] at hb
      generalize comp.door = Dr at hb hD ⊢
      nock_open crK0
      simp [nock_exec, crSubj, hD, comp_bomb_arm, CGoal.toL, CGoalL.toNoun, Jmp.toNoun, unitNoun, hb,
        runL, bombL, cd_emit_eq, NextL.goal, Next.goal, CGoal.toNoun, Lazy.toNoun_ofSure, Functor.map,
        StateT.map, jmp0, lazyNoun, Sure.toNoun, Sure.bunt, Need.toNoun, HoonSet.toNoun_empty, listNoun]
  · have h0' : ¬ (0 = ax) := fun h => h0 h.symm
    have hD2 := comp_from_at
    have hsn := comp_simple_next hc x g (CGoal.toL gl) mono (C (A 0) (A ax)) (listNoun A region) sup
    rcases e : simpleNextL (CGoal.toL gl) g with _ | ⟨nex, g1⟩
    · rw [e] at hsn
      simp only [crSubj, compCore, Option.map_none] at hsn
      simp only [compCore]
      generalize comp.door = Dr at hsn hD2 ⊢
      nock_open crK0
      simp [nock_exec, crSubj, h0, h0', hsn, cr_bat_sn, runL, e, bind, StateT.bind]
    · obtain ⟨s, hs, hs0⟩ := cr_sn_shape gl hlok g nex g1 e
      obtain ⟨laz, th⟩ := nex
      simp only at hs
      subst hs
      rw [e] at hsn
      simp only [crSubj, compCore, Option.map_some] at hsn
      have hng : (NextL.goal ⟨Lazy.ofSure s, th⟩ : CGoalL CSet).toNoun
          = C (A 0x7478656e) (C (lazyNoun s) th.toNoun) := by
        simp [NextL.goal, CGoalL.toNoun, Lazy.toNoun_ofSure]
      rw [hng] at hsn
      have hf := comp_from hc (genNoun g1 x) ax s hs0
      simp only [compCore]
      generalize comp.door = Dr at hsn hD2 hf ⊢
      nock_open crK0
      by_cases h1 : ax = 1
      · subst h1
        simp [nock_exec, crSubj, hsn, cr_bat_sn, runL, e, hng, pure, StateT.pure, bind, StateT.bind]
      · have h1' : ¬ (1 = ax) := fun h => h1 h.symm
        cases ef : «from» ax s with
        | none =>
          rw [ef] at hf
          simp [nock_exec, crSubj, h0, h0', h1, h1', hsn, cr_bat_sn, runL, e, hng, pure, StateT.pure, bind, StateT.bind, hD2, comp_from_arm, hf,
            Lazy.fromL_ofSure, ef]
        | some s' =>
          rw [ef] at hf
          simp [nock_exec, crSubj, h0, h0', h1, h1', hsn, cr_bat_sn, runL, e, hng, pure, StateT.pure, bind, StateT.bind, hD2, comp_from_arm, hf,
            Lazy.fromL_ofSure, ef]
          simp [NextL.goal, CGoalL.toNoun, Lazy.toNoun_ofSure]

/-! ## The case `%7` -/

theorem cr_disp_n7 (t mono goal region sup D : Noun) :
    nock (crSubj mono (C (A 7) t) goal region sup D) crDol
      = nock (crSubj mono (C (A 7) t) goal region sup D) crK7 := by
  nock_open crDol
  simp [nock_exec, crSubj, crTc, crT]

/-- **The case `%7` of `+run`**: `q` with the goal, then `p` with the goal
that `q` returns, given both recursive calls (the first with `sup` set to
`` `p ``, which the model does not read). -/
theorem comp_run_n7 (p q : Nomm) (goal : CGoalL CSet) (region : List Nat) (g : Gen (TreapMap mugF))
    (hq : CompRunAt ctx q goal region g)
    (hp : ∀ nex g1, runL q goal region g = some (nex, g1) → CompRunAt ctx p nex.goal region g1) :
    CompRunAt ctx (Nomm.n7 p q) goal region g := by
  intro x mono sup hx
  have h1 := hq x mono (C (A 0) p.toNoun) hx
  simp only [crSubj, compCore] at h1
  simp only [Nomm.toNoun]
  rw [cr_disp_n7]
  cases e : runL q goal region g with
  | none =>
    rw [e] at h1
    simp only [compCore]
    generalize comp.door = Dr at h1 ⊢
    nock_open crK7
    simp [nock_exec, crSubj, cr_bat_dol, h1, runL, e, bind, StateT.bind]
  | some r =>
    obtain ⟨nex, g1⟩ := r
    rw [e] at h1
    have h2 := hp nex g1 e x mono sup hx
    simp only [crSubj, compCore] at h2 h1
    simp only [compCore]
    generalize comp.door = Dr at h1 h2 ⊢
    nock_open crK7
    simp [nock_exec, crSubj, cr_bat_dol, h1, h2, runL, e, bind, StateT.bind]

/-! ## The case `%1` -/

theorem cr_disp_n1 (t mono goal region sup D : Noun) :
    nock (crSubj mono (C (A 1) t) goal region sup D) crDol
      = nock (crSubj mono (C (A 1) t) goal region sup D) crK1 := by
  nock_open crDol
  simp [nock_exec, crSubj, crTc, crT]

/-- The noun of `*need-lazy`. -/
theorem cr_bunt_noun : (Lazy.ofSure (Sure.bunt : Sure CSet)).toNoun
    = C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)) := by
  simp [Lazy.toNoun_ofSure, lazyNoun, Sure.toNoun, Sure.bunt, Need.toNoun, HoonSet.toNoun_empty, Tag.none]

theorem cr_bunt_lazy : lazyNoun (Sure.bunt : Sure CSet)
    = C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)) := by
  simp [lazyNoun, Sure.toNoun, Sure.bunt, Need.toNoun, HoonSet.toNoun_empty, Tag.none]

/-- The arm `mede` builds its gate. -/
theorem comp_md_arm (d : Noun) : nock d mdArm =
    some (C mdBat (C (C (C (A 0) (A 0)) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))))) d)) := by
  unfold mdArm; simp only [nock_exec]

/-- **The case `%1` of `+run`** on a fork-free goal with no look at `0`:
`%done` emits a block that makes the constant and returns it, `%pick` takes
the branch of `0` or `1` (or `(bomb ~)`), `%next` is `+mede`. -/
theorem comp_run_n1 (h7 : slot? 7 ctx = some compK) (k : Noun) (gl : CGoal CSet) (region : List Nat)
    (g : Gen (TreapMap mugF)) (hlok : crLokOk gl) :
    CompRunAt ctx (Nomm.n1 k) (CGoal.toL gl) region g := by
  obtain ⟨hc, hl, hm⟩ := comp_ctx_pill ctx h7
  intro x mono sup hx
  simp only [Nomm.toNoun]
  rw [cr_disp_n1]
  cases gl with
  | next laz th =>
    have hmd := comp_mede hc hl hm x g th k laz (hx g.bo) hlok
    have hD := comp_md_at
    simp only [compCore, Jmp.toNoun] at hmd ⊢
    generalize comp.door = Dr at hmd hD ⊢
    nock_open crK1
    cases e : mede th k laz g with
    | none =>
      rw [e] at hmd
      simp [nock_exec, crSubj, hD, comp_md_arm, CGoal.toL, CGoalL.toNoun, Jmp.toNoun, hmd, runL,
        medeL_toL, Lazy.toNoun_ofSure, e, bind, StateT.bind]
    | some r =>
      rw [e] at hmd
      simp [nock_exec, crSubj, hD, comp_md_arm, CGoal.toL, CGoalL.toNoun, Jmp.toNoun, hmd, runL,
        medeL_toL, e, bind, StateT.bind, pure, StateT.pure, NextL.goal, Lazy.toNoun_ofSure, cr_bunt_noun,
        cr_bunt_lazy, jmp0, listNoun]
  | done =>
    have hre := comp_re' ctx x g
    have he := comp_emit x hc { g with re := g.re + 1 } ⟨[], [Pole.imm k g.re], Termin.don g.re⟩
    simp only [compCore, Blob.toNoun, listNoun, Termin.toNoun, Pole.toNoun, Tag.don, Tag.imm] at he
    rw [cd_emit_eq] at he
    have hD1 := comp_re_at
    have hD2 := comp_emit_at
    simp only [compCore] at hre ⊢
    generalize comp.door = Dr at hD1 hD2 he hre ⊢
    nock_open crK1
    simp [nock_exec, crSubj, CGoal.toL, CGoalL.toNoun, hre, hD1, hD2, comp_emit_arm, he, cd_emit_eq,
      runL, re, bind, StateT.bind, pure, StateT.pure, NextL.goal, Lazy.toNoun_ofSure, lazyNoun,
      Sure.toNoun, Sure.bunt, Need.toNoun, HoonSet.toNoun_empty, Tag.none, jmp0, listNoun, Jmp.toNoun]
  | pick z o =>
    nock_open crK1
    by_cases h0 : k = A 0
    · subst h0
      simp [nock_exec, crSubj, CGoal.toL, CGoalL.toNoun, eqCode, runL, pure, StateT.pure, NextL.goal,
        Lazy.toNoun_ofSure, lazyNoun, Sure.toNoun, Sure.bunt, Need.toNoun, HoonSet.toNoun_empty, Tag.none]
    · by_cases h1 : k = A 1
      · subst h1
        simp [nock_exec, crSubj, CGoal.toL, CGoalL.toNoun, eqCode, runL, pure, StateT.pure, NextL.goal,
          Lazy.toNoun_ofSure, lazyNoun, Sure.toNoun, Sure.bunt, Need.toNoun, HoonSet.toNoun_empty, Tag.none]
      · have h0' : ¬ (A 0 = k) := fun h => h0 h.symm
        have h1' : ¬ (A 1 = k) := fun h => h1 h.symm
        have hb := comp_bomb (S := CSet) x hc g Option.none
        simp [compCore, bomb, cd_emit_eq, bind, StateT.bind, pure, StateT.pure, unitNoun, Next.goal,
          CGoal.toNoun, Jmp.toNoun, jmp0, lazyNoun, Sure.toNoun, Sure.bunt, Need.toNoun,
          HoonSet.toNoun_empty, Tag.none, listNoun] at hb
        have hD := comp_bomb_at
        simp only [compCore]
        generalize comp.door = Dr at hb hD ⊢
        simp [nock_exec, crSubj, hD, comp_bomb_arm, CGoal.toL, CGoalL.toNoun, eqCode, h0, h1, h0', h1',
          unitNoun, hb, runL, bombL, cd_emit_eq, NextL.goal, Lazy.toNoun_ofSure, Functor.map,
          StateT.map, jmp0, lazyNoun, Sure.toNoun, Sure.bunt, Need.toNoun, HoonSet.toNoun_empty, Tag.none,
          listNoun, Jmp.toNoun, bind, StateT.bind, pure, StateT.pure]

end Compiler
end Formalization
