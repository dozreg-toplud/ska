import lemmas.Compiler.CompRunDirectN

/-!
# The direct call of `%2`: the cut of the call (`tools/gen/direct.py`)

`crDCall` (the branch of the drop test that emits a call block) cut at its
pushes, in the order of the Hoon (README Gaps 19): step `i` is `crDKc<i>`
(what is pushed) and `crDKr<i>` (the noun from step `i` on).  `0` the `=*`
of `call-cole`; `1` `rin`; `2` `b-ned`; `3` `sub-ned`
(`+need-ord-alloc-regs`); `4` `sub-v` (`+flatten-need`); `5` `b-sur`; `6`
`sof`; `7` `call-blocks` (`crD7`: the gates `crD7Op`, `crD7Jop`, the test
`crD7T` of `%done` with no key, the branch `crD7D` under `%done`, `mono` `&`
in `crD7Dm` and `|` in the chain `crD7U`, the other branch `crD7Nr0`:
`+simple-next` `crD7Nc0`, `+kerf` `crD7Nc1`, then `crD7Ne`, `mono` `&` in
`crD7Nm` and `|` in the chain `crD7V`); `8` `[sub-ned call-block]`; `9`
`nex-arg`; `10` the run of `q`; `11` `+past`; `12` the run of `p`; `13`,
`14` `+copy`.  `crdk_eq` checks the cut against the pill.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon

def crDKc1 : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 764) (C (A 10) (C (C (A 6) (C (A 0) (A 0xffabe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 8030))) (C (A 0) (A 2))))))))

def crDKc2 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 8031))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 0x3ebe)))) (C (C (A 3) (C (A 0) (A 0x3ebf))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (C (A 1) (C (A 0x73696874) (A 0))) (C (A 0) (A 254))) (C (A 8) (C (C (A 9) (C (A 0x55ffc) (C (A 0) (A 63)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 0x3f5e))) (C (A 0) (A 2)))))))))))))

def crDKc3 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 702) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2))))))))))

def crDKc4 : Noun :=
  (C (A 8) (C (C (A 9) (C (A 348) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2))))))))

def crDKc5 : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 92) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 62)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 764) (C (A 10) (C (C (A 6) (C (A 0) (A 0x1fff6))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 6108) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 0x1ff5e))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (C (A 0x656e6f6e) (A 0))))))))))

def crDKc6 : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 0x1ff5f)))) (C (C (A 6) (C (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 0x5556) (C (A 0) (A 1023)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0x55f6) (C (A 0) (A 1023)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 0x7fea)) (C (A 0) (A 0x7fef)))) (C (A 0) (A 2)))))))))) (C (A 0) (A 62)))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 6) (C (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 5466) (C (A 0) (A 0x3fff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 62)) (C (C (A 0) (A 6)) (C (A 0) (A 0x7febc))))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 0x17774) (C (A 0) (A 0x3fff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 0x7fea)) (C (A 0) (A 0x3fff4)))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 0x17774) (C (A 0) (A 0x3fff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 0xffd6)) (C (A 0) (A 0x3fff4)))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))))))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1)))))

def crD7Op : Noun :=
  (C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (C (A 1) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 0xfff5f))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 510)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 12)))) (C (C (C (A 1) (A 0x6c6163)) (C (C (A 0) (A 0xfff5e)) (C (C (A 0) (A 62)) (C (A 0) (A 13))))) (C (C (A 1) (A 0x6c7363)) (C (C (A 0) (A 0xfff5e)) (C (C (A 0) (A 25)) (C (A 0) (A 13)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 12)))) (C (C (C (A 1) (A 0x666163)) (C (C (A 0) (A 0xfff5e)) (C (C (A 0) (A 62)) (C (C (A 0) (A 13)) (C (A 0) (A 1021)))))) (C (C (A 1) (A 0x667363)) (C (C (A 0) (A 0xfff5e)) (C (C (A 0) (A 25)) (C (C (A 0) (A 13)) (C (A 0) (A 1021)))))))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 12)))) (C (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 0x1ffebf))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (C (A 1) (A 0x6d6163)) (C (C (A 0) (A 0xfff5e)) (C (C (A 0) (A 62)) (C (C (A 0) (A 13)) (C (A 0) (A 0x1ffebf)))))) (C (C (A 1) (A 0x6d7363)) (C (C (A 0) (A 0xfff5e)) (C (C (A 0) (A 124)) (C (C (A 0) (A 13)) (C (A 0) (A 0x1ffebf))))))))) (C (C (A 1) (A 0x6d7363)) (C (C (A 0) (A 0xfff5e)) (C (C (A 0) (A 25)) (C (C (A 0) (A 13)) (C (A 0) (A 0x1ffebf))))))))))))) (C (A 0) (A 1)))))

def crD7Jop : Noun :=
  (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 1022)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 6)))) (C (C (C (A 1) (A 0x706d6a)) (C (C (A 0) (A 0x1fff5e)) (C (A 0) (A 126)))) (C (C (A 1) (A 0x70736a)) (C (C (A 0) (A 0x1fff5e)) (C (A 0) (A 13))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 6)))) (C (C (C (A 1) (A 0x666d6a)) (C (C (A 0) (A 0x1fff5e)) (C (C (A 0) (A 126)) (C (A 0) (A 2045))))) (C (C (A 1) (A 0x66736a)) (C (C (A 0) (A 0x1fff5e)) (C (C (A 0) (A 13)) (C (A 0) (A 2045)))))))))))) (C (A 0) (A 1)))))

def crD7T : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 0xfff5f)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f64)) (C (A 0) (A 0x1ffec)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1)))))

def crD7Dm : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 8191)))))) (C (A 7) (C (C (A 10) (C (C (A 0xfffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 0x3fff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 0) (A 6)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0))))) (C (A 0) (A 2))))))))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 0x1fffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 0x7fff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 0) (A 14)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0)) (C (A 0) (A 6)))))) (C (A 0) (A 2))))))))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 0x3fffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 0) (A 6)) (C (C (A 0) (A 14)) (C (A 0) (A 2)))) (C (A 0) (A 0x3fffe)))))))))))))))))))))))))))

def crD7Uc0 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 8191)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 0) (A 2)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0))))) (C (A 0) (A 2))))))))))))) (C (A 0) (A 2))))))))))

def crD7Ur1 : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 0xfffe) (C (A 6) (C (C (A 0) (A 30)) (C (C (A 8) (C (C (A 9) (C (A 382) (C (A 0) (A 0x3fff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x6c696174)))) (C (C (A 0) (A 0x3fff5e)) (C (C (A 0) (A 2046)) (C (C (A 0) (A 510)) (C (C (A 0) (A 126)) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0))))))))))))) (C (A 0) (A 2)))))))) (C (A 0) (A 0xfffe)))))) (C (A 0) (A 1)))) (C (C (A 0) (A 2)) (C (A 0) (A 0xfffe)))))

def crD7Ur0 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C crD7Uc0 (C (A 7) (C (C (A 10) (C (C (A 0xfffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) crD7Ur1))))))))

def crD7D : Noun :=
  (C (A 6) (C (C (A 0) (A 0x3ffc)) (C crD7Dm crD7Ur0)))

def crD7Nm : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 0x7fff)))))) (C (A 7) (C (C (A 10) (C (C (A 0x3fffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 0xffff)))))) (C (A 7) (C (C (A 10) (C (C (A 0x7fffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 0x1ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (A 0) (A 6)) (C (A 1) (A 0))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0x766f6d)) (C (C (A 0) (A 6)) (C (A 0) (A 29)))) (C (A 1) (A 0))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x706f68)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 60))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 0xffffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 0x3ffff)))))) (C (A 7) (C (C (A 10) (C (C (A 0x1ffffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 0x7ffff)))))) (C (A 7) (C (C (A 10) (C (C (A 0x3ffffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (A 8) (C (C (A 0) (A 1022)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 14)))) (C (A 0) (A 2)))))))) (C (A 1) (A 0))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x706f68)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0)) (C (A 0) (A 6))) (C (A 1) (A 0))))) (C (A 0) (A 30))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 0x7ffffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (A 8) (C (C (A 0) (A 2046)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (A 0)) (C (A 0) (A 62))))) (C (A 0) (A 14)))) (C (A 0) (A 2)))))))) (C (A 1) (A 0))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x706f68)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (C (A 1) (A 0)) (C (A 0) (A 6))) (C (A 1) (A 0))))) (C (A 0) (A 62))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 0xfffffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (A 0) (A 6)) (C (C (A 0) (A 126)) (C (A 0) (A 2)))) (C (A 0) (A 0xfffffe)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def crD7Vc0 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 0x7fff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (A 8) (C (C (A 0) (A 30)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 13)))) (C (A 0) (A 2)))))))) (C (A 1) (A 0))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x706f68)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 12))))))) (C (A 0) (A 2))))))))))

def crD7Vr1 : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 0x3fffe) (C (A 6) (C (C (A 0) (A 126)) (C (C (A 8) (C (C (A 9) (C (A 382) (C (A 0) (A 0xffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x6c6c6163)))) (C (C (A 0) (A 0xffff5e)) (C (C (A 0) (A 8190)) (C (C (A 0) (A 2046)) (C (C (A 0) (A 510)) (C (C (A 0) (A 29)) (C (C (A 0) (A 28)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0))))))))))))) (C (A 0) (A 2)))))))) (C (A 0) (A 0x3fffe)))))) (C (A 0) (A 1)))) (C (C (A 0) (A 2)) (C (A 0) (A 0x3fffe)))))

def crD7Vr0 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C crD7Vc0 (C (A 7) (C (C (A 10) (C (C (A 0x3fffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) crD7Vr1))))))))

def crD7Ne : Noun :=
  (C (A 6) (C (C (A 0) (A 0xfffc)) (C crD7Nm crD7Vr0)))

def crD7Nc0 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 4) (C (A 0) (A 1023))))))

def crD7Nc1 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xabb4) (C (A 0) (A 0x3fff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2))))))))))

def crD7Nr1 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C crD7Nc1 (C (A 7) (C (C (A 10) (C (C (A 0x1fffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) crD7Ne))))))))

def crD7Nr0 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C crD7Nc0 (C (A 7) (C (C (A 10) (C (C (A 0xfffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) crD7Nr1))))))))

def crD7 : Noun :=
  (C (A 8) (C crD7Op (C (A 8) (C crD7Jop (C (A 6) (C crD7T (C crD7D crD7Nr0)))))))

def crDKc7 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) crD7))

def crDKc8 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (C (C (A 0) (A 62)) (C (A 0) (A 2))) (C (A 0) (A 0x3ffe))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaabbf) (C (A 0) (A 4095)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 126)) (C (A 0) (A 6)))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 0x7ffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (C (C (A 1) (A 0x73696874)) (C (A 0) (A 26))) (C (A 0) (A 2))) (C (A 0) (A 0x7ffe))))))))))))))))

def crDKc9 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (C (A 1) (A 0x7478656e)) (C (C (A 8) (C (C (A 9) (C (A 94) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 12))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 0)) (C (A 0) (A 5))))) (C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1ffffffff)))) (C (A 9) (C (A 3061) (C (A 10) (C (C (A 6) (C (A 0) (A 0x3fffdfe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 9) (C (A 698) (C (A 0) (A 0x3fff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 0) (A 0x7ffee)))) (C (A 0) (A 2)))))))) (C (C (A 0) (A 2)) (C (A 0) (A 0xfffe))))))))))

def crDKc10 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 767) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 0xfffd6))) (C (A 0) (A 2)))))))) (C (C (C (C (A 1) (A 0x7478656e)) (C (C (A 1) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (A 0) (A 11)))) (C (A 0) (A 0xfffe))) (C (A 9) (C (A 5) (C (A 10) (C (C (A 118) (C (C (A 1) (A 0x7478656e)) (C (C (A 1) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (A 0) (A 11))))) (C (A 10) (C (C (A 58) (C (A 0) (A 0x7ffd6))) (C (A 0) (A 2047)))))))))))))

def crDKc11 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x2bfe) (C (A 0) (A 0x7fff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (C (A 0) (A 0xfffea)) (C (A 0) (A 0xfffee))))) (C (A 0) (A 2))))))))))

def crDKc12 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 5) (C (A 10) (C (C (A 118) (C (C (A 1) (A 0x7478656e)) (C (C (A 0) (A 58)) (C (A 0) (A 11))))) (C (A 10) (C (C (A 58) (C (A 0) (A 0xfffea))) (C (A 0) (A 8191))))))))))

def crDKc13 : Noun :=
  (C (A 9) (C (A 0x55dae) (C (A 0) (A 0x1ffff))))

def crDKr14 : Noun :=
  (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 0) (A 58)))) (C (A 0) (A 2))))))

def crDKr13 : Noun :=
  (C (A 8) (C crDKc13 crDKr14))

def crDKr12 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C crDKc12 (C (A 7) (C (C (A 10) (C (C (A 0x7fffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) crDKr13))))))))

def crDKr11 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C crDKc11 (C (A 7) (C (C (A 10) (C (C (A 0x3fffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) crDKr12))))))))

def crDKr10 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C crDKc10 (C (A 7) (C (C (A 10) (C (C (A 0x1fffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) crDKr11))))))))

def crDKr9 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C crDKc9 (C (A 7) (C (C (A 10) (C (C (A 0xfffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) crDKr10))))))))

def crDKr8 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C crDKc8 (C (A 7) (C (C (A 10) (C (C (A 0x7ffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) crDKr9))))))))

def crDKr7 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C crDKc7 (C (A 7) (C (C (A 10) (C (C (A 0x3ffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) crDKr8))))))))

def crDKr6 : Noun :=
  (C (A 8) (C crDKc6 crDKr7))

def crDKr5 : Noun :=
  (C (A 8) (C crDKc5 crDKr6))

def crDKr4 : Noun :=
  (C (A 8) (C crDKc4 crDKr5))

def crDKr3 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C crDKc3 (C (A 7) (C (C (A 10) (C (C (A 1022) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) crDKr4))))))))

def crDKr2 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C crDKc2 (C (A 7) (C (C (A 10) (C (C (A 510) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) crDKr3))))))))

def crDKr1 : Noun :=
  (C (A 8) (C crDKc1 crDKr2))

def crDKr0 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) crDKr1))

theorem crdk_eq : crDCall = crDKr0 := by kernel_rfl

end Compiler
end Formalization
