import lemmas.Compiler.CompRunLink

/-!
# The Nock of `+sect`, cut into named parts

Written by `tools/gen/sect.py` between the markers; do not edit by hand.
The gate is door arm `6906`, `[7 [8 [1 scBunt] [1 scBat] 0 1] [11 %fast ..]]`
(`sc_at`); `scBat` is built from the parts, so `sc_at` checks the cut.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon

-- BEGIN sect

def scParG : Noun :=
  (C (A 10) (C (C (A 2) (C (A 0) (A 59))) (C (A 0) (A 6))))

def scInner : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706f68)) (C (A 0) (A 54)))) (C (C (A 10) (C (C (A 30) (C (A 0) (A 30))) (C (A 0) (A 6)))) (C (A 0) (A 0)))))

def scLensB : Noun :=
  (C (A 8) (C (C (A 1) (C (A 0) (C (A 0) (C (A 0x6d6f62) (A 0))))) (C (C (A 1) scInner) (C (A 0) (A 1)))))

def scLB : Noun :=
  (C (A 7) (C (C (A 8) (C (C (A 9) (C (A 1407) (C (A 0) (A 0x7fffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0x9ddf) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x64697875)))) (C (A 0) (A 14)))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 5) (C (C (A 0) (A 14)) (C (A 0) (A 2)))) (C (A 0) (A 6))))))) (C (A 0) (A 1)))))))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))

def scGS : Noun :=
  (C (A 10) (C (C (A 0xfff7e) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1ffffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0xffff7e))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 120)) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 0) (A 5)) (C (A 0) (A 115))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 15))))

def scG0Y : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 0x3fff)))))) (C (A 7) (C (C (A 10) (C (C (A 0x1fffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3ffffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 254))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 498)) (C (A 0) (A 6)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 124) (C (C (C (A 1) (A 0)) (C (A 0) (A 242))) (C (A 0) (A 124)))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 250) (C (C (A 1) (A 0)) (C (A 0) (A 250)))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 251) (C (C (A 0) (A 2)) (C (A 0) (A 251)))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 0xffff7e) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3ffffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0x1ffff7e))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 248)) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 0) (A 2)) (C (A 0) (A 243))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 0) (A 31))))))))))))))))))))

def scG1Y : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 0x55ffff) (C (A 0) (A 0x3fff)))))) (C (A 7) (C (C (A 10) (C (C (A 0x1fffe) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3ffffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 254))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 498)) (C (A 0) (A 6)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 250) (C (C (C (A 1) (A 0)) (C (A 0) (A 242))) (C (A 0) (A 250)))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 124) (C (C (A 1) (A 0)) (C (A 0) (A 124)))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 251) (C (C (A 0) (A 2)) (C (A 0) (A 251)))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 0xffff7e) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3ffffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0x1ffff7e))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 248)) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 0) (A 2)) (C (A 0) (A 243))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 0) (A 31))))))))))))))))))))

def scG0 : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 7) (C (A 0) (A 13))) (C (A 0) (A 1)))) (C (A 6) (C (C (A 8) (C (C (A 0) (A 62)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 115))) (C (A 0) (A 2)))))))) (C (C (A 0) (A 7)) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffffff)))) (C (A 9) (C (A 764) (C (A 10) (C (C (A 6) (C (A 0) (A 62))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 114))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C scG0Y scGS))))))))))

def scG1 : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 7) (C (A 0) (A 13))) (C (A 0) (A 1)))) (C (A 6) (C (C (A 8) (C (C (A 0) (A 62)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 115))) (C (A 0) (A 2)))))))) (C (C (A 0) (A 7)) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffffff)))) (C (A 9) (C (A 764) (C (A 10) (C (C (A 6) (C (A 0) (A 62))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 114))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C scG1Y scGS))))))))))

def scRep0 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 767) (C (A 10) (C (C (A 6) (C (A 0) (A 254))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (C (A 1) (A 0)) (C (C (A 1) (A 0)) scLB)) (C (A 0) (A 1))) (C (C (A 1) scG0) (C (A 0) (A 1)))))))) (C (A 0) (A 2))))))))))

def scRep1 : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 767) (C (A 10) (C (C (A 6) (C (A 0) (A 126))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (C (A 1) (A 0)) (C (C (A 1) (A 0)) scLB)) (C (A 0) (A 1))) (C (C (A 1) scG1) (C (A 0) (A 1)))))))) (C (A 0) (A 2))))))))))

def scJabs : Noun :=
  (C (A 7) (C (C (A 10) (C (C (A 0x3ffde) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 379) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7ffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 62)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (C (A 0) (C (A 0x6d6f62) (A 0))))) (C (C (A 1) scParG) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) scLensB) (C (A 0) (A 1))))) (C (A 7) (C (C (A 10) (C (C (A 0x7ffde) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffffff)))) (C (A 9) (C (A 379) (C (A 10) (C (C (A 6) (C (A 0) (A 0xfffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 0xfff6)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 0) (A 2)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 0x7ffde) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffffff)))) (C (A 9) (C (A 379) (C (A 10) (C (C (A 6) (C (A 0) (A 0xfffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 0x1ffee)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 0) (A 2)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 58))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 0) (A 0x3ffe))))))))))

def scArgs : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 0x3ffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 0x3ff6))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706f68)) (C (A 0) (A 22)))) (C (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7ffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 0xffee))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706f68)) (C (A 0) (A 22)))) (C (C (C (A 0) (A 110)) (C (C (A 0) (A 46)) (C (A 7) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 0xfffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 126))) (C (A 0) (A 2)))))))) (C (A 0) (A 2)))))) (C (A 0) (A 0))))))) (C (A 0) (A 0)))))))

def scOt : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7fde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 2038))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 0xffde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 8174))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706f68)) (C (A 0) (A 54)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706f68)) (C (A 0) (A 22)))) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 111)) (C (A 0) (A 47)))) (C (C (A 0) (A 111)) (C (A 0) (A 0))))) (C (A 0) (A 0))))) (C (A 0) (A 0)))))))))

def scND : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 687) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7f7e))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 4031))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 687) (C (A 10) (C (C (A 6) (C (A 0) (A 8127))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 8126))) (C (A 0) (A 2)))))))) (C (A 8) (C scOt (C (A 8) (C (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) (C (A 8) (C (C (A 9) (C (A 0x2fbde) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) (C (A 5) (C (C (A 0) (A 6)) (C (A 0) (A 0x3ffbc))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1))))) (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C scArgs (C (A 7) (C scRep0 (C (A 7) (C scRep1 scJabs))))))))))))))))

def scThr : Noun :=
  (C (A 6) (C (C (A 9) (C (A 1398) (C (A 0) (A 31)))) (C (C (A 0) (A 126)) scND)))

def scTail : Noun :=
  (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 486)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 982)))) (C (C (C (C (A 1) (C (C (A 0x656e6f6e) (A 0)) (A 0))) (C (C (C (C (C (A 0) (A 6)) (C (A 0) (A 242))) (C (C (A 0) (A 2)) (C (A 0) (A 490)))) (C (A 1) (A 0))) (C (A 1) (A 0)))) (C (C (A 0) (A 6)) (C (A 0) (A 2)))) (C (A 0) (A 0))))) (C (A 0) (A 0))))) (C (A 0) (A 126)))

def scB : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x706f68)))) (C (A 0) (A 115)))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 62) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0xaaaa) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x706f68)))) (C (A 0) (A 491)))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 8) (C (C (A 9) (C (A 0x555de) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 0) (A 2014)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 126) (C (A 8) (C (C (A 9) (C (A 0x555de) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 0) (A 2014)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 126) scThr) (C (A 0) (A 1)))) scTail))))))))))))))))))))))

def scBat : Noun :=
  (C (A 6) (C (C (A 3) (C (A 0) (A 222))) (C scB (C (A 0) (A 0)))))

def scBunt : Noun :=
  (C (C (A 0x7478656e) (C (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))) (C (A 0) (A 0)))) (C (C (A 0x7478656e) (C (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))) (C (A 0) (A 0)))) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0)))))))

-- END sect

/-- The arm `+sect` of the door, with its `%fast` hint. -/
def scArm : Noun :=
  C (A 7) (C (C (A 8) (C (C (A 1) scBunt) (C (C (A 1) scBat) (C (A 0) (A 1)))))
    (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x746365732d706d6f63) (C (C (A 0) (A 0x7ffff)) (A 0)))))
      (C (A 0) (A 1)))))

theorem sc_at : slot? 6906 comp.door = some scArm := by kernel_rfl

end Compiler
end Formalization
