import lemmas.Compiler.CompMemberGate
import lemmas.Hoon.RollUni
import lemmas.Hoon.Ju

/-!
# `+compile-scc-in` on an SCC of one bell

The gate `+compile-scc-in` (arm `2732` of `K`, `csi_at`, its body `csiBody`,
cut by `tools/gen/member.py`) on `[scc long-ska jets-hot cache]`:

1. `csiLevy`: `(levy ~(tap in scc) ~(has by nary.cache))`, then `csiHit` (the
   straights from the cache) or the rest;
2. `=|  map-local`, `csiKids` (`kids`, a `+rep:in` over `scc` with `+int:in`,
   not linked: a hypothesis on its product), `csiDone` (`done`), the push of
   `member` (`memArm`) and of `final` (`csiFinalA`);
3. on `done`, `csiDoneCall`: `(final | map-local cache)`, otherwise the fixed
   point `csiFix` (not run for a lone bell that does not call itself).

`final` (`fBody`) rolls `member` over `~(tap in scc)` (`fRoll`, with the gate
`fGate`) and unites the straights into `nary.cache` (`fUni`, `+uni:by`, not
linked: a hypothesis on its product).
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The nouns -/

/-- The fixed point of the shapes (`?.  done`), not run for a lone bell. -/
def csiFix : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 186) (C (A 10) (C (C (A 6) (C (A 0) (A 4092))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 1) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 14)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 6)))) (C (C (A 8) (C (C (A 9) (C (A 0x2fbd7f) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 125))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 381) (C (A 10) (C (C (A 6) (C (A 0) (A 124))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 13))) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 60) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 84) (C (A 10) (C (C (A 6) (C (A 0) (A 124))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2))))))))) (C (A 10) (C (C (A 14) (C (C (C (A 0) (A 12)) (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 186) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 760) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 46) (C (A 10) (C (C (A 6) (C (A 0) (A 1022))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2))))))))) (C (A 1) (A 0)))) (C (A 10) (C (C (A 6) (C (A 0) (A 13))) (C (A 0) (A 1)))))))))))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 57)))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 61) (C (C (A 0) (A 56)) (C (A 0) (A 61)))) (C (A 10) (C (C (A 14) (C (A 0) (A 29))) (C (A 0) (A 1)))))))) (C (A 8) (C (C (A 0) (A 114)) (C (A 8) (C (C (C (C (A 0) (A 120)) (C (A 0) (A 243))) (C (A 0) (A 61))) (C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 381) (C (A 10) (C (C (A 6) (C (A 0) (A 508))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (A 0) (A 2))) (C (A 0) (A 7)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 60) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 84) (C (A 10) (C (C (A 6) (C (A 0) (A 508))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2))))))))) (C (A 10) (C (C (A 14) (C (C (C (A 0) (A 6)) (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 186) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 760) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 46) (C (A 10) (C (C (A 6) (C (A 0) (A 4094))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 2)))) (C (A 0) (A 7)))))))))))))))))))))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))))))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (A 7) (C (C (A 9) (C (A 382) (C (A 0) (A 8191)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (C (A 7) (C (C (A 8) (C (C (A 9) (C (A 0x2fa6) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 382) (C (A 0) (A 8191)))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 22) (C (A 0) (A 1023)))))))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (A 0) (A 4087)))) (C (C (A 1) (C (A 7) (C (C (A 8) (C (C (A 0) (A 62)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x79616d)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 1)))) (C (C (A 0) (A 58)) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 59)))))))) (C (A 0) (A 2)))))))) (C (C (A 0) (A 6)) (C (A 0) (A 7)))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 10) (C (C (A 8183) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 766) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (C (A 0x656e6f6e) (A 0)) (C (A 0) (A 0)))) (C (C (A 1) (C (A 0) (A 12))) (C (A 0) (A 1)))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 1) (C (A 1) (C (A 0) (C (A 0) (A 0))))) (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 1) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 254)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (C (A 7) (C (C (A 9) (C (A 382) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (C (A 0) (A 14)) (C (C (A 0) (A 4094)) (C (A 0) (A 0x1fff7))))) (C (C (A 1) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffffff)))) (C (A 9) (C (A 764) (C (A 10) (C (C (A 6) (C (A 0) (A 470))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0xffffffff)))) (C (A 9) (C (A 4) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 760) (C (A 0) (A 0xffffffff)))) (C (A 9) (C (A 46) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7ffe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 60))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (C (A 1) (A 0)) (C (A 0) (A 0)))) (C (C (A 1) (C (A 8) (C (C (A 9) (C (A 38) (C (A 0) (A 0x7ffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3ffffffff)))) (C (A 9) (C (A 1531) (C (A 10) (C (C (A 6) (C (A 0) (A 4055))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))))) (C (A 0) (A 2)))))))))) (C (A 0) (A 61)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))))))) (C (A 0) (A 2))))))))))))) (C (A 6) (C (C (A 0) (A 2)) (C (C (A 8) (C (C (A 4) (C (A 0) (A 234))) (C (A 8) (C (C (A 8) (C (C (A 0) (A 8190)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 124)) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x7473756d)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 75) (C (A 0) (A 0x3ffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 8) (C (A 0) (A 0x3ffffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 4)))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x1ffffffff)))) (C (A 9) (C (A 92) (C (A 10) (C (C (A 6) (C (A 0) (A 0xffffc))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2)))))))))) (C (C (A 0) (A 502)) (C (C (A 0) (A 1022)) (C (A 0) (A 503)))))))) (C (A 0) (A 2)))))))) (C (C (C (A 1) (A 0)) (C (C (A 0) (A 6)) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3ffffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 4054))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 252)) (C (A 0) (A 14)))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 0) (A 4)) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3ffffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 4055))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 252)) (C (A 0) (A 14)))) (C (A 0) (A 2)))))))) (C (A 0) (A 2007)))))))) (C (A 7) (C (C (A 0) (A 2)) (C (C (A 0) (A 6)) (C (A 0) (A 7)))))))))) (C (C (A 0) (A 58)) (C (C (A 0) (A 118)) (C (A 0) (A 119)))))))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 0) (A 8)) (C (C (A 8) (C (C (A 8) (C (C (A 0) (A 0xfffffe)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (C (C (A 1) (A 0x6661656c)) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 1) (C (C (A 1) (A 91)) (C (C (A 1) (A 102)) (C (C (A 1) (A 105)) (C (C (A 1) (A 120)) (C (C (A 1) (A 112)) (C (C (A 1) (A 111)) (C (C (A 1) (A 105)) (C (C (A 1) (A 110)) (C (C (A 1) (A 116)) (C (C (A 1) (A 45)) (C (C (A 1) (A 99)) (C (C (A 1) (A 111)) (C (C (A 1) (A 109)) (C (C (A 1) (A 112)) (C (C (A 1) (A 105)) (C (C (A 1) (A 108)) (C (C (A 1) (A 97)) (C (C (A 1) (A 116)) (C (C (A 1) (A 105)) (C (C (A 1) (A 111)) (C (C (A 1) (A 110)) (C (C (A 1) (A 32)) (C (A 8) (C (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 1498) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x6475)))) (C (A 0) (A 62)))) (C (A 0) (A 2)))))))))) (C (A 1) (C (A 93) (A 0)))) (C (A 8) (C (C (A 1) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 12))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 0) (A 13)) (C (C (A 0) (A 24)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 25))) (C (A 0) (A 1))))))))))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))))))))))))))))))))))))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))))) (C (A 0) (A 1))))))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 0x1fff7) (C (A 0) (A 11))) (C (A 10) (C (C (A 4094) (C (A 0) (A 10))) (C (A 10) (C (C (A 14) (C (A 10) (C (C (A 2) (C (A 1) (A 1))) (C (A 0) (A 4))))) (C (A 10) (C (C (A 6) (C (A 4) (C (A 0) (A 14)))) (C (A 0) (A 3))))))))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 510)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (C (A 0) (A 0x3ffe)) (C (A 0) (A 0x7fff7))))) (C (A 0) (A 2)))))))))))))))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))))))))))))))))

/-- The cache hit: the straights from `nary.cache`. -/
def csiHit : Noun :=
  (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 378) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0))))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 186) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (C (A 1) (A 0)) (C (A 0) (A 0)))) (C (C (A 1) (C (C (A 0) (A 6)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 1006))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))))) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))) (C (A 0) (A 55)))

/-- `(levy ~(tap in scc) ~(has by nary.cache))`. -/
def csiLevy : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0x2fbc) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 186) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 3061) (C (A 10) (C (C (A 6) (C (A 0) (A 238))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))

/-- `kids`: the `+rep:in` over `scc` of the callees in `scc`. -/
def csiKids : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x7ffff)))) (C (A 9) (C (A 383) (C (A 10) (C (C (A 6) (C (A 0) (A 60))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (C (C (A 1) (A 0)) (C (A 0) (A 0))) (A 0))) (C (C (A 1) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 85) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 1531) (C (A 10) (C (C (A 6) (C (A 0) (A 2027))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 252))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))))))) (C (A 0) (A 2))))))))

/-- `done`: `&(?=([* ~ ~] scc) !(~(has ju kids) n.scc n.scc))`. -/
def csiDone : Noun :=
  (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 60))) (C (C (A 6) (C (C (A 3) (C (A 0) (A 121))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 242)))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 243)))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 6) (C (C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 760) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 47) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 248)) (C (A 0) (A 248)))) (C (A 0) (A 2)))))))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1)))))

/-- The gate of the `+roll` of `final`: `member` on `%done`, then `[+<.r +>.r]`. -/
def fGate : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 0) (A 62)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0x656e6f64)))) (C (C (A 0) (A 124)) (C (C (A 0) (A 58)) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))) (C (A 0) (A 59)))))))) (C (A 0) (A 2)))))))) (C (C (A 0) (A 10)) (C (A 0) (A 11)))))

/-- `~(tap in scc)` in `final`. -/
def fTap : Noun :=
  (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 186) (C (A 10) (C (C (A 6) (C (A 0) (A 2044))) (C (A 0) (A 2))))))))))

/-- The sample bunt of that gate. -/
def fRBunt : Noun :=
  (C (C (A 7) (C (C (A 9) (C (A 382) (C (A 0) (A 8191)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (C (A 0) (A 26)) (C (A 0) (A 27))))

/-- The `+roll` of `member` over `~(tap in scc)`. -/
def fRoll : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C fTap (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C fRBunt (C (C (A 1) fGate) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))

/-- `(~(uni by nary.c) m)`. -/
def fUni : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 686) (C (A 10) (C (C (A 6) (C (A 0) (A 26))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 12))) (C (A 0) (A 2))))))))

/-- The body of the gate `final`. -/
def fBody : Noun :=
  (C (A 8) (C fRoll (C (C (A 0) (A 4)) (C (A 10) (C (C (A 2) fUni) (C (A 0) (A 5)))))))

/-- Its sample bunt. -/
def fBunt : Noun :=
  (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0)))))))

/-- The formula that builds `final`. -/
def csiFinalA : Noun :=
  (C (A 8) (C (C (A 1) fBunt) (C (C (A 1) fBody) (C (A 0) (A 1)))))

/-- `(final | map-local cache)`. -/
def csiDoneCall : Noun :=
  (C (A 8) (C (C (A 0) (A 2)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 1)))) (C (C (A 0) (A 126)) (C (A 0) (A 4087))))) (C (A 0) (A 2))))))))

/-- The gate body of `+compile-scc-in`. -/
def csiBody : Noun :=
  (C (A 6) (C csiLevy (C csiHit (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C csiKids (C (A 8) (C csiDone (C (A 8) (C memArm (C (A 8) (C csiFinalA (C (A 6) (C (C (A 0) (A 14)) (C csiDoneCall csiFix))))))))))))))))

/-- Its sample bunt. -/
def csiBunt : Noun :=
  (C (A 0) (C (C (A 0) (C fBunt (A 0))) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (C (A 0) (A 0))))))))

/-- Its `%fast` hint. -/
def csiHint : Noun :=
  (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x6e692d6363732d656c69706d6f63) (C (C (A 0) (A 0x7fff)) (A 0))))) (C (A 0) (A 1))))


/-- The arm `+compile-scc-in`. -/
def csiArm : Noun := C (A 7) (C (C (A 8) (C (C (A 1) csiBunt) (C (C (A 1) csiBody) (C (A 0) (A 1))))) csiHint)

/-- `+compile-scc-in` is arm `2732` of `K`. -/
theorem csi_at : slot? 2732 compK = some csiArm := by kernel_rfl

/-- The bunt of `bell`, which the gate of the `+roll` of `final` computes
for its sample. -/
def bellBuntF : Noun := C (A 7) (C (C (A 9) (C (A 382) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))

noncomputable def bellBunt : Noun := (evalFuel 2000 compK bellBuntF).getD (A 0)

theorem bell_bunt : nock compK bellBuntF = some bellBunt := nock_of_evalFuel (fuel := 2000) (by kernel_rfl)

/-! ## The subjects -/

/-- The sample of `+compile-scc-in`. -/
def csiSam (SCC LONG JH CACHE : Noun) : Noun := C SCC (C LONG (C JH CACHE))

/-- The context of `member` and `final`: `memCtx` with `map-local` empty
and the body of `+compile-scc-in`. -/
def csiCtx (DN KIDS SCC LONG JH CACHE : Noun) : Noun := memCtx DN KIDS (A 0) csiBody SCC LONG JH CACHE

/-- The subject of `final`: the gate `member` on `csiCtx`. -/
def csiSM (DN KIDS SCC LONG JH CACHE : Noun) : Noun :=
  C (C memBody (C memBunt (csiCtx DN KIDS SCC LONG JH CACHE))) (csiCtx DN KIDS SCC LONG JH CACHE)

/-- The core of `final` slammed on `[keep map-local cache]`. -/
def csiFC (KEEP ML CACHE DN KIDS SCC LONG JH CACHE0 : Noun) : Noun :=
  C fBody (C (C KEEP (C ML CACHE)) (csiSM DN KIDS SCC LONG JH CACHE0))

/-- The noun of a set of one element, `[b ~ ~]`. -/
def setOne (b : Noun) : Noun := C b (C (A 0) (A 0))

theorem juIn_layer2 : JuIn mugF layer2 :=
  ⟨by.arm_at, in.arm_at, someIn_layer2, gorIn_morIn_layer2.1, gorIn_morIn_layer2.2⟩

/-! ## From the gate to `final` -/

/-- **`+compile-scc-in` on an SCC of one bell `b` not in `nary.cache`, which
does not call itself**: the cache test fails (`hnary`: `+get:by` of
`nary.cache` at `b` is `~`), `kids` is `KIDS` (`hkids`, the `+rep:in` with
`+int:in`, not linked), `~(has ju kids) b b` is `|` (`hju`), so `done` is `&`
and the gate is `final` on `[| ~ cache]`. -/
theorem csi_to_final (b LONG JH NARY CR KIDS : Noun)
    (hnary : getF mugF b NARY = some (A 0))
    (hkids : nock (C (A 0) (C csiBody (C (csiSam (setOne b) LONG JH (C NARY CR)) compK))) csiKids = some KIDS)
    (hju : juHasF mugF b b KIDS = some false) :
    nock (C csiBody (C (csiSam (setOne b) LONG JH (C NARY CR)) compK)) csiBody
      = nock (csiFC (A 1) (A 0) (C NARY CR) (A 0) KIDS (setOne b) LONG JH (C NARY CR)) fBody := by
  have hL := compK_layer2
  have hhas := has_gate (mug := mugF) layer2 ⟨someIn_layer2, gorIn_morIn_layer2.1⟩ b NARY (A 0) hnary
  have hlevy := levy_gate layer2 by.has.battery (A 0) (C by.battery (C NARY layer2)) (fun _ => false) [b]
    (by intro x hx; simp at hx; subst hx; simpa using hhas)
  simp only [listN, appendN, List.all_cons, List.all_nil, Bool.and_true] at hlevy
  have hjh := ju_has_gate layer2 juIn_layer2 b b KIDS false hju
  have hma : ∀ d, nock d memArm = some (C memBody (C memBunt d)) := by
    intro d; unfold memArm memHint; generalize memBody = B; generalize memBunt = U; simp [nock_exec]
  conv => { lhs; arg 2; unfold csiBody }
  unfold csiFC csiSM csiCtx csiSam setOne memCtx at *
  generalize compK = KC at hL hkids ⊢
  simp [nock_exec, hL, csiLevy, levy.arm_at, levy_arm, in.arm_at, in_arm, in.tap.arm_at, tap_arm, tap_loop, tapF,
    by.arm_at, by_arm, by.has.arm_at, has_arm, hlevy, hkids, csiDone, ju.arm_at, ju_arm, ju.has.arm_at, ju_has_arm,
    hjh, hma, csiFinalA, csiDoneCall]

/-! ## `final` on a set of one bell -/

/-- **`final` on `[| map-local cache]` for `scc = [b ~ ~]`**: the `+roll`
over `~(tap in scc)`, which is `[b ~]`, slams `member` once (`hm`: it returns
`[chg ml cache]` with `nary` at the head of the cache), keeps `[ml cache]`,
and puts `(~(uni by nary) ml)` (`huni`, `+uni:by` not linked) at `nary`. -/
theorem csi_final_one (b ML CACHE DN KIDS LONG JH CACHE0 CHG ML' NARY REST NARYU : Noun)
    (hm : nock (C memBody (C (memSam b (A 0x656e6f64) (A 1) ML (A 0) CACHE) (csiCtx DN KIDS (setOne b) LONG JH CACHE0)))
      memBody = some (C CHG (C ML' (C NARY REST))))
    (huni : nock (C by.uni.battery (C ML' (C by.battery (C NARY layer2)))) by.uni.battery = some NARYU) :
    nock (csiFC (A 1) ML CACHE DN KIDS (setOne b) LONG JH CACHE0) fBody = some (C ML' (C NARYU REST)) := by
  have hL := compK_layer2
  have hbb := bell_bunt
  have hr := roll_gate_one layer2 fGate bellBunt (C ML CACHE)
    (csiFC (A 1) ML CACHE DN KIDS (setOne b) LONG JH CACHE0) b
  simp only [listN, appendN] at hr
  have hmc : nock (C fGate (C (C b (C ML CACHE)) (csiFC (A 1) ML CACHE DN KIDS (setOne b) LONG JH CACHE0))) fGate
      = some (C ML' (C NARY REST)) := by
    unfold fGate
    unfold csiFC csiSM memSam at *
    generalize memBody = MB at hm ⊢
    simp [nock_exec, hm]
  conv => { lhs; arg 2; unfold fBody }
  unfold csiFC csiSM csiCtx setOne memCtx at *
  generalize compK = KC at hL hbb hr hmc ⊢
  unfold bellBuntF at hbb
  simp only [nock_exec] at hbb
  simp [nock_exec, hL, fRoll, roll.arm_at, roll_arm, fTap, in.arm_at, in_arm, in.tap.arm_at, tap_arm, tap_loop, tapF,
    fRBunt, hbb, hr, hmc, fUni, by.arm_at, by_arm, by.uni.arm_at, uni_by_arm, huni]

/-! ## The gate on an SCC of one bell -/

/-- **`+compile-scc-in` on an SCC of one bell `b` that is not in
`nary.cache` and does not call itself**, on the final pass whose straight
`st` the model gives (`hst`): it returns `[[[b st] ~ ~] cache]`, where
`cache` is the cache of `+inlined` with `sure.cache` updated (`SURE'`) and
`nary` united with `[[b st] ~ ~]` (`NARYU`, `huni`).  The other hypotheses
are those of `csi_to_final` (the cache test, `kids`, `done`) and of
`mem_gate` (with `keep` false, as `final` is called with `|`). -/
theorem csi_gate_one (cape : Cape) (DATA FOL CODE LSR JH NARY CR KIDS : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0))
    (hkids : nock (C (A 0) (C csiBody (C (csiSam (setOne (C (C cape.toNoun DATA) FOL)) (C CODE LSR) JH (C NARY CR))
      compK))) csiKids = some KIDS)
    (hju : juHasF mugF (C (C cape.toNoun DATA) FOL) (C (C cape.toNoun DATA) FOL) KIDS = some false)
    (nm : Nomm) (C1 C2 C3 C4 SURE : Noun)
    (hinl : nock (C inlBody (C (C (C (C cape.toNoun DATA) FOL) (C (C CODE LSR) (C JH (C NARY CR)))) compK)) inlBody
      = some (C nm.toNoun (cacheN C1 C2 C3 C4 SURE)))
    (hpu : nm.pure = true) (h6 : noSix nm = true) (ht : tenOk nm = true)
    (nex : NextL CSet) (g1 : Gen (TreapMap mugF))
    (hrunL : runL nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))
    (s : Sure CSet) (hlaz : nex.laz = Lazy.ofSure s)
    (ord : NeedOrd) (hsc : nock (C scBody (C (C nex.laz.toNoun cape.toNoun) compK)) scBody = some ord.toNoun)
    (hargs : nex.th.args = []) (nedF : Need) (g2 : Gen (TreapMap mugF))
    (hnoar : needOrdAllocRegs ord g1 = some (nedF, g2))
    (hb : NoBake nedF (Sock.mk cape DATA))
    (sur : NeedOrd) (hsur : sureOf (needToOrd s.ned) s.lok cape = some sur)
    (WAS SURE' : Noun) (hwas : getF mugF (C (C cape.toNoun DATA) FOL) SURE = some WAS)
    (hw : WAS = A 0 ∨ ∃ u, WAS = C (A 0) u)
    (hput : putF mugF (C (C cape.toNoun DATA) FOL) (memSurKN false WAS sur.toNoun) SURE = some SURE')
    (st : Straight (TreapMap mugF))
    (hst : finishLF (S := CSet) (Map := TreapMap mugF) nm ord cape (fun n => (n, [])) = some st)
    (NARYU : Noun)
    (huni : nock (C by.uni.battery (C (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0)))
      (C by.battery (C C1 layer2)))) by.uni.battery = some NARYU) :
    nock (C csiBody (C (csiSam (setOne (C (C cape.toNoun DATA) FOL)) (C CODE LSR) JH (C NARY CR)) compK)) csiBody
      = some (C (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))) (C NARYU (C C2 (C C3 (C C4 SURE'))))) := by
  rw [csi_to_final _ _ _ _ _ _ hnary hkids hju]
  have hm := mem_gate cape DATA FOL false (C NARY CR) (A 0) KIDS (A 0) csiBody
    (setOne (C (C cape.toNoun DATA) FOL)) CODE LSR JH (C NARY CR) nm C1 C2 C3 C4 SURE hinl hpu h6 ht nex g1 hrunL s
    hlaz ord hsc hargs nedF g2 hnoar hb sur hsur WAS SURE' hwas hw hput
  rw [hst, Option.map_some] at hm
  exact csi_final_one (hm := hm) (huni := huni)

/-! ## The call in `+compile-unary` -/

theorem csi_arm (d : Noun) : nock d csiArm = some (C csiBody (C csiBunt d)) := by
  unfold csiArm csiHint; generalize csiBody = B; generalize csiBunt = U; simp [nock_exec]

/-- **The call of `+compile-scc-in` in the trap of `+compile-unary`** is the
gate on `+.args`. -/
theorem cu_csi_eq (FUNC SCC CODE LSR JH CACHE : Noun) :
    nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuCsi
      = nock (C csiBody (C (csiSam SCC (C CODE LSR) JH CACHE) compK)) csiBody := by
  have ha := csi_at
  unfold cuTC cuSam cuCsi csiSam
  generalize compK = KC at ha ⊢
  simp [nock_exec, ha, csi_arm]

/-- **`hcsi` of `cu_gate` on an SCC of one bell**: under the hypotheses of
`csi_gate_one`, `+compile-scc-in` called from the trap of `+compile-unary`
on `[[b ~ ~] long-ska jets-hot cache]` returns `[[[b st] ~ ~] cache']`, so
the gate of `+compile-unary` is `finishLU` of the nomm of `func`
(`cu_gate`) with these `NM` and `CA`. -/
theorem cu_gate_scc_one (cape : Cape) (DATA FOL CODE LSR JH NARY CR KIDS : Noun)
    (hnary : getF mugF (C (C cape.toNoun DATA) FOL) NARY = some (A 0))
    (hkids : nock (C (A 0) (C csiBody (C (csiSam (setOne (C (C cape.toNoun DATA) FOL)) (C CODE LSR) JH (C NARY CR))
      compK))) csiKids = some KIDS)
    (hju : juHasF mugF (C (C cape.toNoun DATA) FOL) (C (C cape.toNoun DATA) FOL) KIDS = some false)
    (nm : Nomm) (C1 C2 C3 C4 SURE : Noun)
    (hinl : nock (C inlBody (C (C (C (C cape.toNoun DATA) FOL) (C (C CODE LSR) (C JH (C NARY CR)))) compK)) inlBody
      = some (C nm.toNoun (cacheN C1 C2 C3 C4 SURE)))
    (hpu : nm.pure = true) (h6 : noSix nm = true) (ht : tenOk nm = true)
    (nex : NextL CSet) (g1 : Gen (TreapMap mugF))
    (hrunL : runL nm (CGoalL.done : CGoalL CSet) [] (gen0 : Gen (TreapMap mugF)) = some (nex, g1))
    (s : Sure CSet) (hlaz : nex.laz = Lazy.ofSure s)
    (ord : NeedOrd) (hsc : nock (C scBody (C (C nex.laz.toNoun cape.toNoun) compK)) scBody = some ord.toNoun)
    (hargs : nex.th.args = []) (nedF : Need) (g2 : Gen (TreapMap mugF))
    (hnoar : needOrdAllocRegs ord g1 = some (nedF, g2))
    (hb : NoBake nedF (Sock.mk cape DATA))
    (sur : NeedOrd) (hsur : sureOf (needToOrd s.ned) s.lok cape = some sur)
    (WAS SURE' : Noun) (hwas : getF mugF (C (C cape.toNoun DATA) FOL) SURE = some WAS)
    (hw : WAS = A 0 ∨ ∃ u, WAS = C (A 0) u)
    (hput : putF mugF (C (C cape.toNoun DATA) FOL) (memSurKN false WAS sur.toNoun) SURE = some SURE')
    (st : Straight (TreapMap mugF))
    (hst : finishLF (S := CSet) (Map := TreapMap mugF) nm ord cape (fun n => (n, [])) = some st)
    (NARYU : Noun)
    (huni : nock (C by.uni.battery (C (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0)))
      (C by.battery (C C1 layer2)))) by.uni.battery = some NARYU)
    (FUNC V : Noun) (n : Nomm) (hpu' : n.pure = true) (h6' : noSix n = true) (ht' : tenOk n = true)
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    nock (C cuGB (C (cuSam FUNC (setOne (C (C cape.toNoun DATA) FOL)) CODE LSR JH (C NARY CR)) compK)) cuGB
      = (finishLU (S := CSet) (Map := TreapMap mugF) n).map fun st' =>
          C (C st'.toNoun (C (C (C (C cape.toNoun DATA) FOL) st.toNoun) (C (A 0) (A 0))))
            (C NARYU (C C2 (C C3 (C C4 SURE')))) := by
  have hcsi := csi_gate_one cape DATA FOL CODE LSR JH NARY CR KIDS hnary hkids hju nm C1 C2 C3 C4 SURE hinl hpu h6 ht
    nex g1 hrunL s hlaz ord hsc hargs nedF g2 hnoar hb sur hsur WAS SURE' hwas hw hput st hst NARYU huni
  rw [← cu_csi_eq FUNC] at hcsi
  exact cu_gate FUNC _ CODE LSR JH _ _ _ V n hpu' h6' ht' hcsi hgot hv

end Compiler
end Formalization
