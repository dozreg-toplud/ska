import lemmas.Compiler.OptLinkBase
import lemmas.Hoon.ListsMore

/-!
# The helpers of the optimizer: `+get-jmps`, `+jmp-regs`, `+get-regs`, `+get-reg-safe-assignment`

Four arms of `compTypes` (the core of the IR types, axis `7` of `optC`),
each `[8 [1 bunt] [1 body] [0 1]]` with no hint (`gj_at`, `jr_at`, `gr_at`,
`gs_at`, kernel facts).  The nouns are written by `tools/gen/optlink.py
helpers`.  An arm pulled from `compTypes` builds the gate `[body [bunt
compTypes]]`, so the gate theorems are stated with the context `compTypes`.

* `gj_gate`: `+get-jmps` on a terminator other than `%lti` is `getJmps`
  (`Ska/Opt.lean`); `gj_gate_lti`: on `%lti` it is `~`, where `getJmps`
  gives `[z, o]` (the last case of its `?-`, `%bom`, runs with no test under a
  `%toss` hint, so every tag not tested before gives `~`).
* `jr_gate`: `+jmp-regs` is `jmpRegs` (`+murn` with `+same`).
* `gr_gate_pole`, `gr_gate_fin`: `+get-regs` on an op is `poleRegs`, on a
  terminator other than `%lti` `finRegs`; `gr_gate_lti`: `~` on `%lti`.
* `gs_gate`: `+get-reg-safe-assignment` is `safeAssign`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## The nouns -/

/-- The sample bunt of `+get-jmps`. -/
def gjBunt : Noun :=
  (C (A 0x6d6f62) (A 0))

/-- The gate body of `+get-jmps` (arm `1502` of `compTypes`). -/
def gjBody : Noun :=
  (C (A 7) (C (C (A 0) (A 6)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x716c63)) (C (A 0) (A 2)))) (C (C (C (A 0) (A 14)) (C (C (A 0) (A 15)) (C (A 1) (A 0)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x717165)) (C (A 0) (A 2)))) (C (C (C (A 0) (A 30)) (C (C (A 0) (A 31)) (C (A 1) (A 0)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6e7262)) (C (A 0) (A 2)))) (C (C (C (A 0) (A 14)) (C (C (A 0) (A 15)) (C (A 1) (A 0)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x7a7262)) (C (A 0) (A 2)))) (C (C (C (A 0) (A 14)) (C (C (A 0) (A 15)) (C (A 1) (A 0)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706f68)) (C (A 0) (A 2)))) (C (C (C (A 0) (A 3)) (C (A 1) (A 0))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706d6a)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x666d6a)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x70736a)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x66736a)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6e6f64)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x6d6f62)) (C (A 0) (A 2))))) (C (A 1) (A 0))))))))))))))))))))))))))))))))))))

/-- The sample bunt of `+jmp-regs`. -/
def jrBunt : Noun :=
  (C (A 0) (A 0))

/-- The gate body of `+jmp-regs` (arm `175` of `compTypes`). -/
def jrBody : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0x17defea) (C (A 0) (A 0x1ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 0x17dae) (C (A 0) (A 0x1ffff)))))))) (C (A 0) (A 2))))))))

/-- The sample bunt of `+get-regs`. -/
def grBunt : Noun :=
  gjBunt

/-- The gate body of `+get-regs` (arm `84` of `compTypes`). -/
def grBody : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6d6d69)) (C (A 0) (A 12)))) (C (C (A 7) (C (C (A 0) (A 6)) (C (C (A 0) (A 7)) (C (A 1) (A 0))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x766f6d)) (C (A 0) (A 12)))) (C (C (A 7) (C (C (A 0) (A 6)) (C (C (A 0) (A 6)) (C (C (A 0) (A 7)) (C (A 1) (A 0)))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x636e69)) (C (A 0) (A 12)))) (C (C (A 7) (C (C (A 0) (A 6)) (C (C (A 0) (A 6)) (C (C (A 0) (A 7)) (C (A 1) (A 0)))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6e6f63)) (C (A 0) (A 12)))) (C (C (A 7) (C (C (A 0) (A 6)) (C (C (A 0) (A 6)) (C (C (A 0) (A 14)) (C (C (A 0) (A 15)) (C (A 1) (A 0))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x646568)) (C (A 0) (A 12)))) (C (C (A 7) (C (C (A 0) (A 6)) (C (C (A 0) (A 6)) (C (C (A 0) (A 7)) (C (A 1) (A 0)))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6c6174)) (C (A 0) (A 12)))) (C (C (A 7) (C (C (A 0) (A 6)) (C (C (A 0) (A 6)) (C (C (A 0) (A 7)) (C (A 1) (A 0)))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6c6563)) (C (A 0) (A 12)))) (C (C (A 7) (C (C (A 0) (A 6)) (C (C (A 0) (A 3)) (C (A 1) (A 0))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x626f6c)) (C (A 0) (A 12)))) (C (C (A 7) (C (C (A 0) (A 6)) (C (C (A 0) (A 3)) (C (A 1) (A 0))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x757165)) (C (A 0) (A 12)))) (C (C (A 7) (C (C (A 0) (A 6)) (C (C (A 0) (A 6)) (C (C (A 0) (A 7)) (C (A 1) (A 0)))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x707368)) (C (A 0) (A 12)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x657368)) (C (A 0) (A 12)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706468)) (C (A 0) (A 12)))) (C (C (A 7) (C (C (A 0) (A 6)) (C (C (A 0) (A 14)) (C (A 1) (A 0))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656468)) (C (A 0) (A 12)))) (C (C (A 7) (C (C (A 0) (A 6)) (C (C (A 0) (A 14)) (C (A 1) (A 0))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706d68)) (C (A 0) (A 12)))) (C (C (A 0) (A 54)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656d68)) (C (A 0) (A 12)))) (C (C (A 0) (A 54)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706368)) (C (A 0) (A 12)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656368)) (C (A 0) (A 12)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x797073)) (C (A 0) (A 12)))) (C (C (A 7) (C (C (A 0) (A 6)) (C (C (A 0) (A 6)) (C (C (A 0) (A 14)) (C (C (A 0) (A 15)) (C (A 1) (A 0))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6b6f6e)) (C (A 0) (A 12)))) (C (C (A 7) (C (C (A 0) (A 6)) (C (C (A 0) (A 6)) (C (C (A 0) (A 14)) (C (C (A 0) (A 15)) (C (A 1) (A 0))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6c6163)) (C (A 0) (A 12)))) (C (C (A 7) (C (C (A 0) (A 6)) (C (C (A 0) (A 15)) (C (A 0) (A 14))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x666163)) (C (A 0) (A 12)))) (C (C (A 7) (C (C (A 0) (A 6)) (C (C (A 0) (A 30)) (C (A 0) (A 14))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6d6163)) (C (A 0) (A 12)))) (C (C (A 7) (C (C (A 0) (A 6)) (C (C (A 0) (A 30)) (C (A 0) (A 14))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6c7363)) (C (A 0) (A 12)))) (C (C (A 7) (C (C (A 0) (A 6)) (C (C (A 0) (A 14)) (C (C (A 0) (A 15)) (C (A 1) (A 0)))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x667363)) (C (A 0) (A 12)))) (C (C (A 7) (C (C (A 0) (A 6)) (C (C (A 0) (A 14)) (C (C (A 0) (A 30)) (C (A 1) (A 0)))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6d7363)) (C (A 0) (A 12)))) (C (C (A 7) (C (C (A 0) (A 6)) (C (C (A 0) (A 14)) (C (C (A 0) (A 30)) (C (A 1) (A 0)))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x716c63)) (C (A 0) (A 12)))) (C (C (C (A 0) (A 26)) (C (A 8) (C (C (A 9) (C (A 0xbef7f4) (C (A 0) (A 0x1ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 175) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 118))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 175) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 119))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x717165)) (C (A 0) (A 12)))) (C (C (C (A 0) (A 26)) (C (C (A 0) (A 54)) (C (A 8) (C (C (A 9) (C (A 0xbef7f4) (C (A 0) (A 0x1ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 175) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 238))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 175) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 239))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2)))))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6e7262)) (C (A 0) (A 12)))) (C (C (C (A 0) (A 26)) (C (A 8) (C (C (A 9) (C (A 0xbef7f4) (C (A 0) (A 0x1ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 175) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 118))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 175) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 119))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x7a7262)) (C (A 0) (A 12)))) (C (C (C (A 0) (A 26)) (C (A 8) (C (C (A 9) (C (A 0xbef7f4) (C (A 0) (A 0x1ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 175) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 118))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 175) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 119))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706f68)) (C (A 0) (A 12)))) (C (C (A 8) (C (C (A 9) (C (A 175) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706d6a)) (C (A 0) (A 12)))) (C (C (A 0) (A 27)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x666d6a)) (C (A 0) (A 12)))) (C (C (A 0) (A 54)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x70736a)) (C (A 0) (A 12)))) (C (C (A 7) (C (C (A 0) (A 6)) (C (C (A 0) (A 7)) (C (A 1) (A 0))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x66736a)) (C (A 0) (A 12)))) (C (C (A 7) (C (C (A 0) (A 6)) (C (C (A 0) (A 14)) (C (A 1) (A 0))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6e6f64)) (C (A 0) (A 12)))) (C (C (A 7) (C (C (A 0) (A 6)) (C (C (A 0) (A 3)) (C (A 1) (A 0))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x6d6f62)) (C (A 0) (A 12))))) (C (A 1) (A 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- The sample bunt of `+get-reg-safe-assignment`. -/
def gsBunt : Noun :=
  (C (A 0x6d7363) (C (C (C (A 1) (A 0)) jrBunt) (C (A 0) jrBunt)))

/-- The gate body of `+get-reg-safe-assignment` (arm `750` of `compTypes`). -/
def gsBody : Noun :=
  (C (A 7) (C (C (A 0) (A 6)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6d6d69)) (C (A 0) (A 2)))) (C (C (C (A 1) (A 0)) (C (A 0) (A 7))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x766f6d)) (C (A 0) (A 2)))) (C (C (C (A 1) (A 0)) (C (A 0) (A 7))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x636e69)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6e6f63)) (C (A 0) (A 2)))) (C (C (C (A 1) (A 0)) (C (A 0) (A 15))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x646568)) (C (A 0) (A 2)))) (C (C (C (A 1) (A 0)) (C (A 0) (A 7))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6c6174)) (C (A 0) (A 2)))) (C (C (C (A 1) (A 0)) (C (A 0) (A 7))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6c6563)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x626f6c)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x757165)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x707368)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x657368)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706468)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656468)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706d68)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656d68)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x706368)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656368)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x797073)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6b6f6e)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6c6163)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x666163)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6d6163)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x6c7363)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x667363)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 0x6d7363)) (C (A 0) (A 2))))) (C (A 1) (A 0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- The arm `+get-jmps`. -/
def gjArm : Noun := C (A 8) (C (C (A 1) gjBunt) (C (C (A 1) gjBody) (C (A 0) (A 1))))
/-- The arm `+jmp-regs`. -/
def jrArm : Noun := C (A 8) (C (C (A 1) jrBunt) (C (C (A 1) jrBody) (C (A 0) (A 1))))
/-- The arm `+get-regs`. -/
def grArm : Noun := C (A 8) (C (C (A 1) grBunt) (C (C (A 1) grBody) (C (A 0) (A 1))))
/-- The arm `+get-reg-safe-assignment`. -/
def gsArm : Noun := C (A 8) (C (C (A 1) gsBunt) (C (C (A 1) gsBody) (C (A 0) (A 1))))

theorem gj_at : slot? 1502 compTypes = some gjArm := by kernel_rfl
theorem jr_at : slot? 175 compTypes = some jrArm := by kernel_rfl
theorem gr_at : slot? 84 compTypes = some grArm := by kernel_rfl
theorem gs_at : slot? 750 compTypes = some gsArm := by kernel_rfl

@[nock_exec] theorem gj_arm (d : Noun) : nock d gjArm = some (C gjBody (C gjBunt d)) := by
  unfold gjArm; generalize gjBody = B; generalize gjBunt = U; simp [nock_exec]
@[nock_exec] theorem jr_arm (d : Noun) : nock d jrArm = some (C jrBody (C jrBunt d)) := by
  unfold jrArm; generalize jrBody = B; generalize jrBunt = U; simp [nock_exec]
@[nock_exec] theorem gr_arm (d : Noun) : nock d grArm = some (C grBody (C grBunt d)) := by
  unfold grArm; generalize grBody = B; generalize grBunt = U; simp [nock_exec]
@[nock_exec] theorem gs_arm (d : Noun) : nock d gsArm = some (C gsBody (C gsBunt d)) := by
  unfold gsArm; generalize gsBody = B; generalize gsBunt = U; simp [nock_exec]

/-! ## `+get-jmps` -/

/-- **`+get-jmps`** on a terminator other than `%lti`: `getJmps`. -/
theorem gj_gate (T : Noun) (t : Termin) (h : finPlain t = true) :
    nock (C gjBody (C t.toNoun T)) gjBody = some (listNoun Jmp.toNoun (Opt.getJmps t)) := by
  cases t <;> simp [finPlain] at h <;>
    simp [nock_exec, gjBody, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf,
      Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Opt.getJmps, listNoun]

/-- `+get-jmps` on `%lti` is `~`. -/
theorem gj_gate_lti (T : Noun) (n s : Nat) (z o : Jmp) :
    nock (C gjBody (C (Termin.lti n s z o).toNoun T)) gjBody = some (A 0) := by
  simp [nock_exec, gjBody, Termin.toNoun, Tag.clq, Tag.eqq, Tag.brn, Tag.brz, Tag.hop, Tag.jmp, Tag.jmf,
    Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti]

/-! ## `+jmp-regs` -/

theorem unitVal_unitNoun (u : Option Nat) : unitVal (unitNoun A u) = u.map A := by
  cases u <;> rfl

theorem filterMap_unitVal (l : List (Option Nat)) :
    (l.map (unitNoun A)).filterMap unitVal = (l.filterMap id).map A := by
  induction l with
  | nil => rfl
  | cons x l ih => cases x <;> simp only [List.map_cons, List.filterMap_cons, unitVal_unitNoun, ih] <;> rfl

/-- **`+jmp-regs`**: `jmpRegs`. -/
theorem jr_gate (j : Jmp) :
    nock (C jrBody (C j.toNoun compTypes)) jrBody = some (listNoun A (Opt.jmpRegs j)) := by
  have hL := mr_types_layer2
  have hm := murn_gate layer2 homoIn_layer2 (C (A 0) (A 6)) (A 0) layer2 (fun x => x)
    (j.args.map (unitNoun A)) (fun x hx => by
      obtain ⟨u, -, rfl⟩ := List.mem_map.1 hx
      refine ⟨by simp [nock_exec], ?_⟩
      cases u with
      | none => exact Or.inl rfl
      | some r => exact Or.inr ⟨_, _, rfl⟩)
  rw [filterMap_unitVal, ← listNoun_map_listN, ← listNoun_map_listN] at hm
  have hs : slot? 97710 layer2 = some (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) (C (A 0) (A 6))) (C (A 0) (A 1))))) := by
    kernel_rfl
  have hma : ∀ c, nock c murn.arm = some (C murn.battery (C (C (A 0) (C (C (A 0) (A 15)) (C (A 0) (C (A 0) (A 0))))) c)) := by
    intro c; nock_open murn.arm; simp only [nock_exec]
  unfold Opt.jmpRegs
  generalize compTypes = T at hL ⊢
  simp [nock_exec, jrBody, Jmp.toNoun, hL, murn.arm_at, hma, hs, hm]

/-- `+jmp-regs` as a list of atoms. -/
theorem jr_gate_N (j : Jmp) :
    nock (C jrBody (C j.toNoun compTypes)) jrBody = some (listN ((Opt.jmpRegs j).map A)) := by
  rw [jr_gate, listNoun_map_listN]

/-! ## `+get-regs` -/

/-- **`+get-regs`** on an op: `poleRegs`. -/
theorem gr_gate_pole (p : Pole) :
    nock (C grBody (C p.toNoun compTypes)) grBody = some (listNoun A (Opt.poleRegs p)) := by
  cases p <;>
    simp [nock_exec, grBody, Pole.toNoun, Tag.imm, Tag.mov, Tag.inc, Tag.con, Tag.hed, Tag.tal, Tag.cel,
      Tag.lob, Tag.equ, Tag.hsp, Tag.hse, Tag.hdp, Tag.hde, Tag.hmp, Tag.hme, Tag.hcp, Tag.hce, Tag.spy,
      Tag.nok, Tag.cal, Tag.caf, Tag.cam, Tag.csl, Tag.csf, Tag.csm, Opt.poleRegs, listNoun]

/-- **`+get-regs`** on a terminator other than `%lti`: `finRegs`. -/
theorem gr_gate_fin (t : Termin) (h : finPlain t = true) :
    nock (C grBody (C t.toNoun compTypes)) grBody = some (listNoun A (Opt.finRegs t)) := by
  have hL := mr_types_layer2
  have hj := jr_at
  have hz := fun j => jr_gate_N j
  have hw := fun l l' => weld_gate_list layer2 l l'
  generalize compTypes = T at hL hj hz ⊢
  cases t <;> simp [finPlain] at h <;>
    simp [nock_exec, grBody, Termin.toNoun, Tag.imm, Tag.mov, Tag.inc, Tag.con, Tag.hed, Tag.tal, Tag.cel,
      Tag.lob, Tag.equ, Tag.hsp, Tag.hse, Tag.hdp, Tag.hde, Tag.hmp, Tag.hme, Tag.hcp, Tag.hce, Tag.spy,
      Tag.nok, Tag.cal, Tag.caf, Tag.cam, Tag.csl, Tag.csf, Tag.csm, Tag.clq, Tag.eqq, Tag.brn, Tag.brz,
      Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Opt.finRegs, listNoun, hL, hj, hz, hw,
      weld.arm_at, weld_arm, listNoun_map_listN]

/-- `+get-regs` on `%lti` is `~`. -/
theorem gr_gate_lti (T : Noun) (n s : Nat) (z o : Jmp) :
    nock (C grBody (C (Termin.lti n s z o).toNoun T)) grBody = some (A 0) := by
  simp [nock_exec, grBody, Termin.toNoun, Tag.imm, Tag.mov, Tag.inc, Tag.con, Tag.hed, Tag.tal, Tag.cel,
    Tag.lob, Tag.equ, Tag.hsp, Tag.hse, Tag.hdp, Tag.hde, Tag.hmp, Tag.hme, Tag.hcp, Tag.hce, Tag.spy,
    Tag.nok, Tag.cal, Tag.caf, Tag.cam, Tag.csl, Tag.csf, Tag.csm, Tag.clq, Tag.eqq, Tag.brn, Tag.brz,
    Tag.hop, Tag.jmp, Tag.jmf, Tag.jsp, Tag.jsf, Tag.don, Tag.bom, Tag.lti]

/-! ## `+get-reg-safe-assignment` -/

/-- **`+get-reg-safe-assignment`**: `safeAssign`, as a unit. -/
theorem gs_gate (T : Noun) (p : Pole) :
    nock (C gsBody (C p.toNoun T)) gsBody = some (unitNoun A (Opt.safeAssign p)) := by
  cases p <;>
    simp [nock_exec, gsBody, Pole.toNoun, Tag.imm, Tag.mov, Tag.inc, Tag.con, Tag.hed, Tag.tal, Tag.cel,
      Tag.lob, Tag.equ, Tag.hsp, Tag.hse, Tag.hdp, Tag.hde, Tag.hmp, Tag.hme, Tag.hcp, Tag.hce, Tag.spy,
      Tag.nok, Tag.cal, Tag.caf, Tag.cam, Tag.csl, Tag.csf, Tag.csm, Opt.safeAssign, unitNoun]

end Compiler
end Formalization
