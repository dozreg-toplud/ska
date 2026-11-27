import lemmas.Compiler.CompCtx

/-!
# The Nock of the `+leap` family, cut into named parts

Written by `tools/gen/leap.py` between the markers; do not edit by hand.
Each arm is a gate `[8 [1 <p>Bunt] [1 <p>Bat] 0 1]` (`<p>Arm`), tied to the
pill by the kernel fact `<p>_at`: `+need-from` (door `14`, `ndf`),
`+need-cut` (door `16375`, `ndc`), `+pass-bomb` (K `715742`, `pbo`), `+pass`
(K `340`, `pas`), `+pass-then` (K `86`, `pth`), `+pass-edit` (K `48046`,
`ped`), `+pass-both` (K `94`, `pbt`), `+lazy-leap` (door `442366`, `lzl`),
`+leap` (door `441179`, `lpx`, the nouns of `lp6Arm` cut further).
The gates built inside a battery are `<p>G<i>`, its traps `<p>L<i>`
(innermost first); the batteries are built from them, so `<p>_at` checks the
cut.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon

-- BEGIN leap

/-- A trap of `+need-from`. -/
def ndfL1 : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 28)))) (C (C (A 0) (A 29)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 22) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 60))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 2)) (C (A 0) (A 2)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 28) (C (A 8) (C (C (A 9) (C (A 47) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 60))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))))) (C (A 1) (C (A 0x656e6f6e) (A 0)))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 3)) (C (A 0) (A 2))))) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 1) (C (A 0x656e6f6e) (A 0))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 28) (C (A 8) (C (C (A 9) (C (A 47) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 60))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))))))))))))))))))

/-- The battery of `+need-from` (door arm `14`). -/
def ndfBat : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 26)))) (C (C (A 0) (A 13)) (C (A 8) (C (C (A 1) ndfL1) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))))

def ndfBunt : Noun :=
  (C (A 0) (C (A 0x656e6f6e) (A 0)))

def ndfArm : Noun := C (A 8) (C (C (A 1) ndfBunt) (C (C (A 1) ndfBat) (C (A 0) (A 1))))

theorem ndf_at : slot? 14 comp.door = some ndfArm := by kernel_rfl

theorem ndf_arm (d : Noun) : nock d ndfArm = some (C ndfBat (C ndfBunt d)) := by
  unfold ndfArm; simp only [nock_exec]

/-- The battery of `+need-cut` (door arm `16375`). -/
def ndcBat : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 12)))) (C (C (C (A 1) (A 0)) (C (C (A 0) (A 13)) (C (A 1) (C (A 0x656e6f6e) (A 0))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 26)))) (C (C (C (A 1) (A 0)) (C (C (A 0) (A 13)) (C (A 0) (A 13)))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 26)))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 26)))) (C (C (A 1) (A 0)) (C (A 11) (C (C (A 0x73736f74) (C (A 3) (C (A 0) (A 26)))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 22) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 2)) (C (A 0) (A 2)))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 47) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))) (C (A 0) (A 26)))) (C (A 0) (A 1)))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (C (A 1) (A 0)) (C (C (A 0) (A 10)) (C (A 8) (C (C (A 9) (C (A 350) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 27)) (C (A 0) (A 123)))) (C (A 0) (A 2))))))))))))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 5) (C (C (A 1) (A 3)) (C (A 0) (A 2))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 47) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))) (C (A 0) (A 27)))) (C (A 0) (A 1)))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (C (A 1) (A 0)) (C (C (A 0) (A 10)) (C (A 8) (C (C (A 9) (C (A 350) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 122)) (C (A 0) (A 27)))) (C (A 0) (A 2))))))))))))))))))))))))))))))))))))))

def ndcBunt : Noun :=
  (C (A 0) (C (A 0x656e6f6e) (A 0)))

def ndcArm : Noun := C (A 8) (C (C (A 1) ndcBunt) (C (C (A 1) ndcBat) (C (A 0) (A 1))))

theorem ndc_at : slot? 16375 comp.door = some ndcArm := by kernel_rfl

theorem ndc_arm (d : Noun) : nock d ndcArm = some (C ndcBat (C ndcBunt d)) := by
  unfold ndcArm; simp only [nock_exec]

/-- The battery of `+pass-bomb` (K arm `715742`). -/
def pboBat : Noun :=
  (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 12)))) (C (A 1) (A 1))))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 13)))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 5) (C (C (A 1) (A 11)) (C (A 0) (A 12)))) (C (A 1) (A 1))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 54))) (C (A 0) (A 1)))))) (C (A 11) (C (C (A 0x73736f74) (C (A 1) (A 0))) (C (A 1) (A 1))))))))))

def pboBunt : Noun :=
  (C (A 0) (A 0))

def pboArm : Noun := C (A 8) (C (C (A 1) pboBunt) (C (C (A 1) pboBat) (C (A 0) (A 1))))

theorem pbo_at : slot? 715742 compK = some pboArm := by kernel_rfl

theorem pbo_arm (d : Noun) : nock d pboArm = some (C pboBat (C pboBunt d)) := by
  unfold pboArm; simp only [nock_exec]

/-- A gate built in `+pass`. -/
def pasG1 : Noun :=
  (C (C (A 8) (C (C (A 9) (C (A 46) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 2)))) (C (A 0) (A 28)))) (C (A 0) (A 2)))))))) (C (A 0) (A 13)))

/-- A gate built in `+pass`. -/
def pasG2 : Noun :=
  (C (C (A 8) (C (C (A 9) (C (A 46) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 3)))) (C (A 0) (A 28)))) (C (A 0) (A 2)))))))) (C (A 0) (A 13)))

/-- The battery of `+pass` (K arm `340`). -/
def pasBat : Noun :=
  (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 3) (C (A 0) (A 12))) (C (A 1) (A 1))))) (C (C (A 8) (C (C (A 9) (C (A 0xbef7f4) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 12))) (C (A 0) (A 1)))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (C (A 1) pasG1) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 13))) (C (A 0) (A 1)))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (C (A 1) pasG2) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 12)))) (C (A 1) (A 1))))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 13)))) (C (C (A 1) (A 0)) (C (C (C (A 1) (A 1)) (C (A 0) (A 13))) (C (A 1) (A 0)))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 5) (C (C (A 1) (A 6)) (C (A 0) (A 12)))) (C (A 1) (A 1))))) (C (C (A 8) (C (C (A 9) (C (A 94) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 118)) (C (A 0) (A 119)))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 5) (C (C (A 1) (A 7)) (C (A 0) (A 12)))) (C (A 1) (A 1))))) (C (C (A 8) (C (C (A 9) (C (A 86) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 26))) (C (A 0) (A 1)))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 27))) (C (A 0) (A 1)))))))))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 5) (C (C (A 1) (A 10)) (C (A 0) (A 12)))) (C (A 1) (A 1))))) (C (C (A 8) (C (C (A 9) (C (A 0xbbae) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 116)) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 53))) (C (A 0) (A 1)))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 27))) (C (A 0) (A 1))))))))))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 6))) (C (C (A 5) (C (C (A 1) (A 11)) (C (A 0) (A 12)))) (C (A 1) (A 1))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 54))) (C (A 0) (A 1)))))) (C (A 11) (C (C (A 0x73736f74) (C (A 1) (A 0))) (C (A 1) (A 0))))))))))))))))))))))

def pasBunt : Noun :=
  (C (A 0) (A 0))

def pasArm : Noun := C (A 8) (C (C (A 1) pasBunt) (C (C (A 1) pasBat) (C (A 0) (A 1))))

theorem pas_at : slot? 340 compK = some pasArm := by kernel_rfl

theorem pas_arm (d : Noun) : nock d pasArm = some (C pasBat (C pasBunt d)) := by
  unfold pasArm; simp only [nock_exec]

/-- A gate built in `+pass-then`. -/
def pthG1 : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 5597) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 0) (A 125)))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 5597) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 253)) (C (A 0) (A 60)))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (C (A 1) (A 0)) (C (C (A 8) (C (C (A 9) (C (A 46) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 508)) (C (A 0) (A 13)))) (C (A 0) (A 2)))))))) (C (A 0) (A 61))))))))) (C (C (A 1) (A 0)) (C (C (A 0) (A 124)) (C (A 8) (C (C (A 9) (C (A 46) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 61)) (C (A 0) (A 13)))) (C (A 0) (A 2)))))))))))))))

/-- A gate built in `+pass-then`. -/
def pthG2 : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0x17defea) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 124)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (C (A 1) pthG1) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))

/-- The battery of `+pass-then` (K arm `86`). -/
def pthBat : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 12)))) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 9) (C (A 0x17defa) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 29)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (C (A 1) pthG2) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))))))

def pthBunt : Noun :=
  (C (A 0) (A 0))

def pthArm : Noun := C (A 8) (C (C (A 1) pthBunt) (C (C (A 1) pthBat) (C (A 0) (A 1))))

theorem pth_at : slot? 86 compK = some pthArm := by kernel_rfl

theorem pth_arm (d : Noun) : nock d pthArm = some (C pthBat (C pthBunt d)) := by
  unfold pthArm; simp only [nock_exec]

/-- A gate built in `+pass-edit`. -/
def pedG1 : Noun :=
  (C (C (A 8) (C (C (A 9) (C (A 46) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 124)) (C (A 0) (A 28)))) (C (A 0) (A 2)))))))) (C (A 0) (A 13)))

/-- A trap of `+pass-edit`. -/
def pedL1 : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 1)) (C (A 0) (A 6)))) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 22) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 2)) (C (A 0) (A 2)))) (C (C (A 1) (A 3)) (C (A 1) (A 2))))) (C (C (C (A 8) (C (C (A 9) (C (A 46) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1020)) (C (A 0) (A 6)))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 9) (C (A 46) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1021)) (C (A 0) (A 6)))) (C (A 0) (A 2))))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 62) (C (C (A 8) (C (C (A 9) (C (A 46) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1020)) (C (A 0) (A 14)))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 9) (C (A 46) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1021)) (C (A 0) (A 14)))) (C (A 0) (A 2)))))))))) (C (A 10) (C (C (A 6) (C (A 8) (C (C (A 9) (C (A 47) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 62))) (C (A 0) (A 2))))))))) (C (A 0) (A 7))))))))))))))))

/-- A gate built in `+pass-edit`. -/
def pedG2 : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 5597) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 124)) (C (A 0) (A 28)))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 5597) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 0) (A 124)))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (C (C (A 0) (A 28)) (C (A 0) (A 29))) (C (A 1) (A 0))) (C (A 8) (C (C (A 0) (A 5)) (C (A 8) (C (C (A 1) pedL1) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))))))))

/-- The battery of `+pass-edit` (K arm `48046`). -/
def pedBat : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0xbef7f4) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 58)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (C (A 1) pedG1) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0x17defa) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 59)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (C (A 1) pedG2) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))))))) (C (A 0) (A 2))))))))

def pedBunt : Noun :=
  (C (A 0) (C (A 0) (A 0)))

def pedArm : Noun := C (A 8) (C (C (A 1) pedBunt) (C (C (A 1) pedBat) (C (A 0) (A 1))))

theorem ped_at : slot? 48046 compK = some pedArm := by kernel_rfl

theorem ped_arm (d : Noun) : nock d pedArm = some (C pedBat (C pedBunt d)) := by
  unfold pedArm; simp only [nock_exec]

/-- A gate built in `+pass-both`. -/
def pbtG1 : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 5597) (C (A 0) (A 511)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 124)) (C (A 0) (A 28)))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 5597) (C (A 0) (A 1023)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 60)) (C (A 0) (A 252)))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 5) (C (C (A 0) (A 253)) (C (A 8) (C (C (A 9) (C (A 46) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 125)) (C (A 0) (A 13)))) (C (A 0) (A 2)))))))))) (C (C (C (A 1) (A 0)) (C (C (A 0) (A 252)) (C (A 0) (A 253)))) (C (A 1) (A 0)))))))))) (C (A 6) (C (C (A 5) (C (C (A 0) (A 29)) (C (A 8) (C (C (A 9) (C (A 46) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 253)) (C (A 0) (A 13)))) (C (A 0) (A 2)))))))))) (C (C (C (A 1) (A 0)) (C (C (A 0) (A 28)) (C (A 0) (A 29)))) (C (A 1) (A 0))))))))))

/-- A gate built in `+pass-both`. -/
def pbtG2 : Noun :=
  (C (A 8) (C (C (A 9) (C (A 0x17defea) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 30)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (C (A 1) pbtG1) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))

/-- The battery of `+pass-both` (K arm `94`). -/
def pbtBat : Noun :=
  (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 0xaebde) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 9) (C (A 340) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 0xaebde) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 9) (C (A 340) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 340) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 340) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 61))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 9) (C (A 0x17defa) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (A 0))) (C (C (A 1) pbtG2) (C (A 0) (A 1))))))))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2))))))))))))))))))))))))

def pbtBunt : Noun :=
  (C (C (A 0) (A 0)) (C (A 0) (A 0)))

def pbtArm : Noun := C (A 8) (C (C (A 1) pbtBunt) (C (C (A 1) pbtBat) (C (A 0) (A 1))))

theorem pbt_at : slot? 94 compK = some pbtArm := by kernel_rfl

theorem pbt_arm (d : Noun) : nock d pbtArm = some (C pbtBat (C pbtBunt d)) := by
  unfold pbtArm; simp only [nock_exec]

/-- A gate built in `+lazy-leap`. -/
def lzlG1 : Noun :=
  (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 5597) (C (A 0) (A 1023)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 252)) (C (A 0) (A 28)))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (C (A 0) (A 58)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 84) (C (A 10) (C (C (A 6) (C (A 0) (A 123))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 60))) (C (A 0) (A 2))))))))) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 84) (C (A 10) (C (C (A 6) (C (A 0) (A 122))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 46) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1018)) (C (A 0) (A 13)))) (C (A 0) (A 2))))))))))) (C (A 0) (A 2)))))))) (C (A 0) (A 59))))))))

/-- A gate built in `+lazy-leap`. -/
def lzlG2 : Noun :=
  (C (A 8) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 27) (C (A 0) (A 25))) (C (A 0) (A 31)))))) (C (A 8) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 27) (C (A 0) (A 59))) (C (A 0) (A 63)))))) (C (C (C (C (A 0) (A 120)) (C (A 0) (A 12))) (C (C (A 0) (A 122)) (C (A 0) (A 4)))) (C (C (C (A 0) (A 120)) (C (A 0) (A 13))) (C (C (A 0) (A 122)) (C (A 0) (A 5)))))))))

/-- A gate built in `+lazy-leap`. -/
def lzlG3 : Noun :=
  (C (A 8) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 27) (C (A 0) (A 13))) (C (A 0) (A 63)))))) (C (C (C (A 0) (A 28)) (C (A 0) (A 4))) (C (C (A 0) (A 28)) (C (A 0) (A 5))))))

/-- The battery of `+lazy-leap` (door arm `442366`). -/
def lzlBat : Noun :=
  (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0x5ff7) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 0) (A 236)))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 2)))) (C (C (C (A 1) (C (C (A 0x656e6f6e) (A 0)) (A 0))) (C (A 0) (A 118))) (C (A 8) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 383) (C (A 10) (C (C (A 6) (C (A 0) (A 493))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (C (A 0) (A 0)))) (C (C (A 1) lzlG1) (C (A 0) (A 1)))))))) (C (A 0) (A 2)))))))) (C (C (C (A 8) (C (C (A 9) (C (A 22) (C (A 0) (A 31)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 250)) (C (A 0) (A 58)))) (C (A 0) (A 2)))))))) (C (A 0) (A 4))) (C (C (A 0) (A 27)) (C (A 0) (A 5))))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 1006)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))))) (C (C (A 1) lzlG2) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x1ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 2031)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))))) (C (C (A 1) lzlG3) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 9) (C (A 0x15577c) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 60)) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 0xbedd) (C (A 0) (A 0x3ffffff)))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 0xbedd) (C (A 0) (A 0x3ffffff)))))))) (C (A 0) (A 2))))))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 9) (C (A 0x15577c) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 61)) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 14)) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 0x5f6be) (C (A 0) (A 0x3ffffff)))))))) (C (A 0) (A 2)))))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 0xbef7e) (C (A 0) (A 0x3ffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 6)) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 0x5f6be) (C (A 0) (A 0x3ffffff)))))))) (C (A 0) (A 2))))))))))))) (C (A 0) (A 2)))))))))))))))))))

def lzlBunt : Noun :=
  (C (A 0) (C (A 0) (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0)))))

def lzlArm : Noun := C (A 8) (C (C (A 1) lzlBunt) (C (C (A 1) lzlBat) (C (A 0) (A 1))))

theorem lzl_at : slot? 442366 comp.door = some lzlArm := by kernel_rfl

theorem lzl_arm (d : Noun) : nock d lzlArm = some (C lzlBat (C lzlBunt d)) := by
  unfold lzlArm; simp only [nock_exec]

/-- A trap of `+leap`. -/
def lpxL1 : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 30)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 6)))) (C (C (A 1) (A 0)) (C (C (A 1) (A 0)) (C (C (C (A 0) (A 504)) (C (C (A 0) (A 58)) (C (A 0) (A 59)))) (C (A 0) (A 6))))))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 0xabffe) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 248)) (C (C (A 0) (A 249)) (C (A 0) (A 30))))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 86) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 12))) (C (A 0) (A 2)))))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 125))) (C (A 0) (A 3)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 30) (C (A 0) (A 125))) (C (A 10) (C (C (A 14) (C (A 0) (A 5))) (C (A 10) (C (C (A 6) (C (C (A 0) (A 4)) (C (A 0) (A 14)))) (C (A 0) (A 3))))))))))))))))))

/-- The battery of `+leap` (door arm `441179`). -/
def lpxBat : Noun :=
  (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 50)))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 51)))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 94) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 58)) (C (A 0) (A 59)))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (C (A 1) (C (C (A 0x656e6f6e) (A 0)) (A 0))) (C (C (A 0) (A 114)) (C (A 0) (A 115)))) (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 1) lpxL1) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))))))))))

def lpxBunt : Noun :=
  (C (C (C (C (A 0x656e6f6e) (A 0)) (A 0)) (C (A 0) (A 0))) (C (C (A 0) (A 0)) (C (A 0) (A 0))))

def lpxArm : Noun := C (A 8) (C (C (A 1) lpxBunt) (C (C (A 1) lpxBat) (C (A 0) (A 1))))

theorem lpx_at : slot? 441179 comp.door = some lpxArm := by kernel_rfl

theorem lpx_arm (d : Noun) : nock d lpxArm = some (C lpxBat (C lpxBunt d)) := by
  unfold lpxArm; simp only [nock_exec]

-- END leap

end Compiler
end Formalization
