import lemmas.Compiler.CompPastLink

/-!
# The arms the push of `sof` slams (README Gaps 19, item (f))

Written by `tools/gen/sofpush.py` from the pill: `+sound` (door arm
`13654`, `(sound-far nom ned code.long-ska 3)`), `+sound-far` (arm `5467` of
`K`, behind its `%fast` hint), `+need-soft` (arm `5466` of `K`), each with
its gate battery and the kernel fact of where it sits.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

/-- The gate battery of `+sound` (door arm `13654`) (21 cells). -/
def sndBat : Noun :=
  (C (A 8) (C (C (A 9) (C (A 5467) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (C (A 0) (A 29)) (C (C (A 0) (A 2036)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 3)))))))) (C (A 0) (A 2))))))))

/-- The arm `+sound` (door arm `13654`). -/
def sndArm : Noun :=
  (C (A 8) (C (C (A 1) (C (C (A 0) (A 0)) (C (A 0x656e6f6e) (A 0)))) (C (C (A 1) sndBat) (C (A 0) (A 1)))))

theorem comp_sound_at : slot? 13654 comp.door = some sndArm := by kernel_rfl

/-- The gate battery of `+sound-far` (arm `5467` of `K`) (329 cells). -/
def sfBat : Noun :=
  (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 52)))) (C (C (A 1) (A 0)) (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 52))))))) (C (C (A 1) (A 0)) (C (A 11) (C (C (A 0x6f6d656d) (C (A 1) (A 0))) (C (A 8) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 52)))) (C (C (C (A 0) (A 106)) (C (A 0) (A 107))) (C (C (A 0) (A 52)) (C (A 0) (A 53)))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 28))) (C (C (A 3) (C (A 0) (A 56))) (C (A 1) (A 1))))) (C (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 26) (C (A 0) (A 4))) (C (A 10) (C (C (A 12) (C (A 0) (A 56))) (C (A 0) (A 3)))))))) (C (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 26) (C (A 0) (A 5))) (C (A 10) (C (C (A 12) (C (A 0) (A 57))) (C (A 0) (A 3)))))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 28))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 56)))) (C (A 1) (A 1))))) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 57)))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 28))) (C (C (A 5) (C (C (A 1) (A 6)) (C (A 0) (A 56)))) (C (A 1) (A 1))))) (C (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 230))) (C (A 0) (A 3)))))) (C (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 231))) (C (A 0) (A 3)))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 28))) (C (C (A 5) (C (C (A 1) (A 7)) (C (A 0) (A 56)))) (C (A 1) (A 1))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 115))) (C (A 0) (A 3)))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 28))) (C (C (A 5) (C (C (A 1) (A 11)) (C (A 0) (A 56)))) (C (A 1) (A 1))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 230))) (C (A 0) (A 3)))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 28))) (C (C (A 5) (C (C (A 1) (A 0x6e61656d)) (C (A 0) (A 56)))) (C (A 1) (A 1))))) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 12) (C (A 0) (A 462))) (C (A 0) (A 3)))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 28))) (C (C (A 5) (C (C (A 1) (A 2)) (C (A 0) (A 56)))) (C (A 1) (A 1))))) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 231)))) (C (C (A 1) (A 1)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 119)))) (C (C (A 1) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 55) (C (A 8) (C (C (A 9) (C (A 2398) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 247))) (C (A 0) (A 2))))))))) (C (A 10) (C (C (A 12) (C (A 7) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 246))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 1950))) (C (A 0) (A 2)))))))) (C (A 0) (A 2))))) (C (A 0) (A 3)))))))))))))) (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 28))) (C (C (A 5) (C (C (A 1) (A 10)) (C (A 0) (A 56)))) (C (A 1) (A 1))))) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 5596) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 484)) (C (A 0) (A 122)))) (C (A 0) (A 2)))))))) (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 26) (C (A 0) (A 4))) (C (A 10) (C (C (A 12) (C (A 0) (A 485))) (C (A 0) (A 7)))))))) (C (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 26) (C (A 0) (A 5))) (C (A 10) (C (C (A 12) (C (A 0) (A 243))) (C (A 0) (A 7)))))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))))) (C (A 11) (C (C (A 0x73736f74) (C (A 1) (A 0))) (C (A 1) (A 1)))))))))))))))))))))))))))))))))))

/-- The arm `+sound-far` (arm `5467` of `K`). -/
def sfArm : Noun :=
  (C (A 7) (C (C (A 8) (C (C (A 1) (C (C (A 0) (A 0)) (C (C (A 0x656e6f6e) (A 0)) (C (A 0) (A 0))))) (C (C (A 1) sfBat) (C (A 0) (A 1))))) (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x7261662d646e756f73) (C (C (A 0) (A 0x7fff)) (A 0))))) (C (A 0) (A 1))))))

theorem compK_sf : slot? 5467 compK = some sfArm := by kernel_rfl

/-- The gate battery of `+need-soft` (arm `5466` of `K`) (134 cells). -/
def nsBat : Noun :=
  (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x656e6f6e)) (C (A 0) (A 24)))) (C (C (A 1) (A 0)) (C (A 5) (C (C (A 1) (A 0x73696874)) (C (A 0) (A 24))))))) (C (C (A 1) (A 1)) (C (A 6) (C (C (A 8) (C (C (A 9) (C (A 0xbbaf) (C (A 0) (A 7)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 58)) (C (A 0) (A 59)))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x68746f62)) (C (A 0) (A 24)))) (C (C (C (A 0) (A 50)) (C (A 0) (A 51))) (C (C (A 0) (A 24)) (C (A 0) (A 25)))))) (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 4)) (C (C (A 8) (C (C (A 9) (C (A 374) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 122))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 11) (C (A 0) (A 511)))) (C (A 9) (C (A 175) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 123))) (C (A 0) (A 2))))))))))) (C (A 0) (A 3)))))) (C (C (A 1) (A 0)) (C (A 6) (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 5)) (C (C (A 8) (C (C (A 9) (C (A 92) (C (A 0) (A 15)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 122))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 11) (C (A 0) (A 511)))) (C (A 9) (C (A 23) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 123))) (C (A 0) (A 2))))))))))) (C (A 0) (A 3)))))) (C (C (A 1) (A 0)) (C (A 1) (A 1)))))))))) (C (A 1) (A 0))))))))

/-- The arm `+need-soft` (arm `5466` of `K`). -/
def nsArm : Noun :=
  (C (A 8) (C (C (A 1) (C (C (A 0x656e6f6e) (A 0)) (C (C (A 0x656e6f6e) (A 0)) (C (A 1) (A 0))))) (C (C (A 1) nsBat) (C (A 0) (A 1)))))

theorem compK_ns : slot? 5466 compK = some nsArm := by kernel_rfl

end Compiler
end Formalization
