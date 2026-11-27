import lemmas.Compiler.PokeLinkSccHit
import lemmas.Compiler.CompTarjanLink

/-!
# The cut of the cache miss of `+scc-of` (track Q)

`sccMiss` (`PokeLinkSccHit.lean`: axis `62` of `sccBat`, 373 cells) runs on
`[s gc]`, `s` the `~` of `(~(get by sccs) b)` and `gc = [sccBat [[b calls
sccs] ctx]]` the gate core.  Its parts, each a `getD` slot of its parent,
and their shapes (`kernel_rfl`), from `tools/gen/sccofmiss.py`
(`tools/capped.sh -m 3G python3 tools/gen/sccofmiss.py tools/gen lean`):

* `sccMiss` `[8 smSub smRest]`;
* `smSub` (222 cells) `=|  sub  =/  q  ~[b]  |-`: `[8 [1 0] [8 [[0 60] [1 0]]
  [8 [1 smTrap] [9 2 0 1]]]]`; the trap `smTrap` `[6 ?~(q) [0 14]
  smTrapNo]`, `smTrapNo` `[6 smHasQ $(q t.q) smMain]` (`smHasQ` the
  `+has:by` of `sub`), `smMain` `[8 smCs smRec]`: `smCs` the `+rep:in` of
  the set `smGut` (`+gut:by` of `calls`) with the gate `smCsG` (`+has:by` of
  `sccs`, `+put:in`; its sample bunt is the constant `[[[1 0] [0 0]] 0]`),
  `smRec` the recursion with `+weld` of `+tap:in` and `+put:by`;
* `smRest` `[7 smRollE smGot]`: `smRollE` `[10 [123 smRoll] [0 1]]` writes
  `sccs`; `smRoll` slams `+roll` on `smTj` (`+tarjan` of `sub`, arm `2815`
  at axis `255`) and the gate whose sample bunt is `[smB1 sccs]` (`smB1`:
  the mold `(set bell)`, arms `6098` of the hoon core and `382` of the core
  at axis `511`) and whose battery `smGBat` is the `+rep:in` of `s` with the
  inner gate (sample bunt `[smB2 acc]`, `smB2` the mold `bell`; battery
  `smIBat`, the `+put:by` of `[m s]`); `smGot` `[(~(got by sccs) b) sccs]`.
-/

namespace Formalization
namespace Compiler

open Nock Pill

/-- axis `6` of `sccMiss`, 222 cells. -/
def smSub : Noun := (slot? 6 sccMiss).getD (A 0)
/-- axis `7` of `sccMiss`, 149 cells. -/
def smRest : Noun := (slot? 7 sccMiss).getD (A 0)
/-- axis `253` of `smSub`, 208 cells. -/
def smTrap : Noun := (slot? 253 smSub).getD (A 0)
/-- axis `15` of `smTrap`, 200 cells. -/
def smTrapNo : Noun := (slot? 15 smTrap).getD (A 0)
/-- axis `6` of `smTrapNo`, 21 cells. -/
def smHasQ : Noun := (slot? 6 smTrapNo).getD (A 0)
/-- axis `15` of `smTrapNo`, 169 cells. -/
def smMain : Noun := (slot? 15 smTrapNo).getD (A 0)
/-- axis `6` of `smMain`, 107 cells. -/
def smCs : Noun := (slot? 6 smMain).getD (A 0)
/-- axis `3575` of `smCs`, 26 cells. -/
def smGut : Noun := (slot? 3575 smCs).getD (A 0)
/-- axis `16253` of `smCs`, 46 cells. -/
def smCsG : Noun := (slot? 16253 smCs).getD (A 0)
/-- axis `7` of `smMain`, 60 cells. -/
def smRec : Noun := (slot? 7 smMain).getD (A 0)
/-- axis `6` of `smRest`, 124 cells. -/
def smRollE : Noun := (slot? 6 smRest).getD (A 0)
/-- axis `13` of `smRollE`, 120 cells. -/
def smRoll : Noun := (slot? 13 smRollE).getD (A 0)
/-- axis `2027` of `smRoll`, 12 cells. -/
def smTj : Noun := (slot? 2027 smRoll).getD (A 0)
/-- axis `16252` of `smRoll`, 22 cells. -/
def smB1 : Noun := (slot? 16252 smRoll).getD (A 0)
/-- axis `32509` of `smRoll`, 61 cells. -/
def smGBat : Noun := (slot? 32509 smRoll).getD (A 0)
/-- axis `8124` of `smGBat`, 8 cells. -/
def smB2 : Noun := (slot? 8124 smGBat).getD (A 0)
/-- axis `16253` of `smGBat`, 23 cells. -/
def smIBat : Noun := (slot? 16253 smGBat).getD (A 0)
/-- axis `7` of `smRest`, 23 cells. -/
def smGot : Noun := (slot? 7 smRest).getD (A 0)

theorem sccMiss_eq : sccMiss = (C (A 8) (C smSub smRest)) := by kernel_rfl
theorem smSub_eq : smSub = (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (C (A 0) (A 60)) (C (A 1) (A 0))) (C (A 8) (C (C (A 1) smTrap) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))))) := by kernel_rfl
theorem smRest_eq : smRest = (C (A 7) (C smRollE smGot)) := by kernel_rfl
theorem smTrap_eq : smTrap = (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 6)))) (C (C (A 0) (A 14)) smTrapNo))) := by kernel_rfl
theorem smTrapNo_eq : smTrapNo = (C (A 6) (C smHasQ (C (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 13))) (C (A 0) (A 1)))))) smMain))) := by kernel_rfl
theorem smHasQ_eq : smHasQ = (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 3061) (C (A 10) (C (C (A 6) (C (A 0) (A 30))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))) := by kernel_rfl
theorem smMain_eq : smMain = (C (A 8) (C smCs smRec)) := by kernel_rfl
theorem smCs_eq : smCs = (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 383) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) smGut))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 1) (C (C (C (A 1) (A 0)) (C (A 0) (A 0))) (A 0))) (C (C (A 1) smCsG) (C (A 0) (A 1)))))))) (C (A 0) (A 2)))))))) := by kernel_rfl
theorem smGut_eq : smGut = (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 1531) (C (A 10) (C (C (A 6) (C (A 0) (A 1018))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (A 0)))))) (C (A 0) (A 2)))))))) := by kernel_rfl
theorem smCsG_eq : smCsG = (C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 3061) (C (A 10) (C (C (A 6) (C (A 0) (A 4091))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))) (C (C (A 0) (A 13)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 84) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2))))))))))) := by kernel_rfl
theorem smRec_eq : smRec = (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 62))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 60)) (C (A 0) (A 6)))) (C (A 0) (A 2))))))))) (C (A 10) (C (C (A 6) (C (A 8) (C (C (A 9) (C (A 0xbef7f4) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 186) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))))) (C (A 0) (A 61)))) (C (A 0) (A 2))))))))) (C (A 0) (A 3)))))))) := by kernel_rfl
theorem smRollE_eq : smRollE = (C (A 10) (C (C (A 123) smRoll) (C (A 0) (A 1)))) := by kernel_rfl
theorem smRoll_eq : smRoll = (C (A 8) (C (C (A 9) (C (A 0x2fbdfc) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) smTj)) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C smB1 (C (A 0) (A 123))) (C (C (A 1) smGBat) (C (A 0) (A 1))))))))) (C (A 0) (A 2)))))))) := by kernel_rfl
theorem smTj_eq : smTj = (C (A 8) (C (C (A 9) (C (A 2815) (C (A 0) (A 255)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2)))))))) := by kernel_rfl
theorem smB1_eq : smB1 = (C (A 7) (C (C (A 8) (C (C (A 9) (C (A 6098) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 9) (C (A 382) (C (A 0) (A 511))))))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) := by kernel_rfl
theorem smGBat_eq : smGBat = (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 383) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C smB2 (C (A 0) (A 13))) (C (C (A 1) smIBat) (C (A 0) (A 1)))))))) (C (A 0) (A 2)))))))) := by kernel_rfl
theorem smB2_eq : smB2 = (C (A 7) (C (C (A 9) (C (A 382) (C (A 0) (A 2047)))) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) := by kernel_rfl
theorem smIBat_eq : smIBat = (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 29))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 28)) (C (A 0) (A 124)))) (C (A 0) (A 2)))))))) := by kernel_rfl
theorem smGot_eq : smGot = (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0xfffff)))) (C (A 9) (C (A 701) (C (A 10) (C (C (A 6) (C (A 0) (A 251))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 124))) (C (A 0) (A 2)))))))) (C (A 0) (A 123))) := by kernel_rfl

end Compiler
end Formalization
