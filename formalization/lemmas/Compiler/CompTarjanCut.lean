import lemmas.Compiler.GitG

/-!
# The cut of `++  tarjan` (track Q)

`+tarjan` is the wet gate at arm `2815` of `ana` (axis `15` of `K`, the core
of `+scc-of`: `slot? 15 compK = slot? 1 ana`), 837 cells.  The pill holds one
copy: the battery the library's core was compiled with; the calls of
`+ska-poke` (`[9 2815 ..]` under `%poke-tarjan`) and of `+scc-of`
(`[9 2815 [0 255]]` in its miss) slam it.  The parts, each a `getD` slot of
its parent, and their shapes (`kernel_rfl`), from `tools/gen/tarjancut.py`
(`tools/capped.sh -m 3G python3 tools/gen/tarjancut.py tools/gen lean`):

* `tjArm` `[8 [1 0] [1 tjBat] 0 1]`: the gate, sample bunt `0`;
* `tjBat` `=<  fin  ^-  gen  (~(rep by g) ..)`: `tjRun`, then `[0 31]`;
* `tjRun` `[8 tjRepDoor [9 2 [10 [6 tjOGate] 0 2]]]`: the door `~(rep by g)`
  (arm `767` of `by`) slammed on the gate `tjOGate`;
* `tjOGate` `[7 [0 3] [8 tjSamB [1 tjOBat] 0 1]]`: the gate of the `rep`;
  `tjSamB` (342 cells) is the bunt of its sample `[[v=vertex kids] acc=gen]`:
  the molds `_p.n.-.g` (it reads axis `120`, the root node's key of `g`: a
  crash on `g = ~`), `(set vertex)` and `gen` (arms `6098`, `1407`,
  `12198`, `40415` of the hoon core, not linked); the `rep` starts from the
  bunt of `gen`;
* `tjOBat` `[6 tjHasV [0 13] tjElse]`: `?:  (~(has by vis.acc) v)  acc`;
* `tjElse` `[7 [8 [1 tjConn] [9 2 0 1]] [0 3]]`: `=<  +  |-`;
* `tjConn` (418 cells) the trap `connect`: `=/  index  idx.acc`
  (`[8 [0 58] ..]`), `tjEnter` (the `%_` of `acc`), `tjKidsRep` (`=^  lowest
  acc  (~(rep in kids) tjKGate)`), `tjAfter` (`:-  lowest  ?.  =(index
  lowest)  acc  ..`);
* `tjKGate` `[7 [0 3] [8 tjKSam [1 tjKBat] 0 1]]`, `tjKSam` the bunt
  `[[*vertex index] acc]`; `tjKBat` `[8 tjKGet [6 ?=(@ kid-idx) tjKUnvis
  tjKVis]]`: `tjKGet` `(~(get by vis.acc) kid)`, `tjKUnvis` the recursion
  `connect(v kid, kids (~(get ju g) kid), acc acc)` and `(min lowest
  lowest-kid)`, `tjKVis` `:_  acc  ?.  (~(has in cur.acc) kid)  lowest  (min
  lowest u.kid-idx)`;
* `tjPopBr` `[7 [8 [1 0] [8 [1 tjPopBat] [9 2 0 1]]] [10 [31 [0 2] 0 63] 0
  3]]`: `=|  out` then the pop loop `tjPopBat` (99 cells), then
  `acc(fin [done fin.acc])`.

The helper arms (axis in the hoon core `layer2` at axis `8191` of `ana`):
`by` `6103` (`rep` `767`, `has` `3061`, `put` `340`, `get` `764`), `in`
`6102` (`rep` `383`, `put` `84`, `del` `94`, `has` `381`), `ju` `760`
(`get` `46`), `min` `156` of `layer1`.
-/

namespace Formalization
namespace Compiler

open Nock Pill

/-- axis `2815` of `ana`, 837 cells. -/
def tjArm : Noun := (slot? 2815 ana).getD (A 0)
/-- axis `29` of `tjArm`, 831 cells. -/
def tjBat : Noun := (slot? 29 tjArm).getD (A 0)
/-- axis `126` of `tjBat`, 822 cells. -/
def tjRun : Noun := (slot? 126 tjBat).getD (A 0)
/-- axis `6` of `tjRun`, 12 cells. -/
def tjRepDoor : Noun := (slot? 6 tjRun).getD (A 0)
/-- axis `253` of `tjRun`, 802 cells. -/
def tjOGate : Noun := (slot? 253 tjRun).getD (A 0)
/-- axis `30` of `tjOGate`, 342 cells. -/
def tjSamB : Noun := (slot? 30 tjOGate).getD (A 0)
/-- axis `125` of `tjOGate`, 452 cells. -/
def tjOBat : Noun := (slot? 125 tjOGate).getD (A 0)
/-- axis `6` of `tjOBat`, 21 cells. -/
def tjHasV : Noun := (slot? 6 tjOBat).getD (A 0)
/-- axis `15` of `tjOBat`, 427 cells. -/
def tjElse : Noun := (slot? 15 tjOBat).getD (A 0)
/-- axis `53` of `tjElse`, 418 cells. -/
def tjConn : Noun := (slot? 53 tjElse).getD (A 0)
/-- axis `126` of `tjConn`, 66 cells. -/
def tjEnter : Noun := (slot? 126 tjConn).getD (A 0)
/-- axis `2046` of `tjConn`, 200 cells. -/
def tjKidsRep : Noun := (slot? 2046 tjConn).getD (A 0)
/-- axis `1021` of `tjKidsRep`, 177 cells. -/
def tjKGate : Noun := (slot? 1021 tjKidsRep).getD (A 0)
/-- axis `30` of `tjKGate`, 28 cells. -/
def tjKSam : Noun := (slot? 30 tjKGate).getD (A 0)
/-- axis `125` of `tjKGate`, 141 cells. -/
def tjKBat : Noun := (slot? 125 tjKGate).getD (A 0)
/-- axis `6` of `tjKBat`, 21 cells. -/
def tjKGet : Noun := (slot? 6 tjKBat).getD (A 0)
/-- axis `62` of `tjKBat`, 67 cells. -/
def tjKUnvis : Noun := (slot? 62 tjKBat).getD (A 0)
/-- axis `63` of `tjKBat`, 41 cells. -/
def tjKVis : Noun := (slot? 63 tjKBat).getD (A 0)
/-- axis `2047` of `tjConn`, 139 cells. -/
def tjAfter : Noun := (slot? 2047 tjConn).getD (A 0)
/-- axis `510` of `tjAfter`, 117 cells. -/
def tjPopBr : Noun := (slot? 510 tjAfter).getD (A 0)
/-- axis `221` of `tjPopBr`, 99 cells. -/
def tjPopBat : Noun := (slot? 221 tjPopBr).getD (A 0)

theorem tjArm_eq : tjArm = (C (A 8) (C (C (A 1) (A 0)) (C (C (A 1) tjBat) (C (A 0) (A 1))))) := by kernel_rfl
theorem tjBat_eq : tjBat = (C (A 7) (C (C (A 0) (A 1)) (C (A 7) (C (C (A 0) (A 1)) (C (A 7) (C tjRun (C (A 0) (A 31)))))))) := by kernel_rfl
theorem tjRun_eq : tjRun = (C (A 8) (C tjRepDoor (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) tjOGate) (C (A 0) (A 2)))))))) := by kernel_rfl
theorem tjRepDoor_eq : tjRepDoor = (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7fff)))) (C (A 9) (C (A 767) (C (A 10) (C (C (A 6) (C (A 0) (A 14))) (C (A 0) (A 2)))))))) := by kernel_rfl
theorem tjOGate_eq : tjOGate = (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C tjSamB (C (C (A 1) tjOBat) (C (A 0) (A 1))))))) := by kernel_rfl
theorem tjOBat_eq : tjOBat = (C (A 6) (C tjHasV (C (C (A 0) (A 13)) tjElse))) := by kernel_rfl
theorem tjHasV_eq : tjHasV = (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1ffff)))) (C (A 9) (C (A 3061) (C (A 10) (C (C (A 6) (C (A 0) (A 118))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 56))) (C (A 0) (A 2)))))))) := by kernel_rfl
theorem tjElse_eq : tjElse = (C (A 7) (C (C (A 8) (C (C (A 1) tjConn) (C (A 9) (C (A 2) (C (A 0) (A 1)))))) (C (A 0) (A 3)))) := by kernel_rfl
theorem tjConn_eq : tjConn = (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 0) (A 58)) (C (A 7) (C tjEnter (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C tjKidsRep tjAfter)))))))))) := by kernel_rfl
theorem tjEnter_eq : tjEnter = (C (A 10) (C (C (A 61) (C (A 10) (C (C (A 30) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x7ffff)))) (C (A 9) (C (A 84) (C (A 10) (C (C (A 6) (C (A 0) (A 2014))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 248))) (C (A 0) (A 2))))))))) (C (A 10) (C (C (A 14) (C (C (A 0) (A 120)) (C (A 0) (A 494)))) (C (A 10) (C (C (A 6) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x7ffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 502))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 248)) (C (A 0) (A 6)))) (C (A 0) (A 2))))))))) (C (A 10) (C (C (A 2) (C (A 4) (C (A 0) (A 122)))) (C (A 0) (A 61))))))))))) (C (A 0) (A 1)))) := by kernel_rfl
theorem tjKidsRep_eq : tjKidsRep = (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x7ffff)))) (C (A 9) (C (A 383) (C (A 10) (C (C (A 6) (C (A 0) (A 249))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) tjKGate) (C (A 0) (A 2)))))))))) := by kernel_rfl
theorem tjKGate_eq : tjKGate = (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C tjKSam (C (C (A 1) tjKBat) (C (A 0) (A 1))))))) := by kernel_rfl
theorem tjKBat_eq : tjKBat = (C (A 8) (C tjKGet (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C tjKUnvis tjKVis))))) := by kernel_rfl
theorem tjKGet_eq : tjKGet = (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffff)))) (C (A 9) (C (A 764) (C (A 10) (C (C (A 6) (C (A 0) (A 238))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))) := by kernel_rfl
theorem tjKUnvis_eq : tjKUnvis = (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 9) (C (A 2) (C (A 10) (C (C (A 14) (C (C (C (A 0) (A 28)) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 760) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 46) (C (A 10) (C (C (A 6) (C (A 0) (A 2046))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 60))) (C (A 0) (A 2))))))))) (C (A 0) (A 59)))) (C (A 0) (A 31)))))))) (C (A 7) (C (C (A 10) (C (C (A 123) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (A 8) (C (C (A 9) (C (A 156) (C (A 0) (A 0xffffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 250)) (C (A 0) (A 6)))) (C (A 0) (A 2)))))))) (C (A 0) (A 123))))))))))) := by kernel_rfl
theorem tjKVis_eq : tjKVis = (C (C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x3fffff)))) (C (A 9) (C (A 381) (C (A 10) (C (C (A 6) (C (A 0) (A 1982))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 60))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 9) (C (A 156) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 122)) (C (A 0) (A 13)))) (C (A 0) (A 2)))))))) (C (A 0) (A 58))))) (C (A 0) (A 59))) := by kernel_rfl
theorem tjAfter_eq : tjAfter = (C (A 7) (C (C (A 10) (C (C (A 125) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (C (A 0) (A 2)) (C (A 6) (C (C (A 5) (C (C (A 0) (A 6)) (C (A 0) (A 2)))) (C tjPopBr (C (A 0) (A 125)))))))))) := by kernel_rfl
theorem tjPopBr_eq : tjPopBr = (C (A 7) (C (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 1) tjPopBat) (C (A 9) (C (A 2) (C (A 0) (A 1)))))))) (C (A 10) (C (C (A 31) (C (C (A 0) (A 2)) (C (A 0) (A 63)))) (C (A 0) (A 3)))))) := by kernel_rfl
theorem tjPopBat_eq : tjPopBat = (C (A 7) (C (C (A 0) (A 1)) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C (C (A 7) (C (C (A 0) (A 1)) (C (A 6) (C (C (A 5) (C (C (A 1) (A 0)) (C (A 0) (A 4078)))) (C (C (A 0) (A 0)) (C (A 0) (A 4078))))))) (C (A 7) (C (C (A 10) (C (C (A 8174) (C (A 0) (A 5))) (C (A 0) (A 1)))) (C (A 7) (C (C (C (A 0) (A 4)) (C (A 0) (A 3))) (C (A 7) (C (C (A 10) (C (C (A 0x3fde) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 94) (C (A 10) (C (C (A 6) (C (A 0) (A 0x7fde))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 7) (C (C (A 10) (C (C (A 14) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x7fffff)))) (C (A 9) (C (A 84) (C (A 10) (C (C (A 6) (C (A 0) (A 30))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 6))) (C (A 0) (A 2))))))))) (C (A 0) (A 1)))) (C (A 6) (C (C (A 5) (C (C (A 0) (A 2040)) (C (A 0) (A 2)))) (C (C (C (A 0) (A 14)) (C (A 0) (A 1021))) (C (A 9) (C (A 2) (C (A 0) (A 3))))))))))))))))))))) := by kernel_rfl

/-- The hoon core of `+tarjan`'s context. -/
theorem ana_layer2' : slot? 8191 ana = some layer2 := ana_layer2

end Compiler
end Formalization
