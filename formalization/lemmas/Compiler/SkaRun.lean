import lemmas.Compiler.SkaCull
import lemmas.Compiler.MsgCa

/-!
# `+run` of the core of `+ska-callgraph`

The arm `95` of the core `K` (`SkaCore.lean`) against `Ana.runStep`, over an
evaluator `nockW c` with `c` equal to `nock` off `FFar`, with the trap
`fol-loop` as a parameter (`GoIsW`).

The battery `ska_run.battery` counts the run, reads the old datum with
`+git-g`, pushes `bus`, `fol` and `sub`, and runs `[8 runFolF runDatumF]`:
`runFolF` builds `gen` and the trap's subject and kicks the trap
(`ska_run_battery_eq`, by the kernel), and `runDatumF` makes the datum from
the trap's result and writes it into `g`.  The datum construction is its own
lemma (`run_datum`), so a change to it (for example `less-code` merged with
the old entry's) changes only that lemma.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon SkaModel.Ana

variable {R : Type}

/-! ## The formulas -/

def rdLess : Noun :=
  (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 16383)))) (C (A 9) (C (A 341) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 26)) (C (A 0) (A 62)))) (C (A 0) (A 2))))))))

def rdDark : Noun :=
  (C (A 6) (C (C (A 6) (C (C (A 3) (C (A 0) (A 62))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 1)) (C (A 0) (A 124)))))

def rdIndi : Noun :=
  (C (A 10) (C (C (A 118) (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 65535)))) (C (A 9) (C (A 171) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 246)) (C (A 0) (A 6)))) (C (A 0) (A 2))))))))) (C (A 0) (A 1))))

def rdNew : Noun :=
  (C (C (A 0) (A 478)) (C (C (A 0) (A 56)) (C (C (A 0) (A 6)) (C (C (A 0) (A 118)) (C (C (A 0) (A 238)) (C (C (A 0) (A 114)) (C (A 0) (A 958))))))))

def rdPm : Noun :=
  (C (A 6) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0x7ffffff)))) (C (A 9) (C (A 381) (C (A 10) (C (C (A 6) (C (A 0) (A 0xfbffe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 8188))) (C (A 0) (A 2)))))))) (C (C (A 8) (C (C (A 9) (C (A 5495) (C (A 0) (A 32767)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 7) (C (C (A 0) (A 2)) (C (C (A 0) (A 252)) (C (A 0) (A 253))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 7) (C (C (A 0) (A 510)) (C (C (A 0) (A 252)) (C (A 0) (A 253))))))))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 9) (C (A 4) (C (A 0) (A 0x1ffff)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 7) (C (C (A 0) (A 2)) (C (C (A 0) (A 252)) (C (A 0) (A 253))))))) (C (A 7) (C (C (A 0) (A 3)) (C (A 7) (C (C (A 0) (A 510)) (C (C (A 0) (A 252)) (C (A 0) (A 253))))))))) (C (A 0) (A 2)))))))))))

def rdProd : Noun :=
  (C (A 10) (C (C (A 892) (C (A 0) (A 4))) (C (A 0) (A 1))))

def rdMap : Noun :=
  (C (A 10) (C (C (A 893) (C (A 0) (A 5))) (C (A 0) (A 1))))

def rdMoved : Noun :=
  (C (A 10) (C (C (A 0xfbffe) (C (A 6) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 1) (A 0x64696f76)) (C (A 0) (A 0x1ff7c)))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 2)) (C (A 7) (C (C (A 0) (A 1022)) (C (C (A 0) (A 252)) (C (A 0) (A 253))))))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6102) (C (A 0) (A 0xfffffff)))) (C (A 9) (C (A 84) (C (A 10) (C (C (A 6) (C (A 0) (A 0x1fbffe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 16380))) (C (A 0) (A 2)))))))) (C (A 0) (A 0xfbffe)))))) (C (A 0) (A 1))))

def rdIndi2 : Noun :=
  (C (A 10) (C (C (A 110) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 7) (C (C (A 0) (A 6)) (C (C (A 0) (A 14)) (C (C (A 0) (A 252)) (C (A 0) (A 253)))))) (C (A 7) (C (C (A 0) (A 1022)) (C (C (A 0) (A 14)) (C (C (A 0) (A 252)) (C (A 0) (A 253)))))))) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 110)) (C (A 0) (A 16366)))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 8) (C (C (A 7) (C (C (A 9) (C (A 20) (C (A 0) (A 0x3ffff)))) (C (A 9) (C (A 171) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 7) (C (C (A 0) (A 3)) (C (A 8) (C (C (A 9) (C (A 187) (C (A 0) (A 65535)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 238)) (C (A 0) (A 32750)))) (C (A 0) (A 2)))))))))) (C (A 0) (A 30)))) (C (A 0) (A 2)))))))) (C (A 0) (A 110)))))) (C (A 0) (A 1))))

def rdSeek : Noun :=
  (C (A 10) (C (C (A 222) (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 7) (C (C (A 0) (A 6)) (C (C (A 0) (A 14)) (C (C (A 0) (A 252)) (C (C (A 0) (A 253)) (C (A 0) (A 30))))))) (C (A 7) (C (C (A 0) (A 1022)) (C (C (A 0) (A 14)) (C (C (A 0) (A 252)) (C (C (A 0) (A 253)) (C (A 0) (A 30))))))))) (C (C (A 6) (C (C (A 6) (C (C (A 5) (C (C (A 0) (A 222)) (C (A 0) (A 32734)))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))) (C (C (A 1) (A 0)) (C (A 1) (A 1))))) (C (A 1) (A 1))))) (C (C (A 8) (C (C (A 9) (C (A 187) (C (A 0) (A 65535)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 478)) (C (A 0) (A 65502)))) (C (A 0) (A 2)))))))) (C (A 0) (A 222)))))) (C (A 0) (A 1))))

def rdChanged : Noun :=
  (C (A 6) (C (C (A 5) (C (C (A 7) (C (C (A 0) (A 6)) (C (C (A 0) (A 14)) (C (C (A 0) (A 252)) (C (C (A 0) (A 253)) (C (C (A 0) (A 30)) (C (A 0) (A 62)))))))) (C (A 7) (C (C (A 0) (A 1022)) (C (C (A 0) (A 14)) (C (C (A 0) (A 252)) (C (C (A 0) (A 253)) (C (C (A 0) (A 30)) (C (A 0) (A 62)))))))))) (C (C (A 1) (A 1)) (C (A 1) (A 0)))))

def rdTick : Noun :=
  (C (A 10) (C (C (A 0x3f7ffe) (C (A 4) (C (A 0) (A 0x3f7ffe)))) (C (A 0) (A 1))))

def rdTicks : Noun :=
  (C (A 10) (C (C (A 0x7efffe) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0xfefffe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 32764)) (C (A 7) (C (C (A 0) (A 3)) (C (C (A 0) (A 0x3f7ffe)) (C (A 6) (C (C (A 0) (A 2)) (C (C (A 0) (A 0x3f7ffe)) (C (A 7) (C (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 1531) (C (A 10) (C (C (A 6) (C (A 0) (A 0xfefffe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 32764)) (C (A 7) (C (C (A 0) (A 3)) (C (A 1) (C (A 0) (A 0))))))) (C (A 0) (A 2)))))))) (C (A 0) (A 3)))))))))))) (C (A 0) (A 2))))))))) (C (A 0) (A 1))))

def rdFin : Noun :=
  (C (C (C (A 0) (A 16254)) (C (C (A 0) (A 32510)) (C (A 0) (A 2)))) (C (A 10) (C (C (A 2) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 0x1fffffff)))) (C (A 9) (C (A 340) (C (A 10) (C (C (A 6) (C (A 0) (A 0x1fdfe))) (C (A 0) (A 2)))))))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 32764)) (C (A 0) (A 30)))) (C (A 0) (A 2))))))))) (C (A 0) (A 32511)))))

/-- The datum construction of `+run`, the formula after `fol-loop`. -/
def runDatumF : Noun :=
  C (A 8) (C rdLess (C (A 8) (C rdDark (C (A 7) (C rdIndi (C (A 8) (C rdNew (C (A 8) (C rdPm (C (A 7) (C rdProd (C (A 7) (C rdMap (C (A 7) (C rdMoved (C (A 7) (C rdIndi2 (C (A 7) (C rdSeek (C (A 8) (C rdChanged (C (A 7) (C rdTick (C (A 7) (C rdTicks (rdFin))))))))))))))))))))))))))

/-- The run of `fol-loop` in `+run`: its `gen` and the trap, kicked. -/
def runFolF : Noun :=
  (C (A 8) (C (C (C (A 1) (A 1)) (C (C (A 1) (A 1)) (C (C (A 1) (A 1)) (C (C (A 1) (A 0)) (C (C (A 1) (A 0)) (C (C (A 0) (A 506)) (C (C (A 1) (A 1)) (C (A 0) (A 507))))))))) (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 1) (A 1)) (C (A 8) (C (C (A 1) (A 1)) (C (A 7) (C (C (A 8) (C (C (A 1) fol_loop.battery) (C (A 11) (C (C (A 0x74736166) (C (A 1) (C (A 0x706f6f6c2d6c6f66) (C (C (A 0) (A 0x3ffffff)) (A 0))))) (C (A 0) (A 1)))))) (C (A 9) (C (A 2) (C (A 0) (A 1))))))))))))))))

/-- The battery of `+run`, split at the trap and the datum construction. -/
theorem ska_run_battery_eq : ska_run.battery =
    (C (A 7) (C (C (A 10) (C (C (A 28670) (C (A 4) (C (A 0) (A 28670)))) (C (A 0) (A 1)))) (C (A 8) (C (C (A 8) (C (C (A 9) (C (A 4) (C (A 0) (A 127)))) (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (C (A 0) (A 118)) (C (A 0) (A 28)))) (C (A 0) (A 2)))))))) (C (A 8) (C (C (A 0) (A 56)) (C (A 8) (C (C (A 0) (A 121)) (C (A 8) (C (C (C (A 0) (A 6)) (C (A 1) (A 1))) (C (A 7) (C (C (A 0) (A 1)) (C (A 8) (C runFolF runDatumF)))))))))))))) := by kernel_rfl

end Compiler
end Formalization
