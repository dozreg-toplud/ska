import lemmas.Compiler.CompSccLoopSoftTryCut
import lemmas.Compiler.CompSccLoopSoftEmitBase
import lemmas.Ska.SccLoopSoftTry

/-! # The subjects of the try path of `+soft-emit` (README Gaps 21.22)

`seTryPath` (cut in `CompSccLoopSoftTryCut.lean`) runs on `tpS0`: the head block `hed`, `tries`,
`ops`, `cut`, `axs`, the battery and the sample `[o s]` of the gate, the core with `gen`.  Each
push puts its product in front: `lat` (`tp0`), the gate `flag` (`tpY0`, the core `tpFlagN`),
`tom` (`tpY1`), `[kon rub]` (`tpY2` to `tpY5`, `gen` replaced), `pes` (`tpYN0` to `tpYN3`),
`fail` (`tpYN4` to `tpYN7`), `def` (`tpYN8`); then `+soft-free` (`tpYN9`).  `softPesM` is the
model's `pes` (the call of the subject version, inline in `softEmit`). -/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

/-- The subject of `seTryPath`: `[hed tries ops cut axs seBat [o s] core]`. -/
abbrev tpS0 (HD TR OPS CUT AXS : Noun) (o : Nat) (s : SoftCall) (g : Gen (TreapMap mugF)) (x : GenRest)
    (ctx : Noun) : Noun :=
  C HD (C TR (C OPS (C CUT (C AXS (seS0 g x ctx o s)))))

/-- The gate `flag` that `tpY0` pushes on the subject `S` (the bunt of `fail` is `0`). -/
abbrev tpFlagN (S : Noun) : Noun := C tpYH0Bat (C (A 0) S)

/-- The noun of `[kon rub]`. -/
abbrev tpKR (kon : List Pole) (rub : Nat) : Noun := C (listNoun Pole.toNoun kon) (A rub)

variable {Map : Type → Type} [HoonMap Map]

/-- **`pes`** (line 5433), as `softEmit` has it: the call of the subject version. -/
def softPesM (s : SoftCall) (rub : Nat) : CM Map Nat :=
  if s.kin = 1 then emitCold ⟨[], [], Termin.jsp s.b rub⟩
  else if s.kin = 0 then do
    let proOpt ← re
    let proPes ← re
    let merged ← re
    let merge ← emit ⟨[merged], [Pole.mov merged s.pro], Termin.hop (jmp0 s.out)⟩
    emir s.plain ⟨[], [Pole.cal s.b (flattenNeed s.ned) proOpt], Termin.hop ⟨[some proOpt], merge⟩⟩
    emitCold ⟨[], [Pole.csl s.b rub proPes], Termin.hop ⟨[some proPes], merge⟩⟩
  else crashM

/-- `def` (line 5458): the registers that the tries define. -/
def softDefs (tries : List (Nat × Nat × Need)) : List Nat :=
  (tries.map fun (_, _, n) => flattenNeed n).flatten

end Compiler
end Formalization
