import lemmas.Compiler.CompSccLoopNouns
import lemmas.Exec

/-! # The loop skeleton `csiFix` of `+compile-scc-in` in the pill (README Gaps 21.11)

The first links of the cut of `tools/gen/csifix.py` (`CompSccLoopNouns.lean`):

* `csf_enter`: the pushes of `st` (`[| 0 ~ ~]`), `counter` (`0`) and of the trap of the sweeps
  enter the trap on the core `[csfTrap 0 csfSt0 X]`.
* `csf_trap`: one turn of the trap.  The sweep `csfSwRoll` gives `res = [[any ..] ..]`; on
  `any = &` the trap goes on with `csfRec` (the print and the `%=  sweep-loop`), on `any = |`
  it ends with `csfFin` (`(final & map-local cache)`).
* `csf_fix`: `csiFix` is the DFS `csfOrder`, the `%may` sweep `csfMay` and its `=^`, `top`
  (`csfTop`) and then the trap, given the products of those pushes. -/

namespace Formalization
namespace Compiler

open Nock

/-- The trap core of the sweeps: the battery, `counter`, `st` and the rest of the subject. -/
def csfCore (CNT ST X : Noun) : Noun := C csfTrap (C CNT (C ST X))

/-- **The entry of the trap**: `st` and `counter` pushed, then the `|-` on its core. -/
theorem csf_enter (X : Noun) :
    nock X (C (A 8) (C (C (A 1) csfSt0) (C (A 8) (C (C (A 1) (A 0)) (C (A 8) (C (C (A 1) csfTrap)
      (C (A 9) (C (A 2) (C (A 0) (A 1)))))))))) = nock (csfCore (A 0) csfSt0 X) csfTrap := by
  simp only [nock_exec, csfCore]

/-- **One turn of the trap of the sweeps**: the sweep `csfSwRoll` on the core gives `res`,
whose `any.st` (axis 8 of `[res core]`) picks the recursion `csfRec` (`&`) or the end
`csfFin` (`|`), both on `[res core]`. -/
theorem csf_trap (CNT ST X ANY TK RN CG MC : Noun)
    (h : nock (csfCore CNT ST X) csfSwRoll = some (C (C ANY (C TK (C RN CG))) MC)) :
    nock (csfCore CNT ST X) csfTrap =
      (pick ANY csfRec csfFin).bind fun next =>
        nock (C (C (C ANY (C TK (C RN CG))) MC) (csfCore CNT ST X)) next := by
  conv => lhs; arg 2; rw [csfTrap_eq]
  simp only [nock_exec, h]

/-- The trap on `any = |`: the end, `csfFin` on `[res core]`. -/
theorem csf_trap_end (CNT ST X TK RN CG MC : Noun)
    (h : nock (csfCore CNT ST X) csfSwRoll = some (C (C (A 1) (C TK (C RN CG))) MC)) :
    nock (csfCore CNT ST X) csfTrap =
      nock (C (C (C (A 1) (C TK (C RN CG))) MC) (csfCore CNT ST X)) csfFin := by
  rw [csf_trap CNT ST X (A 1) TK RN CG MC h]; rfl

/-- The trap on `any = &`: `csfRec` on `[res core]`. -/
theorem csf_trap_rec (CNT ST X TK RN CG MC : Noun)
    (h : nock (csfCore CNT ST X) csfSwRoll = some (C (C (A 0) (C TK (C RN CG))) MC)) :
    nock (csfCore CNT ST X) csfTrap =
      nock (C (C (C (A 0) (C TK (C RN CG))) MC) (csfCore CNT ST X)) csfRec := by
  rw [csf_trap CNT ST X (A 0) TK RN CG MC h]; rfl

/-- **`csiFix` from its pushes**: the DFS gives `ORD` on the subject `S`; the `%may` sweep gives
the pair `[MAY CACHE']` on `[ORD S]`; the `=^` (`csfPut`, `csfCons`) gives the subject `S2`; `top`
gives `TOP` on it; then the trap is entered on `[TOP S2]`. -/
theorem csf_fix (S ORD MP S1 S2 TOP : Noun)
    (hord : nock S csfOrder = some ORD)
    (hmay : nock (C ORD S) csfMay = some MP)
    (hput : nock (C MP (C ORD S)) csfPut = some S1)
    (hcons : nock S1 csfCons = some S2)
    (htop : nock S2 csfTop = some TOP) :
    nock S csiFix = nock (csfCore (A 0) csfSt0 (C TOP S2)) csfTrap := by
  rw [csiFix_cut, csfFix_eq]
  simp only [nock_exec, hord, hmay, hput, hcons, htop, csfCore]

end Compiler
end Formalization
