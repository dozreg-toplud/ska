import lemmas.Compiler.PokeLinkScc

/-!
# `+scc-of`: the gate on its sample, and the cache hit

The map of `+scc-of` is in README Gaps 23 (`tools/gen/sccof.py`).  The arm
`96127` of the core `sccCore` (axis `7` of the library) is
`[7 [8 [1 bunt] [1 bat] 0 1] [11 [%fast [1 clue]] [0 1]]]`, and its battery
`sccBat` (409 cells) is `[8 get [6 ?=(@ s) miss hit]]`:

* `sccG_eq`: `sccG` is the battery on `[sample sccCore]`;
* `sccG_hit`: when `sccs` already has the bell, the gate returns its SCC
  and `sccs` unchanged (`(~(get by sccs) b)`, `get_gate`, the `?^`).

The miss (373 cells: the `sub` loop, the roll over `+tarjan`, `got:by`) is
`sccMiss`, not opened here.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Ana SkaModel.Bake SkaModel.PokeM

/-- The core of `+scc-of` (`..ride`): axis `7` of the library. -/
def sccCore : Noun := (slot? 7 corLib).getD (A 0)
/-- The arm `96127` of `sccCore`. -/
def sccArm : Noun := (slot? 96127 sccCore).getD (A 0)
def sccBunt : Noun := (slot? 53 sccArm).getD (A 0)
/-- The battery of the gate (409 cells). -/
def sccBat : Noun := (slot? 109 sccArm).getD (A 0)
/-- The cache miss (373 cells). -/
def sccMiss : Noun := (slot? 62 sccBat).getD (A 0)

/-- `s=(~(get by sccs) b)`. -/
def sccGetF : Noun :=
  C (A 8) (C (C (A 8) (C (C (A 9) (C (A 6103) (C (A 0) (A 262143))))
    (C (A 9) (C (A 764) (C (A 10) (C (C (A 6) (C (A 0) (A 59))) (C (A 0) (A 2))))))))
    (C (A 9) (C (A 2) (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))
/-- `?=(@ s)`. -/
def sccTestF : Noun := C (A 6) (C (C (A 3) (C (A 0) (A 2))) (C (C (A 1) (A 1)) (C (A 1) (A 0))))
/-- `[u.s sccs]`. -/
def sccHitF : Noun := C (C (A 0) (A 5)) (C (A 0) (A 59))
/-- The `%fast` hint of `~%  %scc-of  ..ride  ~`. -/
def sccHint : Noun := C (A 1953718630) (C (A 1) (C (A 112627688891251) (C (C (A 0) (A 32767)) (A 0))))

theorem corLib_sccCore : slot? 7 corLib = some sccCore := by kernel_rfl
theorem sccCore_arm : slot? 96127 sccCore = some (C (A 7) (C (C (A 8) (C (C (A 1) sccBunt)
    (C (C (A 1) sccBat) (C (A 0) (A 1))))) (C (A 11) (C sccHint (C (A 0) (A 1)))))) := by kernel_rfl
theorem sccBat_eq : sccBat = C (A 8) (C sccGetF (C (A 6) (C sccTestF (C sccMiss sccHitF)))) := by kernel_rfl
theorem sccCore_hoon : slot? 65535 sccCore = some layer2 := by kernel_rfl

/-- **The gate of `+scc-of` on its sample.** -/
theorem sccG_eq (func ca sc : Noun) :
    sccG func ca sc = nock (C sccBat (C (C func (C ca sc)) sccCore)) sccBat := by
  simp [sccG, corLib_sccCore, gateAt, sccCore_arm, slamG, sccHint, nock_exec]

/-- The battery on a sample, with the hit branch open. -/
theorem sccBat_run (sub : Noun) :
    nock sub sccBat = (nock sub sccGetF).bind fun s =>
      (nock (C s sub) sccTestF).bind fun t =>
        if t = A 0 then nock (C s sub) sccMiss else if t = A 1 then nock (C s sub) sccHitF else none := by
  conv => lhs; rw [sccBat_eq]
  simp only [nock_exec]
  cases nock sub sccGetF with
  | none => rfl
  | some s =>
    simp only [Option.bind_some]
    cases nock (C s sub) sccTestF with
    | none => rfl
    | some t =>
      simp only [Option.bind_some]
      rcases t with (_ | _ | t) | ⟨_, _⟩ <;> simp [nock_exec, Nock.pick]

/-- **The cache hit**: when `sccs` has the bell, `+scc-of` returns its SCC
and `sccs` unchanged. -/
theorem sccG_hit (b : Bell) (ca : Noun) (sc : FinMap Bell (FinMap Bell Unit)) (v : FinMap Bell Unit)
    (hv : sc.get b = some v) :
    sccG b.toNoun ca (sccsNoun sc) = some (sccPairNoun (v, sc)) := by
  have hgc : SomeIn layer2 ∧ GorIn mugF layer2 := ⟨someIn_layer2, gorIn_morIn_layer2.1⟩
  have hget : getF mugF b.toNoun (sccsNoun sc) = some (C (A 0) (FinMap.setNoun v)) := by
    have h := FinMap.getF_toNoun FinMap.setNoun sc b
    rw [hv] at h
    exact h
  have hg := get_gate layer2 hgc b.toNoun (sccsNoun sc) _ hget
  rw [sccG_eq, sccBat_run]
  have h1 : nock (C sccBat (C (C b.toNoun (C ca (sccsNoun sc))) sccCore)) sccGetF =
      some (C (A 0) (FinMap.setNoun v)) := by
    simp [sccGetF, by.arm_at, by_arm, by.get.arm_at, get_arm, nock_exec, hg]
  rw [h1]
  simp [sccTestF, sccHitF, sccPairNoun, nock_exec]

/-- **The image of `+scc-of` on a cache miss** (open: the 373 cells of
`sccMiss`, with `+tarjan`). -/
def SccImageMiss : Prop :=
  ∀ (b : Bell) (L : LongB FinMap) (sc : FinMap Bell (FinMap Bell Unit)) x, sc.get b = none →
    sccG b.toNoun (callsNoun L) (sccsNoun sc) = some x → ∃ r, x = sccPairNoun r

/-- **`SccImage` from the miss**: the hit is `sccG_hit`. -/
theorem sccImage_of_miss (h : SccImageMiss) : SccImage := by
  intro b L sc x hx
  cases e : sc.get b with
  | none => exact h b L sc x e hx
  | some v =>
    rw [sccG_hit b (callsNoun L) sc v e] at hx
    exact ⟨(v, sc), (Option.some.inj hx).symm⟩


end Compiler
end Formalization
