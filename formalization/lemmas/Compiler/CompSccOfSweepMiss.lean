import lemmas.Compiler.CompSccOfSweep

/-!
# The miss of `+callee-compiled` inside a sweep call (README Gaps 19 (g))

In the Hoon, `+run-shape` (the `%may` / `%must` calls of `+member` in the sweeps of
`+compile-scc-in`) reaches a callee through the same `+callee-need` as `+run`: a callee outside the
SCC goes to `+callee-compiled`, which on a `nary.cache` miss runs `+scc-of` and `+compile-scc-in`
on the callee's SCC and returns the extended `cache.gen`, so the cache a sweep call leaves can be
larger than the cache of `+inlined` (`CA1`).  This is the common case, not a corner: the first
sweep (`%may`, or `%must` without the dedicated shape pass) is where a member's outside callees are
met first.

What the loop needs of that cache (the second alternative of `MemSweepCallK`: `QK` and the
members' `sure` entries) follows from

* the step's own facts, which a compile of a miss gives (`CalleeCompiledP`: `Ext`, `AgreeIP` with
  the bells in progress, the rest predicate), and
* that the compile leaves the `nary` and `sure` entries at the keys of the SCC `S` as they were
  (the compile writes only bells reachable from the callee, and none of them is in `S`, else the
  callee would be in `S`).

* `SweepMissK`: these facts, from `CA1` to the cache `CA2` the branch leaves;
* **`sweepMiss_keeps`**: `QK` and `SureHolds` at `CA1` give them at `CA2`;
* `MemSweepCallKM`: `MemSweepCallK` with the miss case as a third alternative stated by
  `SweepMissK`; **`memSweepCall_of_KDM`**: it gives track I's `MemSweepCall` at `RKD`, as
  `memSweepCall_of_KD` does for the other two.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp SkaModel.SccLoop

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **The miss case of a sweep call, from `CA1` to `CA2`**: a `CalleeCompiledP` step (`Ext`,
`AgreeIP` with the bells in progress and `S`, the rest predicate) that leaves the `nary` and
`sure` entries at the keys of `S` as they were. -/
def SweepMissK (env : CallEnv) (RR : GenRest → Prop) (P : Noun → Prop) (S : Noun) (x : GenRest) (CA1 CA2 : Noun) :
    Prop :=
  Ext ⟨CA1, x.soft, x.sofs⟩ ⟨CA2, x.soft, x.sofs⟩ ∧
    AgreeIP env (fun k => P k ∨ k ∈ tapList S) ⟨CA2, x.soft, x.sofs⟩ ∧ RR ⟨CA2, x.soft, x.sofs⟩ ∧
    (∀ NR1 REST1, CA1 = C NR1 REST1 → ∃ NR2 REST2, CA2 = C NR2 REST2 ∧
      ∀ k ∈ tapList S, getF mugF k NR2 = getF mugF k NR1) ∧
    (∀ SU1, slot? 31 CA1 = some SU1 → ∃ SU2, slot? 31 CA2 = some SU2 ∧
      ∀ k ∈ tapList S, getF mugF k SU2 = getF mugF k SU1)

/-- **`QK` and the members' `sure` entries survive the miss step.** -/
theorem sweepMiss_keeps {env : CallEnv} {RR : GenRest → Prop} {P : Noun → Prop} {S : Noun} {x : GenRest}
    {sure : Noun → Option NeedOrd} {CA1 CA2 : Noun} (hQ : QK env RR P S x CA1)
    (hS : SureHolds (tapList S) sure CA1) (hM : SweepMissK env RR P S x CA1 CA2) :
    QK env RR P S x CA2 ∧ SureHolds (tapList S) sure CA2 := by
  obtain ⟨hA, hE, -, NR1, REST1, hc1, hmiss⟩ := hQ
  obtain ⟨hE2, hA2, hR2, hN, hU⟩ := hM
  obtain ⟨NR2, REST2, hc2, hk⟩ := hN NR1 REST1 hc1
  obtain ⟨SU1, hs1, hall⟩ := hS
  obtain ⟨SU2, hs2, hk2⟩ := hU SU1 hs1
  refine ⟨⟨hA2, ext_trans hE hE2, hR2, NR2, REST2, hc2, fun k hk' => by rw [hk k hk']; exact hmiss k hk'⟩,
    SU2, hs2, fun b hb => ?_⟩
  rw [hk2 b hb]
  exact hall b hb

/-- **`MemSweepCallK` with the miss of `+callee-compiled` inside `+run-shape`**: the cache the
branch leaves is `CA1`, or one with `QK` and `sure` (the old second case), or `CA2` with
`SweepMissK` from `CA1`. -/
def MemSweepCallKM (r : RealCfg) (xs : ShapeX) (order : List Noun) (kids : Noun → List Noun)
    (nout : Noun → NeedOrd) (envK : CallEnv) (RR : GenRest → Prop) (inl : Noun → Option Nomm) (P : Noun → Prop)
    (S : Noun) (x : GenRest) (mode : Mode) (top : Noun → NeedOrd) (TOP : Noun)
    (st : St Noun NeedOrd) (keep : Bool) (DN KIDS ML0 CB SCC CODE LSR JH CACHE0 b ML CACHE : Noun) : Prop :=
  ∃ (cape : Cape) (DATA FOL : Noun) (nm : Nomm) (fuel : Nat), b = C (C cape.toNoun DATA) FOL ∧
    r.info b = ⟨nm, cape, DATA, fuel⟩ ∧ ∃ CA1,
    nock (C inlBody (C (C b (C (C CODE LSR) (C JH CACHE))) compK)) inlBody = some (C nm.toNoun CA1) ∧
    InlKeep inl CACHE CA1 ∧
    ∃ (col sur : NeedOrd) (G2 : Noun),
      MemShapeBranch xs mode (envView r.env r.scc (viewN top st) (viewS (cfgRealShape r xs order kids) st))
        cape DATA FOL nm fuel keep SCC (C CODE LSR) JH ML TOP CA1 (memCtx DN KIDS ML0 CB SCC (C CODE LSR) JH CACHE0)
        col sur G2 ∧
    (slot? 510 G2 = some CA1 ∨
      (∃ C1 C2 C3 C4 SURE, slot? 510 G2 = some (cacheN C1 C2 C3 C4 SURE) ∧ QK envK RR P S x (cacheN C1 C2 C3 C4 SURE) ∧
        SureHolds r.scc st.sure (cacheN C1 C2 C3 C4 SURE)) ∨
      ∃ CA2, slot? 510 G2 = some CA2 ∧ SweepMissK envK RR P S x CA1 CA2)

/-- **`MemSweepCall` from `MemSweepCallKM` at `RKD`** (`memSweepCall_of_KD` with the miss case:
`eMD_start` gives `QK` and `sure` at `CA1`, `sweepMiss_keeps` carries them to `CA2`). -/
theorem memSweepCall_of_KDM {r : RealCfg} {xs : ShapeX} {order : List Noun} {kids : Noun → List Noun}
    {nout : Noun → NeedOrd} {env : CallEnv} {SC0 MO0 : Noun} {inl : Noun → Option Nomm} {P Pf : Noun → Prop}
    {S : Noun} {x : GenRest} {mode : Mode} {top : Noun → NeedOrd} {TOP : Noun} {st : St Noun NeedOrd} {keep : Bool}
    {DN KIDS ML0 CB SCC CODE LSR JH CACHE0 b ML CACHE : Noun}
    (hrs : r.scc = tapList S) (hPS : ∀ k ∈ tapList S, ¬ P k)
    (hR : LoopRS r.scc (fun _ => []) nout (QK env (RKD SC0 MO0 inl Pf) P S x) st.ml st.sure ML CACHE)
    (h : MemSweepCallKM r xs order kids nout env (RKD SC0 MO0 inl Pf) inl P S x mode top TOP st keep DN KIDS ML0 CB SCC
      CODE LSR JH CACHE0 b ML CACHE) :
    MemSweepCall r xs order kids (fun _ => []) nout env (RKD SC0 MO0 inl Pf) P S x mode top TOP st keep DN KIDS ML0 CB
      SCC CODE LSR JH CACHE0 b ML CACHE := by
  obtain ⟨cape, DATA, FOL, nm, fuel, hb, hinfo, CA1, hinl, hik, col, sur, G2, hbrn, hc⟩ := h
  rcases hc with hc | hc | ⟨CA2, hG, hM⟩
  · exact memSweepCall_of_KD hrs hPS hR ⟨cape, DATA, FOL, nm, fuel, hb, hinfo, CA1, hinl, hik, col, sur, G2, hbrn,
      Or.inl hc⟩
  · exact memSweepCall_of_KD hrs hPS hR ⟨cape, DATA, FOL, nm, fuel, hb, hinfo, CA1, hinl, hik, col, sur, G2, hbrn,
      Or.inr hc⟩
  · have hsh : SureHolds (tapList S) st.sure CACHE := by rw [← hrs]; exact hR.1.2.1
    obtain ⟨hA1, -, hQ1, hS1⟩ := eMD_start hPS hR.1.2.2.2 hsh hik
    obtain ⟨hQ2, hS2⟩ := sweepMiss_keeps hQ1 hS1 hM
    obtain ⟨-, C1, C2, C3, C4, SU, hc2, -⟩ := hQ2.1
    change CA2 = cacheN C1 C2 C3 C4 SU at hc2
    subst hc2
    refine ⟨cape, DATA, FOL, nm, fuel, hb, hinfo, CA1, hinl, col, sur, G2, hbrn, ?_⟩
    exact ⟨C1, C2, C3, C4, SU, hG, hQ2, by rw [hrs]; exact hS2, fun b' _ k hk => by simp at hk⟩

end Compiler
end Formalization
