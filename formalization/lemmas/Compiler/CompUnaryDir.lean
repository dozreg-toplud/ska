import lemmas.Compiler.CompRunRClass
import lemmas.Compiler.CompStraightMapSix
import lemmas.Ska.CompDirectMEq

/-!
# The gate of `+compile-unary` on code with direct calls (README Gaps 19)

`+compile-unary` (K arm `2810`, line 3396) runs `(~(run comp gen) & nomm
[%done ~] ~ ~)` after `+compile-scc-in` and `+comp scc long-ska jets-hot
n-ary-map ~ func`: the run at `mono` `&` with `msup = ~` from `genEntry`,
then `+kerf` and `+to-straight`.  On a nomm of `DirOk` whose direct calls
meet `CallOk` (`DirCalls`) in the context `cuCtx` that `+comp` builds and at
the one rest `cuRest CA` (the cache `+compile-scc-in` returned), the run is
`runLCM env true` (`comp_run_dirMM`), so the gate is `finishLUCM env n`.

* `cu_trap_dir`: the trap, as `cu_trap_six` with `comp_run_dirMM` for the
  run, `res_dir` for what it returns (`LAll CrLok` for `+kerf`),
  `comp_kerf_all`, `ts_at_all`.
* **`cu_gate_dir`**: the gate of `+compile-unary` on `DirOk` is `finishLUCM
  env n`, given `DirCalls`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSectionVars false

/-- **The trap of `+compile-unary` on `DirOk`**: if `+compile-scc-in` returns
`[NM CA]`, `code` holds the nomm `n` at `func` and every direct call of `n`
meets `CallOk` at the rest `cuRest CA`, the trap returns `[[straight NM] CA]`
with `straight` the noun of `finishLUCM env n`, and crashes when that is
`none`. -/
theorem cu_trap_dir (FUNC SCC CODE LSR JH CACHE NM CA V : Noun) (env : CallEnv) (n : Nomm) (hn : DirOk n = true)
    (hd : DirCalls env CODE (cuCtx FUNC SCC CODE LSR JH NM) (· = cuRest CA) Option.none n)
    (hcsi : nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuCsi = some (C NM CA))
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuTrap
      = (finishLUCM (S := CSet) (Map := TreapMap mugF) env n).map fun st => C (C st.toNoun NM) CA := by
  have h7 : slot? 7 (cuCtx FUNC SCC CODE LSR JH NM) = some compK := rfl
  have hcode : slot? 52 (cuCtx FUNC SCC CODE LSR JH NM) = some CODE := by simp [cuCtx, nock_exec]
  obtain ⟨hc, hl, hm⟩ := comp_ctx_pill _ h7
  have hrun := comp_run_dirMM h7 hcode env (· = cuRest CA) n hn Option.none [] hd (CGoal.toL CGoal.done) genEntry
    (show genEntry.drop = false from rfl) (cuRest CA) (cu_entry_nosoft CA) rfl
  simp only [RunAtR, unitNoun] at hrun
  have hres := res_dir h7 hcode env (· = cuRest CA) n hn Option.none [] hd
  rw [cu_trap_entry FUNC SCC CODE LSR JH CACHE NM CA hcsi,
    cu_trap_run FUNC SCC CODE LSR JH CACHE NM CA V n hgot hv, hrun]
  have hf : finishLUCM (S := CSet) (Map := TreapMap mugF) env n
      = ((runLCM env true Option.none n (CGoal.toL (CGoal.done : CGoal CSet)) [] genEntry).bind
          fun p => kerf p.1 p.2).bind
          fun q => toStraightF q.2.cond q.2.blocks (Need.this q.1.2) q.1.1 := by
    rw [Option.bind_assoc]; rfl
  rw [hf]
  cases e : runLCM (S := CSet) (Map := TreapMap mugF) env true Option.none n (CGoal.toL (CGoal.done : CGoal CSet)) []
      genEntry with
  | none => simp
  | some p =>
    obtain ⟨nex, g1⟩ := p
    obtain ⟨-, -, hG, -⟩ := hres CGoalL.done genEntry g1 nex rfl e
    simp only [NextL.goal, GInv] at hG
    have hlok : LAll CrLok nex.laz := lall_mono (fun s h => h.1) hG.1.1
    have hk := comp_kerf_all hc hl hm (cuRest CA) g1 nex (walk_mdP (cu_entry_nosoft CA) g1.bo hlok)
    simp only [compCore] at hk
    simp only [Option.bind_some, Option.map_some, NextL.goal, CGoalL.toNoun]
    rw [cu_trap_kerf, hk]
    cases e2 : kerf nex g1 with
    | none => simp
    | some q =>
      obtain ⟨⟨o, sub⟩, g2⟩ := q
      have h : nock (C tsBat (C (tsSampleN (A o) (C (A 0x73696874) (A sub)))
            (C comp.door (C (genNoun g2 (cuRest CA)) (cuCtx FUNC SCC CODE LSR JH NM))))) tsBat
          = (toStraightF g2.cond g2.blocks (Need.this sub) o).map Straight.toNoun :=
        ts_at_all h7 g2 (cuRest CA) o (Need.this sub) (by simp [flattenNeed, isRun])
      simp only [Option.map_some, Option.bind_some]
      unfold cuS4
      rw [cu_trap_end, tsSample_eq, h, cu_gen_cache]
      cases toStraightF g2.cond g2.blocks (Need.this sub) o <;> rfl

/-- **The gate of `+compile-unary` on `DirOk`** (plan item 0 of README Gaps
19): `finishLUCM env n`, the whole-subject code with the direct calls
through `+mono-try-call`, given `DirCalls` at the rest `cuRest CA`. -/
theorem cu_gate_dir (FUNC SCC CODE LSR JH CACHE NM CA V : Noun) (env : CallEnv) (n : Nomm) (hn : DirOk n = true)
    (hd : DirCalls env CODE (cuCtx FUNC SCC CODE LSR JH NM) (· = cuRest CA) Option.none n)
    (hcsi : nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuCsi = some (C NM CA))
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    nock (C cuGB (C (cuSam FUNC SCC CODE LSR JH CACHE) compK)) cuGB
      = (finishLUCM (S := CSet) (Map := TreapMap mugF) env n).map fun st => C (C st.toNoun NM) CA := by
  rw [cu_gate_rp, ← cu_trap_dir FUNC SCC CODE LSR JH CACHE NM CA V env n hn hd hcsi hgot hv]
  apply Option.ext
  intro y
  rw [cu_rp_iff]
  have hk : nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) rpK
      = nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuTrap := by
    unfold cuTC
    simp [rpK, nock_exec]
  rw [hk]

end Compiler
end Formalization
