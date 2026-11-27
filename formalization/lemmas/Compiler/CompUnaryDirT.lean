import lemmas.Compiler.CompRunTClass
import lemmas.Compiler.CompUnaryDir

/-!
# The gate of `+compile-unary` with the cache the run ends with (README Gaps 19 (g))

* **`cu_trap_dirT`**, **`cu_gate_dirT`**: on `DirOk` with `DirCallsT` (each direct
  call may miss in `nary.cache` and compile its callee), for every `Y` with
  `YOk`: some rest `x'` with `Y (cuRest CA) x'`, and the gate returns
  `finishLUCM env n` with the cache `x'.cache`.
* `ExtE E`: `Ext` that keeps a predicate `E` on rests (`yOk_extE`), and
  **`cu_gate_dirExt`**: `∃ CA'`, `Ext (cuRest CA) (cuRest CA')`, `E` at
  `cuRest CA'` (the invariant `E` that the per-call facts read, e.g. that the
  entries agree with `env`, holds at the FINAL cache), and the product's cache
  `CA'`.
* `cu_gate_dir_of_T`: the old `cu_gate_dir` is the case `Y = (· = ·)`.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-- **The trap of `+compile-unary` on `DirOk`, threaded**: the whole-subject
run starts at `cuRest CA` and ends at some `x'`, and the trap returns the
product with `x'.cache`. -/
theorem cu_trap_dirT (FUNC SCC CODE LSR JH CACHE NM CA V : Noun) (env : CallEnv) (n : Nomm) (hn : DirOk n = true)
    (E : GenRest → Prop) (Y : GenRest → GenRest → Prop) (hY : ∀ msup, YOk (XM E msup) Y) (hE0 : E (cuRest CA))
    (hd : DirCallsT env CODE (cuCtx FUNC SCC CODE LSR JH NM) E Y Option.none n)
    (hcsi : nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuCsi = some (C NM CA))
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    ∃ x', Y (cuRest CA) x' ∧ nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuTrap
      = (finishLUCM (S := CSet) (Map := TreapMap mugF) env n).map fun st => C (C st.toNoun NM) x'.cache := by
  have h7 : slot? 7 (cuCtx FUNC SCC CODE LSR JH NM) = some compK := rfl
  have hcode : slot? 52 (cuCtx FUNC SCC CODE LSR JH NM) = some CODE := by simp [cuCtx, nock_exec]
  obtain ⟨hc, hl, hm⟩ := comp_ctx_pill _ h7
  obtain ⟨x', hy, hrun⟩ := comp_run_dirXT h7 hcode env E Y hY n hn Option.none [] hd (CGoal.toL CGoal.done) genEntry
    (show genEntry.drop = false from rfl) (cuRest CA) (A 0) (unitNoun Nomm.toNoun Option.none) (cu_entry_nosoft CA)
    ⟨hE0, rfl, rfl⟩
  have hx' : x'.NoSoft := (hY Option.none).soft (cu_entry_nosoft CA) hy
  refine ⟨x', hy, ?_⟩
  simp only [unitNoun] at hrun
  have hres := res_dirT h7 hcode env E Y hY n hn Option.none [] hd
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
    have hk := comp_kerf_all hc hl hm x' g1 nex (walk_mdP hx' g1.bo hlok)
    simp only [compCore] at hk
    simp only [Option.bind_some, Option.map_some, NextL.goal, CGoalL.toNoun]
    rw [cu_trap_kerf, hk]
    cases e2 : kerf nex g1 with
    | none => simp
    | some q =>
      obtain ⟨⟨o, sub⟩, g2⟩ := q
      have h : nock (C tsBat (C (tsSampleN (A o) (C (A 0x73696874) (A sub)))
            (C comp.door (C (genNoun g2 x') (cuCtx FUNC SCC CODE LSR JH NM))))) tsBat
          = (toStraightF g2.cond g2.blocks (Need.this sub) o).map Straight.toNoun :=
        ts_at_all h7 g2 x' o (Need.this sub) (by simp [flattenNeed, isRun])
      simp only [Option.map_some, Option.bind_some]
      unfold cuS4
      rw [cu_trap_end, tsSample_eq, h, cu_gen_cache]
      cases toStraightF g2.cond g2.blocks (Need.this sub) o <;> rfl

/-- **The gate of `+compile-unary` on `DirOk`, threaded** (README Gaps 19
(g)): some rest `x'` with `Y (cuRest CA) x'`, and the gate is `finishLUCM env
n` with the cache `x'.cache` the whole-subject run ends with. -/
theorem cu_gate_dirT (FUNC SCC CODE LSR JH CACHE NM CA V : Noun) (env : CallEnv) (n : Nomm) (hn : DirOk n = true)
    (E : GenRest → Prop) (Y : GenRest → GenRest → Prop) (hY : ∀ msup, YOk (XM E msup) Y) (hE0 : E (cuRest CA))
    (hd : DirCallsT env CODE (cuCtx FUNC SCC CODE LSR JH NM) E Y Option.none n)
    (hcsi : nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuCsi = some (C NM CA))
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    ∃ x', Y (cuRest CA) x' ∧ nock (C cuGB (C (cuSam FUNC SCC CODE LSR JH CACHE) compK)) cuGB
      = (finishLUCM (S := CSet) (Map := TreapMap mugF) env n).map fun st => C (C st.toNoun NM) x'.cache := by
  obtain ⟨x', hy, ht⟩ := cu_trap_dirT FUNC SCC CODE LSR JH CACHE NM CA V env n hn E Y hY hE0 hd hcsi hgot hv
  refine ⟨x', hy, ?_⟩
  rw [cu_gate_rp, ← ht]
  apply Option.ext
  intro y
  rw [cu_rp_iff]
  have hk : nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) rpK
      = nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuTrap := by
    unfold cuTC
    simp [rpK, nock_exec]
  rw [hk]

/-- `Ext` keeping a predicate `E` on rests (what the per-call facts read). -/
def ExtE (E : GenRest → Prop) (x y : GenRest) : Prop := Ext x y ∧ (E x → E y)

theorem yOk_extE (E : GenRest → Prop) (msup : Option Nomm) : YOk (XM E msup) (ExtE E) :=
  yOk_xm msup (fun x => ⟨ext_refl x, id⟩) (fun h1 h2 => ⟨ext_trans h1.1 h2.1, fun h => h2.2 (h1.2 h)⟩)
    (fun hx h => ext_noSoft hx h.1) (fun hE h => h.2 hE)

/-- A rest `Ext` of `cuRest CA` is `cuRest` of its cache. -/
theorem ext_cuRest {CA : Noun} {x : GenRest} (h : Ext (cuRest CA) x) : x = cuRest x.cache := by
  obtain ⟨c, s, f⟩ := x
  obtain ⟨hs, hf, -⟩ := h
  simp only [cuRest] at hs hf
  subst hs hf
  rfl

/-- **The gate of `+compile-unary` on `DirOk` with the final cache**: for an
invariant `E` on rests that holds at `cuRest CA` and that every miss keeps
(inside `DirCallsT` at `ExtE E`), the gate returns `finishLUCM env n` with a
cache `CA'` that only extends `CA` in `nary.cache` and `sure.cache`, and `E`
holds at `cuRest CA'`. -/
theorem cu_gate_dirExt (FUNC SCC CODE LSR JH CACHE NM CA V : Noun) (env : CallEnv) (n : Nomm) (hn : DirOk n = true)
    (E : GenRest → Prop) (hE0 : E (cuRest CA))
    (hd : DirCallsT env CODE (cuCtx FUNC SCC CODE LSR JH NM) E (ExtE E) Option.none n)
    (hcsi : nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuCsi = some (C NM CA))
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    ∃ CA', Ext (cuRest CA) (cuRest CA') ∧ E (cuRest CA') ∧
      nock (C cuGB (C (cuSam FUNC SCC CODE LSR JH CACHE) compK)) cuGB
        = (finishLUCM (S := CSet) (Map := TreapMap mugF) env n).map fun st => C (C st.toNoun NM) CA' := by
  obtain ⟨x', ⟨he, hEE⟩, h⟩ :=
    cu_gate_dirT FUNC SCC CODE LSR JH CACHE NM CA V env n hn E (ExtE E) (yOk_extE E) hE0 hd hcsi hgot hv
  have hx := ext_cuRest he
  refine ⟨x'.cache, hx ▸ he, hx ▸ hEE hE0, h⟩

/-- **The old gate is the case with no miss**: `cu_gate_dir` from
`cu_gate_dirT` at `Y = (· = ·)` (`dirCallsT_of`). -/
theorem cu_gate_dir_of_T (FUNC SCC CODE LSR JH CACHE NM CA V : Noun) (env : CallEnv) (n : Nomm) (hn : DirOk n = true)
    (hd : DirCalls env CODE (cuCtx FUNC SCC CODE LSR JH NM) (· = cuRest CA) Option.none n)
    (hcsi : nock (cuTC (cuSam FUNC SCC CODE LSR JH CACHE)) cuCsi = some (C NM CA))
    (hgot : getF mugF FUNC CODE = some (C (A 0) V)) (hv : slot? 2 V = some n.toNoun) :
    nock (C cuGB (C (cuSam FUNC SCC CODE LSR JH CACHE) compK)) cuGB
      = (finishLUCM (S := CSet) (Map := TreapMap mugF) env n).map fun st => C (C st.toNoun NM) CA := by
  obtain ⟨x', hy, h⟩ := cu_gate_dirT FUNC SCC CODE LSR JH CACHE NM CA V env n hn (· = cuRest CA) (· = ·)
    (fun _ => yOk_eq _) rfl (dirCallsT_of (fun _ => rfl) Option.none n hd) hcsi hgot hv
  subst hy
  exact h

end Compiler
end Formalization
