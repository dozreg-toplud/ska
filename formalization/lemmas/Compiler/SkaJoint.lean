import lemmas.Compiler.SkaAnalyze

/-!
# The joint induction on the depth of calls

`E j` runs every formula that `FFar` excludes (the batteries and loops of the
core of `+ska-callgraph` whose calls the induction follows) with
`nockW (E (j - 1))`, none at `j = 0`, and every other formula with `nock`.
So `E j` is `nock` on every formula with `FFar` (`E_far`), every run of
`nock` is a run of some `E j` (`E_complete`), and `E j` is below `nock`
(`E_le_nock`).  Every step theorem over an evaluator applies with
`c := E (j - 1)`.

This file also gives the bunt of `identity` that `+cull` computes, over every
evaluator that is `nock` off `FFar` (`bunt_W`): arm `186` of the tail of `ana`
is the mold `identMoldArm`, which makes the core `[identMoldBat [identBunt anaTail]]`,
and both the arm and the battery `identMoldBat` are `FFar`.  `identMoldBat` has no name
in the generated nouns; `mold_arm_at` ties it to the pill.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon SkaModel.Ana

variable {R : Type}

set_option linter.unusedSimpArgs false

/-! ## The bunt of `identity` over an evaluator -/

/-- The battery of the mold core made by arm `186` of the tail of `ana`. -/
def identMoldBat : Noun :=
  (C (A 8) (C (C (C (A 8) (C (C (A 7) (C (C (A 0) (A 7)) (C (A 9) (C (A 11) (C (A 0) (A 7)))))) (C (A 9) (C (A 2)
    (C (A 10) (C (C (A 6) (C (A 0) (A 28))) (C (A 0) (A 2)))))))) (C (C (A 0) (A 26)) (C (A 0) (A 27)))) (C (A 8)
    (C (C (A 5) (C (C (A 0) (A 14)) (C (A 0) (A 2)))) (C (A 0) (A 6))))))

/-- Arm `186` of the tail of `ana`, the mold `identity`:
`[8 [1 identBunt] [[1 identMoldBat] [0 1]]]`. -/
def identMoldArm : Noun := C (A 8) (C (C (A 1) identBunt) (C (C (A 1) identMoldBat) (C (A 0) (A 1))))

theorem mold_arm_at : slot? 186 anaTail = some identMoldArm := by kernel_rfl

theorem identMoldArm_far : FFar identMoldArm := by ffar_disch

theorem identMoldBat_far : FFar identMoldBat := by ffar_disch

/-- The mold kicked with its default sample returns the bunt. -/
theorem mold_bat_bunt : nock (C identMoldBat (C identBunt anaTail)) identMoldBat = some identBunt :=
  nock_of_evalFuel (fuel := 300) (by kernel_rfl)

theorem mold_arm_run : nock anaTail identMoldArm = some (C identMoldBat (C identBunt anaTail)) := by
  unfold identMoldArm
  simp [nock_exec]

/-- **The bunt of `identity`** in `+cull`, over an evaluator `c` that is
`nock` off `FFar`: the `hbunt` of `cull_runW`. -/
theorem bunt_W (c : Noun → Noun → Option Noun) (hcf : ∀ s f, FFar f → c s f = nock s f) (X : Noun)
    (h : slot? 2047 X = some anaTail) : nockW c X buntF = some identBunt := by
  unfold buntF
  rw [nockW_op7, nockW_op9, nockW_op0, h]
  simp only [Option.bind_some, mold_arm_at, hcf _ _ identMoldArm_far, mold_arm_run]
  rw [nockW_op9, nockW_op0]
  simp only [slot?_one, Option.bind_some]
  rw [show slot? 2 (C identMoldBat (C identBunt anaTail)) = some identMoldBat from rfl]
  simp only [Option.bind_some, hcf _ _ identMoldBat_far, mold_bat_bunt]

/-! ## The call function -/

/-- The formulas `FFar` excludes, nested at most `j` deep, every other
formula by `nock`. -/
def E : Nat → Noun → Noun → Option Noun
  | 0 => fun s f => if FFar f then nock s f else none
  | j + 1 => fun s f => if FFar f then nock s f else nockW (E j) s f

theorem E_far (j : Nat) {s f : Noun} (h : FFar f) : E j s f = nock s f := by
  cases j <;> simp only [E, if_pos h]

theorem E_zero {s f : Noun} (h : ¬ FFar f) : E 0 s f = none := by simp only [E, if_neg h]

theorem E_succ (j : Nat) {s f : Noun} (h : ¬ FFar f) : E (j + 1) s f = nockW (E j) s f := by
  simp only [E, if_neg h]

theorem E_le_nock : ∀ (j : Nat) (s f : Noun), Below? (E j s f) (nock s f)
  | 0, s, f => by
    by_cases h : FFar f
    · rw [E_far 0 h]; exact Below?.refl _
    · rw [E_zero h]; exact fun _ e => by cases e
  | j + 1, s, f => by
    by_cases h : FFar f
    · rw [E_far _ h]; exact Below?.refl _
    · rw [E_succ j h, nock_eq_nockW]; exact nockW_mono (E_le_nock j) s f

theorem iterN_le_E : ∀ (j : Nat) (s f : Noun), Below? (iterN j s f) (E j s f)
  | 0, _, _ => fun _ h => by simp [iterN] at h
  | j + 1, s, f => by
    by_cases h : FFar f
    · rw [E_far _ h]; exact iterN_sound _ s f
    · rw [E_succ j h, iterN_succ]; exact nockW_mono (iterN_le_E j) s f

/-- Every run of `nock` is a run of some `E j`. -/
theorem E_complete {s f x : Noun} (h : nock s f = some x) : ∃ j, E j s f = some x :=
  let ⟨j, hj⟩ := iterN_complete h
  ⟨j, iterN_le_E j s f x hj⟩

theorem E_hcf (j : Nat) : ∀ s f, FFar f → E j s f = nock s f := fun _ _ h => E_far j h

/-! ## The formulas the induction follows are not `FFar` -/

theorem nf_fol : ¬ FFar fol_loop.battery := fun h => h.1 rfl
theorem nf_res : ¬ FFar fol_loop.resolve := fun h => h.2.1 rfl
theorem nf_dir : ¬ FFar fol_loop.direct := fun h => h.2.2.1 rfl
theorem nf_ana : ¬ FFar ska_analyze.battery := fun h => h.2.2.2.1 rfl
theorem nf_run : ¬ FFar ska_run.battery := fun h => h.2.2.2.2.1 rfl
theorem nf_loop0 : ¬ FFar ska_analyze.loop0 := fun h => h.2.2.2.2.2.1 rfl
theorem nf_loop1 : ¬ FFar ska_analyze.loop1 := fun h => h.2.2.2.2.2.2.1 rfl
theorem nf_swl : ¬ FFar ska_cg.sweep.loop := fun h => h.2.2.2.2.2.2.2.1 rfl
theorem nf_live : ¬ FFar ska_cg.cull.loop := fun h => h.2.2.2.2.2.2.2.2.1 rfl
theorem nf_swb : ¬ FFar ska_cg.sweep.battery := fun h => h.2.2.2.2.2.2.2.2.2.1 rfl
theorem nf_cub : ¬ FFar ska_cg.cull.battery := fun h => h.2.2.2.2.2.2.2.2.2.2 rfl

/-! ## `+cull` over `E (j + 1)` -/

theorem slot_K92 {K : Noun} (h : slot? 2 K = some ska_cg.k_bat) : slot? 92 K = some ska_analyze.arm := by
  cases K with
  | atom n => simp [nock_exec] at h
  | cell b t =>
    have hb : b = ska_cg.k_bat := by simpa [nock_exec] using h
    subst hb
    exact runRest_Ka kc_analyze_at t

/-- The battery of `+cull` over an evaluator crashes when `id` is not on the
stack. -/
theorem cull_run_noneW (c : Noun → Noun → Option Noun) (hcf : ∀ s f, FFar f → c s f = nock s f)
    (regsNoun : R → Noun) (K : Noun) (hK : slot? 31 K = some ana)
    (hKb : slot? 2 K = some ska_cg.k_bat) (id : Ident) (st : SkaState FinMap R)
    (hab : Ana.above id st.stk = none) :
    nockW c (cullS0 regsNoun K id st) ska_cg.cull.battery = none := by
  have hl2 := K_layer2 hK
  have hK22 := slot_K22 hKb
  have habv := above_gate K id st.stk
  rw [hab] at habv
  obtain ⟨g, done, order, stk, next, moved, tick, ticks, regs, stats⟩ := st
  simp only [Option.map_none] at habv
  unfold cullS0
  nockW_open ska_cg.cull.battery
  simp (disch := ffar_disch) [nock_exec, hcf, SkaState.toNoun, hK22, habv, hl2, silt_arm_at]

/-- The gate `+cull` under `E (j + 1)` is `Ana.cull j`, given the loop `live`
under `E j`. -/
theorem cull_E (j : Nat) (regsNoun : R → Noun) (K : Noun) (hK : slot? 31 K = some ana)
    (hKb : slot? 2 K = some ska_cg.k_bat) (id : Ident) (st : SkaState FinMap R)
    (hl : ∀ members q live, E j (liveSubj regsNoun K id st members q live) ska_cg.cull.loop
      = (liveLoop st members j q live).map Treap.setNoun) :
    E (j + 1) (cullS0 regsNoun K id st) ska_cg.cull.battery = (Ana.cull j id st).map (SkaState.toNoun regsNoun) := by
  rw [E_succ j nf_cub, cull_eq]
  cases hab : Ana.above id st.stk with
  | none => exact cull_run_noneW (E j) (E_hcf j) regsNoun K hK hKb id st hab
  | some ab =>
    simp only [Option.bind_some]
    exact cull_runW (E j) (E_hcf j) regsNoun K hK hKb id st ab hab _ (bunt_W (E j) (E_hcf j)) (hl _ _ _)

/-! ## The models at each level -/

/-- The arms the induction follows, as models: the trap `fol-loop`, the
trap `nock-2-direct-non-inlined` (`rt`, the loop `resolve` begun at the call's
identity), the loop `resolve` for each `orig`, the gate `+analyze`, the gate
`+run`, the member loop and the pass loop. -/
structure Lv (R : Type) where
  fol : FolGoS FinMap R
  rt : ResGo FinMap R
  res : Ident → ResGo FinMap R
  ana : AnaGo FinMap R
  run : RunGo FinMap R
  mem : MemGo FinMap R
  pass : PassGo FinMap R

/-- The gate `+sweep` at level `j`: its loop runs at level `j - 1`. -/
noncomputable def swAt : Nat → Ident → FinMap Ident Unit → SkaState FinMap R → Option (List Ident)
  | 0 => fun _ _ _ => none
  | j + 1 => fun i was st => Ana.sweep j i was st

/-- The gate `+cull` at level `j`: its loop runs at level `j - 1`. -/
noncomputable def cuAt : Nat → Ident → SkaState FinMap R → Option (SkaState FinMap R)
  | 0 => fun _ _ => none
  | j + 1 => Ana.cull j

/-- What the arms compute under `E j`: each level is the model's step with
the level below for the calls. -/
noncomputable def lv (env : Env R) (memoF : Memo FinMap) : Nat → Lv R
  | 0 => ⟨fun _ _ _ _ _ _ _ => none, fun _ _ => none, fun _ _ _ => none, fun _ _ => none,
      fun _ _ _ => none, fun _ _ _ _ => none, fun _ _ _ _ => none⟩
  | j + 1 =>
    let p := lv env memoF j
    { fol := Ana.folStep env p.rt p.fol
      rt := fun i => p.res i i
      res := fun orig => resolveStepH env (p.res orig) p.ana orig
      ana := analyzeStepH (cuAt j) memoF p.run p.pass
      run := Ana.runStep p.fol
      mem := memberStep p.run p.mem
      pass := passStepH (swAt j) (cuAt j) p.mem p.pass }

/-- Under `E j`, every arm the induction follows computes its model at
level `j`, exactly. -/
structure LvIs (regsNoun : R → Noun) (env : Env R) (memoF : Memo FinMap) (K : Noun) (j : Nat) : Prop where
  fol : ∀ rest, slot? 511 rest = some ana → slot? 31 rest = some K →
    GoIsW (E j) regsNoun rest (lv env memoF j).fol
  dir : ∀ rest, slot? 511 rest = some ana → slot? 31 rest = some K →
    DirIsW (E j) regsNoun rest (lv env memoF j).rt
  res : ∀ rest, slot? 511 rest = some ana → slot? 31 rest = some K →
    ∀ fol sub seat mk bc df gen fa fb f s idT,
    E j (resSubj regsNoun rest fol sub seat mk bc df gen fa fb f s idT) fol_loop.resolve
      = ((lv env memoF j).res (s.prod.sock, C fa fb) idT gen).map (resOutNoun regsNoun)
  ana : AnaIsW (E j) regsNoun K (lv env memoF j).ana
  run : RunIsW (E j) regsNoun K (lv env memoF j).run
  mem : ∀ nb pl lbc hit gb id index pass ms st,
    E j (memSubj regsNoun K nb pl lbc hit gb id index pass ms st) ska_analyze.loop0
      = ((lv env memoF j).mem index pass ms st).map (memNoun regsNoun)
  pass : ∀ lbc hit gb id index pass st,
    E j (passSubj regsNoun K lbc hit gb id index pass st) ska_analyze.loop1
      = ((lv env memoF j).pass id index pass st).map (anaNoun regsNoun)
  sw : ∀ id was st, E j (sweepS0 regsNoun K id was st) ska_cg.sweep.battery
      = (swAt j id was st).map (listNoun identNoun)
  cu : ∀ id st, E j (cullS0 regsNoun K id st) ska_cg.cull.battery
      = (cuAt j id st).map (SkaState.toNoun regsNoun)
  swl : ∀ id was st seen stack out, E j (sweepSubj regsNoun K id was st seen stack out) ska_cg.sweep.loop
      = (sweepLoop st was j seen stack out).map (listNoun identNoun)
  live : ∀ id st members q live, E j (liveSubj regsNoun K id st members q live) ska_cg.cull.loop
      = (liveLoop st members j q live).map Treap.setNoun

section
variable (regsNoun : R → Noun) (env : Env R) (memoF : Memo FinMap) (K : Noun)
  (hK : slot? 31 K = some ana) (hKb : slot? 2 K = some ska_cg.k_bat)
  (hmemo : slot? 122 K = some (memoNoun memoF))
  (hhe : env.he = heSock) (hth : env.threshold = 32) (hsoft : env.softSpot = softSpotF)
  (hreg : RegisterFastIs regsNoun env)
include hK hKb hmemo hhe hth hsoft hreg

/-- **The joint induction**: under `E j` every arm the induction follows
computes its model at level `j`. -/
theorem lvIs : ∀ j, LvIs regsNoun env memoF K j
  | 0 => {
      fol := fun _ _ _ _ _ _ _ _ _ _ => by rw [E_zero nf_fol]; rfl
      dir := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by rw [E_zero nf_dir]; rfl
      res := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by rw [E_zero nf_res]; rfl
      ana := fun _ _ => by rw [E_zero nf_ana]; rfl
      run := fun _ _ _ => by rw [E_zero nf_run]; rfl
      mem := fun _ _ _ _ _ _ _ _ _ _ => by rw [E_zero nf_loop0]; rfl
      pass := fun _ _ _ _ _ _ _ => by rw [E_zero nf_loop1]; rfl
      sw := fun _ _ _ => by rw [E_zero nf_swb]; rfl
      cu := fun _ _ => by rw [E_zero nf_cub]; rfl
      swl := fun _ _ _ _ _ _ => by rw [E_zero nf_swl]; simp [sweepLoop]
      live := fun _ _ _ _ _ => by rw [E_zero nf_live]; simp [liveLoop] }
  | j + 1 =>
    have ih := lvIs j
    have hKa := slot_K92 hKb
    { fol := fun rest hana hKr fol sub seat mk bc df gen => by
        rw [E_succ j nf_fol]
        exact fol_loop_step_allW' (E j) (E_hcf j) regsNoun env hsoft _ _ rest (ih.fol rest hana hKr) hana hreg
          (ih.dir rest hana hKr) fol sub seat mk bc df gen
      dir := fun rest hana hKr =>
        dirIsW_of (E (j + 1)) (E j) (fun _ => E_succ j nf_dir) (E_hcf j) regsNoun _ rest hana
          (fun s f fa fb fol sub seat mk bc df gen => ih.res rest hana hKr fol sub seat mk bc df gen fa fb f s _)
          calleePutIs
      res := fun rest hana hKr fol sub seat mk bc df gen fa fb f s idT => by
        rw [E_succ j nf_res]
        exact resolve_stepW (E j) (E_hcf j) regsNoun env hhe hth rest K hana hKr hKa _ ih.ana fol sub seat mk bc df
          gen fa fb f s _ idT (fun i _ _ _ => ih.res rest hana hKr fol sub seat mk bc df gen fa fb f s i)
      ana := fun id st => by
        rw [E_succ j nf_ana]
        exact analyze_stepW (E j) (E_hcf j) regsNoun K hK hKb id memoF hmemo _ ih.run _ (fun st => ih.cu id st) _
          (fun lbc index st => ih.pass lbc (A 0) ska_analyze.battery id index 1 st) st
      run := fun m o st => by
        rw [E_succ j nf_run]
        exact run_stepW (E j) (E_hcf j) regsNoun K hK m o st _
          (ih.fol _ (runTrapRest_ana regsNoun K hK m o st).1 (runTrapRest_ana regsNoun K hK m o st).2)
      mem := fun nb pl lbc hit gb id index pass ms st => by
        rw [E_succ j nf_loop0]
        exact member_stepW (E j) (E_hcf j) regsNoun K hK hKb nb pl lbc hit gb id index pass _ ih.run _
          (fun ms st => ih.mem nb pl lbc hit gb id index pass ms st) ms st
      pass := fun lbc hit gb id index pass st => by
        rw [E_succ j nf_loop1]
        exact pass_stepW (E j) (E_hcf j) regsNoun K hK hKb lbc hit gb id index pass _ (fun was st => ih.sw id was st)
          _ (fun st => ih.cu id st) _ (fun nb ms st => ih.mem (A nb) ska_analyze.loop1 lbc hit gb id index pass ms st)
          _ (fun st => ih.pass lbc hit gb id index (pass + 1) st) st
      sw := fun id was st => by
        rw [E_succ j nf_swb, sweep_batteryW (E j) (E_hcf j) regsNoun K hK id was st, ih.swl]
        rfl
      cu := fun id st => cull_E j regsNoun K hK hKb id st (ih.live id st)
      swl := fun id was st seen stack out => by
        rw [E_succ j nf_swl, sweep_stepW (E j) (E_hcf j) regsNoun K hK id was st _ (ih.swl id was st) seen stack out,
          sweepLoop_succ]
      live := fun id st members q live => by
        rw [E_succ j nf_live, live_stepW (E j) (E_hcf j) regsNoun K hK id st members _ (ih.live id st members) q live,
          liveLoop_succ] }

end

end Compiler
end Formalization
