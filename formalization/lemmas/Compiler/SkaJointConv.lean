import lemmas.Compiler.SkaJoint

/-!
# The levels against the model, in both directions

Each level `lv j` of `SkaJoint.lean` is below the model of
`Ska/Analysis.lean` at every fuel `m ≥ j` (`lv_below`), and the model at fuel
`m` is below the level `J` for every `J ≥ 2 m` (`lv_above`).  The factor `2`
comes from the trap `fol-loop`, whose level `J` reads the loop `resolve` at
level `J - 2` (through the trap `nock-2-direct-non-inlined` at `J - 1`), while
the model's `folLoop` at fuel `m + 1` reads `resolve` at fuel `m`.  For
example the model's `folLoop` at fuel `3` is below the trap's level `6`.

Both directions are monotonicity: of each step in the arms it calls
(`folStep_le`, `resolveStep_le`, `runStep_le`, `memberStep_le` of
`AnaFuel.lean`, and `analyzeStepH_le`, `passStepH_le` here for the Hoon's
steps with `+sweep` and `+cull` given), and of the model in its fuel.

With `lvIs`, `E_complete` and `E_le_nock` this gives the pill's arms exactly
the model's results at some fuel (`nock_iff_levels`): the gate `+analyze`
(`analyze_iff`), the trap `fol-loop` (`fol_loop_iff_full`), the loop
`resolve` (`resolve_iff_full`), the gate `+run` (`ska_run_iff`), the pass
loop (`pass_loop_iff`) and the member loop (`member_loop_iff`), with no
hypothesis on `+analyze` left.
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon SkaModel.Ana

variable {R : Type}

/-! ## The Hoon's steps are monotone in `+sweep` and `+cull` -/

theorem analyzeStepH_le (memoF : Memo FinMap) {cu cu' : Ident → SkaState FinMap R → Option (SkaState FinMap R)}
    {run run' : RunGo FinMap R} {pl pl' : PassGo FinMap R}
    (hcu : ∀ i st, OLe (cu i st) (cu' i st))
    (hrun : ∀ i index st, OLe (run i index st) (run' i index st))
    (hpl : ∀ id index pass st, OLe (pl id index pass st) (pl' id index pass st))
    (id : Ident) (st : SkaState FinMap R) :
    OLe (analyzeStepH cu memoF run pl id st) (analyzeStepH cu' memoF run' pl' id st) := by
  unfold analyzeStepH
  split
  · exact OLe.refl _
  · exact OLe.refl _
  · refine OLe.bind (hrun _ _ _) fun r => ?_
    split
    · exact OLe.refl _
    · split
      · exact OLe.bind (hcu _ _) fun _ => hpl _ _ _ _
      · refine OLe.bind (OLe.refl _) fun ab => ?_
        split
        · exact OLe.bind (hcu _ _) fun _ => hpl _ _ _ _
        · exact OLe.refl _

theorem passStepH_le {sw sw' : Ident → FinMap Ident Unit → SkaState FinMap R → Option (List Ident)}
    {cu cu' : Ident → SkaState FinMap R → Option (SkaState FinMap R)}
    {ml ml' : MemGo FinMap R} {pl pl' : PassGo FinMap R}
    (hsw : ∀ i was st, OLe (sw i was st) (sw' i was st))
    (hcu : ∀ i st, OLe (cu i st) (cu' i st))
    (hml : ∀ index pass ms st, OLe (ml index pass ms st) (ml' index pass ms st))
    (hpl : ∀ id index pass st, OLe (pl id index pass st) (pl' id index pass st))
    (id : Ident) (index pass : Nat) (st : SkaState FinMap R) :
    OLe (passStepH sw cu ml pl id index pass st) (passStepH sw' cu' ml' pl' id index pass st) := by
  unfold passStepH
  refine OLe.bind (OLe.refl _) fun ab => OLe.bind (hsw _ _ _) fun members => ?_
  refine OLe.bind (hml _ _ _ _) fun r => ?_
  split
  · exact OLe.refl _
  · refine OLe.bind (hcu _ _) fun st' => ?_
    split
    · exact OLe.refl _
    · exact hpl _ _ _ _

/-! ## `+sweep` and `+cull` at a level against the model's fuel -/

theorem sweep_fuel_le {n m : Nat} (h : n ≤ m) (i : Ident) (was : FinMap Ident Unit) (st : SkaState FinMap R) :
    OLe (Ana.sweep n i was st) (Ana.sweep m i was st) :=
  fuel_chain (f := fun k => Ana.sweep k i was st) (fun k => sweep_fuel k i was st) h

theorem cull_fuel_le {n m : Nat} (h : n ≤ m) (i : Ident) (st : SkaState FinMap R) :
    OLe (Ana.cull n i st) (Ana.cull m i st) :=
  fuel_chain (f := fun k => Ana.cull k i st) (fun k => cull_fuel k i st) h

theorem swAt_le {j m : Nat} (h : j ≤ m + 1) (i : Ident) (was : FinMap Ident Unit) (st : SkaState FinMap R) :
    OLe (swAt j i was st) (Ana.sweep m i was st) := by
  cases j with
  | zero => exact fun _ e => by cases e
  | succ j => exact sweep_fuel_le (by omega) i was st

theorem cuAt_le {j m : Nat} (h : j ≤ m + 1) (i : Ident) (st : SkaState FinMap R) :
    OLe (cuAt j i st) (Ana.cull m i st) := by
  cases j with
  | zero => exact fun _ e => by cases e
  | succ j => exact cull_fuel_le (by omega) i st

/-! ## The levels below the model -/

/-- Every arm of the level `p` is below the model at fuel `m`. -/
structure LvBelow (env : Env R) (memoF : Memo FinMap) (p : Lv R) (m : Nat) : Prop where
  fol : Ana.GoLe p.fol (Ana.folLoop env memoF m)
  rt : Ana.ResLe p.rt (Ana.resolveR env memoF m)
  res : ∀ orig, Ana.ResLe (p.res orig) (Ana.resolve env memoF m orig)
  ana : ∀ i st, OLe (p.ana i st) (Ana.analyze env memoF m i st)
  run : ∀ i index st, OLe (p.run i index st) (Ana.run env memoF m i index st)
  mem : ∀ index pass ms st, OLe (p.mem index pass ms st) (Ana.memberLoop env memoF m index pass ms st)
  pass : ∀ id index pass st, OLe (p.pass id index pass st) (Ana.passLoop env memoF m id index pass st)

/-- **The level `j` is below the model at every fuel `m ≥ j`.** -/
theorem lv_below (env : Env R) (memoF : Memo FinMap) : ∀ j m, j ≤ m → LvBelow env memoF (lv env memoF j) m
  | 0, _, _ => {
      fol := fun _ _ _ _ _ _ _ _ h => by cases h
      rt := fun _ _ _ h => by cases h
      res := fun _ _ _ _ h => by cases h
      ana := fun _ _ _ h => by cases h
      run := fun _ _ _ _ h => by cases h
      mem := fun _ _ _ _ _ h => by cases h
      pass := fun _ _ _ _ _ h => by cases h }
  | j + 1, 0, h => absurd h (by omega)
  | j + 1, m + 1, h =>
    have ih := lv_below env memoF j m (by omega)
    { fol := by
        intro fol sub seat mk bc df gen
        rw [Ana.folLoop_unfold env memoF m]
        exact folStep_le env ih.rt ih.fol fol sub seat mk bc df gen
      rt := fun i gen a hh => Ana.resolve_fuel_le env memoF (Nat.le_succ m) i i gen a (ih.res i i gen a hh)
      res := fun orig i gen => by
        rw [Ana.resolve_unfold env memoF m]
        exact resolveStep_le env (ih.res orig) ih.ana orig i gen
      ana := fun i st => by
        rw [Ana.analyze_unfold env memoF m, ← analyzeStepH_eq]
        exact analyzeStepH_le memoF (fun i st => cuAt_le (by omega) i st) ih.run ih.pass i st
      run := fun i index st => by
        rw [Ana.run_unfold env memoF m]
        exact runStep_le ih.fol i index st
      mem := fun index pass ms st => by
        rw [Ana.memberLoop_unfold env memoF m]
        exact memberStep_le ih.run ih.mem index pass ms st
      pass := fun id index pass st => by
        rw [Ana.passLoop_unfold env memoF m, ← passStepH_eq]
        exact passStepH_le (fun i was st => swAt_le (by omega) i was st) (fun i st => cuAt_le (by omega) i st)
          ih.mem ih.pass id index pass st }

/-! ## The model below the levels -/

/-- Every arm of the model at fuel `m` is below the level `p`. -/
structure LvAbove (env : Env R) (memoF : Memo FinMap) (m : Nat) (p : Lv R) : Prop where
  fol : Ana.GoLe (Ana.folLoop env memoF m) p.fol
  res : ∀ orig, Ana.ResLe (Ana.resolve env memoF m orig) (p.res orig)
  ana : ∀ i st, OLe (Ana.analyze env memoF m i st) (p.ana i st)
  run : ∀ i index st, OLe (Ana.run env memoF m i index st) (p.run i index st)
  mem : ∀ index pass ms st, OLe (Ana.memberLoop env memoF m index pass ms st) (p.mem index pass ms st)
  pass : ∀ id index pass st, OLe (Ana.passLoop env memoF m id index pass st) (p.pass id index pass st)

/-- **The model at fuel `m` is below every level `J ≥ 2 m`.** -/
theorem lv_above (env : Env R) (memoF : Memo FinMap) : ∀ m J, 2 * m ≤ J → LvAbove env memoF m (lv env memoF J)
  | 0, _, _ => {
      fol := fun _ _ _ _ _ _ _ _ h => by simp [Ana.folLoop] at h
      res := fun _ _ _ _ h => by simp [Ana.resolve] at h
      ana := fun _ _ _ h => by simp [Ana.analyze] at h
      run := fun _ _ _ _ h => by simp [Ana.run] at h
      mem := fun _ _ _ _ _ h => by simp [Ana.memberLoop] at h
      pass := fun _ _ _ _ _ h => by simp [Ana.passLoop] at h }
  | m + 1, 0, h => absurd h (by omega)
  | m + 1, 1, h => absurd h (by omega)
  | m + 1, J + 2, h =>
    have ih1 := lv_above env memoF m (J + 1) (by omega)
    have ih0 := lv_above env memoF m J (by omega)
    { fol := by
        intro fol sub seat mk bc df gen
        rw [Ana.folLoop_unfold env memoF m]
        exact folStep_le env (fun i gen => ih0.res i i gen) ih1.fol fol sub seat mk bc df gen
      res := fun orig i gen => by
        rw [Ana.resolve_unfold env memoF m]
        exact resolveStep_le env (ih1.res orig) ih1.ana orig i gen
      ana := fun i st => by
        rw [Ana.analyze_unfold env memoF m, ← analyzeStepH_eq]
        exact analyzeStepH_le memoF (fun i st => cull_fuel_le (by omega) i st) ih1.run ih1.pass i st
      run := fun i index st => by
        rw [Ana.run_unfold env memoF m]
        exact runStep_le ih1.fol i index st
      mem := fun index pass ms st => by
        rw [Ana.memberLoop_unfold env memoF m]
        exact memberStep_le ih1.run ih1.mem index pass ms st
      pass := fun id index pass st => by
        rw [Ana.passLoop_unfold env memoF m, ← passStepH_eq]
        exact passStepH_le (fun i was st => sweep_fuel_le (by omega) i was st)
          (fun i st => cull_fuel_le (by omega) i st) ih1.mem ih1.pass id index pass st }

/-! ## The pill's arms against the model -/

/-- A formula whose run under every `E j` is a model at level `j`, below the
model at fuel `j` and above it at fuel `m` from level `2 m`, returns exactly
what the model returns at some fuel. -/
theorem nock_iff_levels {α : Type} (s f : Noun) (enc : α → Noun) (lvf an : Nat → Option α)
    (his : ∀ j, E j s f = (lvf j).map enc) (hb : ∀ j, OLe (lvf j) (an j)) (ha : ∀ m, OLe (an m) (lvf (2 * m)))
    (x : Noun) : nock s f = some x ↔ ∃ r m, an m = some r ∧ x = enc r := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := E_complete h
    rw [his] at hj
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 hj
    exact ⟨r, j, hb j r hr, rfl⟩
  · rintro ⟨r, m, hm, rfl⟩
    have e := his (2 * m)
    rw [ha m r hm, Option.map_some] at e
    exact E_le_nock _ _ _ _ e

section
variable (regsNoun : R → Noun) (env : Env R) (memoF : Memo FinMap) (K : Noun)
  (hK : slot? 31 K = some ana) (hKb : slot? 2 K = some ska_cg.k_bat)
  (hmemo : slot? 122 K = some (memoNoun memoF))
  (hhe : env.he = heSock) (hth : env.threshold = 32) (hsoft : env.softSpot = softSpotF)
  (hreg : RegisterFastIs regsNoun env)
include hK hKb hmemo hhe hth hsoft hreg

/-- **`+analyze`**: the pill's gate returns exactly what `Ana.analyze`
returns at some fuel, in every context `K` of `+ska-callgraph` with `ana` at
axis `31`, the battery at `2` and `memo-final` at `122`. -/
theorem analyze_iff (id : Ident) (st : SkaState FinMap R) (y : Noun) :
    nock (anaSubj regsNoun K id st) ska_analyze.battery = some y ↔
      ∃ r m, Ana.analyze env memoF m id st = some r ∧ y = anaNoun regsNoun r :=
  nock_iff_levels _ _ (anaNoun regsNoun) (fun j => (lv env memoF j).ana id st)
    (fun m => Ana.analyze env memoF m id st)
    (fun j => (lvIs regsNoun env memoF K hK hKb hmemo hhe hth hsoft hreg j).ana id st)
    (fun j => (lv_below env memoF j j (Nat.le_refl j)).ana id st)
    (fun m => (lv_above env memoF m (2 * m) (Nat.le_refl _)).ana id st) y

/-- **`+run`**: the pill's gate returns exactly what `Ana.run` returns at
some fuel. -/
theorem ska_run_iff (id : Ident) (index : Nat) (st : SkaState FinMap R) (x : Noun) :
    nock (runSubj regsNoun K id index st) ska_run.battery = some x ↔
      ∃ r m, Ana.run env memoF m id index st = some r ∧ x = runNoun regsNoun r :=
  nock_iff_levels _ _ (runNoun regsNoun) (fun j => (lv env memoF j).run id index st)
    (fun m => Ana.run env memoF m id index st)
    (fun j => (lvIs regsNoun env memoF K hK hKb hmemo hhe hth hsoft hreg j).run id index st)
    (fun j => (lv_below env memoF j j (Nat.le_refl j)).run id index st)
    (fun m => (lv_above env memoF m (2 * m) (Nat.le_refl _)).run id index st) x

/-- **The pass loop** of `+analyze`: it returns exactly what `Ana.passLoop`
returns at some fuel. -/
theorem pass_loop_iff (lbc hit gb : Noun) (id : Ident) (index pass : Nat) (st : SkaState FinMap R) (x : Noun) :
    nock (passSubj regsNoun K lbc hit gb id index pass st) ska_analyze.loop1 = some x ↔
      ∃ r m, Ana.passLoop env memoF m id index pass st = some r ∧ x = anaNoun regsNoun r :=
  nock_iff_levels _ _ (anaNoun regsNoun) (fun j => (lv env memoF j).pass id index pass st)
    (fun m => Ana.passLoop env memoF m id index pass st)
    (fun j => (lvIs regsNoun env memoF K hK hKb hmemo hhe hth hsoft hreg j).pass lbc hit gb id index pass st)
    (fun j => (lv_below env memoF j j (Nat.le_refl j)).pass id index pass st)
    (fun m => (lv_above env memoF m (2 * m) (Nat.le_refl _)).pass id index pass st) x

/-- **The member loop** of `+analyze`: it returns exactly what
`Ana.memberLoop` returns at some fuel. -/
theorem member_loop_iff (nb pl lbc hit gb : Noun) (id : Ident) (index pass : Nat) (ms : List Ident)
    (st : SkaState FinMap R) (x : Noun) :
    nock (memSubj regsNoun K nb pl lbc hit gb id index pass ms st) ska_analyze.loop0 = some x ↔
      ∃ r m, Ana.memberLoop env memoF m index pass ms st = some r ∧ x = memNoun regsNoun r :=
  nock_iff_levels _ _ (memNoun regsNoun) (fun j => (lv env memoF j).mem index pass ms st)
    (fun m => Ana.memberLoop env memoF m index pass ms st)
    (fun j => (lvIs regsNoun env memoF K hK hKb hmemo hhe hth hsoft hreg j).mem nb pl lbc hit gb id index pass ms st)
    (fun j => (lv_below env memoF j j (Nat.le_refl j)).mem index pass ms st)
    (fun m => (lv_above env memoF m (2 * m) (Nat.le_refl _)).mem index pass ms st) x

variable (rest : Noun) (hana : slot? 511 rest = some ana) (hKr : slot? 31 rest = some K)
include hana hKr

/-- **`fol-loop`**: the trap returns exactly what `Ana.folLoop` returns at
some fuel, with no hypothesis on `+analyze`. -/
theorem fol_loop_iff_full (fol : Noun) (sub : Anno) (seat mk : Option Noun) (bc df : Bool)
    (gen : GenS FinMap R) (x : Noun) :
    nock (folSubj regsNoun rest fol sub seat mk bc df gen) fol_loop.battery = some x ↔
      ∃ r m, Ana.folLoop env memoF m fol sub seat mk bc df gen = some r ∧ x = folOutNoun regsNoun r :=
  nock_iff_levels _ _ (folOutNoun regsNoun) (fun j => (lv env memoF j).fol fol sub seat mk bc df gen)
    (fun m => Ana.folLoop env memoF m fol sub seat mk bc df gen)
    (fun j => (lvIs regsNoun env memoF K hK hKb hmemo hhe hth hsoft hreg j).fol rest hana hKr
      fol sub seat mk bc df gen)
    (fun j => (lv_below env memoF j j (Nat.le_refl j)).fol fol sub seat mk bc df gen)
    (fun m => (lv_above env memoF m (2 * m) (Nat.le_refl _)).fol fol sub seat mk bc df gen) x

/-- **The loop `resolve`** on every identity `idT`, for the call whose site
sock and formula are `orig = [sock.prod.s fol-new]`: it returns exactly what
`Ana.resolve` for that `orig` returns at some fuel. -/
theorem resolve_iff_full (fol : Noun) (sub : Anno) (seat mk : Option Noun) (bc df : Bool)
    (gen : GenS FinMap R) (fa fb : Noun) (f s : FolOut) (idT : Ident) (y : Noun) :
    nock (resSubj regsNoun rest fol sub seat mk bc df gen fa fb f s idT) fol_loop.resolve = some y ↔
      ∃ r m, Ana.resolve env memoF m (s.prod.sock, C fa fb) idT gen = some r ∧ y = resOutNoun regsNoun r :=
  nock_iff_levels _ _ (resOutNoun regsNoun) (fun j => (lv env memoF j).res (s.prod.sock, C fa fb) idT gen)
    (fun m => Ana.resolve env memoF m (s.prod.sock, C fa fb) idT gen)
    (fun j => (lvIs regsNoun env memoF K hK hKb hmemo hhe hth hsoft hreg j).res rest hana hKr
      fol sub seat mk bc df gen fa fb f s idT)
    (fun j => (lv_below env memoF j j (Nat.le_refl j)).res _ idT gen)
    (fun m => (lv_above env memoF m (2 * m) (Nat.le_refl _)).res _ idT gen) y

end

end Compiler
end Formalization
