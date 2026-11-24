import lemmas.Compiler.ResolveLoop
import lemmas.Ska.AnaFuel

/-!
# What the pill's `fol-loop` and `resolve` return, the model returns

The converse of `fol_loop_le` and `resolve_le`, by induction on the depth of
the calls, with `+analyze` a parameter.

The induction runs on `ev j`, a call function that runs the trap's battery,
the trap `nock-2-direct-non-inlined` and the loop `resolve` (`FolRt`) with
`ev (j - 1)` (none at `j = 0`), the gate `+analyze` with `iterN j`, and every
other formula with `nock`.  So `ev j` is `nock` off the four formulas
(`ev_far`), and the case theorems over an evaluator (`fol_loop_step_allW'`,
`dirIsW_of`, `resolve_stepW`) describe it exactly, level by level: the trap
under `ev j` computes `folE j`, the loop computes `resE j` (`folE_is`,
`resE_is`), with `+analyze` the decoded run of `iterN j` (`anaE`).  For
example `folE (j + 1)` is `Ana.folStep` with `folE j` for the calls of the
trap to itself and `resE (j - 1)` for `resolve`.  Every run of `nock` is a run
of some `ev j` (`ev_complete`, from `iterN_complete` and `iterN_le_ev`).

The exact models are below the model of `Ska/Analysis.lean` at a fuel that
depends on `j` only (`folE_le`, `resE_le`), by `folStep_mono`,
`resolveStepH_mono`, the fuel monotonicity of `AnaFuel.lean`, and the
hypothesis on `+analyze` (`AnaGe`: what `iterN j` of the gate returns decodes,
and `Ana.analyze` returns it at a fuel that depends on `j` only).

The model's `Ana.resolveStep` departs from the Hoon in the `%rec` branch
(`resolveStepH`, `Compiler/ResolveLoop.lean`); the results are stated against
`Ana.resolve` under the bridge `hStep : resolveStepH = Ana.resolveStep`, which
is `rfl` once the model patches with `orig.1`.

With the converse, `FolDecodes` and `ResIs` of the limit of the model
(`resInf`) hold, so `fol_loop_le` needs no hypothesis on the pill's runs
(`fol_loop_le'`), and the trap returns exactly what the model returns at some
fuel (`fol_loop_iff`).
-/

namespace Formalization
namespace Compiler

open Nock Pill SkaModel Hoon SkaModel.Ana

variable {R : Type}

/-! ## The call function -/

/-- The formulas run one level down: the trap's battery, the trap
`nock-2-direct-non-inlined` and the loop `resolve`. -/
def FolRt (f : Noun) : Prop := f = fol_loop.battery ∨ f = fol_loop.direct ∨ f = fol_loop.resolve

instance : DecidablePred FolRt := fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The three of `FolRt` nested at most `j` deep, `+analyze` by `iterN j`,
every other formula by `nock`. -/
def ev : Nat → Noun → Noun → Option Noun
  | 0 => fun s f => if FolRt f then none else if f = ska_analyze.battery then iterN 0 s f else nock s f
  | j + 1 => fun s f =>
    if FolRt f then nockW (ev j) s f else if f = ska_analyze.battery then iterN (j + 1) s f else nock s f

theorem FFar.out {f : Noun} (h : FFar f) : ¬ FolRt f ∧ ¬ f = ska_analyze.battery := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, fun e => h4 (e ▸ rfl)⟩
  rintro (e | e | e) <;> subst e <;> simp_all

theorem ev_far (j : Nat) {s f : Noun} (h : FFar f) : ev j s f = nock s f := by
  cases j <;> simp only [ev, if_neg h.out.1, if_neg h.out.2]

theorem ev_zero_rt {s f : Noun} (h : FolRt f) : ev 0 s f = none := by simp only [ev, if_pos h]

theorem ev_succ_rt (j : Nat) {s f : Noun} (h : FolRt f) : ev (j + 1) s f = nockW (ev j) s f := by
  simp only [ev, if_pos h]

theorem ana_not_rt : ¬ FolRt ska_analyze.battery := by
  rintro (e | e | e) <;> exact absurd (congrArg (ftrunc 8) e) (by decide)

theorem ev_ana (j : Nat) (s : Noun) : ev j s ska_analyze.battery = iterN j s ska_analyze.battery := by
  cases j <;> simp only [ev, if_neg ana_not_rt, if_true]

theorem iterN_le_ev : ∀ (j : Nat) (s f : Noun), Below? (iterN j s f) (ev j s f)
  | 0, _, _ => fun _ h => by simp [iterN] at h
  | j + 1, s, f => by
    by_cases h1 : FolRt f
    · rw [ev_succ_rt j h1, iterN_succ]; exact nockW_mono (iterN_le_ev j) s f
    · by_cases h2 : f = ska_analyze.battery
      · subst h2; rw [ev_ana]; exact Below?.refl _
      · simp only [ev, if_neg h1, if_neg h2]; exact iterN_sound _ s f

/-- Every run of `nock` is a run of some `ev j`. -/
theorem ev_complete {s f x : Noun} (h : nock s f = some x) : ∃ j, ev j s f = some x :=
  let ⟨j, hj⟩ := iterN_complete h
  ⟨j, iterN_le_ev j s f x hj⟩

/-! ## Monotonicity of the Hoon's turn of `resolve` -/

theorem Below?.map {α β : Type} {x y : Option α} (f : α → β) (h : Below? x y) :
    Below? (x.map f) (y.map f) := by
  intro b hb
  cases x with
  | none => simp at hb
  | some a => rw [h a rfl]; exact hb

variable {M : Type → Type → Type} [Treap M] in
/-- `resolveStepH` is monotone in its loop and in `+analyze`. -/
theorem resolveStepH_mono (env : Env R) {rl rl' : ResGo M R} {an an' : AnaGo M R}
    (hrl : ResBelow rl rl') (han : ∀ i st, Below? (an i st) (an' i st)) (orig idT : Ident)
    (gen : GenS M R) :
    Below? (resolveStepH env rl an orig idT gen) (resolveStepH env rl' an' orig idT gen) := by
  unfold resolveStepH
  repeat (first
    | exact Below?.refl _
    | exact hrl _ _
    | exact Below?.map _ (han _ _)
    | split)

/-! ## The hypotheses -/

/-- The subject of the gate `+analyze` in the context `K`. -/
noncomputable def anaSubj (regsNoun : R → Noun) (K : Noun) (id : Ident) (st : SkaState FinMap R) : Noun :=
  C ska_analyze.battery (C (C (identNoun id) (st.toNoun regsNoun)) K)

/-- The noun of a result of `+analyze`: `[low st]`. -/
noncomputable def anaNoun (regsNoun : R → Noun) (r : Nat × SkaState FinMap R) : Noun :=
  C (A r.1) (r.2.toNoun regsNoun)

/-- What the gate `+analyze` returns at depth `j`, `Ana.analyze` returns at a
fuel that depends on `j` only. -/
def AnaGe (regsNoun : R → Noun) (env : Env R) (memoF : Memo FinMap) (K : Noun) : Prop :=
  ∀ j, ∃ m, ∀ id st y, iterN j (anaSubj regsNoun K id st) ska_analyze.battery = some y →
    ∃ r, y = anaNoun regsNoun r ∧ Ana.analyze env memoF m id st = some r

/-- The bridge from the Hoon's turn of `resolve` to the model's: `rfl` once
`Ana.resolveStep` patches the `%rec` product with `orig.1`. -/
def StepBridge (env : Env R) : Prop :=
  ∀ (rl : ResGo FinMap R) (an : AnaGo FinMap R) (orig idT : Ident) (gen : GenS FinMap R),
    resolveStepH env rl an orig idT gen = Ana.resolveStep env rl an orig idT gen

section
variable (regsNoun : R → Noun) (env : Env R) (memoF : Memo FinMap) (rest K : Noun)
  (hA : AnaGe regsNoun env memoF K)

/-- `+analyze` at depth `j`, decoded. -/
noncomputable def anaE (j : Nat) : AnaGo FinMap R := fun id st => by
  classical
  exact if h : ∃ r, iterN j (anaSubj regsNoun K id st) ska_analyze.battery = some (anaNoun regsNoun r) ∧
      Ana.analyze env memoF (Classical.choose (hA j)) id st = some r then some (Classical.choose h) else none

theorem anaE_is (j : Nat) : AnaIsW (ev j) regsNoun K (anaE regsNoun env memoF K hA j) := by
  intro id st
  have hs : C ska_analyze.battery (C (C (identNoun id) (st.toNoun regsNoun)) K) = anaSubj regsNoun K id st :=
    rfl
  rw [hs, ev_ana]
  cases e : iterN j (anaSubj regsNoun K id st) ska_analyze.battery with
  | none =>
    have hn : ¬ ∃ r, iterN j (anaSubj regsNoun K id st) ska_analyze.battery = some (anaNoun regsNoun r) ∧
        Ana.analyze env memoF (Classical.choose (hA j)) id st = some r := by
      rintro ⟨r, hr, -⟩; rw [e] at hr; cases hr
    simp only [anaE, dif_neg hn, Option.map_none]
  | some y =>
    obtain ⟨r, rfl, hr⟩ := Classical.choose_spec (hA j) id st y e
    have hp : ∃ r, iterN j (anaSubj regsNoun K id st) ska_analyze.battery = some (anaNoun regsNoun r) ∧
        Ana.analyze env memoF (Classical.choose (hA j)) id st = some r := ⟨r, e, hr⟩
    simp only [anaE, dif_pos hp, Option.map_some]
    exact e.symm.trans (Classical.choose_spec hp).1

theorem anaE_le (j : Nat) (id : Ident) (st : SkaState FinMap R) :
    Below? (anaE regsNoun env memoF K hA j id st) (Ana.analyze env memoF (Classical.choose (hA j)) id st) := by
  intro r h
  simp only [anaE] at h
  split at h
  · rename_i hp
    cases h
    exact (Classical.choose_spec hp).2
  · cases h

/-- The loop `resolve` under `ev j`, exactly. -/
noncomputable def resE : Nat → Ident → ResGo FinMap R
  | 0 => fun _ _ _ => none
  | j + 1 => fun orig => resolveStepH env (resE j orig) (anaE regsNoun env memoF K hA j) orig

/-- `resolve` as the trap enters it under `ev j`. -/
noncomputable def resRt : Nat → ResGo FinMap R
  | 0 => fun _ _ => none
  | j + 1 => fun i => resE regsNoun env memoF K hA j i i

/-- The trap under `ev j`, exactly. -/
noncomputable def folE : Nat → FolGoS FinMap R
  | 0 => fun _ _ _ _ _ _ _ => none
  | j + 1 => Ana.folStep env (resRt regsNoun env memoF K hA j) (folE j)

variable (hhe : env.he = heSock) (hth : env.threshold = 32) (hana : slot? 511 rest = some ana)
  (hK : slot? 31 rest = some K) (hKa : slot? 92 K = some ska_analyze.arm)
include hhe hth hana hK hKa

theorem resE_is : ∀ (j : Nat) (fol : Noun) (sub : Anno) (seat mk : Option Noun) (bc df : Bool)
    (gen : GenS FinMap R) (fa fb : Noun) (f s : FolOut) (idT : Ident),
    ev j (resSubj regsNoun rest fol sub seat mk bc df gen fa fb f s idT) fol_loop.resolve
      = (resE regsNoun env memoF K hA j (s.prod.sock, C fa fb) idT gen).map (resOutNoun regsNoun)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => by
    rw [ev_zero_rt (Or.inr (Or.inr rfl))]; rfl
  | j + 1, fol, sub, seat, mk, bc, df, gen, fa, fb, f, s, idT => by
    rw [ev_succ_rt j (Or.inr (Or.inr rfl))]
    exact resolve_stepW (ev j) (fun _ _ h => ev_far j h) regsNoun env hhe hth rest K hana hK hKa
      (anaE regsNoun env memoF K hA j) (anaE_is regsNoun env memoF K hA j) fol sub seat mk bc df gen fa fb f s
      (resE regsNoun env memoF K hA j (s.prod.sock, C fa fb)) idT
      (fun i _ _ _ => resE_is j fol sub seat mk bc df gen fa fb f s i)

theorem resIs_ev (j : Nat) :
    ResIsW (ev j) regsNoun rest (fun i => resE regsNoun env memoF K hA j i i) :=
  fun s f fa fb fol sub seat mk bc df gen =>
    resE_is regsNoun env memoF rest K hA hhe hth hana hK hKa j fol sub seat mk bc df gen fa fb f s _

theorem dirIs_ev : ∀ j, DirIsW (ev j) regsNoun rest (resRt regsNoun env memoF K hA j)
  | 0 => fun _ _ _ _ _ _ _ _ _ _ _ => by rw [ev_zero_rt (Or.inr (Or.inl rfl))]; rfl
  | j + 1 => dirIsW_of (ev (j + 1)) (ev j) (fun _ => ev_succ_rt j (Or.inr (Or.inl rfl)))
      (fun _ _ h => ev_far j h) regsNoun _ rest hana (resIs_ev regsNoun env memoF rest K hA hhe hth hana hK hKa j)
      calleePutIs

variable (hsoft : env.softSpot = softSpotF) (hreg : RegisterFastIs regsNoun env)
include hsoft hreg

theorem folE_is : ∀ j, GoIsW (ev j) regsNoun rest (folE regsNoun env memoF K hA j)
  | 0 => fun _ _ _ _ _ _ _ => by rw [ev_zero_rt (Or.inl rfl)]; rfl
  | j + 1 => fun fol sub seat mk bc df gen => by
    rw [ev_succ_rt j (Or.inl rfl)]
    exact fol_loop_step_allW' (ev j) (fun _ _ h => ev_far j h) regsNoun env hsoft _ _ rest
      (folE_is j) hana hreg (dirIs_ev regsNoun env memoF rest K hA hhe hth hana hK hKa j) fol sub seat mk bc df gen

end

/-! ## Below the model -/

section
variable (regsNoun : R → Noun) (env : Env R) (memoF : Memo FinMap) (K : Noun)
  (hA : AnaGe regsNoun env memoF K) (hStep : StepBridge env)
include hStep

theorem resE_le : ∀ j, ∃ m, ∀ orig idT gen,
    Below? (resE regsNoun env memoF K hA j orig idT gen) (Ana.resolve env memoF m orig idT gen)
  | 0 => ⟨0, fun _ _ _ _ h => by simp [resE] at h⟩
  | j + 1 => by
    obtain ⟨m1, h1⟩ := resE_le j
    let ma := Classical.choose (hA j)
    refine ⟨max m1 ma + 1, fun orig idT gen => ?_⟩
    rw [Ana.resolve_unfold env memoF (max m1 ma) orig, ← hStep]
    exact resolveStepH_mono env
      (fun i g r h => Ana.resolve_fuel_le env memoF (Nat.le_max_left m1 ma) orig i g r (h1 orig i g r h))
      (fun i st r h => Ana.analyze_fuel_le env memoF (Nat.le_max_right m1 ma) i st r
        (anaE_le regsNoun env memoF K hA j i st r h)) orig idT gen

theorem resRt_le (j : Nat) : ∃ m, ResBelow (resRt regsNoun env memoF K hA j) (Ana.resolveR env memoF m) := by
  cases j with
  | zero => exact ⟨0, fun _ _ _ h => by simp [resRt] at h⟩
  | succ j =>
    obtain ⟨m, hm⟩ := resE_le regsNoun env memoF K hA hStep j
    exact ⟨m, fun i gen => hm i i gen⟩

theorem folE_le : ∀ j, ∃ m, GoBelow (folE regsNoun env memoF K hA j) (Ana.folLoop env memoF m)
  | 0 => ⟨0, fun _ _ _ _ _ _ _ _ h => by simp [folE] at h⟩
  | j + 1 => by
    obtain ⟨m1, h1⟩ := folE_le j
    obtain ⟨m2, h2⟩ := resRt_le regsNoun env memoF K hA hStep j
    refine ⟨max m1 m2 + 1, fun fol sub seat mk bc df gen => ?_⟩
    rw [Ana.folLoop_unfold env memoF (max m1 m2)]
    exact folStep_mono env
      (fun i g r h => Ana.resolveR_fuel_le env memoF (Nat.le_max_right m1 m2) i g r (h2 i g r h))
      (fun fol sub seat mk bc df gen r h =>
        Ana.folLoop_fuel_le env memoF (Nat.le_max_left m1 m2) fol sub seat mk bc df gen r
          (h1 fol sub seat mk bc df gen r h)) fol sub seat mk bc df gen

end

/-! ## The converse -/

section
variable (regsNoun : R → Noun) (env : Env R) (memoF : Memo FinMap) (rest K : Noun)
  (hA : AnaGe regsNoun env memoF K) (hStep : StepBridge env)
  (hhe : env.he = heSock) (hth : env.threshold = 32) (hana : slot? 511 rest = some ana)
  (hK : slot? 31 rest = some K) (hKa : slot? 92 K = some ska_analyze.arm)

include hA hStep hhe hth hana hK hKa in
/-- What the pill's loop `resolve` returns, on every identity, `Ana.resolve`
returns at some fuel, for the identity the trap began with. -/
theorem resolve_ge (fol : Noun) (sub : Anno) (seat mk : Option Noun) (bc df : Bool)
    (gen : GenS FinMap R) (fa fb : Noun) (f s : FolOut) (idT : Ident) (y : Noun)
    (h : nock (resSubj regsNoun rest fol sub seat mk bc df gen fa fb f s idT) fol_loop.resolve = some y) :
    ∃ r m, y = resOutNoun regsNoun r ∧ Ana.resolve env memoF m (s.prod.sock, C fa fb) idT gen = some r := by
  obtain ⟨j, hj⟩ := ev_complete h
  rw [resE_is regsNoun env memoF rest K hA hhe hth hana hK hKa] at hj
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 hj
  obtain ⟨m, hm⟩ := resE_le regsNoun env memoF K hA hStep j
  exact ⟨r, m, rfl, hm _ _ _ r hr⟩

variable (hsoft : env.softSpot = softSpotF) (hreg : RegisterFastIs regsNoun env)

include hA hStep hhe hth hana hK hKa hsoft hreg in
/-- What the pill's trap `fol-loop` returns, `Ana.folLoop` returns at some
fuel. -/
theorem fol_loop_ge (fol : Noun) (sub : Anno) (seat mk : Option Noun) (bc df : Bool)
    (gen : GenS FinMap R) (x : Noun)
    (h : nock (folSubj regsNoun rest fol sub seat mk bc df gen) fol_loop.battery = some x) :
    ∃ r m, x = folOutNoun regsNoun r ∧ Ana.folLoop env memoF m fol sub seat mk bc df gen = some r := by
  obtain ⟨j, hj⟩ := ev_complete h
  rw [folE_is regsNoun env memoF rest K hA hhe hth hana hK hKa hsoft hreg] at hj
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 hj
  obtain ⟨m, hm⟩ := folE_le regsNoun env memoF K hA hStep j
  exact ⟨r, m, rfl, hm _ _ _ _ _ _ _ r hr⟩

include hA hStep hhe hth hana hK hKa hsoft hreg in
theorem folDecodes : FolDecodes regsNoun rest := fun fol sub seat mk bc df gen x h =>
  let ⟨r, _, hx, _⟩ := fol_loop_ge regsNoun env memoF rest K hA hStep hhe hth hana hK hKa hsoft hreg
    fol sub seat mk bc df gen x h
  ⟨r, hx⟩

end

/-! ## Both directions -/

section
variable (regsNoun : R → Noun) (env : Env R) (memoF : Memo FinMap) (an : AnaGo FinMap R)

include env in
/-- The model's `resolve` is below the Hoon's loop with `an` for `+analyze`,
when every fuel of the model's `+analyze` is below `an`. -/
theorem resolve_below_H (hStep : StepBridge env)
    (hle : ∀ m i st, Below? (Ana.analyze env memoF m i st) (an i st)) :
    ∀ m orig, ResBelow (Ana.resolve env memoF m orig) (resolveH env an m orig)
  | 0, _ => fun _ _ _ h => by simp [Ana.resolve] at h
  | m + 1, orig => by
    intro i gen r h
    rw [Ana.resolve_unfold, ← hStep] at h
    exact resolveStepH_mono env (resolve_below_H hStep hle m orig) (fun i st => hle m i st) orig i gen r h

/-- The model's `resolve` begun at the call's own identity, at a fuel where it
returns. -/
noncomputable def resInf : ResGo FinMap R := fun i gen => by
  classical
  exact if h : ∃ m r, Ana.resolveR env memoF m i gen = some r then
    some (Classical.choose (Classical.choose_spec h)) else none

theorem resInf_spec {i : Ident} {gen : GenS FinMap R} {r : (Ident × FDatum FinMap) × GenS FinMap R}
    (h : resInf env memoF i gen = some r) : ∃ m, Ana.resolveR env memoF m i gen = some r := by
  simp only [resInf] at h
  split at h
  · rename_i hp
    cases h
    exact ⟨_, Classical.choose_spec (Classical.choose_spec hp)⟩
  · cases h

theorem resInf_below (n : Nat) : ResBelow (Ana.resolveR env memoF n) (resInf env memoF) := by
  intro i gen r h
  have hp : ∃ m r, Ana.resolveR env memoF m i gen = some r := ⟨n, r, h⟩
  obtain ⟨r', hr'⟩ : ∃ r', resInf env memoF i gen = some r' := by
    simp only [resInf, dif_pos hp]; exact ⟨_, rfl⟩
  obtain ⟨m', hm'⟩ := resInf_spec env memoF hr'
  have e1 := Ana.resolveR_fuel_le env memoF (Nat.le_max_left n m') i gen r h
  have e2 := Ana.resolveR_fuel_le env memoF (Nat.le_max_right n m') i gen r' hm'
  rw [e1] at e2
  cases e2
  exact hr'

end

section
variable (regsNoun : R → Noun) (env : Env R) (memoF : Memo FinMap) (rest K : Noun)
  (hA : AnaGe regsNoun env memoF K) (hStep : StepBridge env)
  (hhe : env.he = heSock) (hth : env.threshold = 32) (hana : slot? 511 rest = some ana)
  (hK : slot? 31 rest = some K) (hKa : slot? 92 K = some ska_analyze.arm)
  (an : AnaGo FinMap R) (han : AnaIs regsNoun K an)
  (hle : ∀ m i st, Below? (Ana.analyze env memoF m i st) (an i st))

include hA hStep hhe hth hana hK hKa han hle in
/-- The pill's loop `resolve`, entered from the trap, computes the limit of
the model's `resolve` (`resInf`). -/
theorem resIs_inf : ResIs regsNoun rest (resInf env memoF) := by
  intro s f fa fb fol sub seat mk bc df gen
  cases e : resInf env memoF (s.prod.sock, C fa fb) gen with
  | some r =>
    obtain ⟨m, hm⟩ := resInf_spec env memoF e
    exact resolve_le regsNoun env hhe hth rest K hana hK hKa an han fol sub seat mk bc df gen fa fb f s m
      (s.prod.sock, C fa fb) r (resolve_below_H env memoF an hStep hle m _ _ gen r hm)
  | none =>
    cases ey : nock (C fol_loop.resolve (C (identNoun (s.prod.sock, C fa fb))
        (dirSubj regsNoun rest fol sub seat mk bc df gen (C fa fb) f.toNoun s.toNoun))) fol_loop.resolve with
    | none => rfl
    | some y =>
      obtain ⟨r, m, -, hm⟩ := resolve_ge regsNoun env memoF rest K hA hStep hhe hth hana hK hKa fol sub seat mk
        bc df gen fa fb f s _ y ey
      have hp : ∃ m r, Ana.resolveR env memoF m (s.prod.sock, C fa fb) gen = some r := ⟨m, r, hm⟩
      simp only [resInf, dif_pos hp] at e
      cases e

include hA hStep hhe hth hana hK hKa han hle in
/-- The loop `resolve` entered from the trap: it returns exactly what the
model's `resolve` begun at the call's identity returns at some fuel. -/
theorem resolve_iff (fol : Noun) (sub : Anno) (seat mk : Option Noun) (bc df : Bool)
    (gen : GenS FinMap R) (fa fb : Noun) (f s : FolOut) (y : Noun) :
    nock (resSubj regsNoun rest fol sub seat mk bc df gen fa fb f s (s.prod.sock, C fa fb)) fol_loop.resolve
        = some y ↔
      ∃ r m, Ana.resolveR env memoF m (s.prod.sock, C fa fb) gen = some r ∧ y = resOutNoun regsNoun r := by
  constructor
  · intro h
    obtain ⟨r, m, hy, hm⟩ := resolve_ge regsNoun env memoF rest K hA hStep hhe hth hana hK hKa fol sub seat mk
      bc df gen fa fb f s _ y h
    exact ⟨r, m, hm, hy⟩
  · rintro ⟨r, m, hm, rfl⟩
    exact resolve_le regsNoun env hhe hth rest K hana hK hKa an han fol sub seat mk bc df gen fa fb f s m
      _ r (resolve_below_H env memoF an hStep hle m _ _ gen r hm)

variable (hsoft : env.softSpot = softSpotF) (hreg : RegisterFastIs regsNoun env)

include hA hStep hhe hth hana hK hKa han hle hsoft hreg in
/-- `fol_loop_le` with its hypotheses on the pill's runs discharged by the
converse: what `Ana.folLoop` returns at any fuel, the trap returns. -/
theorem fol_loop_le' : ∀ n fol sub seat mk bc df gen r,
    Ana.folLoop env memoF n fol sub seat mk bc df gen = some r →
      nock (folSubj regsNoun rest fol sub seat mk bc df gen) fol_loop.battery
        = some (folOutNoun regsNoun r) :=
  fol_loop_le regsNoun env hsoft memoF rest hana hreg
    (folDecodes regsNoun env memoF rest K hA hStep hhe hth hana hK hKa hsoft hreg)
    (fun n => ⟨resInf env memoF,
      resIs_inf regsNoun env memoF rest K hA hStep hhe hth hana hK hKa an han hle, resInf_below env memoF n⟩)

include hA hStep hhe hth hana hK hKa han hle hsoft hreg in
/-- The trap `fol-loop` returns exactly what `Ana.folLoop` returns at some
fuel. -/
theorem fol_loop_iff (fol : Noun) (sub : Anno) (seat mk : Option Noun) (bc df : Bool)
    (gen : GenS FinMap R) (x : Noun) :
    nock (folSubj regsNoun rest fol sub seat mk bc df gen) fol_loop.battery = some x ↔
      ∃ r m, Ana.folLoop env memoF m fol sub seat mk bc df gen = some r ∧ x = folOutNoun regsNoun r := by
  constructor
  · intro h
    obtain ⟨r, m, hx, hm⟩ := fol_loop_ge regsNoun env memoF rest K hA hStep hhe hth hana hK hKa hsoft hreg
      fol sub seat mk bc df gen x h
    exact ⟨r, m, hm, hx⟩
  · rintro ⟨r, m, hm, rfl⟩
    exact fol_loop_le' regsNoun env memoF rest K hA hStep hhe hth hana hK hKa an han hle hsoft hreg
      m fol sub seat mk bc df gen r hm

end

end Compiler
end Formalization
