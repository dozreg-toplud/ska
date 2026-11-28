import lemmas.Ska.RawInvCLSARunD

/-!
# Single assignment with direct calls, `mono` `|`: the count on `runLCM env false` over `PlainD`

README Gaps 14 (b), track D (fork `kxs`).  The definition count `HRS` for the
runs of `runLCM env false` (`runLC`, the n-ary runs of `finishLFC`) on
`PlainD`, whose `%2` with a bell is `callL`'s direct branch: the drop path,
else (no memo key, no ring, `sof` false) `+need-ord-alloc-regs`, the call
block (`%done`: `[jmp b sub-v]`; otherwise `+simple-next`, `+kerf`, `[cal b
sub-v pro]` hopping to `out`), and the chain with the goal "`sub-ned` at the
call block".  The other arms are those of `ksd_run` (`RawInvCLSARunD.lean`)
with `env false`.

* `kxs_callBlockDone`, `kxs_callBlockRest`: the call block.
* `kxs_calPath`, **`kxs_callL`**: the direct branch of `callL`.
* `kxs_run`, **`sarRunF_plainD`**: `HRS (runLCM env false sup nm)` on `PlainD`.
* **`topSAR_plainDF`**: `TopSAR` (the `runLC` form of `RawInvCLTopN.lean`) on
  `PlainD`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map] [MapKeys Map]

/-! ## The call block -/

/-- **The call block under `%done`**: `[jmp b sub-v]`, which defines nothing. -/
theorem kxs_callBlockDone (b : Bell) (subNed : Need) :
    HC (fun g => GFL (Map := Map) (CGoalL.done : CGoalL S) g ∧ LG (CGoalL.done : CGoalL S) g)
      (sarG (CGoalL.done : CGoalL S) ++ flattenNeed subNed)
      (emit ⟨[], [], Termin.jmp b (flattenNeed subNed)⟩ : CM Map Nat) (fun x g => Fresh g (jmp0 x))
      (fun _ => flattenNeed subNed) := by
  refine HC.weak (P := fun _ => True) ?_ (fun _ _ => trivial)
  exact HC.conseq (hc_emit (P := fun _ => True) (ro := flattenNeed subNed) rfl (js_nil rfl) stab_true (by simp)
    (fun y => by simp [blockDefs, sarG])) (fun _ h => h) (fun _ _ h => h.2) (fun _ => Nat.le_refl _)
    (fun _ _ => Nat.le_refl _)

/-- **The call block otherwise**: `+simple-next`, `+kerf`, `[cal b sub-v pro]`
hopping to `out` (it defines `pro`). -/
theorem kxs_callBlockRest (St : SarSteps S Map) (b : Bell) (subNed : Need) (goal : CGoalL S) :
    HC (fun g => GFL (Map := Map) goal g ∧ LG goal g) (sarG goal ++ flattenNeed subNed) (do
      let nex ← simpleNextL goal
      let (out, pro) ← kerf nex
      emit ⟨[], [Pole.cal b (flattenNeed subNed) pro], Termin.hop (jmp0 out)⟩ : CM Map Nat)
      (fun x g => Fresh g (jmp0 x)) (fun _ => flattenNeed subNed) := by
  refine HC.bind' (HC.weak (HC.frame (hcl_simpleNextL goal) stab_true (flattenNeed subNed))
    fun g h => ⟨h, trivial⟩) fun nex => ?_
  refine HC.bind' (HC.frame (HC.ofC (HT.weak (ht_kerf nex) fun _ h => h.1) (fun _ h => fresh_args h.1)
    (St.kerf nex)) stab_true (flattenNeed subNed)) fun a => ?_
  rcases a with ⟨out, pro⟩
  exact HC.conseq (hc_emit (P := fun g => Fresh g (jmp0 out) ∧ True) (ro := flattenNeed subNed) rfl
    (js_hop fun g h => h.1) (stab_and (stab_fresh _) stab_true) (by simp [trOp])
    (cnt_app_le (by simp [blockDefs, aliasDst])))
    (fun _ h => h) (fun _ _ h => h.2) (fun _ => Nat.le_refl _) (fun _ _ => Nat.le_refl _)

/-! ## The direct branch -/

/-- **The direct branch of `callL` past the `sof` test**, for any call block
`m` that defines nothing of the callee's need. -/
theorem kxs_calPath (St : SarSteps S Map) (env : CallEnv) {rp rq : CGoalL S → List Nat → CM Map (NextL S)}
    (p q : Nomm) (bNed : NeedOrd) (hp : HRS (Map := Map) rp) (hq : HRS (Map := Map) rq)
    (goal : CGoalL S) (region : List Nat) (m : Need → CM Map Nat)
    (hm : ∀ subNed, HC (fun g => GFL (Map := Map) goal g ∧ LG goal g) (sarG goal ++ flattenNeed subNed) (m subNed)
      (fun x g => Fresh g (jmp0 x)) (fun _ => flattenNeed subNed)) :
    HC (fun g => GFL (Map := Map) goal g ∧ LG goal g) (sarG goal) (do
      let subNed ← needOrdAllocRegs bNed
      let callBlock ← m subNed
      let nexArg : NextL S := ⟨ofSure ⟨subNed, HoonSet.empty⟩, jmp0 callBlock⟩
      let nexFol ← (if safeFolFol q then pure ⟨ofSure Sure.bunt, nexArg.th⟩
        else rq (CGoalL.next (ofSure Sure.bunt) nexArg.th) region : CM Map (NextL S))
      let nexFol ← pastL env.cod nexFol p region
      let nexSub ← rp (CGoalL.next nexArg.laz nexFol.th) region
      copyL nexSub nexFol.laz : CM Map (NextL S)) (fun nex g => Fresh g nex.th ∧ LG nex.goal g)
      (fun nex => sarR nex.laz) := by
  refine HC.bind' (ksd_needOrd (stab_and (stab_gfl goal) (stab_lg goal)) bNed (sarG goal)) fun subNed => ?_
  refine HC.bind' (hm subNed) fun callBlock => ?_
  exact HC.conseq (ksd_bin St env.cod p hp (ksd_fol hq q (jmp0 callBlock) region)
    (ofSure ⟨subNed, HoonSet.empty⟩) region)
    (fun g h => ⟨h, ll_ofSure _ _⟩) (fun _ _ h => h)
    (fun y => by simp [sarR_ofSure]) (fun _ _ => Nat.le_refl _)

/-- **The direct call with `mono` `|`** (`callL` with a bell): the drop path
and the `%cal` / `%jmp` path. -/
theorem kxs_callL (St : SarSteps S Map) (env : CallEnv) {rp rq : CGoalL S → List Nat → CM Map (NextL S)}
    (p q : Nomm) (sup : Option Nomm) (b : Bell) (key : Option Noun) (hp : HRS (Map := Map) rp)
    (hq : HRS (Map := Map) rq) (goal : CGoalL S) (region : List Nat) :
    HC (fun g => GFL (Map := Map) goal g ∧ LG goal g) (sarG goal)
      (callL env rp rq p q (some (b, key)) sup goal region : CM Map (NextL S))
      (fun nex g => Fresh g nex.th ∧ LG nex.goal g) (fun nex => sarR nex.laz) := by
  cases goal with
  | next laz th =>
    unfold callL
    dsimp only
    by_cases hd : (env.pure b && noneEquivalentL laz) = true
    · simp only [hd, if_true]
      exact HC.conseq (ksd_bin St env.cod p hp (ksd_fol hq q th region) (ofSure Sure.bunt) region)
        (fun g h => ⟨h.1, ll_ofSure _ _⟩) (fun _ _ h => h)
        (fun y => by simp [sarR_ofSure, Sure.bunt, flattenNeed]) (fun _ _ => Nat.le_refl _)
    · simp only [hd, Bool.false_eq_true, if_false]
      cases key with
      | some k => exact HC.fail
      | none =>
        cases hr : env.ring b with
        | some _ => simp only [hr]; exact HC.fail
        | none =>
          cases hn : env.need b with
          | none => simp only [hr, hn]; exact HC.fail
          | some bNed =>
            simp only [hr, hn]
            refine HC.ite' _ HC.fail ?_
            exact kxs_calPath St env p q bNed hp hq _ region _ (fun subNed => kxs_callBlockRest St b subNed _)
  | pick z o =>
    unfold callL
    dsimp only
    cases key with
    | some k => exact HC.fail
    | none =>
      cases hr : env.ring b with
      | some _ => simp only [hr]; exact HC.fail
      | none =>
        cases hn : env.need b with
        | none => simp only [hr, hn]; exact HC.fail
        | some bNed =>
          simp only [hr, hn]
          refine HC.ite' _ HC.fail ?_
          exact kxs_calPath St env p q bNed hp hq _ region _ (fun subNed => kxs_callBlockRest St b subNed _)
  | done =>
    unfold callL
    dsimp only
    cases key with
    | some k => exact HC.fail
    | none =>
      cases hr : env.ring b with
      | some _ => simp only [hr]; exact HC.fail
      | none =>
        cases hn : env.need b with
        | none => simp only [hr, hn]; exact HC.fail
        | some bNed =>
          simp only [hr, hn]
          refine HC.ite' _ HC.fail ?_
          exact kxs_calPath St env p q bNed hp hq _ region _ (fun subNed => kxs_callBlockDone b subNed)

/-! ## The induction -/

/-- **Single assignment at run level on `PlainD`** (`runLCM env false`), from the walks' counts. -/
theorem kxs_run (env : CallEnv) (St : SarSteps S Map) : ∀ (nm : Nomm), PlainD nm → ∀ (sup : Option Nomm),
    HRS (Map := Map) (runLCM (S := S) env false sup nm)
  | Nomm.cons p q, h, sup, goal, region => by
    have ihp := kxs_run env St p h.1 sup
    have ihq := kxs_run env St q h.2 sup
    unfold runLCM
    refine HC.bind' (R := fun (goal' : CGoalL S) (g : Comp.Gen Map) => GFL goal' g ∧ LG goal' g)
      (r1 := sarG) ?_ fun goal' => ?_
    · cases goal with
      | done =>
        refine HC.weak (P := fun _ => True) ?_ (fun _ _ => trivial)
        exact HC.bind' (hc_re stab_true _) fun r =>
          HC.bind' (hc_emit (ro := [r]) rfl (js_nil rfl) stab_true (by simp)
            (cnt_app_le (by simp [blockDefs, sarG]))) fun o =>
            HC.pure' (fun g h => ⟨h.2, lg_ofSure _ _ _⟩) (fun y => by simp [sarG, sarR_ofSure, lazyReg, flattenNeed])
      | next laz th => exact HC.pure' (fun g h => h) (fun _ => Nat.le_refl _)
      | pick z o => exact HC.pure' (fun g h => h) (fun _ => Nat.le_refl _)
    · cases goal' with
      | pick z o =>
        exact HC.bind' (HC.conseq (hc_emit (ro := []) rfl (js_nil rfl) stab_true (by simp)
            (fun y => by simp [blockDefs])) (fun _ _ => trivial) (fun _ _ h => h) (fun _ => Nat.le_refl _)
            (fun _ _ => Nat.le_refl _))
          fun o => HC.conseq (hcl_bin St env.cod p ihp ihq _ _ _ _) (fun g h => ⟨h.2, ll_ofSure _ _, ll_ofSure _ _⟩)
            (fun _ _ h => h) (fun y => by simp [sarR_ofSure, Sure.bunt, flattenNeed]) (fun _ _ => Nat.le_refl _)
      | done => exact HC.fail
      | next laz th =>
        refine HC.bind' (HC.weak (hcl_splitL St ⟨laz, th⟩) fun g h => h) fun a => ?_
        rcases a with ⟨hed, tel, o⟩
        refine HC.bind' (HC.weak (HC.frame (hcl_pastL env.cod ⟨hed, jmp0 o⟩ q region) (stab_ll tel) (sarR tel))
          fun g h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩) fun nexh => ?_
        exact HC.conseq (hcl_bin St env.cod p ihp ihq tel nexh.laz nexh.th region) (fun g h => ⟨h.1.1, h.2, h.1.2⟩)
          (fun _ _ h => h) (sar_comm _ _) (fun _ _ => Nat.le_refl _)
  | Nomm.n0 ax, _, sup, goal, region => by
    unfold runLCM
    refine HC.ite' _ (hcl_bombL _ _) (HC.bind' (hcl_simpleNextL _) fun nex =>
      HC.ite' _ (HC.pure' (fun g h => h) (fun _ => Nat.le_refl _)) ?_)
    cases hf : Lazy.fromL ax nex.laz with
    | none => exact HC.fail
    | some laz =>
      exact HC.pure' (fun g h => ⟨h.1, (labSteps (S := S) (Map := Map)).fromL (Q := fun n => n < g.bo) hf h.2.1 h.2.2⟩)
        (St.fromL ax _ _ hf)
  | Nomm.n1 k, _, sup, goal, region => by
    unfold runLCM
    cases goal with
    | done =>
      refine HC.weak (P := fun _ => True) ?_ (fun _ _ => trivial)
      exact HC.bind' (hc_re stab_true _) fun r =>
        HC.bind' (hc_emit (ro := []) rfl (js_nil rfl) stab_true (by simp [trOp])
          (cnt_app_le (by simp [blockDefs, aliasDst, sarG]))) fun o =>
          HC.pure' (fun g h => ⟨h.2, lg_ofSure _ _ _⟩) (fun y => by simp [sarR_ofSure, Sure.bunt, flattenNeed])
    | pick z o =>
      exact HC.ite' _ (HC.pure' (fun g h => ⟨h.1.1, lg_ofSure _ _ _⟩)
          (fun y => by simp [sarR_ofSure, Sure.bunt, flattenNeed]))
        (HC.ite' _ (HC.pure' (fun g h => ⟨h.1.2, lg_ofSure _ _ _⟩)
          (fun y => by simp [sarR_ofSure, Sure.bunt, flattenNeed])) (hcl_bombL _ _))
    | next laz th =>
      exact HC.bind' (HC.ofC (HT.weak (ht_medeL _ _ _) fun _ h => h.1) (fun _ h => fresh_args h.1) (St.mede _ _ _))
        fun o => HC.pure' (fun g h => ⟨h, lg_ofSure _ _ _⟩) (fun y => by simp [sarR_ofSure, Sure.bunt, flattenNeed])
  | Nomm.n3 p, h, sup, goal, region => by
    have ih := kxs_run env St p h sup
    unfold runLCM
    cases goal with
    | pick z o =>
      refine HC.weak (P := GFL (Map := Map) (CGoalL.pick (S := S) z o)) ?_ (fun _ h => h.1)
      exact HC.bind' (hc_re (stab_gfl (CGoalL.pick (S := S) z o)) _) fun r =>
        hcl_tail ih rfl (js_two rfl fun g h => h) (stab_gfl (CGoalL.pick (S := S) z o)) (by simp) (lazyReg r) _
          (cnt_app_le (by simp [blockDefs, lazyReg, flattenNeed, sarG]))
    | done =>
      refine HC.bind' (HC.conseq (HC.of ht_doneBlocks (sc_doneBlocks _)) (fun _ _ => trivial) (fun _ _ h => h)
        (fun _ => Nat.le_refl _) (fun _ _ => Nat.le_refl _)) fun a => ?_
      rcases a with ⟨o0, o1⟩
      exact HC.bind' (hc_re (stab_and (stab_fresh _) (stab_fresh _)) _) fun r =>
        hcl_tail ih rfl (js_two rfl fun g h => h) (stab_and (stab_fresh _) (stab_fresh _)) (by simp) (lazyReg r) _
          (cnt_app_le (by simp [blockDefs, lazyReg, flattenNeed, sarG]))
    | next laz th =>
      refine HC.ite' _ (ih _ _) (HC.bind' (HC.ofC (HT.weak (ht_collapse ⟨laz, th⟩) fun _ h => h.1)
        (fun _ _ => trivial) (fun _ => St.collapse ⟨laz, th⟩)) fun a => ?_)
      rcases a with _ | ⟨r, o⟩
      · exact HC.fail
      · refine HC.bind' (HC.conseq (HC.of (ht_forl r o) (sc_forl r o)) (fun _ h => h r o rfl) (fun _ _ h => h)
          (fun _ => Nat.le_refl _) (fun _ _ => Nat.le_refl _)) fun x => ?_
        rcases x with ⟨z, o'⟩
        exact HC.bind' (hc_re (stab_and (stab_fresh _) (stab_fresh _)) _) fun r' =>
          hcl_tail ih rfl (js_two rfl fun g h => h) (stab_and (stab_fresh _) (stab_fresh _)) (by simp) (lazyReg r') _
            (cnt_app_le (by simp [blockDefs, lazyReg, flattenNeed]))
  | Nomm.n4 p, h, sup, goal, region => by
    have ih := kxs_run env St p h sup
    unfold runLCM
    cases goal with
    | done =>
      refine HC.weak (P := fun _ => True) ?_ (fun _ _ => trivial)
      exact HC.bind' (hc_re stab_true _) fun pro => HC.bind' (hc_re stab_true _) fun arg =>
        hcl_tail ih rfl (js_nil rfl) stab_true (by simp [trOp]) (lazyReg arg) _
          (cnt_app_le (by simp [blockDefs, aliasDst, lazyReg, flattenNeed, sarG]))
    | pick z o =>
      refine HC.weak (P := GFL (Map := Map) (CGoalL.pick (S := S) z o)) ?_ (fun _ h => h.1)
      exact HC.bind' (hc_re (stab_gfl (CGoalL.pick (S := S) z o)) _) fun pro =>
        HC.bind' (hc_re (stab_gfl (CGoalL.pick (S := S) z o)) _) fun arg =>
          hcl_tail ih rfl (js_two rfl fun g h => h) (stab_gfl (CGoalL.pick (S := S) z o)) (by simp [trOp])
            (lazyReg arg) _ (cnt_app_le (by simp [blockDefs, aliasDst, lazyReg, flattenNeed, sarG]))
    | next laz th =>
      refine HC.bind' (HC.weak (HC.frame0 (HC.ofC (ht_collapse ⟨laz, th⟩) (fun _ _ => trivial)
        (fun _ => St.collapse ⟨laz, th⟩)) (stab_fresh th)) fun _ h => ⟨h.1, h.1⟩) fun a => ?_
      refine HC.bind' (R := fun (x : Nat × Nat) (g : Comp.Gen Map) => Fresh g (jmp0 x.2)) (r1 := fun x => [x.1])
        ?_ fun x => ?_
      · cases a with
        | some x => exact HC.pure' (fun g h => h.1 x.1 x.2 rfl) (fun _ => Nat.le_refl _)
        | none =>
          refine HC.bind' (HC.conseq (HC.of (ht_qf QM.re' th) (sc_re _)) (fun _ h => h.2) (fun _ _ h => h)
            (fun _ => Nat.le_refl _) (fun _ _ => Nat.le_refl _)) fun r => ?_
          exact HC.ite' _ (HC.pure' (fun g h => fresh_jmp0 h) (fun y => by simp)) HC.fail
      · rcases x with ⟨pro, th'⟩
        exact HC.bind' (HC.of (ht_qf QM.re' _) (sc_re _)) fun arg =>
          hcl_tail ih rfl (js_hop fun g h => h) (stab_fresh _) (by simp [trOp]) (lazyReg arg) _
            (cnt_app_le (by simp [blockDefs, aliasDst, lazyReg, flattenNeed]))
  | Nomm.n5 p q, h, sup, goal, region => by
    have ihp := kxs_run env St p h.1 sup
    have ihq := kxs_run env St q h.2 sup
    unfold runLCM
    refine HC.weak (P := GFL (Map := Map) goal) ?_ (fun _ h => h.1)
    refine HC.bind' (hc_re (stab_gfl goal) _) fun rp => HC.bind' (hc_re (stab_gfl goal) _) fun rq =>
      HC.bind' (R := fun (o : Nat) (g : Comp.Gen Map) => Fresh g (jmp0 o)) (r1 := fun _ => [rq, rp]) ?_ fun o =>
        HC.conseq (hcl_bin St env.cod p ihp ihq _ _ _ _) (fun g h => ⟨h, ll_ofSure _ _, ll_ofSure _ _⟩)
          (fun _ _ h => h) (fun y => by simp [sarR_ofSure, lazyReg, flattenNeed]) (fun _ _ => Nat.le_refl _)
    cases goal with
    | pick z o =>
      exact HC.conseq (hc_emit (ro := [rq, rp]) rfl (js_two rfl fun g h => h) (stab_gfl (CGoalL.pick (S := S) z o))
        (by simp) (cnt_perm_le (List.Perm.swap _ _ _))) (fun _ h => h) (fun _ _ h => h.2)
        (fun _ => Nat.le_refl _) (fun _ _ => Nat.le_refl _)
    | done =>
      refine HC.bind' (HC.conseq (HC.of ht_doneBlocks (sc_doneBlocks _)) (fun _ _ => trivial) (fun _ _ h => h)
        (fun _ => Nat.le_refl _) (fun _ _ => Nat.le_refl _)) fun a => ?_
      rcases a with ⟨o0, o1⟩
      exact HC.conseq (hc_emit (ro := [rq, rp]) rfl (js_two rfl fun g h => h)
        (stab_and (stab_fresh _) (stab_fresh _)) (by simp) (cnt_perm_le (List.Perm.swap _ _ _)))
        (fun _ h => h) (fun _ _ h => h.2) (fun _ => Nat.le_refl _) (fun _ _ => Nat.le_refl _)
    | next laz th =>
      refine HC.bind' (HC.conseq (HC.frame (HC.weak (HC.frame0 (HC.ofC (ht_collapse ⟨laz, th⟩) (fun _ _ => trivial)
        (fun _ => St.collapse ⟨laz, th⟩)) (stab_fresh th)) fun _ h => ⟨h, h⟩) stab_true [rp, rq])
        (fun _ h => ⟨h, trivial⟩) (fun _ _ h => h.1) (fun y => by simp [sarG, List.count_append])
        (fun _ _ => Nat.le_refl _)) fun a => ?_
      cases a with
      | none =>
        refine HC.ite' _ ?_ HC.fail
        exact HC.conseq (hc_emit (ro := [rq, rp]) rfl (js_hop fun g h => fresh_jmp0 h) (stab_fresh th)
          (by simp [trOp]) (cnt_perm_le (List.Perm.swap _ _ _))) (fun _ h => h.2)
          (fun _ _ h => h.2) (fun _ => Nat.le_refl _) (fun _ _ => Nat.le_refl _)
      | some x =>
        rcases x with ⟨r, o⟩
        refine HC.bind' (HC.conseq (HC.frame (HC.of (ht_forl r o) (sc_forl r o)) stab_true [rp, rq])
          (fun _ h => ⟨h.1 r o rfl, trivial⟩) (fun _ _ h => h.1) (fun _ => Nat.le_refl _)
          (fun _ _ => Nat.le_refl _)) fun x => ?_
        rcases x with ⟨z, o'⟩
        exact HC.conseq (hc_emit (ro := [rq, rp]) rfl (js_two rfl fun g h => h)
          (stab_and (stab_fresh _) (stab_fresh _)) (by simp)
          (cnt_perm_le (List.Perm.swap _ _ _))) (fun _ h => h) (fun _ _ h => h.2)
          (fun _ => Nat.le_refl _) (fun _ _ => Nat.le_refl _)
  | Nomm.n7 p q, h, sup, goal, region => by
    unfold runLCM
    exact HC.bind' (kxs_run env St q h.2 (some p) goal region) fun nex =>
      HC.weak (kxs_run env St p h.1 sup nex.goal region) fun _ h => h
  | Nomm.n10 a v q, h, sup, goal, region => by
    have ihv := kxs_run env St v h.1 sup
    have ihq := kxs_run env St q h.2 sup
    unfold runLCM
    refine HC.bind' (hcl_simpleNextL _) fun next => HC.bind' (HC.weak (hcl_intoL St _ _) fun g h => h) fun x => ?_
    rcases x with ⟨don, rec, o⟩
    refine HC.bind' (HC.conseq (HC.frame (hcl_pastL env.cod ⟨rec, jmp0 o⟩ v region) (stab_ll don) (sarR don))
      (fun g h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩) (fun _ _ h => h) (sar_comm _ _) (fun _ _ => Nat.le_refl _)) fun nexR => ?_
    exact HC.conseq (hcl_bin St env.cod q ihq ihv don nexR.laz nexR.th region) (fun g h => ⟨h.1.1, h.2, h.1.2⟩)
      (fun _ _ h => h) (sar_comm _ _) (fun _ _ => Nat.le_refl _)
  | Nomm.n2 p q info, h, sup, goal, region => by
    unfold runLCM
    cases info with
    | none =>
      rw [callLM_none]
      exact hcl_callL St env p q sup (kxs_run env St p h.1 sup) (kxs_run env St q h.2 sup) goal region
    | some bk =>
      obtain ⟨b, key⟩ := bk
      rw [callLM_false]
      exact kxs_callL St env p q sup b key (kxs_run env St p h.1 sup) (kxs_run env St q h.2 sup) goal region
  | Nomm.n6 _ _ _, h, _, _, _ => h.elim
  | Nomm.n11s _ _ _, h, _, _, _ => h.elim
  | Nomm.n11d _ _ _ _, h, _, _, _ => h.elim
  | Nomm.n12 _ _, h, _, _, _ => h.elim
  | Nomm.mean _ _ _ _ _, h, _, _, _ => h.elim

/-- **Single assignment at run level with direct calls, `mono` `|`**: `HRS`
of every run of `runLCM env false` on `PlainD`. -/
theorem sarRunF_plainD (env : CallEnv) : ∀ (nm : Nomm), PlainD nm → ∀ (sup : Option Nomm),
    HRS (Map := Map) (runLCM (S := S) env false sup nm) :=
  kxs_run env ksd_steps

/-- **`TopSAR` on `PlainD`** (the n-ary top run, `runLC`). -/
theorem topSAR_plainDF {env : CallEnv} {nm : Nomm} (hp : PlainD nm) : TopSAR S Map env nm := by
  unfold TopSAR
  intro nex g1 h
  rw [← runLCM_false env nm Option.none CGoalL.done []] at h
  obtain ⟨s1, -, c1⟩ := (sarRunF_plainD env nm hp Option.none CGoalL.done []).sc gen0 nex g1 ats_gen0
    ⟨trivial, trivial⟩ sarSt_gen0 h
  refine sar_sab s1 fun y => ?_
  have h1 := c1 y
  have h2 := fr_le_one (gen0 : Comp.Gen Map).re g1.re y
  rw [sarDc_gen0] at h1
  simp only [sarG, List.count_nil] at h1
  omega

end Raw
end SkaModel
end Formalization
