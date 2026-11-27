import lemmas.Ska.RawInvCLSARunSteps
import lemmas.Ska.RawInvCLTopN

/-!
# Single assignment with calls: the induction on `PlainN`

README Gaps 14 (b), track D.  `HRS rp`: `HRL` (`Fresh` goals with the label
clause `LG`, `RawInvCLLab.lean`) with the linear count of definitions of
`RawInvCLSARunBase.lean`.  The induction follows `labRun_plainOf` step for
step, each `HT` with its count (`hcl_*`); the walks' counts are the fields of
`SarSteps`.

* `hcl_simpleNextL`, `hcl_bombL`, `hcl_splitL`, `hcl_intoL`, `hcl_pastL`,
  `hcl_copyL`, `hcl_tail`, `hcl_bin` (run q, `+past`, run p, `+copy`),
  `hcl_callL`.
* **`sarRun_plainOf`**: `HRS (runLC env sup nm)` on all of `PlainN`, from
  `SarSteps`.
* **`topSAR_plain_of`**, **`topSAU_plain_of`**: the open facts `TopSAR`
  (`RawInvCLTopN.lean`) and `TopSAU` (`RawInvCLTopU.lean`) on `PlainN`, from
  `SarSteps`.
* `SarStepsW` (the fields of `SarSteps` still open: `+split`, `+into`,
  `+copy`, `+collapse-lazy-atom`, `+kerf`; `+mede` and `+from` are proved in
  `RawInvCLSARunSteps.lean`), `sarSteps_of`, **`topSAR_plainW`**,
  **`topSAU_plainW`**.
-/

set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map] [MapKeys Map]

/-- **`HRL` with the count of definitions.** -/
abbrev HRS (rp : CGoalL S → List Nat → CM Map (NextL S)) : Prop :=
  ∀ goal region, HC (fun g => GFL (Map := Map) goal g ∧ LG goal g) (sarG goal) (rp goal region)
    (fun nex g => Fresh g nex.th ∧ LG nex.goal g) (fun nex => sarR nex.laz)

theorem sar_comm (a b : List Nat) (y : Nat) : (a ++ b).count y ≤ (b ++ a).count y := by
  simp only [List.count_append]; omega

/-! ## The steps with counts -/

theorem hcl_simpleNextL (goal : CGoalL S) :
    HC (fun g => GFL (Map := Map) goal g ∧ LG goal g) (sarG goal) (simpleNextL goal : CM Map (NextL S))
      (fun nex g => Fresh g nex.th ∧ LG nex.goal g) (fun nex => sarR nex.laz) :=
  HC.ofC (htl_simpleNextL goal) (fun _ h => sarGA_of h.1) (sc_simpleNextL goal)

theorem hcl_bombL {P : Comp.Gen Map → Prop} (ri : List Nat) (miss : Option Nat) :
    HC P ri (bombL miss : CM Map (NextL S)) (fun nex g => Fresh g nex.th ∧ LG nex.goal g) (fun nex => sarR nex.laz) :=
  HC.of (htl_bombL miss) (sc_bombL ri miss)

theorem hcl_splitL (St : SarSteps S Map) (nex : NextL S) :
    HC (fun g => Fresh g nex.th ∧ LL nex.laz g) (sarR nex.laz) (splitL nex : CM Map (Lazy S × Lazy S × Nat))
      (fun x g => Fresh g (jmp0 x.2.2) ∧ (LL x.1 g ∧ LL x.2.1 g)) (fun x => sarR x.1 ++ sarR x.2.1) :=
  HC.ofC (htl_splitL labSteps nex) (fun _ h => fresh_args h.1) (St.split nex)

theorem hcl_intoL (St : SarSteps S Map) (nex : NextL S) (axe : Nat) :
    HC (fun g => Fresh g nex.th ∧ LL nex.laz g) (sarR nex.laz) (intoL nex axe : CM Map (Lazy S × Lazy S × Nat))
      (fun x g => Fresh g (jmp0 x.2.2) ∧ (LL x.1 g ∧ LL x.2.1 g)) (fun x => sarR x.1 ++ sarR x.2.1) :=
  HC.ofC (htl_intoL labSteps nex axe) (fun _ h => fresh_args h.1) (St.into nex axe)

theorem hcl_pastL (cod : Bell → Option Bool) (nex : NextL S) (nom : Nomm) (region : List Nat) :
    HC (fun g => Fresh g nex.th ∧ LL nex.laz g) (sarR nex.laz) (pastL cod nex nom region : CM Map (NextL S))
      (fun x g => Fresh g x.th ∧ LL x.laz g) (fun x => sarR x.laz) :=
  HC.ofC (htl_pastL labSteps cod nex nom region) (fun _ h => fresh_args h.1) (sc_pastL cod nex nom region)

theorem hcl_copyL (St : SarSteps S Map) (first : NextL S) (second : Lazy S) :
    HC (fun g => Fresh g first.th ∧ (LL first.laz g ∧ LL second g)) (sarR first.laz ++ sarR second)
      (copyL first second : CM Map (NextL S)) (fun x g => Fresh g x.th ∧ LL x.laz g) (fun x => sarR x.laz) :=
  HC.ofC (C := first.th.args = [] ∧ LabUniq first.laz ∧ LabUniq second) (htl_copyL labSteps first second)
    (fun _ h => ⟨fresh_args h.1, h.2.1.1, h.2.2.1⟩)
    fun c => St.copy first second c.1 c.2.1 c.2.2

/-- A run for an `ofSure` goal at a block just emitted. -/
theorem hcl_tail {P : Comp.Gen Map → Prop} {rp : CGoalL S → List Nat → CM Map (NextL S)}
    (h : HRS (Map := Map) rp) {b : Blob} (hpar : b.par = []) (hb : ∀ g, P g → ∀ j ∈ finJumps b.fin, Fresh g j)
    (hP : Stab P) (htr : ∀ op ∈ b.body, trOp op = false) (s : Sure S) (region : List Nat) {ri : List Nat}
    (hc : ∀ y, (blockDefs b).count y + (flattenNeed s.ned).count y ≤ ri.count y) :
    HC P ri (do let o ← emit b; rp (CGoalL.next (ofSure s) (jmp0 o)) region : CM Map (NextL S))
      (fun nex g => Fresh g nex.th ∧ LG nex.goal g) (fun nex => sarR nex.laz) :=
  HC.bind' (hc_emit (ro := flattenNeed s.ned) hpar hb hP htr hc) fun _ =>
    HC.conseq (h _ _) (fun _ h => ⟨h.2, lg_ofSure _ _ _⟩) (fun _ _ h => h)
      (fun y => Nat.le_of_eq (by rw [sarG_next, sarR_ofSure])) (fun _ _ => Nat.le_refl _)

/-- **The tail of the binary cases**: run `q` for `lq`, `+past`, run `p` for
`lp`, `+copy`. -/
theorem hcl_bin (St : SarSteps S Map) (cod : Bell → Option Bool) {rp rq : CGoalL S → List Nat → CM Map (NextL S)}
    (p : Nomm) (hp : HRS (Map := Map) rp) (hq : HRS (Map := Map) rq) (lq lp : Lazy S) (th : Jmp)
    (region : List Nat) :
    HC (fun g => Fresh g th ∧ LL lq g ∧ LL lp g) (sarR lq ++ sarR lp) (do
      let nex2 ← rq (CGoalL.next lq th) region
      let nex2 ← pastL cod nex2 p region
      let nex1 ← rp (CGoalL.next lp nex2.th) region
      copyL nex1 nex2.laz : CM Map (NextL S)) (fun nex g => Fresh g nex.th ∧ LG nex.goal g)
      (fun nex => sarR nex.laz) := by
  refine HC.bind' (HC.weak (HC.frame (hq (CGoalL.next lq th) region) (stab_ll lp) (sarR lp))
    fun g h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩) fun nex2 => ?_
  refine HC.bind' (HC.weak (HC.frame (hcl_pastL cod nex2 p region) (stab_ll lp) (sarR lp))
    fun g h => ⟨⟨h.1.1, h.1.2⟩, h.2⟩) fun nex2' => ?_
  refine HC.bind' (HC.conseq (HC.frame (hp (CGoalL.next lp nex2'.th) region) (stab_ll nex2'.laz) (sarR nex2'.laz))
    (fun g h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩) (fun _ _ h => h) (sar_comm _ _) (fun _ _ => Nat.le_refl _)) fun nex1 => ?_
  exact HC.conseq (hcl_copyL St nex1 nex2'.laz) (fun g h => ⟨h.1.1, h.1.2, h.2⟩) (fun _ _ h => h)
    (fun _ => Nat.le_refl _) (fun _ _ => Nat.le_refl _)

/-- **The indirect call.** -/
theorem hcl_callL (St : SarSteps S Map) (env : CallEnv) {rp rq : CGoalL S → List Nat → CM Map (NextL S)}
    (p q : Nomm) (sup : Option Nomm) (hp : HRS (Map := Map) rp) (hq : HRS (Map := Map) rq) (goal : CGoalL S)
    (region : List Nat) :
    HC (fun g => GFL (Map := Map) goal g ∧ LG goal g) (sarG goal)
      (callL env rp rq p q Option.none sup goal region : CM Map (NextL S))
      (fun nex g => Fresh g nex.th ∧ LG nex.goal g) (fun nex => sarR nex.laz) := by
  unfold callL
  refine HC.bind' (hcl_simpleNextL goal) fun nex => ?_
  refine HC.bind' (HC.ofC (HT.weak (ht_kerf nex) fun _ h => h.1) (fun _ h => fresh_args h.1) (St.kerf nex))
    fun a => ?_
  rcases a with ⟨out, pro⟩
  refine HC.bind' (HC.of (ht_qf QM.re' _) (sc_re _)) fun rSub => HC.bind' (HC.of (ht_qf QM.re' _) (sc_re _))
    fun rFol => HC.bind' (hc_emit (ro := [rFol, rSub]) rfl (js_hop fun g h => h) (stab_fresh _) (by simp [trOp])
      (cnt_perm_le (List.Perm.cons _ (List.Perm.swap _ _ _)))) fun o => ?_
  exact HC.conseq (hcl_bin St env.cod p hp hq _ _ _ _) (fun g h => ⟨h.2, ll_ofSure _ _, ll_ofSure _ _⟩)
      (fun _ _ h => h) (fun y => by simp [sarR_ofSure, lazyReg, flattenNeed]) (fun _ _ => Nat.le_refl _)

/-! ## The induction -/

/-- **Single assignment at run level on `PlainN`**, from the walks' counts. -/
theorem sarRun_plainOf (env : CallEnv) (St : SarSteps S Map) : ∀ (nm : Nomm), PlainN nm → ∀ (sup : Option Nomm),
    HRS (Map := Map) (runLC (S := S) env sup nm)
  | Nomm.cons p q, h, sup, goal, region => by
    have ihp := sarRun_plainOf env St p h.1 sup
    have ihq := sarRun_plainOf env St q h.2 sup
    unfold runLC
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
    unfold runLC
    refine HC.ite' _ (hcl_bombL _ _) (HC.bind' (hcl_simpleNextL _) fun nex =>
      HC.ite' _ (HC.pure' (fun g h => h) (fun _ => Nat.le_refl _)) ?_)
    cases hf : Lazy.fromL ax nex.laz with
    | none => exact HC.fail
    | some laz =>
      exact HC.pure' (fun g h => ⟨h.1, (labSteps (S := S) (Map := Map)).fromL (Q := fun n => n < g.bo) hf h.2.1 h.2.2⟩)
        (St.fromL ax _ _ hf)
  | Nomm.n1 k, _, sup, goal, region => by
    unfold runLC
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
    have ih := sarRun_plainOf env St p h sup
    unfold runLC
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
    have ih := sarRun_plainOf env St p h sup
    unfold runLC
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
    have ihp := sarRun_plainOf env St p h.1 sup
    have ihq := sarRun_plainOf env St q h.2 sup
    unfold runLC
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
    unfold runLC
    exact HC.bind' (sarRun_plainOf env St q h.2 (some p) goal region) fun nex =>
      HC.weak (sarRun_plainOf env St p h.1 sup nex.goal region) fun _ h => h
  | Nomm.n10 a v q, h, sup, goal, region => by
    have ihv := sarRun_plainOf env St v h.1 sup
    have ihq := sarRun_plainOf env St q h.2 sup
    unfold runLC
    refine HC.bind' (hcl_simpleNextL _) fun next => HC.bind' (HC.weak (hcl_intoL St _ _) fun g h => h) fun x => ?_
    rcases x with ⟨don, rec, o⟩
    refine HC.bind' (HC.conseq (HC.frame (hcl_pastL env.cod ⟨rec, jmp0 o⟩ v region) (stab_ll don) (sarR don))
      (fun g h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩) (fun _ _ h => h) (sar_comm _ _) (fun _ _ => Nat.le_refl _)) fun nexR => ?_
    exact HC.conseq (hcl_bin St env.cod q ihq ihv don nexR.laz nexR.th region) (fun g h => ⟨h.1.1, h.2, h.1.2⟩)
      (fun _ _ h => h) (sar_comm _ _) (fun _ _ => Nat.le_refl _)
  | Nomm.n2 p q Option.none, h, sup, goal, region => by
    unfold runLC
    exact hcl_callL St env p q sup (sarRun_plainOf env St p h.1 sup) (sarRun_plainOf env St q h.2 sup) goal region
  | Nomm.n2 _ _ (some _), h, _, _, _ => h.elim
  | Nomm.n6 _ _ _, h, _, _, _ => h.elim
  | Nomm.n11s _ _ _, h, _, _, _ => h.elim
  | Nomm.n11d _ _ _ _, h, _, _, _ => h.elim
  | Nomm.n12 _ _, h, _, _, _ => h.elim
  | Nomm.mean _ _ _ _ _, h, _, _, _ => h.elim

/-! ## The top -/

/-- **`TopSAR` on `PlainN`**, from the walks' counts. -/
theorem topSAR_plain_of (St : SarSteps S Map) {env : CallEnv} {nm : Nomm} (hp : PlainN nm) :
    TopSAR S Map env nm := by
  unfold TopSAR
  intro nex g1 h
  obtain ⟨s1, -, c1⟩ := (sarRun_plainOf env St nm hp Option.none CGoalL.done []).sc gen0 nex g1 ats_gen0
    ⟨trivial, trivial⟩ sarSt_gen0 h
  refine sar_sab s1 fun y => ?_
  have h1 := c1 y
  have h2 := fr_le_one (gen0 : Comp.Gen Map).re g1.re y
  rw [sarDc_gen0] at h1
  simp only [sarG, List.count_nil] at h1
  omega

/-- **`TopSAU` on `PlainN`**, from the walks' counts. -/
theorem topSAU_plain_of (St : SarSteps S Map) {env : CallEnv} {nm : Nomm} (hp : PlainN nm) :
    TopSAU S Map env nm := by
  unfold TopSAU
  intro nex g1 g2 o sub h hk
  have R := sarRun_plainOf env St nm hp Option.none CGoalL.done []
  obtain ⟨-, -, F1, -⟩ := R.ht.run gen0 nex g1 ats_gen0 ⟨trivial, trivial⟩ h
  obtain ⟨s1, l1, c1⟩ := R.sc gen0 nex g1 ats_gen0 ⟨trivial, trivial⟩ sarSt_gen0 h
  obtain ⟨s2, l2, c2⟩ := St.kerf nex (fresh_args F1) g1 (o, sub) g2 s1 hk
  refine sar_sab s2 fun y => ?_
  have := c1 y
  have := c2 y
  have := fr_add l1 l2 y
  have := fr_le_one (gen0 : Comp.Gen Map).re g2.re y
  rw [sarDc_gen0] at *
  simp only [sarG, List.count_nil] at *
  omega

/-! ## With the proved fields -/

/-- **The fields of `SarSteps` still open.** -/
structure SarStepsW (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] [MapKeys Map] :
    Prop where
  split : ∀ (nex : NextL S), nex.th.args = [] →
    SCR (Map := Map) (sarR nex.laz) (splitL nex) (fun x => sarR x.1 ++ sarR x.2.1)
  into : ∀ (nex : NextL S) (axe : Nat), nex.th.args = [] →
    SCR (Map := Map) (sarR nex.laz) (intoL nex axe) (fun x => sarR x.1 ++ sarR x.2.1)
  copy : ∀ (first : NextL S) (second : Lazy S), first.th.args = [] → LabUniq first.laz → LabUniq second →
    SCR (Map := Map) (sarR first.laz ++ sarR second) (copyL first second) (fun x => sarR x.laz)
  collapse : ∀ (nex : NextL S), SCR (Map := Map) (sarR nex.laz) (collapseLazyAtomL nex)
    (fun a => match a with | some x => [x.1] | Option.none => [])
  kerf : ∀ (nex : NextL S), nex.th.args = [] → SCR (Map := Map) (sarR nex.laz) (kerf nex) (fun x => [x.2])

theorem sarSteps_of (W : SarStepsW S Map) : SarSteps S Map :=
  ⟨W.split, W.into, W.copy, sar_mede, W.collapse, W.kerf, sar_fromL_field⟩

/-- **`TopSAR` on `PlainN`** from the five open walk counts. -/
theorem topSAR_plainW (W : SarStepsW S Map) {env : CallEnv} {nm : Nomm} (hp : PlainN nm) : TopSAR S Map env nm :=
  topSAR_plain_of (sarSteps_of W) hp

/-- **`TopSAU` on `PlainN`** from the five open walk counts. -/
theorem topSAU_plainW (W : SarStepsW S Map) {env : CallEnv} {nm : Nomm} (hp : PlainN nm) : TopSAU S Map env nm :=
  topSAU_plain_of (sarSteps_of W) hp

end Raw
end SkaModel
end Formalization
