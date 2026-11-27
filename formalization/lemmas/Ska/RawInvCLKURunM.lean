import lemmas.Ska.RawInvCLKURun
import lemmas.Ska.CompDirectM
import lemmas.Glue.GuardCallsB

/-!
# The mid-run count with no state, with direct calls: track G's class

README Gaps 14 (b), track D.  `kuRunM_noSix`: every run of `runLCM env true`
on a nomm with no `%6` (track G's `NoSixC`: direct and indirect calls
included; `%11`, `%12` and `mean` fail in `runLCM`) meets `KURun`
(`RawInvCLKUBase.lean`), from the local steps `KUSteps`, with no
precondition on the state.  The arms are those of `kur_run`
(`RawInvCLKURun.lean`) on `runLCM`; the direct call is `kum_callDM`.

* `kum_crashM`, `kum_monoTryLoop`, `kum_monoTryCall`, `kum_needOrdAllocRegs`:
  `RB` (`re` and `bo` grow).
* `kum_monoBlocks`: the call blocks of `+mono-try-call`, from the goal's
  tree to the fresh register `sub-pes`.
* `kum_bin`: a producer of an `LG` result, `+past`, run p, `+copy`.
* **`kum_callDM`**: the direct call (the drop path and the `monoBlocks`
  path).
* `kum_run`, **`kuRunM_noSix`**.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-! ## The steps of the call blocks -/

theorem kum_crashM {α : Type} : RB (Map := Map) (crashM : CM Map α) :=
  fun g x g' e => by simp [crashM] at e

theorem kumK {α : Type} {P : Comp.Gen Map → Prop} {ri : List Nat} {m : CM Map α} {ro : α → List Nat}
    (h : KUC (Map := Map) ri m ro) : kurT (Map := Map) P ri m (fun _ _ => True) ro :=
  kur_ku h fun _ _ _ _ _ _ => trivial

theorem kumB {α : Type} {P : Comp.Gen Map → Prop} {m : CM Map α} (h : RB (Map := Map) m) (ri : List Nat) :
    kurT (Map := Map) P ri m (fun _ _ => True) (fun _ => ri) :=
  kumK (ku_ofRB h ri)

theorem kum_monoTryLoop (fail : Nat) : ∀ (ned : Need) (r o : Nat), RB (Map := Map) (monoTryLoop fail ned r o)
  | Need.none, r, o => by unfold monoTryLoop; exact rb_pure _
  | Need.this rn, r, o => by unfold monoTryLoop; exact rb_ite _ kum_crashM (rb_emit _)
  | Need.pair h t, r, o => by
    unfold monoTryLoop
    exact rb_bind rb_re fun rt => rb_bind rb_re fun rh => rb_bind (kum_monoTryLoop fail t rt o) fun ot =>
      rb_bind (kum_monoTryLoop fail h rh ot) fun oh => rb_bind (rb_emit _) fun os => rb_emit _
  | Need.both rn h t, r, o => by
    unfold monoTryLoop
    exact rb_bind rb_re fun rt => rb_bind rb_re fun rh => rb_bind (kum_monoTryLoop fail t rt o) fun ot =>
      rb_bind (kum_monoTryLoop fail h rh ot) fun oh => rb_ite _ kum_crashM (rb_bind (rb_emit _) fun os => rb_emit _)

theorem kum_monoTryCall (ned : Need) (opt sub pes : Nat) : RB (Map := Map) (monoTryCall ned opt sub pes) :=
  kum_monoTryLoop pes ned sub opt

theorem kum_needOrdAllocRegs : ∀ (bNed : NeedOrd), RB (Map := Map) (needOrdAllocRegs bNed)
  | NeedOrd.none => by unfold needOrdAllocRegs; exact rb_pure _
  | NeedOrd.this => by unfold needOrdAllocRegs; exact rb_bind rb_re fun r => rb_pure _
  | NeedOrd.pair p q => by
    unfold needOrdAllocRegs
    exact rb_bind (kum_needOrdAllocRegs p) fun h => rb_bind (kum_needOrdAllocRegs q) fun t =>
      rb_ite _ kum_crashM (rb_pure _)
  | NeedOrd.both p q => by
    unfold needOrdAllocRegs
    exact rb_bind rb_re fun r => rb_bind (kum_needOrdAllocRegs p) fun h => rb_bind (kum_needOrdAllocRegs q) fun t =>
      rb_ite _ kum_crashM (rb_pure _)

theorem kum_lg_up {goal : CGoalL S} {g g' : Comp.Gen Map} (h : LG goal g) (k : g.bo ≤ g'.bo) : LG goal g' := by
  cases goal with
  | next laz th => exact kur_ll_up (l := laz) g g' k h
  | pick _ _ => trivial
  | done => trivial

/-- **The call blocks**: the goal's tree is consumed by `+kerf`, the result
is the fresh register `sub-pes`. -/
theorem kum_monoBlocks (St : KUSteps S Map) (b : Bell) (subNed : Need) (goal : CGoalL S) :
    kurT (Map := Map) (LG goal) (sarG goal) (monoBlocks b subNed goal) (fun _ _ => True) (fun x => [x.1]) := by
  unfold monoBlocks
  cases goal
  case done =>
    refine kur_bind (kumK (ku_re _)) fun subPes => ?_
    refine kur_bind (kumB (rb_emit _) _) fun opt => ?_
    refine kur_bind (kumB (rb_emit _) _) fun pes => ?_
    refine kur_bind (kumB (kum_monoTryCall _ _ _ _) _) fun o => ?_
    exact kur_pure (fun _ _ => trivial) fun y => by simp [sarG, List.count_append]
  all_goals
    refine kur_bind (kur_simpleNextL _) fun nex => ?_
    refine kur_bind (kur_rb (Q := fun _ _ => True) (ro := fun _ => []) (St.kerf nex) (fun _ y => kur_cnt0 _ y)
      fun _ _ _ _ _ _ => trivial) fun a => ?_
    rcases a with ⟨out, pro⟩
    refine kur_bind (kumB rb_re _) fun merged => ?_
    refine kur_bind (kumK (ku_re _)) fun subPes => ?_
    refine kur_bind (kumB (rb_emit _) _) fun merge => ?_
    refine kur_bind (kumB rb_re _) fun proOpt => ?_
    refine kur_bind (kumB rb_re _) fun proPes => ?_
    refine kur_bind (kumB (rb_emit _) _) fun opt => ?_
    refine kur_bind (kumB (rb_emit _) _) fun pes => ?_
    refine kur_bind (kumB (kum_monoTryCall _ _ _ _) _) fun o => ?_
    exact kur_pure (fun _ _ => trivial) fun y => by simp [List.count_append]

/-! ## The direct call -/

/-- **A producer of an `LG` result, `+past`, run p, `+copy`.** -/
theorem kum_bin (St : KUSteps S Map) (cod : Bell → Option Bool) {rp : CGoalL S → List Nat → CM Map (NextL S)}
    (p : Nomm) (hp : kurR (Map := Map) rp) {P : Comp.Gen Map → Prop} {ri : List Nat} {m : CM Map (NextL S)}
    (hm : kurT (Map := Map) P ri m (fun x g => LG x.goal g) (fun x => sarR x.laz)) (lp : Lazy S)
    (region : List Nat) :
    kurT (Map := Map) (fun g => P g ∧ LL lp g) (ri ++ sarR lp) (do
      let nex2 ← m
      let nex2 ← pastL cod nex2 p region
      let nex1 ← rp (CGoalL.next lp nex2.th) region
      copyL nex1 nex2.laz : CM Map (NextL S)) (fun nex g => LG nex.goal g) (fun nex => sarR nex.laz) := by
  refine kur_bind (kur_frame hm (sarR lp) (F := LL lp) kur_ll_up) fun nex2 => ?_
  refine kur_bind (kur_conseq (kur_frame (kur_pastL St cod nex2 p region) (sarR lp) (F := LL lp) kur_ll_up)
    (fun g h => h) (fun _ _ h => h) (fun y => Nat.le_refl _) (fun _ _ => Nat.le_refl _)) fun nex2' => ?_
  refine kur_bind (kur_conseq (kur_frame (hp (CGoalL.next lp nex2'.th) region) (sarR nex2'.laz)
    (F := LL nex2'.laz) kur_ll_up) (fun g h => ⟨h.2, h.1⟩) (fun _ _ h => h) (fun y => by
      simp only [sarG_next, List.count_append]; omega) (fun _ _ => Nat.le_refl _)) fun nex1 => ?_
  exact kur_copyL St nex1 nex2'.laz

/-- The run of the formula from a `bunt` goal, or its skip. -/
theorem kum_fol {rq : CGoalL S → List Nat → CM Map (NextL S)} (hq : kurR (Map := Map) rq) (q : Nomm) (th : Jmp)
    (region : List Nat) :
    kurT (Map := Map) (fun _ => True) [] (if safeFolFol q then pure ⟨ofSure Sure.bunt, th⟩
      else rq (CGoalL.next (ofSure Sure.bunt) th) region : CM Map (NextL S))
      (fun x g => LG x.goal g) (fun x => sarR x.laz) := by
  refine kur_ite _ (kur_pure (fun g _ => lg_ofSure _ _ _) fun y => ?_) ?_
  · show (sarR (ofSure (Sure.bunt : Sure S))).count y ≤ _
    rw [kur_sarR_bunt]; simp
  · refine kur_conseq (hq (CGoalL.next (ofSure Sure.bunt) th) region) (fun g _ => lg_ofSure _ _ _)
      (fun _ _ h => h) (fun y => ?_) (fun _ _ => Nat.le_refl _)
    rw [sarG_next, kur_sarR_bunt]; simp

/-- **The direct call with `mono` `&`.** -/
theorem kum_callDM (St : KUSteps S Map) (env : CallEnv) {rp rq : CGoalL S → List Nat → CM Map (NextL S)}
    (p q : Nomm) (b : Bell) (key : Option Noun) (hp : kurR (Map := Map) rp) (hq : kurR (Map := Map) rq)
    (goal : CGoalL S) (region : List Nat) :
    kurT (Map := Map) (LG goal) (sarG goal) (callDM env rp rq p q b key goal region)
      (fun nex g => LG nex.goal g) (fun nex => sarR nex.laz) := by
  unfold callDM
  split
  next _ laz th =>
    split
    next hc =>
      dsimp only
      exact kur_conseq (kum_bin St env.cod p hp (kum_fol hq q th region) (ofSure Sure.bunt) region)
        (fun g _ => ⟨trivial, ll_ofSure _ _⟩) (fun _ _ h => h) (fun y => by rw [kur_sarR_bunt]; simp)
        (fun _ _ => Nat.le_refl _)
    next hc =>
      dsimp only
      split
      · rename_i bNed _ _
        refine kur_bind (kur_ku (ku_ofRB (kum_needOrdAllocRegs bNed) _) fun g x g' h e k => kum_lg_up h k)
          fun subNed => ?_
        refine kur_bind (kum_monoBlocks St b subNed _) fun a => ?_
        rcases a with ⟨subPes, callBlock⟩
        exact kur_conseq (kum_bin St env.cod p hp (kum_fol hq q (jmp0 callBlock) region)
          (ofSure (lazyReg subPes)) region) (fun g _ => ⟨trivial, ll_ofSure _ _⟩) (fun _ _ h => h)
          (fun y => by rw [kur_sarR_reg]; simp) (fun _ _ => Nat.le_refl _)
      · exact kur_fail
  next hne =>
    dsimp only
    split
    · rename_i bNed _ _
      refine kur_bind (kur_ku (ku_ofRB (kum_needOrdAllocRegs bNed) _) fun g x g' h e k => kum_lg_up h k)
        fun subNed => ?_
      refine kur_bind (kum_monoBlocks St b subNed _) fun a => ?_
      rcases a with ⟨subPes, callBlock⟩
      exact kur_conseq (kum_bin St env.cod p hp (kum_fol hq q (jmp0 callBlock) region)
        (ofSure (lazyReg subPes)) region) (fun g _ => ⟨trivial, ll_ofSure _ _⟩) (fun _ _ h => h)
        (fun y => by rw [kur_sarR_reg]; simp) (fun _ _ => Nat.le_refl _)
    · exact kur_fail

/-! ## The induction on `runLCM` -/

theorem kum_run (env : CallEnv) (St : KUSteps S Map) : ∀ (nm : Nomm), Glue.NoSixC nm → ∀ (sup : Option Nomm),
    kurR (Map := Map) (runLCM (S := S) env true sup nm)
  | Nomm.cons p q, h, sup, goal, region => by
    have ihp := kum_run env St p h.1 sup
    have ihq := kum_run env St q h.2 sup
    unfold runLCM
    refine kur_bind (R := fun (goal' : CGoalL S) (g : Comp.Gen Map) => LG goal' g) (r1 := fun goal' => sarG goal')
      ?_ fun goal' => ?_
    · cases goal with
      | done =>
        refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_re _) fun _ _ _ _ _ _ => trivial) fun r => ?_
        refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_emit _ _) fun _ _ _ _ _ _ => trivial) fun o => ?_
        refine kur_pure (fun g _ => lg_ofSure _ _ _) fun y => ?_
        rw [sarG_next, kur_sarR_reg]; simp
      | next laz th => exact kur_pure (fun g h => h) (fun y => Nat.le_refl _)
      | pick z o => exact kur_pure (fun g h => h) (fun y => Nat.le_refl _)
    · cases goal' with
      | pick z o =>
        refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_emit _ _) fun _ _ _ _ _ _ => trivial) fun o => ?_
        refine kur_conseq (kur_bin St env.cod p ihp ihq _ _ _ region) (fun g _ => ⟨ll_ofSure _ _, ll_ofSure _ _⟩)
          (fun _ _ h => h) (fun y => ?_) (fun _ _ => Nat.le_refl _)
        rw [kur_sarR_bunt]; exact kur_cnt0 _ y
      | done => exact kur_fail
      | next laz th =>
        refine kur_bind (kur_splitL St ⟨laz, th⟩) fun a => ?_
        rcases a with ⟨hed, tel, o⟩
        refine kur_bind (kur_frame (kur_pastL St env.cod ⟨hed, jmp0 o⟩ q region) (sarR tel) (F := LL tel)
          kur_ll_up) fun nexh => ?_
        exact kur_conseq (kur_bin St env.cod p ihp ihq tel nexh.laz nexh.th region) (fun g h => ⟨h.2, h.1⟩)
          (fun _ _ h => h) (fun y => by simp only [List.count_append]; omega) (fun _ _ => Nat.le_refl _)
  | Nomm.n0 ax, _, sup, goal, region => by
    unfold runLCM
    refine kur_ite _ (kur_bombL _ _) (kur_bind (kur_simpleNextL _) fun nex => kur_ite _
      (kur_pure (fun g h => h) (fun y => Nat.le_refl _)) ?_)
    cases hf : Lazy.fromL ax nex.laz with
    | none => exact kur_fail
    | some laz =>
      refine kur_pure (fun g h => lab_fromL (Q := fun n => n < g.bo) hf h.1 h.2) fun y => ?_
      rw [sar_fromL hf]; exact Nat.le_refl _
  | Nomm.n1 k, _, sup, goal, region => by
    unfold runLCM
    cases goal with
    | done =>
      refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_re _) fun _ _ _ _ _ _ => trivial) fun r => ?_
      refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_emit _ _) fun _ _ _ _ _ _ => trivial) fun o => ?_
      refine kur_pure (fun g _ => lg_ofSure _ _ _) fun y => ?_
      rw [kur_sarR_bunt]; exact kur_cnt0 _ y
    | pick z o =>
      refine kur_ite _ (kur_pure (fun g _ => lg_ofSure _ _ _) fun y => ?_)
        (kur_ite _ (kur_pure (fun g _ => lg_ofSure _ _ _) fun y => ?_) (kur_bombL _ _))
      · rw [kur_sarR_bunt]; exact kur_cnt0 _ y
      · rw [kur_sarR_bunt]; exact kur_cnt0 _ y
    | next laz th =>
      refine kur_bind (kur_rb (Q := fun _ _ => True) (ro := fun _ => []) (St.mede th k laz) (fun _ y => kur_cnt0 _ y)
        fun _ _ _ _ _ _ => trivial) fun o => ?_
      refine kur_pure (fun g _ => lg_ofSure _ _ _) fun y => ?_
      rw [kur_sarR_bunt]; exact Nat.le_refl _
  | Nomm.n3 p, h, sup, goal, region => by
    have ih := kum_run env St p h sup
    unfold runLCM
    cases goal with
    | pick z o =>
      refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_re _) fun _ _ _ _ _ _ => trivial) fun r => ?_
      exact kur_tail ih _ (fun _ => lazyReg r) region fun _ y => by simp only [lazyReg, flattenNeed, List.count_append]; omega
    | done =>
      refine kur_bind (kur_rb (Q := fun _ _ => True) (ro := fun _ => []) St.doneBlocks (fun _ y => kur_cnt0 _ y)
        fun _ _ _ _ _ _ => trivial) fun a => ?_
      rcases a with ⟨o0, o1⟩
      refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_re _) fun _ _ _ _ _ _ => trivial) fun r => ?_
      exact kur_tail ih _ (fun _ => lazyReg r) region fun _ y => by simp only [lazyReg, flattenNeed, List.count_append]; omega
    | next laz th =>
      refine kur_ite _ (ih _ _) (kur_bind (kur_rb (Q := fun _ _ => True) (ro := fun _ => [])
        (St.collapse ⟨laz, th⟩) (fun _ y => kur_cnt0 _ y) fun _ _ _ _ _ _ => trivial) fun a => ?_)
      rcases a with _ | ⟨r, o⟩
      · exact kur_fail
      · refine kur_bind (kur_rb (Q := fun _ _ => True) (ro := fun _ => []) (St.forl r o) (fun _ y => kur_cnt0 _ y)
          fun _ _ _ _ _ _ => trivial) fun x => ?_
        rcases x with ⟨z, o'⟩
        refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_re _) fun _ _ _ _ _ _ => trivial) fun r' => ?_
        exact kur_tail ih _ (fun _ => lazyReg r') region fun _ y => by simp only [lazyReg, flattenNeed, List.count_append]; omega
  | Nomm.n4 p, h, sup, goal, region => by
    have ih := kum_run env St p h sup
    unfold runLCM
    cases goal with
    | done =>
      refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_re _) fun _ _ _ _ _ _ => trivial) fun _ => ?_
      refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_re _) fun _ _ _ _ _ _ => trivial) fun arg => ?_
      exact kur_tail ih _ (fun _ => lazyReg arg) region fun _ y => by simp only [lazyReg, flattenNeed, List.count_append]; omega
    | pick z o =>
      refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_re _) fun _ _ _ _ _ _ => trivial) fun _ => ?_
      refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_re _) fun _ _ _ _ _ _ => trivial) fun arg => ?_
      exact kur_tail ih _ (fun _ => lazyReg arg) region fun _ y => by simp only [lazyReg, flattenNeed, List.count_append]; omega
    | next laz th =>
      refine kur_bind (kur_rb (Q := fun _ _ => True) (ro := fun _ => []) (St.collapse ⟨laz, th⟩)
        (fun _ y => kur_cnt0 _ y) fun _ _ _ _ _ _ => trivial) fun a => ?_
      refine kur_bind (R := fun _ _ => True) (r1 := fun _ => []) ?_ fun x => ?_
      · cases a with
        | some x => exact kur_pure (fun _ _ => trivial) (fun y => Nat.le_refl _)
        | none =>
          refine kur_bind (kur_ku (Q := fun _ _ => True) (ro := fun _ => []) (ku_mono (ku_re []) (fun y => Nat.le_refl _)
            (fun _ y => by simp)) fun _ _ _ _ _ _ => trivial) fun r => ?_
          exact kur_ite _ (kur_pure (fun _ _ => trivial) (fun y => Nat.le_refl _)) kur_fail
      · rcases x with ⟨pro, th'⟩
        refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_re _) fun _ _ _ _ _ _ => trivial) fun arg => ?_
        exact kur_tail ih _ (fun _ => lazyReg arg) region fun _ y => by simp only [lazyReg, flattenNeed, List.count_append]; omega
  | Nomm.n5 p q, h, sup, goal, region => by
    have ihp := kum_run env St p h.1 sup
    have ihq := kum_run env St q h.2 sup
    unfold runLCM
    refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_re _) fun _ _ _ _ _ _ => trivial) fun rp => ?_
    refine kur_bind (kur_ku (Q := fun _ _ => True) (ku_re _) fun _ _ _ _ _ _ => trivial) fun rq => ?_
    refine kur_bind (R := fun _ _ => True) (r1 := fun _ => [rq] ++ [rp]) ?_ fun o => ?_
    · have hc : ∀ (x : Nat) y, ([rq] ++ [rp]).count y ≤ (sarG goal ++ [rp] ++ [rq]).count y := fun _ y => by
        simp only [List.count_append]; omega
      cases goal with
      | pick z o => exact kur_rb (rb_emit _) hc fun _ _ _ _ _ _ => trivial
      | done =>
        exact kur_rb (rb_bind St.doneBlocks fun a => match a with | (o0, o1) => rb_emit _) hc
          fun _ _ _ _ _ _ => trivial
      | next laz th =>
        refine kur_rb (rb_bind (St.collapse ⟨laz, th⟩) fun a => ?_) hc fun _ _ _ _ _ _ => trivial
        cases a with
        | none => exact rb_ite _ (rb_emit _) rb_fail
        | some x =>
          rcases x with ⟨r, o⟩
          exact rb_bind (St.forl r o) fun x => match x with | (z, o') => rb_emit _
    · refine kur_conseq (kur_bin St env.cod p ihp ihq _ _ _ region) (fun g _ => ⟨ll_ofSure _ _, ll_ofSure _ _⟩)
        (fun _ _ h => h) (fun y => ?_) (fun _ _ => Nat.le_refl _)
      rw [kur_sarR_reg, kur_sarR_reg]; exact Nat.le_refl _
  | Nomm.n7 p q, h, sup, goal, region => by
    unfold runLCM
    exact kur_bind (kum_run env St q h.2 (some p) goal region) fun nex =>
      kur_conseq (kum_run env St p h.1 sup nex.goal region) (fun _ h => h) (fun _ _ h => h)
        (fun y => Nat.le_refl _) (fun _ _ => Nat.le_refl _)
  | Nomm.n10 a v q, h, sup, goal, region => by
    have ihv := kum_run env St v h.1 sup
    have ihq := kum_run env St q h.2 sup
    unfold runLCM
    refine kur_bind (kur_simpleNextL _) fun next => ?_
    refine kur_bind (kur_conseq (kur_intoL St next a) (fun _ h => h) (fun _ _ h => h) (fun y => Nat.le_refl _)
      (fun _ _ => Nat.le_refl _)) fun x => ?_
    rcases x with ⟨don, rec, o⟩
    refine kur_bind (kur_conseq (kur_frame (kur_pastL St env.cod ⟨rec, jmp0 o⟩ v region) (sarR don) (F := LL don)
      kur_ll_up) (fun g h => ⟨h.2, h.1⟩) (fun _ _ h => h) (fun y => by simp only [List.count_append]; omega)
      (fun _ _ => Nat.le_refl _)) fun nexR => ?_
    exact kur_conseq (kur_bin St env.cod q ihq ihv don nexR.laz nexR.th region) (fun g h => ⟨h.2, h.1⟩)
      (fun _ _ h => h) (fun y => by simp only [List.count_append]; omega) (fun _ _ => Nat.le_refl _)
  | Nomm.n2 p q info, h, sup, goal, region => by
    unfold runLCM
    cases info with
    | none =>
      rw [callLM_none]
      exact kur_callL St env p q sup (kum_run env St p h.1 sup) (kum_run env St q h.2 sup) goal region
    | some bk =>
      obtain ⟨b, key⟩ := bk
      exact kum_callDM St env p q b key (kum_run env St p h.1 sup) (kum_run env St q h.2 sup) goal region
  | Nomm.n6 _ _ _, h, _, _, _ => h.elim
  | Nomm.n11s _ _ _, _, _, _, _ => by simp only [runLCM]; exact kur_fail
  | Nomm.n11d _ _ _ _, _, _, _, _ => by simp only [runLCM]; exact kur_fail
  | Nomm.n12 _ _, _, _, _, _ => by simp only [runLCM]; exact kur_fail
  | Nomm.mean _ _ _ _ _, _, _, _, _ => by simp only [runLCM]; exact kur_fail

/-- **Every run of `runLCM env true` on a nomm with no `%6` meets `KURun`**
(direct and indirect calls included), from the local steps `KUSteps`, with
no precondition on the state. -/
theorem kuRunM_noSix (env : CallEnv) (St : KUSteps S Map) : ∀ (nm : Nomm), Glue.NoSixC nm →
    ∀ (sup : Option Nomm), KURun (runLCM (S := S) (Map := Map) env true sup nm) :=
  fun nm h sup => kur_toR (kum_run env St nm h sup)

end Raw
end SkaModel
end Formalization
