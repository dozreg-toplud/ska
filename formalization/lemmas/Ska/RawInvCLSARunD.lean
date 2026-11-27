import lemmas.Ska.RawInvCLSARun
import lemmas.Ska.RawInvCLSACountSplit
import lemmas.Ska.RawInvCLSACountInto
import lemmas.Ska.RawInvCLSACountK
import lemmas.Ska.RawInvCLSACountCopy
import lemmas.Ska.RawInvCLTopU
import lemmas.Ska.RawInvCLPlainD
import lemmas.Ska.CompRunLCM
import lemmas.Ska.CompDirectMEq

/-!
# Single assignment with direct calls: the count on `runLCM` over `PlainD`

README Gaps 14 (b), track D.  The definition count `HRS` of
`RawInvCLSARun.lean` (`HRL` with the linear count of definitions) for the
runs of `runLCM env true` on `PlainD` (`PlainN` with direct calls), whose
`%2` with a bell is `callDM` (`+mono-try-call`).  The arms are those of
`sarRun_plainOf`, with one new arm:

* `ksd_steps`: `SarSteps` from the proved walk counts.
* `ksd_needOrd`: `+need-ord-alloc-regs` adds its fresh registers to the
  count list.
* `ksd_loop`: `+mono-try-call`'s loop defines every register of the callee's
  need once (`mov r rn`) and its fresh `rh`/`rt` once (`hed`/`tal`); every
  block it emits has no parameter and jumps `Fresh` (down).
* `ksd_monoBlocks`: the call blocks (`%done`: `jmp`, `jsp`; otherwise
  `+simple-next`, `+kerf`, `merge` with the parameter `[merged]` and
  `mov merged pro`, `opt` with `cal` and the argument `proOpt` it defines,
  `pes` with `csl` and `proPes`), then the loop.
* `ksd_fol`, `ksd_bin` (a producer, `+past`, run p, `+copy`),
  **`ksd_callDM`**.
* **`sarRunM_plainD`**: `HRS (runLCM env true sup nm)` on `PlainD`.
* `TopSARM`, `TopSAUM`: `TopSAR`, `TopSAU` with `runLCM env true`;
  **`topSAR_plainD`**, **`topSAU_plainD`**.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map] [MapKeys Map]

/-- **The walks' counts, all proved.** -/
theorem ksd_steps : SarSteps S Map :=
  sarSteps_of ⟨scsp_split, scit_into, sccp_copy, sccl_collapse, sckf_kerf⟩

/-! ## `+need-ord-alloc-regs` -/

theorem ksd_needOrd {P : Comp.Gen Map → Prop} (hP : Stab P) : ∀ (n : NeedOrd) (ri : List Nat),
    HC P ri (needOrdAllocRegs n : CM Map Need) (fun _ => P) (fun x => ri ++ flattenNeed x)
  | NeedOrd.none, ri => by
    unfold needOrdAllocRegs
    exact HC.pure' (fun g h => h) (fun y => by simp [flattenNeed])
  | NeedOrd.this, ri => by
    unfold needOrdAllocRegs
    exact HC.bind' (hc_re hP ri) fun r => HC.pure' (fun g h => h) (fun y => by simp [flattenNeed])
  | NeedOrd.pair p q, ri => by
    unfold needOrdAllocRegs
    refine HC.bind' (ksd_needOrd hP p ri) fun h => HC.bind' (ksd_needOrd hP q (ri ++ flattenNeed h)) fun t => ?_
    exact HC.ite' _ HC.fail (HC.pure' (fun g h => h) (fun y => by
      simp only [flattenNeed, List.count_append]; omega))
  | NeedOrd.both p q, ri => by
    unfold needOrdAllocRegs
    refine HC.bind' (hc_re hP ri) fun r => HC.bind' (ksd_needOrd hP p (ri ++ [r])) fun h =>
      HC.bind' (ksd_needOrd hP q (ri ++ [r] ++ flattenNeed h)) fun t => ?_
    refine HC.ite' _ HC.fail (HC.pure' (fun g h => h) (fun y => ?_))
    show (ri ++ ([r] ++ (flattenNeed h ++ flattenNeed t))).count y ≤ _
    simp only [List.count_append]; omega

/-! ## `+mono-try-call` -/

theorem ksd_cons (a : Nat) (l : List Nat) (y : Nat) : (a :: l).count y = [a].count y + l.count y := by
  rw [← List.singleton_append, List.count_append]

/-- **The loop of `+mono-try-call`**: it uses up the callee's need (each of
its registers is defined once) and keeps the rest `ri`; from `Fresh` jumps
to `o` and to the pessimistic call `fail`, its block is `Fresh`. -/
theorem ksd_loop (fail : Nat) : ∀ (ned : Need) (r o : Nat) (ri : List Nat),
    HC (fun g => Fresh g (jmp0 o) ∧ Fresh g (jmp0 fail)) (flattenNeed ned ++ ri)
      (monoTryLoop fail ned r o : CM Map Nat) (fun o' g => Fresh g (jmp0 o') ∧ Fresh g (jmp0 fail)) (fun _ => ri)
  | Need.none, r, o, ri => by
    unfold monoTryLoop
    exact HC.pure' (fun g h => h) (fun y => by simp [flattenNeed])
  | Need.this rn, r, o, ri => by
    unfold monoTryLoop
    refine HC.ite' _ HC.fail ?_
    exact HC.conseq (hc_emit (P := fun g => Fresh g (jmp0 o) ∧ Fresh g (jmp0 fail)) (ro := ri) rfl
      (js_hop fun g h => h.1) (stab_and (stab_fresh _) (stab_fresh _)) (by simp [trOp])
      (cnt_app_le (by simp [blockDefs, aliasDst, flattenNeed])))
      (fun g h => h) (fun _ _ h => ⟨h.2, h.1.2⟩) (fun _ => Nat.le_refl _) (fun _ _ => Nat.le_refl _)
  | Need.pair h t, r, o, ri => by
    unfold monoTryLoop
    have hP := stab_and (stab_fresh (Map := Map) (jmp0 o)) (stab_fresh (jmp0 fail))
    refine HC.bind' (hc_re hP _) fun rt => HC.bind' (hc_re hP _) fun rh => ?_
    refine HC.bind' (HC.conseq (ksd_loop fail t rt o (flattenNeed h ++ ri ++ [rh] ++ [rt])) (fun g h => h)
      (fun _ _ h => h) (fun y => by simp only [flattenNeed, List.count_append]; omega)
      (fun _ _ => Nat.le_refl _)) fun ot => ?_
    refine HC.bind' (HC.conseq (ksd_loop fail h rh ot (ri ++ [rh] ++ [rt])) (fun g h => h)
      (fun _ _ h => h) (fun y => by simp only [List.count_append]; omega)
      (fun _ _ => Nat.le_refl _)) fun oh => ?_
    refine HC.bind' (hc_emit (P := fun g => Fresh g (jmp0 oh) ∧ Fresh g (jmp0 fail)) (ro := ri) rfl
      (js_hop fun g h => h.1) (stab_and (stab_fresh _) (stab_fresh _)) (by simp [trOp]) (fun y => by
        show List.count y ([rh] ++ [rt]) + _ ≤ _
        simp only [List.count_append]; omega)) fun os => ?_
    exact HC.conseq (hc_emit (P := fun g => Fresh g (jmp0 os) ∧ Fresh g (jmp0 fail)) (ro := ri) rfl
      (js_two rfl fun g h => ⟨h.1, h.2⟩) (stab_and (stab_fresh _) (stab_fresh _)) (by simp)
      (fun y => by show List.count y [] + _ ≤ _; simp))
      (fun g h => ⟨h.2, h.1.2⟩) (fun _ _ h => ⟨h.2, h.1.2⟩) (fun _ => Nat.le_refl _) (fun _ _ => Nat.le_refl _)
  | Need.both rn h t, r, o, ri => by
    unfold monoTryLoop
    have hP := stab_and (stab_fresh (Map := Map) (jmp0 o)) (stab_fresh (jmp0 fail))
    refine HC.bind' (hc_re hP _) fun rt => HC.bind' (hc_re hP _) fun rh => ?_
    refine HC.bind' (HC.conseq (ksd_loop fail t rt o (flattenNeed h ++ ri ++ [rh] ++ [rt] ++ [rn])) (fun g h => h)
      (fun _ _ h => h) (fun y => by
        show _ ≤ List.count y ((rn :: (flattenNeed h ++ flattenNeed t)) ++ ri ++ [rt] ++ [rh])
        rw [List.cons_append, List.cons_append, List.cons_append, ksd_cons]
        simp only [List.count_append]; omega)
      (fun _ _ => Nat.le_refl _)) fun ot => ?_
    refine HC.bind' (HC.conseq (ksd_loop fail h rh ot (ri ++ [rh] ++ [rt] ++ [rn])) (fun g h => h)
      (fun _ _ h => h) (fun y => by simp only [List.count_append]; omega)
      (fun _ _ => Nat.le_refl _)) fun oh => ?_
    refine HC.ite' _ HC.fail ?_
    refine HC.bind' (hc_emit (P := fun g => Fresh g (jmp0 oh) ∧ Fresh g (jmp0 fail)) (ro := ri) rfl
      (js_hop fun g h => h.1) (stab_and (stab_fresh _) (stab_fresh _)) (by simp [trOp]) (fun y => by
        show List.count y ([rh] ++ [rt] ++ [rn]) + _ ≤ _
        simp only [List.count_append]; omega)) fun os => ?_
    exact HC.conseq (hc_emit (P := fun g => Fresh g (jmp0 os) ∧ Fresh g (jmp0 fail)) (ro := ri) rfl
      (js_two rfl fun g h => ⟨h.1, h.2⟩) (stab_and (stab_fresh _) (stab_fresh _)) (by simp)
      (fun y => by show List.count y [] + _ ≤ _; simp))
      (fun g h => ⟨h.2, h.1.2⟩) (fun _ _ h => ⟨h.2, h.1.2⟩) (fun _ => Nat.le_refl _) (fun _ _ => Nat.le_refl _)

/-! ## The call blocks -/

/-- A block whose one jump is a hop to `merge` with one argument. -/
theorem ksd_batc_merge {g : Comp.Gen Map} {merge x m : Nat} {body : List Pole} (h : HasPar merge [m] g) :
    BATC g.blocks ⟨[], body, Termin.hop ⟨[some x], merge⟩⟩ := by
  refine ⟨fun j hj => ?_, fun ht => by simp [Compiler.twoWay] at ht⟩
  simp only [finJumps, List.mem_cons, List.not_mem_nil, or_false] at hj
  subst hj
  obtain ⟨b2, h2, p2⟩ := h
  exact ⟨b2, h2, by rw [p2]; rfl⟩

/-- **The call blocks of a direct call**, for a goal that is not `%done`:
`+simple-next`, `+kerf`, `merge`, `opt`, `pes`, the loop. -/
theorem ksd_monoBody (St : SarSteps S Map) (b : Bell) (subNed : Need) (goal : CGoalL S) :
    HC (fun g => GFL (Map := Map) goal g ∧ LG goal g) (sarG goal ++ flattenNeed subNed) (do
      let nex ← simpleNextL goal
      let (out, pro) ← kerf nex
      let merged ← re
      let subPes ← re
      let merge ← emit ⟨[merged], [Pole.mov merged pro], Termin.hop (jmp0 out)⟩
      let proOpt ← re
      let proPes ← re
      let opt ← emit ⟨[], [Pole.cal b (flattenNeed subNed) proOpt], Termin.hop ⟨[some proOpt], merge⟩⟩
      let pes ← emit ⟨[], [Pole.csl b subPes proPes], Termin.hop ⟨[some proPes], merge⟩⟩
      let o ← monoTryCall subNed opt subPes pes
      pure (subPes, o) : CM Map (Nat × Nat)) (fun x g => Fresh g (jmp0 x.2)) (fun x => [x.1]) := by
  refine HC.bind' (HC.weak (HC.frame (hcl_simpleNextL goal) stab_true (flattenNeed subNed))
    fun g h => ⟨h, trivial⟩) fun nex => ?_
  refine HC.bind' (HC.frame (HC.ofC (HT.weak (ht_kerf nex) fun _ h => h.1) (fun _ h => fresh_args h.1)
    (St.kerf nex)) stab_true (flattenNeed subNed)) fun a => ?_
  rcases a with ⟨out, pro⟩
  have h1 := stab_and (stab_fresh (Map := Map) (jmp0 out)) stab_true
  refine HC.bind' (hc_re h1 _) fun merged => HC.bind' (hc_re h1 _) fun subPes => ?_
  refine HC.bind' (HC.of (HT.emit' (P := fun g => Fresh g (jmp0 out) ∧ True)
    (fun g h => batc_fresh (js_hop (P := fun g => Fresh g (jmp0 out) ∧ True) (fun g h => h.1) g h)) h1)
    (sc_emit (ro := flattenNeed subNed ++ [subPes]) (by simp [trOp]) (by simp [getJmps, jmp0]) (fun y => by
      show List.count y ([merged] ++ [pro]) + _ ≤ _
      simp only [List.count_append]; omega))) fun merge => ?_
  have h2 := stab_and h1 (stab_hasPar (Map := Map) merge [merged])
  refine HC.bind' (hc_re h2 _) fun proOpt => HC.bind' (hc_re h2 _) fun proPes => ?_
  refine HC.bind' (HC.of (HT.emit' (fun g h => ksd_batc_merge h.2) h2)
    (sc_emit (ro := flattenNeed subNed ++ [subPes] ++ [proPes]) (by simp [trOp])
      (by simp [getJmps, blockDefs, aliasDst]) (fun y => by
      show List.count y [proOpt] + _ ≤ _
      simp only [List.count_append]; omega))) fun opt => ?_
  have h3 := stab_and h2 (stab_hasPar (Map := Map) opt [])
  refine HC.bind' (HC.of (HT.emit' (fun g h => ksd_batc_merge h.1.2) h3)
    (sc_emit (ro := flattenNeed subNed ++ [subPes]) (by simp [trOp])
      (by simp [getJmps, blockDefs, aliasDst]) (fun y => by
      show List.count y [proPes] + _ ≤ _
      simp only [List.count_append]; omega))) fun pes => ?_
  refine HC.bind' (HC.weak (ksd_loop pes subNed subPes opt [subPes])
    fun g h => ⟨fresh_of_hasPar h.1.2, fresh_of_hasPar h.2⟩) fun o => ?_
  exact HC.pure' (fun g h => h.1) (fun y => Nat.le_refl _)

/-- **The call blocks with `mono` `&`.** -/
theorem ksd_monoBlocks (St : SarSteps S Map) (b : Bell) (subNed : Need) (goal : CGoalL S) :
    HC (fun g => GFL (Map := Map) goal g ∧ LG goal g) (sarG goal ++ flattenNeed subNed)
      (monoBlocks b subNed goal : CM Map (Nat × Nat)) (fun x g => Fresh g (jmp0 x.2)) (fun x => [x.1]) := by
  unfold monoBlocks
  cases goal
  case done =>
    refine HC.weak (P := fun _ => True) ?_ (fun _ _ => trivial)
    refine HC.bind' (hc_re stab_true _) fun subPes => ?_
    refine HC.bind' (hc_emit (P := fun _ => True) rfl (js_nil rfl) stab_true (by simp)
      (ro := sarG (CGoalL.done : CGoalL S) ++ flattenNeed subNed ++ [subPes])
      (fun y => by show List.count y [] + _ ≤ _; simp)) fun opt => ?_
    refine HC.bind' (hc_emit (P := fun g => True ∧ Fresh g (jmp0 opt)) rfl (js_nil rfl)
      (stab_and stab_true (stab_fresh _)) (by simp)
      (ro := sarG (CGoalL.done : CGoalL S) ++ flattenNeed subNed ++ [subPes])
      (fun y => by show List.count y [] + _ ≤ _; simp)) fun pes => ?_
    refine HC.bind' (HC.conseq (ksd_loop pes subNed subPes opt [subPes]) (fun g h => ⟨h.1.2, h.2⟩)
      (fun _ _ h => h) (fun y => by simp only [sarG, List.count_append, List.count_nil]; omega)
      (fun _ _ => Nat.le_refl _)) fun o => ?_
    exact HC.pure' (fun g h => h.1) (fun y => Nat.le_refl _)
  all_goals exact ksd_monoBody St b subNed _

/-! ## The direct call -/

/-- The run of the formula from a `bunt` goal, or its skip. -/
theorem ksd_fol {rq : CGoalL S → List Nat → CM Map (NextL S)} (hq : HRS (Map := Map) rq) (q : Nomm) (th : Jmp)
    (region : List Nat) :
    HC (fun g => Fresh g th) [] (if safeFolFol q then pure ⟨ofSure Sure.bunt, th⟩
      else rq (CGoalL.next (ofSure Sure.bunt) th) region : CM Map (NextL S))
      (fun x g => Fresh g x.th ∧ LG x.goal g) (fun x => sarR x.laz) :=
  HC.ite' _ (HC.pure' (fun g h => ⟨h, lg_ofSure _ _ _⟩) (fun y => by simp [sarR_ofSure, Sure.bunt, flattenNeed]))
    (HC.conseq (hq (CGoalL.next (ofSure Sure.bunt) th) region) (fun g h => ⟨h, lg_ofSure _ _ _⟩)
      (fun _ _ h => h) (fun y => by simp [sarG, sarR_ofSure, Sure.bunt, flattenNeed]) (fun _ _ => Nat.le_refl _))

/-- **A producer of a `Fresh`, `LG` result, `+past`, run p, `+copy`.** -/
theorem ksd_bin (St : SarSteps S Map) (cod : Bell → Option Bool) {rp : CGoalL S → List Nat → CM Map (NextL S)}
    (p : Nomm) (hp : HRS (Map := Map) rp) {P : Comp.Gen Map → Prop} {ri : List Nat} {m : CM Map (NextL S)}
    (hm : HC P ri m (fun x g => Fresh g x.th ∧ LG x.goal g) (fun x => sarR x.laz)) (lp : Lazy S)
    (region : List Nat) :
    HC (fun g => P g ∧ LL lp g) (ri ++ sarR lp) (do
      let nex2 ← m
      let nex2 ← pastL cod nex2 p region
      let nex1 ← rp (CGoalL.next lp nex2.th) region
      copyL nex1 nex2.laz : CM Map (NextL S)) (fun nex g => Fresh g nex.th ∧ LG nex.goal g)
      (fun nex => sarR nex.laz) := by
  refine HC.bind' (HC.frame hm (stab_ll lp) (sarR lp)) fun nex2 => ?_
  refine HC.bind' (HC.weak (HC.frame (hcl_pastL cod nex2 p region) (stab_ll lp) (sarR lp))
    fun g h => ⟨⟨h.1.1, h.1.2⟩, h.2⟩) fun nex2' => ?_
  refine HC.bind' (HC.conseq (HC.frame (hp (CGoalL.next lp nex2'.th) region) (stab_ll nex2'.laz) (sarR nex2'.laz))
    (fun g h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩) (fun _ _ h => h) (sar_comm _ _) (fun _ _ => Nat.le_refl _)) fun nex1 => ?_
  exact HC.conseq (hcl_copyL St nex1 nex2'.laz) (fun g h => ⟨h.1.1, h.1.2, h.2⟩) (fun _ _ h => h)
    (fun _ => Nat.le_refl _) (fun _ _ => Nat.le_refl _)

/-- The `monoBlocks` path of the direct call. -/
theorem ksd_monoPath (St : SarSteps S Map) (env : CallEnv) {rp rq : CGoalL S → List Nat → CM Map (NextL S)}
    (p q : Nomm) (b : Bell) (bNed : NeedOrd) (hp : HRS (Map := Map) rp) (hq : HRS (Map := Map) rq)
    (goal : CGoalL S) (region : List Nat) :
    HC (fun g => GFL (Map := Map) goal g ∧ LG goal g) (sarG goal) (do
      let subNed ← needOrdAllocRegs bNed
      let (subPes, callBlock) ← monoBlocks b subNed goal
      let nexArg : NextL S := ⟨ofSure (lazyReg subPes), jmp0 callBlock⟩
      let nexFol ← (if safeFolFol q then pure ⟨ofSure Sure.bunt, nexArg.th⟩
        else rq (CGoalL.next (ofSure Sure.bunt) nexArg.th) region : CM Map (NextL S))
      let nexFol ← pastL env.cod nexFol p region
      let nexSub ← rp (CGoalL.next nexArg.laz nexFol.th) region
      copyL nexSub nexFol.laz : CM Map (NextL S)) (fun nex g => Fresh g nex.th ∧ LG nex.goal g)
      (fun nex => sarR nex.laz) := by
  refine HC.bind' (ksd_needOrd (stab_and (stab_gfl goal) (stab_lg goal)) bNed (sarG goal)) fun subNed => ?_
  refine HC.bind' (ksd_monoBlocks St b subNed goal) fun a => ?_
  rcases a with ⟨subPes, callBlock⟩
  exact HC.conseq (ksd_bin St env.cod p hp (ksd_fol hq q (jmp0 callBlock) region) (ofSure (lazyReg subPes)) region)
    (fun g h => ⟨h, ll_ofSure _ _⟩) (fun _ _ h => h)
    (fun y => by simp [sarR_ofSure, lazyReg, flattenNeed]) (fun _ _ => Nat.le_refl _)

/-- **The direct call with `mono` `&`**: the drop path and the
`+mono-try-call` path. -/
theorem ksd_callDM (St : SarSteps S Map) (env : CallEnv) {rp rq : CGoalL S → List Nat → CM Map (NextL S)}
    (p q : Nomm) (b : Bell) (key : Option Noun) (hp : HRS (Map := Map) rp) (hq : HRS (Map := Map) rq)
    (goal : CGoalL S) (region : List Nat) :
    HC (fun g => GFL (Map := Map) goal g ∧ LG goal g) (sarG goal) (callDM env rp rq p q b key goal region)
      (fun nex g => Fresh g nex.th ∧ LG nex.goal g) (fun nex => sarR nex.laz) := by
  unfold callDM
  split
  next _ laz th =>
    split
    next hc =>
      dsimp only
      exact HC.conseq (ksd_bin St env.cod p hp (ksd_fol hq q th region) (ofSure Sure.bunt) region)
        (fun g h => ⟨h.1, ll_ofSure _ _⟩) (fun _ _ h => h)
        (fun y => by simp [sarR_ofSure, Sure.bunt, flattenNeed]) (fun _ _ => Nat.le_refl _)
    next hc =>
      dsimp only
      split
      · rename_i bNed _ _
        exact ksd_monoPath St env p q b bNed hp hq _ region
      · exact HC.fail
  next hne =>
    dsimp only
    split
    · rename_i bNed _ _
      exact ksd_monoPath St env p q b bNed hp hq _ region
    · exact HC.fail

/-! ## The induction -/

/-- **Single assignment at run level on `PlainD`** (`runLCM env true`), from the walks' counts. -/
theorem ksd_run (env : CallEnv) (St : SarSteps S Map) : ∀ (nm : Nomm), PlainD nm → ∀ (sup : Option Nomm),
    HRS (Map := Map) (runLCM (S := S) env true sup nm)
  | Nomm.cons p q, h, sup, goal, region => by
    have ihp := ksd_run env St p h.1 sup
    have ihq := ksd_run env St q h.2 sup
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
    have ih := ksd_run env St p h sup
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
    have ih := ksd_run env St p h sup
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
    have ihp := ksd_run env St p h.1 sup
    have ihq := ksd_run env St q h.2 sup
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
    exact HC.bind' (ksd_run env St q h.2 (some p) goal region) fun nex =>
      HC.weak (ksd_run env St p h.1 sup nex.goal region) fun _ h => h
  | Nomm.n10 a v q, h, sup, goal, region => by
    have ihv := ksd_run env St v h.1 sup
    have ihq := ksd_run env St q h.2 sup
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
      exact hcl_callL St env p q sup (ksd_run env St p h.1 sup) (ksd_run env St q h.2 sup) goal region
    | some bk =>
      obtain ⟨b, key⟩ := bk
      exact ksd_callDM St env p q b key (ksd_run env St p h.1 sup) (ksd_run env St q h.2 sup) goal region
  | Nomm.n6 _ _ _, h, _, _, _ => h.elim
  | Nomm.n11s _ _ _, h, _, _, _ => h.elim
  | Nomm.n11d _ _ _ _, h, _, _, _ => h.elim
  | Nomm.n12 _ _, h, _, _, _ => h.elim
  | Nomm.mean _ _ _ _ _, h, _, _, _ => h.elim


/-- **Single assignment at run level with direct calls**: `HRS` of every run
of `runLCM env true` on `PlainD`. -/
theorem sarRunM_plainD (env : CallEnv) : ∀ (nm : Nomm), PlainD nm → ∀ (sup : Option Nomm),
    HRS (Map := Map) (runLCM (S := S) env true sup nm) :=
  ksd_run env ksd_steps

/-! ## The top -/

/-- **`TopSAR` for `runLCM env true`.** -/
def TopSARM (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (env : CallEnv)
    (nm : Nomm) : Prop :=
  ∀ (nex : NextL S) (g1 : Comp.Gen Map),
    runLCM env true Option.none nm (CGoalL.done : CGoalL S) [] (gen0 : Comp.Gen Map) = some (nex, g1) → SAB g1.blocks

/-- **`TopSAU` for `runLCM env true`.** -/
def TopSAUM (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (env : CallEnv)
    (nm : Nomm) : Prop :=
  ∀ (nex : NextL S) (g1 g2 : Comp.Gen Map) (o sub : Nat),
    runLCM env true Option.none nm (CGoalL.done : CGoalL S) [] (gen0 : Comp.Gen Map) = some (nex, g1) →
    (kerf nex : CM Map (Nat × Nat)) g1 = some ((o, sub), g2) → SAB g2.blocks

/-- **`TopSARM` on `PlainD`.** -/
theorem topSAR_plainD {env : CallEnv} {nm : Nomm} (hp : PlainD nm) : TopSARM S Map env nm := by
  unfold TopSARM
  intro nex g1 h
  obtain ⟨s1, -, c1⟩ := (sarRunM_plainD env nm hp Option.none CGoalL.done []).sc gen0 nex g1 ats_gen0
    ⟨trivial, trivial⟩ sarSt_gen0 h
  refine sar_sab s1 fun y => ?_
  have h1 := c1 y
  have h2 := fr_le_one (gen0 : Comp.Gen Map).re g1.re y
  rw [sarDc_gen0] at h1
  simp only [sarG, List.count_nil] at h1
  omega

/-- **`TopSAUM` on `PlainD`.** -/
theorem topSAU_plainD {env : CallEnv} {nm : Nomm} (hp : PlainD nm) : TopSAUM S Map env nm := by
  unfold TopSAUM
  intro nex g1 g2 o sub h hk
  have R := sarRunM_plainD (S := S) (Map := Map) env nm hp Option.none CGoalL.done []
  obtain ⟨-, -, F1, -⟩ := R.ht.run gen0 nex g1 ats_gen0 ⟨trivial, trivial⟩ h
  obtain ⟨s1, l1, c1⟩ := R.sc gen0 nex g1 ats_gen0 ⟨trivial, trivial⟩ sarSt_gen0 h
  obtain ⟨s2, l2, c2⟩ := (ksd_steps (S := S) (Map := Map)).kerf nex (fresh_args F1) g1 (o, sub) g2 s1 hk
  refine sar_sab s2 fun y => ?_
  have := c1 y
  have := c2 y
  have := fr_add l1 l2 y
  have := fr_le_one (gen0 : Comp.Gen Map).re g2.re y
  rw [sarDc_gen0] at *
  simp only [sarG, List.count_nil] at *
  omega

/-- On `PlainN` the two runs agree, so `TopSARM` gives the old `TopSAR`. -/
theorem topSAR_of_M {env : CallEnv} {nm : Nomm} (hp : PlainN nm) : TopSAR S Map env nm := fun nex g1 h =>
  topSAR_plainD (plainN_plainD nm hp) nex g1
    (by rw [runLCM_true env (plainN_noDirect nm hp) Option.none CGoalL.done []]; exact h)

end Raw
end SkaModel
end Formalization
