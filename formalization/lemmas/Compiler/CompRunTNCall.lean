import lemmas.Compiler.CompRunTNSixAll
import lemmas.Compiler.CompRunTCall
import lemmas.Compiler.CompRunDirectP

/-!
# The direct call at `mono` `|`, threaded (README Gaps 19 (g))

At `mono` `|` (the member runs of `+compile-scc-in`, lines 3511 and 3531) the direct call
differs from `mono` `&` in substance at three places of `+run`:
* line 4004: on `%done` with no key, one `+emit` of `[~ ~ (jump-op ~)]`, then `=?  gen  sof
  (soft-new ..)`;
* line 4016: otherwise `+simple-next`, `+kerf`, one `+emit` of `[~ [(call-op ~ pro)]~ %hop ~
  out]`, then `=?  gen  sof (soft-new ..)`;
* line 4036: `call-blocks` is an atom, so no `+mono-try-call`; `sub-ned` stays.
With `sof` `|` (the pill's push gives `A 1`, and the model's `env.sof` is `false`) the soft
table is kept; this is `crd_blk_done`, `crd_blk_next` (step 7, model `crdBlockM`).

* `crdCallMN R cd`: the model from step 7 on, against any run model `R` and code table `cd`.
* `crd_from7NT`, `crd_callNT`: steps 7 to 14, and 0 to 14 from the rest after the need step,
  the runs of `q` and `p` threading the rest (`crd_ctailRT`).
* `crd_model_n2N`, `crd_model_dropN`: `runLCM env false` on a direct call (`callL`).
* **`comp_run_n2_callNTT`**, `comp_run_n2_dropNT`, `crd_hpqNT`, **`comp_run_n2_directNTT`**: the
  case `%2` on a direct call at `mono` `|`, dropped or not, parts `PartRTN` at `XN E msup`.
* `res_n2_callN`, `res_n2_dropN`, **`res_n2_directN`**.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun}

/-- **The rest predicate of the link at `mono` `|`**: `E x`, `mono = A 1`, `sup` the noun of
`msup`. -/
def XN (E : GenRest → Prop) (msup : Option Nomm) : GenRest → Noun → Noun → Prop :=
  fun x mono sup => E x ∧ mono = A 1 ∧ sup = unitNoun Nomm.toNoun msup

/-- At `XN E msup`, `YOk` asks that `E` be closed under `Y`. -/
theorem yOk_xn {E : GenRest → Prop} {Y : GenRest → GenRest → Prop} (msup : Option Nomm)
    (hr : ∀ x, Y x x) (ht : ∀ {x y z : GenRest}, Y x y → Y y z → Y x z)
    (hs : ∀ {x y : GenRest}, x.NoSoft → Y x y → y.NoSoft) (hE : ∀ {x y : GenRest}, E x → Y x y → E y) :
    YOk (XN E msup) Y :=
  ⟨hr, ht, hs, fun hX hy => ⟨hE hX.1 hy, hX.2.1, hX.2.2⟩⟩

/-- The model of the call at `mono` `|` from step `7` on, against `R` and `cd`. -/
noncomputable def crdCallMN (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet))
    (cd : Bell → Option Bool) (p q : Nomm) (b : Bell) (subNed : Need) (goal : CGoalL CSet) (region : List Nat) :
    CM (TreapMap mugF) (NextL CSet) := do
  let cb ← crdBlockM b (flattenNeed subNed) goal
  crdTailMR R cd p q (crdArg subNed cb) region

/-- **Steps `7` to `14` at `mono` `|`, threaded** (`crd_from7` with the tail `crd_ctailRT`). -/
theorem crd_from7NT (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)) (cd : Bell → Option Bool) (p q : Nomm)
    (hpn : PastAt ctx cd p) (region : List Nat) (x : GenRest) (hx : x.NoSoft) (V5 V2 PV sup : Noun)
    (subNed : Need) (b : Bell) (goal : CGoalL CSet) (g : Gen (TreapMap mugF)) {Y : GenRest → GenRest → Prop}
    (hr : ∀ x, Y x x) (ht : ∀ {x y z : GenRest}, Y x y → Y y z → Y x z)
    (hblk : nock (crdS6 V5 (listNoun A (flattenNeed subNed)) subNed.toNoun V2 PV
      (crSubj (A 1) (crdN p q b) goal.toNoun (listNoun A region) sup (compCore g x ctx))) crDKc7
      = (crdBlockM b (flattenNeed subNed) goal g).map fun p => C (A p.1) (genNoun p.2 x))
    (hq : ∀ cb g1, crdBlockM b (flattenNeed subNed) goal g = some (cb, g1) →
      RunAtRT R ctx Y x (A 1) sup q (CGoalL.next (Lazy.ofSure Sure.bunt) (jmp0 cb)) region g1)
    (hp : ∀ x1, Y x x1 → ∀ cb g1 nexF g2 nexF' g3, crdBlockM b (flattenNeed subNed) goal g = some (cb, g1) →
      crdFqR R q (jmp0 cb) region g1 = some (nexF, g2) → pastL cd nexF p region g2 = some (nexF', g3) →
      RunAtRT R ctx Y x1 (A 1) sup p (CGoalL.next (Lazy.ofSure ⟨subNed, HoonSet.empty⟩) nexF'.th) region g3)
    (hcp : ∀ cb g1 nexF g2 nexF' g3 nexS g4, crdBlockM b (flattenNeed subNed) goal g = some (cb, g1) →
      crdFqR R q (jmp0 cb) region g1 = some (nexF, g2) → pastL cd nexF p region g2 = some (nexF', g3) →
      R p (CGoalL.next (Lazy.ofSure ⟨subNed, HoonSet.empty⟩) nexF'.th) region g3 = some (nexS, g4) →
      CopyH g4.re nexS.laz nexF'.laz) :
    ∃ x', Y x x' ∧ nock (crdS6 V5 (listNoun A (flattenNeed subNed)) subNed.toNoun V2 PV
      (crSubj (A 1) (crdN p q b) goal.toNoun (listNoun A region) sup (compCore g x ctx))) crDKr7
      = (crdCallMN R cd p q b subNed goal region g).map fun p => C p.1.goal.toNoun (genNoun p.2 x') := by
  have h15 := cr_ctx15 h7
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  unfold crdCallMN
  rw [bind_apply]
  simp only [crSubj, compCore, crdS6] at hblk ⊢
  cases eb : crdBlockM b (flattenNeed subNed) goal g with
  | none =>
    rw [eb] at hblk
    refine ⟨x, hr x, ?_⟩
    generalize comp.door = Dr at hblk ⊢
    unfold crDKr7
    simp [nock_exec, hblk]
  | some r =>
    obtain ⟨cb, g1⟩ := r
    rw [eb] at hblk
    simp only [Option.map_some] at hblk
    obtain ⟨x', hy, ht'⟩ := crd_ctailRT h7 hcode R cd p q hpn region x (A 1) (C (A 0) (C b.toNoun (A 0))) sup
      goal.toNoun (crdArg subNed cb) (C subNed.toNoun (A cb)) (A cb) (A 1) V5 (listNoun A (flattenNeed subNed))
      subNed.toNoun V2 (A 0) PV g1 hr ht (hq cb g1 eb)
      (fun x1 hy1 nexF g2 nexF' g3 e e3 => hp x1 hy1 cb g1 nexF g2 nexF' g3 eb e e3)
      (fun nexF g2 nexF' g3 nexS g4 e e3 e4 => hcp cb g1 nexF g2 nexF' g3 nexS g4 eb e e3 e4)
    refine ⟨x', hy, ?_⟩
    rw [crd_arg_noun] at ht'
    have hs := crn_has x cb (hx cb)
    simp only [crSubj, compCore, crdS9] at ht'
    generalize comp.door = Dr at hblk ht' ⊢
    unfold crDKr7 crDKr8 crDKc8 crDKr9 crDKc9
    simp [nock_exec, hblk, h15, hc, ct_lfn_at, ct_lfn_arm, ct_lfn_gate, by_arm, by.arm_at, by.has.arm_at, has_arm,
      hs, ht']

/-- **The call at `mono` `|`, threaded from the rest after the need step**: steps `0` to `6`
(`crd_head6M` with the push of `sof` giving `|`), step `7` by the goal, `crd_from7NT`. -/
theorem crd_callNT (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)) (cd : Bell → Option Bool)
    (msup : Option Nomm) (p q : Nomm) (hpn : PastAt ctx cd p) (b : Bell) (nb : NeedOrd) (sur : Noun) (x : GenRest)
    (hx : x.NoSoft) (hn : CallNounM msup ctx p q b nb sur x (A 1) (A 1)) (PV : Noun) (goal : CGoalL CSet)
    (region : List Nat) (g : Gen (TreapMap mugF)) {Y : GenRest → GenRest → Prop}
    (hr : ∀ x, Y x x) (ht : ∀ {x y z : GenRest}, Y x y → Y y z → Y x z) (hinv : GInv g goal)
    (hq : ∀ subNed g1 cb g2, needOrdAllocRegs nb g = some (subNed, g1) →
      crdBlockM b (flattenNeed subNed) goal g1 = some (cb, g2) →
      RunAtRT R ctx Y x (A 1) (unitNoun Nomm.toNoun msup) q (CGoalL.next (Lazy.ofSure Sure.bunt) (jmp0 cb)) region g2)
    (hp : ∀ x1, Y x x1 → ∀ subNed g1 cb g2 nexF g3 nexF' g4, needOrdAllocRegs nb g = some (subNed, g1) →
      crdBlockM b (flattenNeed subNed) goal g1 = some (cb, g2) →
      crdFqR R q (jmp0 cb) region g2 = some (nexF, g3) → pastL cd nexF p region g3 = some (nexF', g4) →
      RunAtRT R ctx Y x1 (A 1) (unitNoun Nomm.toNoun msup) p
        (CGoalL.next (Lazy.ofSure ⟨subNed, HoonSet.empty⟩) nexF'.th) region g4)
    (hcp : ∀ subNed g1 cb g2 nexF g3 nexF' g4 nexS g5, needOrdAllocRegs nb g = some (subNed, g1) →
      crdBlockM b (flattenNeed subNed) goal g1 = some (cb, g2) →
      crdFqR R q (jmp0 cb) region g2 = some (nexF, g3) → pastL cd nexF p region g3 = some (nexF', g4) →
      R p (CGoalL.next (Lazy.ofSure ⟨subNed, HoonSet.empty⟩) nexF'.th) region g4 = some (nexS, g5) →
      CopyH g5.re nexS.laz nexF'.laz) :
    ∃ x', Y x x' ∧ nock (C PV (crSubj (A 1) (crdN p q b) goal.toNoun (listNoun A region) (unitNoun Nomm.toNoun msup)
      (compCore g x ctx))) crDCall
      = ((needOrdAllocRegs nb >>= fun subNed => crdCallMN R cd p q b subNed goal region) g).map
          fun p => C p.1.goal.toNoun (genNoun p.2 x') := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  rw [crd_head6M h7 msup p q b nb sur x (A 1) (A 1) hn PV goal.toNoun region g, bind_apply]
  cases e : needOrdAllocRegs nb g with
  | none => exact ⟨x, hr x, rfl⟩
  | some r =>
    obtain ⟨subNed, g1⟩ := r
    simp only [Option.bind_some]
    have hinv1 : GInv g1 goal := ginv_noar hinv e
    have hblk : nock (crdS6 sur (listNoun A (flattenNeed subNed)) subNed.toNoun nb.toNoun PV
        (crSubj (A 1) (crdN p q b) goal.toNoun (listNoun A region) (unitNoun Nomm.toNoun msup) (compCore g1 x ctx)))
        crDKc7 = (crdBlockM b (flattenNeed subNed) goal g1).map fun p => C (A p.1) (genNoun p.2 x) := by
      by_cases hgd : goal = CGoalL.done
      · subst hgd; exact crd_blk_done hc x sur nb.toNoun PV subNed p q b region _ g1
      · exact crd_blk_next h7 x hx sur nb.toNoun PV subNed p q b region _ goal hgd g1 hinv1
    exact crd_from7NT h7 hcode R cd p q hpn region x hx sur nb.toNoun PV _ subNed b goal g1 hr ht hblk
      (fun cb g2 h => hq subNed g1 cb g2 e h)
      (fun x1 hy1 cb g2 nexF g3 nexF' g4 h h3 h4 => hp x1 hy1 subNed g1 cb g2 nexF g3 nexF' g4 e h h3 h4)
      (fun cb g2 nexF g3 nexF' g4 nexS g5 h h3 h4 h5 => hcp subNed g1 cb g2 nexF g3 nexF' g4 nexS g5 e h h3 h4 h5)

/-- **The model at `mono` `|`** on a direct call with no key, not dropped, no ring,
`env.need b = some nb`, `sof` false: `+need-ord-alloc-regs`, then `crdCallMN` with the runs
`runLCM env false msup`. -/
theorem crd_model_n2N (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (b : Bell) (nb : NeedOrd)
    (goal : CGoalL CSet) (region : List Nat) (hdr : crdDrop (env.pure b) goal = false)
    (hri : env.ring b = Option.none) (hnb : env.need b = some nb) (hsof : env.sof (made p msup) p q b nb = false) :
    (runLCM env false msup (Nomm.n2 p q (some (b, Option.none))) goal region : CM (TreapMap mugF) (NextL CSet))
      = needOrdAllocRegs nb >>= fun subNed => crdCallMN (runLCM env false msup) env.cod p q b subNed goal region := by
  cases goal with
  | next laz th =>
    simp only [crdDrop] at hdr
    simp only [runLCM, callLM_false, callL, hdr, hri, hnb, hsof, Bool.false_eq_true, if_false]
    unfold crdCallMN crdTailMR crdFqR crdArg crdBlockM
    rfl
  | done =>
    simp only [runLCM, callLM_false, callL, hri, hnb, hsof, Bool.false_eq_true, if_false]
    unfold crdCallMN crdTailMR crdFqR crdArg crdBlockM
    rfl
  | pick z o =>
    simp only [runLCM, callLM_false, callL, hri, hnb, hsof, Bool.false_eq_true, if_false]
    unfold crdCallMN crdTailMR crdFqR crdArg crdBlockM
    rfl

/-- The model at `mono` `|` on a dropped call. -/
theorem crd_model_dropN (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (b : Bell) (key : Option Noun)
    (laz : Lazy CSet) (th : Jmp) (region : List Nat) (hpu : env.pure b = true)
    (hne : Lazy.noneEquivalentL laz = true) :
    (runLCM env false msup (Nomm.n2 p q (some (b, key))) (CGoalL.next laz th) region
        : CM (TreapMap mugF) (NextL CSet))
      = crdTailMR (runLCM env false msup) env.cod p q ⟨Lazy.ofSure Sure.bunt, th⟩ region := by
  simp only [runLCM, callLM_false, callL, hpu, hne, Bool.and_self, if_true]
  unfold crdTailMR crdFqR
  rfl

/-- **The case `%2` on a direct call at `mono` `|`, threaded through its tail**: the need step
takes `x` to `x'` (`Y x x'`), then the tail from `x'`; `sof` is `|` on both sides. -/
theorem comp_run_n2_callNTT (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q : Nomm)
    (hpn : PastAt ctx env.cod p) (b : Bell) (hcd : CodePure cod env b) (nb : NeedOrd) (sur : Noun)
    (goal : CGoalL CSet) (region : List Nat) (g : Gen (TreapMap mugF)) (hinv : GInv g goal)
    (hdr : crdDrop (env.pure b) goal = false) (hri : env.ring b = Option.none) (hnb : env.need b = some nb)
    (hsof : env.sof (made p msup) p q b nb = false)
    {Y : GenRest → GenRest → Prop} (hr : ∀ x, Y x x) (ht : ∀ {x y z : GenRest}, Y x y → Y y z → Y x z)
    (x x' : GenRest) (hy : Y x x') (hx' : x'.NoSoft) (hT : CallNounMT msup ctx p q b nb sur x x' (A 1) (A 1))
    (hn : CallNounM msup ctx p q b nb sur x' (A 1) (A 1))
    (hq : ∀ subNed g1 cb g2, needOrdAllocRegs nb g = some (subNed, g1) →
      crdBlockM b (flattenNeed subNed) goal g1 = some (cb, g2) →
      RunAtRT (runLCM env false msup) ctx Y x' (A 1) (unitNoun Nomm.toNoun msup) q
        (CGoalL.next (Lazy.ofSure Sure.bunt) (jmp0 cb)) region g2)
    (hp : ∀ x1, Y x' x1 → ∀ subNed g1 cb g2 nexF g3 nexF' g4, needOrdAllocRegs nb g = some (subNed, g1) →
      crdBlockM b (flattenNeed subNed) goal g1 = some (cb, g2) →
      crdFqR (runLCM env false msup) q (jmp0 cb) region g2 = some (nexF, g3) →
      pastL env.cod nexF p region g3 = some (nexF', g4) →
      RunAtRT (runLCM env false msup) ctx Y x1 (A 1) (unitNoun Nomm.toNoun msup) p
        (CGoalL.next (Lazy.ofSure ⟨subNed, HoonSet.empty⟩) nexF'.th) region g4)
    (hcp : ∀ subNed g1 cb g2 nexF g3 nexF' g4 nexS g5, needOrdAllocRegs nb g = some (subNed, g1) →
      crdBlockM b (flattenNeed subNed) goal g1 = some (cb, g2) →
      crdFqR (runLCM env false msup) q (jmp0 cb) region g2 = some (nexF, g3) →
      pastL env.cod nexF p region g3 = some (nexF', g4) →
      runLCM env false msup p (CGoalL.next (Lazy.ofSure ⟨subNed, HoonSet.empty⟩) nexF'.th) region g4
        = some (nexS, g5) →
      CopyH g5.re nexS.laz nexF'.laz) :
    ∃ x'', Y x x'' ∧ nock (crSubj (A 1) (Nomm.n2 p q (some (b, Option.none))).toNoun goal.toNoun (listNoun A region)
        (unitNoun Nomm.toNoun msup) (compCore g x ctx)) crDol
      = (runLCM env false msup (Nomm.n2 p q (some (b, Option.none))) goal region g).map
          fun r => C r.1.goal.toNoun (genNoun r.2 x'') := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  obtain ⟨V, hgot, hv⟩ := hcd
  obtain ⟨x'', hy2, hcall0⟩ := crd_callNT h7 hcode (runLCM env false msup) env.cod msup p q hpn b nb sur x' hx' hn
    (loob (env.pure b)) goal region g hr ht hinv hq hp hcp
  refine ⟨x'', ht hy hy2, ?_⟩
  rw [crd_model_n2N env msup p q b nb goal region hdr hri hnb hsof, crd_noun, cr_disp_n2, cr2_dir, crd_eq]
  have hpure := crd_pure hc hcode p.toNoun q.toNoun b.toNoun (unitNoun id Option.none) V _ (A 1)
    goal.toNoun (listNoun A region) (unitNoun Nomm.toNoun msup) g x hgot hv
  have ht0 := crd_test_all h7 (C (A 2) (C p.toNoun (C q.toNoun (C (A 0) (C b.toNoun (unitNoun id Option.none))))))
    (A 1) (listNoun A region) (unitNoun Nomm.toNoun msup) (env.pure b) goal g x
  rw [hdr] at ht0
  have hcall := (crd_call_shift h7 msup p q b nb sur x x' (A 1) (A 1) hT hn (loob (env.pure b)) goal.toNoun region
    g).trans hcall0
  simp only [crdN] at hcall
  have hu : unitNoun (id : Noun → Noun) Option.none = A 0 := rfl
  rw [hu] at hpure ht0 ⊢
  have hl : loob false = A 1 := rfl
  rw [hl] at ht0
  unfold crDHead
  simp [nock_exec, hpure, ht0, hcall]

/-- **The case `%2` on a dropped call at `mono` `|`, threaded** (the pill's path does not read
`mono`). -/
theorem comp_run_n2_dropNT (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q : Nomm)
    (hpn : PastAt ctx env.cod p) (b : Bell) (key : Option Noun) (hcd : CodePure cod env b)
    (laz : Lazy CSet) (th : Jmp) (region : List Nat) (g : Gen (TreapMap mugF)) (hpu : env.pure b = true)
    (hne : Lazy.noneEquivalentL laz = true) (x : GenRest) (mono sup : Noun) {Y : GenRest → GenRest → Prop}
    (hr : ∀ x, Y x x) (ht : ∀ {x y z : GenRest}, Y x y → Y y z → Y x z)
    (hq : RunAtRT (runLCM env false msup) ctx Y x mono sup q (CGoalL.next (Lazy.ofSure Sure.bunt) th) region g)
    (hp : ∀ x1, Y x x1 → ∀ nexF g2 nexF' g3, crdFqR (runLCM env false msup) q th region g = some (nexF, g2) →
      pastL env.cod nexF p region g2 = some (nexF', g3) →
      RunAtRT (runLCM env false msup) ctx Y x1 mono sup p (CGoalL.next (Lazy.ofSure Sure.bunt) nexF'.th) region g3)
    (hcp : ∀ nexF g2 nexF' g3 nexS g4, crdFqR (runLCM env false msup) q th region g = some (nexF, g2) →
      pastL env.cod nexF p region g2 = some (nexF', g3) →
      runLCM env false msup p (CGoalL.next (Lazy.ofSure Sure.bunt) nexF'.th) region g3 = some (nexS, g4) →
      CopyH g4.re nexS.laz nexF'.laz) :
    RunAtRT (runLCM env false msup) ctx Y x mono sup (Nomm.n2 p q (some (b, key))) (CGoalL.next laz th) region g := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  obtain ⟨V, hgot, hv⟩ := hcd
  obtain ⟨x', hy, hdr⟩ := crd_dropRT h7 hcode (runLCM env false msup) env.cod p q hpn region x mono
    (C (A 0) (C b.toNoun (unitNoun id key))) sup laz th g hr ht hq hp hcp
  refine ⟨x', hy, ?_⟩
  rw [crd_model_dropN env msup p q b key laz th region hpu hne, crd_noun, cr_disp_n2, cr2_dir, crd_eq]
  have hpure := crd_pure hc hcode p.toNoun q.toNoun b.toNoun (unitNoun id key) V _ mono
    (CGoalL.next laz th).toNoun (listNoun A region) sup g x hgot hv
  rw [hpu] at hpure
  have ht0 := crd_test h7 (C (A 2) (C p.toNoun (C q.toNoun (C (A 0) (C b.toNoun (unitNoun id key)))))) mono
    (listNoun A region) sup laz th g x
  rw [hne] at ht0
  unfold crDHead
  simp [nock_exec, hpure, ht0, loob, hdr]

/-- **The runs of `p` and `q` of the call at `mono` `|` from threaded parts**. -/
theorem crd_hpqNT {E : GenRest → Prop} {Y : GenRest → GenRest → Prop} {msup : Option Nomm}
    (hYk : YOk (XN E msup) Y) (env : CallEnv) (p q : Nomm) {region : List Nat}
    (P : PartRTN env msup ctx (XN E msup) Y p region) (Q : PartRTN env msup ctx (XN E msup) Y q region) (b : Bell)
    (nb : NeedOrd) (goal : CGoalL CSet) (g : Gen (TreapMap mugF)) (hinv : GInv g goal) (x : GenRest) (hx : x.NoSoft)
    (hE : E x) :
    (∀ subNed g1 cb g2, needOrdAllocRegs nb g = some (subNed, g1) →
      crdBlockM b (flattenNeed subNed) goal g1 = some (cb, g2) →
      RunAtRT (runLCM env false msup) ctx Y x (A 1) (unitNoun Nomm.toNoun msup) q
        (CGoalL.next (Lazy.ofSure Sure.bunt) (jmp0 cb)) region g2) ∧
    (∀ x1, Y x x1 → ∀ subNed g1 cb g2 nexF g3 nexF' g4, needOrdAllocRegs nb g = some (subNed, g1) →
      crdBlockM b (flattenNeed subNed) goal g1 = some (cb, g2) →
      crdFqR (runLCM env false msup) q (jmp0 cb) region g2 = some (nexF, g3) →
      pastL env.cod nexF p region g3 = some (nexF', g4) →
      RunAtRT (runLCM env false msup) ctx Y x1 (A 1) (unitNoun Nomm.toNoun msup) p
        (CGoalL.next (Lazy.ofSure ⟨subNed, HoonSet.empty⟩) nexF'.th) region g4) ∧
    (∀ subNed g1 cb g2 nexF g3 nexF' g4 nexS g5, needOrdAllocRegs nb g = some (subNed, g1) →
      crdBlockM b (flattenNeed subNed) goal g1 = some (cb, g2) →
      crdFqR (runLCM env false msup) q (jmp0 cb) region g2 = some (nexF, g3) →
      pastL env.cod nexF p region g3 = some (nexF', g4) →
      runLCM env false msup p (CGoalL.next (Lazy.ofSure ⟨subNed, HoonSet.empty⟩) nexF'.th) region g4
        = some (nexS, g5) →
      CopyH g5.re nexS.laz nexF'.laz) := by
  have hX : XN E msup x (A 1) (unitNoun Nomm.toNoun msup) := ⟨hE, rfl, rfl⟩
  refine ⟨fun subNed g1 cb g2 e eb => Q.link _ g2 (crd_goals hinv e eb).1 x _ _ hx hX,
    fun x1 hy1 subNed g1 cb g2 nexF g3 nexF' g4 e eb ef e3 => ?_,
    fun subNed g1 cb g2 nexF g3 nexF' g4 nexS g5 e eb ef e3 e4 => ?_⟩
  · obtain ⟨hq2, hp2, -⟩ := crd_goals hinv e eb
    exact P.link _ _ (tail_pgoal hq2 hp2 (crd_fq_resR Q.res hq2.2.1 hq2.2.2 ef) e3).1 x1 _ _ (hYk.soft hx hy1)
      (hYk.pres hX hy1)
  · obtain ⟨hq2, hp2, -⟩ := crd_goals hinv e eb
    have R2 := crd_fq_resR Q.res hq2.2.1 hq2.2.2 ef
    have ap : (lregs (Lazy.ofSure (⟨subNed, HoonSet.empty⟩ : Sure CSet)) ++ lregs (Lazy.ofSure (Sure.bunt : Sure CSet))).Nodup := by
      rw [lregs_bunt, List.append_nil]; exact hp2.2.1
    exact (tail_copyH hq2 hp2 ap R2 e3 (P.res _ _ _ _ (tail_pgoal hq2 hp2 R2 e3).1 e4)).1

/-- **The direct call at `mono` `|`, threaded through its parts**: dropped
(`comp_run_n2_dropNT`) or not (the need step to `x'`, then `comp_run_n2_callNTT`), with `p`
and `q` threaded parts (`PartRTN`) and `sof` `|` (the pill's push, `CallNounM` at `SOF = A 1`,
and the model's `env.sof`). -/
theorem comp_run_n2_directNTT {E : GenRest → Prop} {Y : GenRest → GenRest → Prop} {msup : Option Nomm}
    (hYk : YOk (XN E msup) Y) (h7 : slot? 7 ctx = some compK) {cod : Noun}
    (hcode : slot? 52 ctx = some cod) (env : CallEnv) (p q : Nomm) {region : List Nat}
    (P : PartRTN env msup ctx (XN E msup) Y p region) (Q : PartRTN env msup ctx (XN E msup) Y q region) (b : Bell)
    (hcd : CodePure cod env b)
    (nb : NeedOrd) (hE : ∀ x, x.NoSoft → E x → ∃ x' sur, Y x x' ∧
      CallNounMT msup ctx p q b nb sur x x' (A 1) (A 1) ∧ CallNounM msup ctx p q b nb sur x' (A 1) (A 1))
    (hri : env.ring b = Option.none) (hnb : env.need b = some nb) (hsof : env.sof (made p msup) p q b nb = false)
    (goal : CGoalL CSet) (g : Gen (TreapMap mugF)) (hinv : GInv g goal) :
    CompRunAtXT (runLCM env false msup) ctx (XN E msup) Y (Nomm.n2 p q (some (b, Option.none))) goal region g := by
  cases hdr : crdDrop (env.pure b) goal with
  | false =>
    rintro x mono sup hx ⟨hEx, rfl, rfl⟩
    obtain ⟨x', sur, hy, hT, hn⟩ := hE x hx hEx
    have hx' := hYk.soft hx hy
    have hE' : E x' := (hYk.pres (show XN E msup x (A 1) (unitNoun Nomm.toNoun msup) from ⟨hEx, rfl, rfl⟩) hy).1
    obtain ⟨hq, hp, hcp⟩ := crd_hpqNT hYk env p q P Q b nb goal g hinv x' hx' hE'
    exact comp_run_n2_callNTT h7 hcode env msup p q P.past b hcd nb sur goal region g hinv hdr hri hnb hsof
      hYk.refl hYk.trans x x' hy hx' hT hn hq hp hcp
  | true =>
    cases goal with
    | done => simp [crdDrop] at hdr
    | pick z o => simp [crdDrop] at hdr
    | next laz th =>
      simp only [crdDrop, Bool.and_eq_true] at hdr
      obtain ⟨hpu, hne⟩ := hdr
      have hd : g.drop = false := hinv.2.1
      have hj : JmpIn (· < g.re) th := hinv.2.2
      rintro x mono sup hx ⟨hEx, rfl, rfl⟩
      have hX : XN E msup x (A 1) (unitNoun Nomm.toNoun msup) := ⟨hEx, rfl, rfl⟩
      exact comp_run_n2_dropNT h7 hcode env msup p q P.past b Option.none hcd laz th region g hpu hne x _ _
        hYk.refl hYk.trans
        (Q.link _ g (ginv_bunt_j hd hj) x _ _ hx hX)
        (fun x1 hy1 nexF g2 nexF' g3 e e3 =>
          P.link _ _ (tail_pgoal (ginv_bunt_j hd hj) (linv_bunt _ _) (crd_fq_resR Q.res hd hj e) e3).1 x1 _ _
            (hYk.soft hx hy1) (hYk.pres hX hy1))
        (fun nexF g2 nexF' g3 nexS g4 e e3 e4 => by
          have R2 := crd_fq_resR Q.res hd hj e
          exact (tail_copyH (ginv_bunt_j hd hj) (linv_bunt _ _) (by simp [lregs_bunt]) R2 e3
            (P.res _ _ _ _ (tail_pgoal (ginv_bunt_j hd hj) (linv_bunt _ _) R2 e3).1 e4)).1)

/-- **What the call at `mono` `|` returns** (`GRes`): not dropped, no ring, `env.need b = some
nb`, `sof` false, on every goal with `GInv`. -/
theorem res_n2_callN {env : CallEnv} {msup : Option Nomm} {p q : Nomm} {region : List Nat}
    (ihp : ResForR (runLCM env false msup) p region) (ihq : ResForR (runLCM env false msup) q region)
    {b : Bell} {nb : NeedOrd} {goal : CGoalL CSet} (hdr : crdDrop (env.pure b) goal = false)
    (hri : env.ring b = Option.none) (hnb : env.need b = some nb) (hsof : env.sof (made p msup) p q b nb = false)
    {g g' : Gen (TreapMap mugF)} {nex : NextL CSet} (hi : GInv g goal)
    (h : runLCM env false msup (Nomm.n2 p q (some (b, Option.none))) goal region g = some (nex, g')) :
    GRes g goal g' nex := by
  rw [crd_model_n2N env msup p q b nb goal region hdr hri hnb hsof] at h
  obtain ⟨subNed, g1, e, h⟩ := bind_some h
  unfold crdCallMN at h
  obtain ⟨cb, g2, eb, h⟩ := bind_some h
  unfold crdTailMR at h
  simp only [crdArg] at h
  obtain ⟨nexF, g3, ef, h⟩ := bind_some h
  obtain ⟨nexF', g4, e3, h⟩ := bind_some h
  obtain ⟨nexS, g5, e4, e5⟩ := bind_some h
  obtain ⟨hq2, hp2, l2, b2, hm⟩ := crd_goals hi e eb
  have R2 := crd_fq_resR ihq hq2.2.1 hq2.2.2 ef
  have P3 := tail_pgoal hq2 hp2 R2 e3
  have ap : (lregs (Lazy.ofSure (⟨subNed, HoonSet.empty⟩ : Sure CSet)) ++ lregs (Lazy.ofSure (Sure.bunt : Sure CSet))).Nodup := by
    rw [lregs_bunt, List.append_nil]; exact hp2.2.1
  obtain ⟨l, bb, i, s⟩ := tail_res hq2 hp2 ap R2 e3 (ihp _ _ _ _ P3.1 e4) e5
  refine ⟨Nat.le_trans l2 l, Nat.le_trans b2 bb, i, fun r hr => ?_⟩
  rcases s r hr with e' | e'
  · rw [lregs_bunt, List.append_nil, lregs_ofSure] at e'
    exact Or.inl (hm r ((mem_flat _ _).1 e'))
  · exact Or.inl (Nat.le_trans l2 e')

theorem res_n2_dropN {env : CallEnv} {msup : Option Nomm} {p q : Nomm} {region : List Nat}
    (ihp : ResForR (runLCM env false msup) p region) (ihq : ResForR (runLCM env false msup) q region)
    {b : Bell} {key : Option Noun} {laz : Lazy CSet} {th : Jmp}
    (hpu : env.pure b = true) (hne : Lazy.noneEquivalentL laz = true) {g g' : Gen (TreapMap mugF)}
    {nex : NextL CSet} (hi : GInv g (CGoalL.next laz th))
    (h : runLCM env false msup (Nomm.n2 p q (some (b, key))) (CGoalL.next laz th) region g = some (nex, g')) :
    GRes g (CGoalL.next laz th) g' nex := by
  have hd : g.drop = false := hi.2.1
  have hj : JmpIn (· < g.re) th := hi.2.2
  rw [crd_model_dropN env msup p q b key laz th region hpu hne] at h
  unfold crdTailMR at h
  obtain ⟨n2, g2, e1, h⟩ := bind_some h
  obtain ⟨n2', g3, e2, h⟩ := bind_some h
  obtain ⟨n1, g4, e3, e4⟩ := bind_some h
  have R2 := crd_fq_resR ihq hd hj e1
  have P3 := tail_pgoal (ginv_bunt_j hd hj) (linv_bunt _ _) R2 e2
  obtain ⟨l, bb, i, s⟩ := tail_res (ginv_bunt_j hd hj) (linv_bunt _ _) (by simp [lregs_bunt]) R2 e2
    (ihp _ _ _ _ P3.1 e3) e4
  refine ⟨l, bb, i, fun r hr => ?_⟩
  rcases s r hr with e | e
  · simp [lregs_bunt] at e
  · exact Or.inl e

/-- **What the case `%2` on a direct call with no memo key at `mono` `|` returns**, dropped or
not. -/
theorem res_n2_directN {env : CallEnv} {msup : Option Nomm} {p q : Nomm} {region : List Nat}
    (ihp : ResForR (runLCM env false msup) p region) (ihq : ResForR (runLCM env false msup) q region)
    {b : Bell} {nb : NeedOrd} (hri : env.ring b = Option.none)
    (hnb : env.need b = some nb) (hsof : env.sof (made p msup) p q b nb = false) :
    ResForR (runLCM env false msup) (Nomm.n2 p q (some (b, Option.none))) region := by
  intro goal g g' nex hi h
  cases hdr : crdDrop (env.pure b) goal with
  | false => exact res_n2_callN ihp ihq hdr hri hnb hsof hi h
  | true =>
    cases goal with
    | done => simp [crdDrop] at hdr
    | pick z o => simp [crdDrop] at hdr
    | next laz th =>
      simp only [crdDrop, Bool.and_eq_true] at hdr
      exact res_n2_dropN ihp ihq hdr.1 hdr.2 hi h

end Compiler
end Formalization
