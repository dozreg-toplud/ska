import lemmas.Compiler.CompRunDirectRing
import lemmas.Compiler.CompRunTNCall

/-!
# The direct call of `%2` through a ring at `mono` `|`, threaded (track K, README Gaps 19 (h))

`CompRunTNCall.lean` links the direct call at `mono` `|` (the member runs of `+compile-scc-in`)
with `rin` pushed as `~` (the subject `crdS6`).  Here `rin` is any unit `unitNoun id rin` of
`RinAt` (no hot driver, `CompRunDirectRing.lean`): the gates `call-op` and `jump-op` (lines
3985 to 4006) then build `[%caf b sub-v pro u]` and `[%jmf b sub-v u]` for `rin = [~ u]`, the
model's `callOpR` / `jumpOpR` (`Ska/CompRingCall.lean`) when `u` is the noun of its ring
(`RingNoun u`, `RinOkN`).

* `crdBlockMR b rin`: `crdBlockM` (step `7`) with the ops `jumpOpR` / `callOpR` of `rin`;
  `crdBlockMR_none`, `km_crdBlockMR`.
* `crd_blk_doneR`, `crd_blk_nextR`: the pill's step `7` at the subject with `rin` is `crdBlockMR`.
* `crdCallMNR`, `crd_from7NTR`, **`crd_callNTG`**: steps `7` to `14`, and `0` to `14` from the
  rest `x` (the need step moves it to `x'`, `crd_head6MTG`), against any run model `R`.
* `callLMR_false`, `crd_model_n2NR`: `runLCMR env false` on a direct call is `callLR`'s
  `crdCallMNR` at `env.ring b`.
* **`comp_run_n2_callNTTG`**: the case `%2` on a direct call through a ring (or none) at `mono`
  `|`, not dropped, against `runLCMR env false msup`.
* `crd_model_dropNR`, `comp_run_n2_dropNTR`: the dropped call against `runLCMR env false` (it
  never reads `rin`).
* `crd_goalsR`, `res_n2_callNR`, `res_n2_dropNR`, **`res_n2_directNR`**: what the call returns
  (`GRes`), ring or not.
* `PartRTNR` (`PartRTN` against `runLCMR`), `crd_hpqNTR`, **`comp_run_n2_directNTTG`**: the call,
  dropped or not, with its parts threaded.
-/

namespace Formalization
namespace Compiler

open Nock Pill Hoon SkaModel SkaModel.Comp

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {ctx : Noun}

/-- **The ring is a ring noun**: what the ops ask of `rin` (`RingNoun`, owner P: every value of
`call.cole` is one). -/
def RinOkN : Option Noun → Prop
  | Option.none => True
  | some u => RingNoun u

/-! ## Step `7` with a ring -/

/-- **The model of step `7` at `mono` `|` with the ring `rin`**: `crdBlockM` with `(jump-op ~)`
and `(call-op ~ pro)` of `rin`. -/
noncomputable def crdBlockMR (b : Bell) (rin : Option Noun) (subV : List Nat) :
    CGoalL CSet → CM (TreapMap mugF) Nat
  | CGoalL.done => emit ⟨[], [], jumpOpR b rin Option.none subV⟩
  | g => do
      let nex ← simpleNextL g
      let (out, pro) ← kerf nex
      emit ⟨[], [callOpR b rin Option.none subV pro], Termin.hop (jmp0 out)⟩

theorem crdBlockMR_none (b : Bell) (subV : List Nat) : crdBlockMR b Option.none subV = crdBlockM b subV := by
  funext goal
  cases goal <;> rfl

theorem km_crdBlockMR (b : Bell) (rin : Option Noun) (subV : List Nat) (goal : CGoalL CSet) :
    KM (crdBlockMR b rin subV goal : CM (TreapMap mugF) Nat) := by
  cases goal with
  | done => exact KM.emit' _
  | next laz th =>
    exact KM.bind' (km_simpleNextL _) fun nex => KM.bind' (km_kerf nex) fun r => by
      obtain ⟨out, pro⟩ := r; exact KM.emit' _
  | pick z o =>
    exact KM.bind' (km_simpleNextL _) fun nex => KM.bind' (km_kerf nex) fun r => by
      obtain ⟨out, pro⟩ := r; exact KM.emit' _

/-- **Step `7` under `%done` through a ring**: one `+emit` of `[~ ~ (jump-op ~)]`, which is
`[%jmf b sub-v u]` for `rin = [~ u]`. -/
theorem crd_blk_doneR (hc : CompIn ctx) (x : GenRest) (V5 V2 PV : Noun) (subNed : Need) (p q : Nomm) (b : Bell)
    (rin : Option Noun) (hrin : RinOkN rin) (region : List Nat) (sup : Noun) (g : Gen (TreapMap mugF)) :
    nock (crdS6mR (A 1) V5 (listNoun A (flattenNeed subNed)) subNed.toNoun V2 (unitNoun id rin) PV
      (crSubj (A 1) (crdN p q b) (CGoalL.done : CGoalL CSet).toNoun (listNoun A region) sup (compCore g x ctx)))
      crDKc7
      = (crdBlockMR b rin (flattenNeed subNed) CGoalL.done g).map fun p => C (A p.1) (genNoun p.2 x) := by
  cases rin with
  | none =>
    rw [crdBlockMR_none]
    exact crd_blk_done hc x V5 V2 PV subNed p q b region sup g
  | some u =>
    have hu : (ringOfNoun u).toNoun = u := hrin
    have he := cf_emit (x := x) hc g ⟨[], [], Termin.jmf b (flattenNeed subNed) (ringOfNoun u)⟩
    simp only [Blob.toNoun, listNoun, Termin.toNoun, Tag.jmf, hu] at he
    have hD := comp_emit_at
    simp only [crdBlockMR, jumpOpR, cf_emit_g, Option.map_some]
    simp only [crSubj, compCore] at he ⊢
    generalize comp.door = Dr at he hD ⊢
    unfold crDKc7 crD7 crD7Op crD7Jop crD7T crD7D crD7Ur0 crD7Uc0 crD7Ur1
    simp [nock_exec, CGoalL.toNoun, hD, comp_emit_arm, he, unitNoun]

theorem crd_blob_caf (b : Bell) (v : List Nat) (d t : Nat) (r : Ring) :
    Blob.toNoun ⟨[], [Pole.caf b v d r], Termin.hop (jmp0 t)⟩
      = C (A 0) (C (C (C (A 0x666163) (C b.toNoun (C (listNoun A v) (C (A d) r.toNoun)))) (A 0))
          (C (A 0x706f68) (C (A 0) (A t)))) := by
  simp [Blob.toNoun, listNoun, Termin.toNoun, Pole.toNoun, Tag.hop, Tag.caf, Jmp.toNoun, jmp0]

/-- **Step `7` on a `%next` or `%pick` goal through a ring**: `+simple-next`, `+kerf`, one
`+emit` of `[~ [(call-op ~ pro)]~ %hop ~ out]`, which is `[%caf b sub-v pro u]` for `rin = [~ u]`. -/
theorem crd_blk_nextR (h7 : slot? 7 ctx = some compK) (x : GenRest) (hx : x.NoSoft) (V5 V2 PV : Noun)
    (subNed : Need) (p q : Nomm) (b : Bell) (rin : Option Noun) (hrin : RinOkN rin) (region : List Nat) (sup : Noun)
    (goal : CGoalL CSet) (hgd : goal ≠ CGoalL.done) (g : Gen (TreapMap mugF)) (hinv : GInv g goal) :
    nock (crdS6mR (A 1) V5 (listNoun A (flattenNeed subNed)) subNed.toNoun V2 (unitNoun id rin) PV
      (crSubj (A 1) (crdN p q b) goal.toNoun (listNoun A region) sup (compCore g x ctx))) crDKc7
      = (crdBlockMR b rin (flattenNeed subNed) goal g).map fun p => C (A p.1) (genNoun p.2 x) := by
  cases rin with
  | none =>
    rw [crdBlockMR_none]
    exact crd_blk_next h7 x hx V5 V2 PV subNed p q b region sup goal hgd g hinv
  | some u =>
  have hu : (ringOfNoun u).toNoun = u := hrin
  obtain ⟨hc, hl, hm⟩ := comp_ctx_pill ctx h7
  have hmod : crdBlockMR b (some u) (flattenNeed subNed) goal = (do
      let nex ← simpleNextL goal
      let (out, pro) ← kerf nex
      emit ⟨[], [Pole.caf b (flattenNeed subNed) pro (ringOfNoun u)], Termin.hop (jmp0 out)⟩ :
        CM (TreapMap mugF) Nat) := by
    cases goal with
    | done => exact absurd rfl hgd
    | _ => rfl
  have htd : ∃ k, goal.toNoun = C (A k) (crdGoalT goal) ∧ k ≠ 0x656e6f64 := by
    cases goal with
    | done => exact absurd rfl hgd
    | next laz th => exact ⟨_, rfl, by decide⟩
    | pick z o => exact ⟨_, rfl, by decide⟩
  obtain ⟨k, hk, hkd⟩ := htd
  have hkd' : (0x656e6f64 : Nat) ≠ k := fun h => hkd h.symm
  have hsn := comp_simple_next hc x g goal (A 1) (crdN p q b) (listNoun A region) sup
  rw [hmod, bind_apply]
  simp only [crSubj, compCore] at hsn ⊢
  cases e : simpleNextL (S := CSet) (Map := TreapMap mugF) goal g with
  | none =>
    rw [e] at hsn
    simp only [Option.map_none] at hsn
    rw [hk] at hsn ⊢
    generalize comp.door = Dr at hsn ⊢
    unfold crDKc7 crD7 crD7Op crD7Jop crD7T crD7Nr0 crD7Nc0
    simp [nock_exec, crdS6mR, hsn, cr_bat_sn, hkd, hkd']
  | some r =>
    obtain ⟨nex0, g1⟩ := r
    rw [e] at hsn
    simp only [Option.map_some] at hsn
    obtain ⟨-, -, ⟨⟨lnb, -⟩, d1, -⟩, -⟩ := simpleNextL_res hinv e
    have hkf := comp_kerf_all hc hl hm x g1 nex0 (walk_mdP hx g1.bo (lall_mono (fun _ hs => hs.1) lnb))
    have hD1 := comp_kerf_at
    have hD3 := comp_emit_at
    rw [cr_next_nounL] at hsn
    simp only [compCore] at hkf
    cases ek : kerf nex0 g1 with
    | none =>
      rw [ek] at hkf
      rw [hk] at hsn ⊢
      generalize comp.door = Dr at hsn hkf hD1 hD3 ⊢
      unfold crDKc7 crD7 crD7Op crD7Jop crD7T crD7Nr0 crD7Nc0 crD7Nr1 crD7Nc1
      simp [nock_exec, crdS6mR, hsn, cr_bat_sn, hkd, hkd', hD1, comp_kerf_arm, hkf, bind, StateT.bind, ek]
    | some r2 =>
      obtain ⟨⟨out, pro⟩, g2⟩ := r2
      rw [ek] at hkf
      simp only [Option.map_some] at hkf
      have he := cf_emit (x := x) hc g2
        ⟨[], [Pole.caf b (flattenNeed subNed) pro (ringOfNoun u)], Termin.hop (jmp0 out)⟩
      rw [crd_blob_caf, hu] at he
      rw [hk] at hsn ⊢
      generalize comp.door = Dr at hsn hkf hD1 hD3 he ⊢
      unfold crDKc7 crD7 crD7Op crD7Jop crD7T crD7Nr0 crD7Nc0 crD7Nr1 crD7Nc1 crD7Ne crD7Vr0 crD7Vc0 crD7Vr1
      simp [nock_exec, crdS6mR, hsn, cr_bat_sn, hkd, hkd', hD1, comp_kerf_arm, hkf, bind, StateT.bind, ek, hD3,
        comp_emit_arm, he, cf_emit_g, unitNoun]

/-! ## Steps `7` to `14`, and the call -/

/-- The model of the call at `mono` `|` from step `7` on, through the ring `rin`. -/
noncomputable def crdCallMNR (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet))
    (cd : Bell → Option Bool) (p q : Nomm) (b : Bell) (rin : Option Noun) (subNed : Need) (goal : CGoalL CSet)
    (region : List Nat) : CM (TreapMap mugF) (NextL CSet) := do
  let cb ← crdBlockMR b rin (flattenNeed subNed) goal
  crdTailMR R cd p q (crdArg subNed cb) region

/-- **Steps `7` to `14` at `mono` `|` through a ring, threaded** (`crd_from7NT` with `rin` the
noun `RIN`). -/
theorem crd_from7NTR (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)) (cd : Bell → Option Bool) (p q : Nomm)
    (hpn : PastAt ctx cd p) (region : List Nat) (x : GenRest) (hx : x.NoSoft) (V5 V2 RIN PV sup : Noun)
    (subNed : Need) (b : Bell) (rin : Option Noun) (goal : CGoalL CSet) (g : Gen (TreapMap mugF))
    {Y : GenRest → GenRest → Prop}
    (hr : ∀ x, Y x x) (ht : ∀ {x y z : GenRest}, Y x y → Y y z → Y x z)
    (hblk : nock (crdS6mR (A 1) V5 (listNoun A (flattenNeed subNed)) subNed.toNoun V2 RIN PV
      (crSubj (A 1) (crdN p q b) goal.toNoun (listNoun A region) sup (compCore g x ctx))) crDKc7
      = (crdBlockMR b rin (flattenNeed subNed) goal g).map fun p => C (A p.1) (genNoun p.2 x))
    (hq : ∀ cb g1, crdBlockMR b rin (flattenNeed subNed) goal g = some (cb, g1) →
      RunAtRT R ctx Y x (A 1) sup q (CGoalL.next (Lazy.ofSure Sure.bunt) (jmp0 cb)) region g1)
    (hp : ∀ x1, Y x x1 → ∀ cb g1 nexF g2 nexF' g3, crdBlockMR b rin (flattenNeed subNed) goal g = some (cb, g1) →
      crdFqR R q (jmp0 cb) region g1 = some (nexF, g2) → pastL cd nexF p region g2 = some (nexF', g3) →
      RunAtRT R ctx Y x1 (A 1) sup p (CGoalL.next (Lazy.ofSure ⟨subNed, HoonSet.empty⟩) nexF'.th) region g3)
    (hcp : ∀ cb g1 nexF g2 nexF' g3 nexS g4, crdBlockMR b rin (flattenNeed subNed) goal g = some (cb, g1) →
      crdFqR R q (jmp0 cb) region g1 = some (nexF, g2) → pastL cd nexF p region g2 = some (nexF', g3) →
      R p (CGoalL.next (Lazy.ofSure ⟨subNed, HoonSet.empty⟩) nexF'.th) region g3 = some (nexS, g4) →
      CopyH g4.re nexS.laz nexF'.laz) :
    ∃ x', Y x x' ∧ nock (crdS6mR (A 1) V5 (listNoun A (flattenNeed subNed)) subNed.toNoun V2 RIN PV
      (crSubj (A 1) (crdN p q b) goal.toNoun (listNoun A region) sup (compCore g x ctx))) crDKr7
      = (crdCallMNR R cd p q b rin subNed goal region g).map fun p => C p.1.goal.toNoun (genNoun p.2 x') := by
  have h15 := cr_ctx15 h7
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  unfold crdCallMNR
  rw [bind_apply]
  simp only [crSubj, compCore, crdS6mR] at hblk ⊢
  cases eb : crdBlockMR b rin (flattenNeed subNed) goal g with
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
      subNed.toNoun V2 RIN PV g1 hr ht (hq cb g1 eb)
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

/-- **The call at `mono` `|` through a ring, threaded from `x`**: steps `0` to `6` move the rest
to `x'` (`crd_head6MTG`), then step `7` by the goal (`crd_blk_doneR`, `crd_blk_nextR`) and
`crd_from7NTR` from `x'`. -/
theorem crd_callNTG (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (R : Nomm → CGoalL CSet → List Nat → CM (TreapMap mugF) (NextL CSet)) (cd : Bell → Option Bool)
    (msup : Option Nomm) (p q : Nomm) (hpn : PastAt ctx cd p) (b : Bell) (nb : NeedOrd) (sur : Noun)
    (rin : Option Noun) (hrin : RinOkN rin) (x x' : GenRest) (hx' : x'.NoSoft)
    (hn : CallNounMTG msup ctx p q b nb sur x x' (A 1) (A 1) rin) (PV : Noun) (goal : CGoalL CSet)
    (region : List Nat) (g : Gen (TreapMap mugF)) {Y : GenRest → GenRest → Prop}
    (hr : ∀ x, Y x x) (ht : ∀ {x y z : GenRest}, Y x y → Y y z → Y x z) (hinv : GInv g goal)
    (hq : ∀ subNed g1 cb g2, needOrdAllocRegs nb g = some (subNed, g1) →
      crdBlockMR b rin (flattenNeed subNed) goal g1 = some (cb, g2) →
      RunAtRT R ctx Y x' (A 1) (unitNoun Nomm.toNoun msup) q (CGoalL.next (Lazy.ofSure Sure.bunt) (jmp0 cb)) region g2)
    (hp : ∀ x1, Y x' x1 → ∀ subNed g1 cb g2 nexF g3 nexF' g4, needOrdAllocRegs nb g = some (subNed, g1) →
      crdBlockMR b rin (flattenNeed subNed) goal g1 = some (cb, g2) →
      crdFqR R q (jmp0 cb) region g2 = some (nexF, g3) → pastL cd nexF p region g3 = some (nexF', g4) →
      RunAtRT R ctx Y x1 (A 1) (unitNoun Nomm.toNoun msup) p
        (CGoalL.next (Lazy.ofSure ⟨subNed, HoonSet.empty⟩) nexF'.th) region g4)
    (hcp : ∀ subNed g1 cb g2 nexF g3 nexF' g4 nexS g5, needOrdAllocRegs nb g = some (subNed, g1) →
      crdBlockMR b rin (flattenNeed subNed) goal g1 = some (cb, g2) →
      crdFqR R q (jmp0 cb) region g2 = some (nexF, g3) → pastL cd nexF p region g3 = some (nexF', g4) →
      R p (CGoalL.next (Lazy.ofSure ⟨subNed, HoonSet.empty⟩) nexF'.th) region g4 = some (nexS, g5) →
      CopyH g5.re nexS.laz nexF'.laz) :
    ∃ x'', Y x' x'' ∧ nock (C PV (crSubj (A 1) (crdN p q b) goal.toNoun (listNoun A region)
      (unitNoun Nomm.toNoun msup) (compCore g x ctx))) crDCall
      = ((needOrdAllocRegs nb >>= fun subNed => crdCallMNR R cd p q b rin subNed goal region) g).map
          fun p => C p.1.goal.toNoun (genNoun p.2 x'') := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  rw [crd_head6MTG h7 msup p q b nb sur x x' (A 1) (A 1) rin hn PV goal.toNoun region g, bind_apply]
  cases e : needOrdAllocRegs nb g with
  | none => exact ⟨x', hr x', rfl⟩
  | some r =>
    obtain ⟨subNed, g1⟩ := r
    simp only [Option.bind_some]
    have hinv1 : GInv g1 goal := ginv_noar hinv e
    have hblk : nock (crdS6mR (A 1) sur (listNoun A (flattenNeed subNed)) subNed.toNoun nb.toNoun (unitNoun id rin) PV
        (crSubj (A 1) (crdN p q b) goal.toNoun (listNoun A region) (unitNoun Nomm.toNoun msup) (compCore g1 x' ctx)))
        crDKc7 = (crdBlockMR b rin (flattenNeed subNed) goal g1).map fun p => C (A p.1) (genNoun p.2 x') := by
      by_cases hgd : goal = CGoalL.done
      · subst hgd; exact crd_blk_doneR hc x' sur nb.toNoun PV subNed p q b rin hrin region _ g1
      · exact crd_blk_nextR h7 x' hx' sur nb.toNoun PV subNed p q b rin hrin region _ goal hgd g1 hinv1
    exact crd_from7NTR h7 hcode R cd p q hpn region x' hx' sur nb.toNoun (unitNoun id rin) PV _ subNed b rin goal g1
      hr ht hblk
      (fun cb g2 h => hq subNed g1 cb g2 e h)
      (fun x1 hy1 cb g2 nexF g3 nexF' g4 h h3 h4 => hp x1 hy1 subNed g1 cb g2 nexF g3 nexF' g4 e h h3 h4)
      (fun cb g2 nexF g3 nexF' g4 nexS g5 h h3 h4 h5 => hcp subNed g1 cb g2 nexF g3 nexF' g4 nexS g5 e h h3 h4 h5)

/-! ## The model and the case `%2` against `runLCMR` -/

/-- `callLMR` at `mono` `|` is `callLR`. -/
theorem callLMR_false {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] (env : CallEnv)
    (rp rq : CGoalL S → List Nat → CM Map (NextL S)) (p q : Nomm)
    (info : Option (Bell × Option Noun)) (sup : Option Nomm) (goal : CGoalL S) (region : List Nat) :
    (callLMR env false rp rq p q info sup goal region : CM Map (NextL S)) = callLR env rp rq p q info sup goal region :=
  rfl

/-- The case `%2` of `runLCMR` is `callLMR`. -/
theorem runLCMR_n2_directN (env : CallEnv) (mono : Bool) (msup : Option Nomm) (p q : Nomm)
    (info : Option (Bell × Option Noun)) (goal : CGoalL CSet) (region : List Nat) :
    (runLCMR env mono msup (Nomm.n2 p q info) goal region : CM (TreapMap mugF) (NextL CSet))
      = callLMR env mono (runLCMR env mono msup p) (runLCMR env mono msup q) p q info msup goal region := by
  simp only [runLCMR]

/-- **The model at `mono` `|` through a ring** on a direct call with no key, not dropped,
`env.need b = some nb`, `sof` false: `+need-ord-alloc-regs`, then `crdCallMNR` at `env.ring b`. -/
theorem crd_model_n2NR (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (b : Bell) (nb : NeedOrd)
    (goal : CGoalL CSet) (region : List Nat) (hdr : crdDrop (env.pure b) goal = false)
    (hnb : env.need b = some nb) (hsof : env.sof (made p msup) p q b nb = false) :
    (runLCMR env false msup (Nomm.n2 p q (some (b, Option.none))) goal region : CM (TreapMap mugF) (NextL CSet))
      = needOrdAllocRegs nb >>= fun subNed =>
          crdCallMNR (runLCMR env false msup) env.cod p q b (env.ring b) subNed goal region := by
  rw [runLCMR_n2_directN, callLMR_false]
  cases goal with
  | next laz th =>
    simp only [crdDrop] at hdr
    simp only [callLR, hdr, hnb, hsof, Bool.false_eq_true, if_false]
    unfold crdCallMNR crdTailMR crdFqR crdArg crdBlockMR
    rfl
  | done =>
    simp only [callLR, hnb, hsof, Bool.false_eq_true, if_false]
    unfold crdCallMNR crdTailMR crdFqR crdArg crdBlockMR
    rfl
  | pick z o =>
    simp only [callLR, hnb, hsof, Bool.false_eq_true, if_false]
    unfold crdCallMNR crdTailMR crdFqR crdArg crdBlockMR
    rfl

/-- **The case `%2` on a direct call through a ring at `mono` `|`, threaded**: the need step
takes `x` to `x'` (`CallNounMTG`, `rin` the callee's `call.cole` entry, no hot driver), then the
call through the ring against `runLCMR env false msup` from `x'`. -/
theorem comp_run_n2_callNTTG (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q : Nomm)
    (hpn : PastAt ctx env.cod p) (b : Bell) (hcd : CodePure cod env b) (nb : NeedOrd) (sur : Noun)
    (rin : Option Noun) (hrin : RinOkN rin)
    (goal : CGoalL CSet) (region : List Nat) (g : Gen (TreapMap mugF)) (hinv : GInv g goal)
    (hdr : crdDrop (env.pure b) goal = false) (hri : env.ring b = rin) (hnb : env.need b = some nb)
    (hsof : env.sof (made p msup) p q b nb = false)
    {Y : GenRest → GenRest → Prop} (hr : ∀ x, Y x x) (ht : ∀ {x y z : GenRest}, Y x y → Y y z → Y x z)
    (x x' : GenRest) (hy : Y x x') (hx' : x'.NoSoft) (hT : CallNounMTG msup ctx p q b nb sur x x' (A 1) (A 1) rin)
    (hq : ∀ subNed g1 cb g2, needOrdAllocRegs nb g = some (subNed, g1) →
      crdBlockMR b rin (flattenNeed subNed) goal g1 = some (cb, g2) →
      RunAtRT (runLCMR env false msup) ctx Y x' (A 1) (unitNoun Nomm.toNoun msup) q
        (CGoalL.next (Lazy.ofSure Sure.bunt) (jmp0 cb)) region g2)
    (hp : ∀ x1, Y x' x1 → ∀ subNed g1 cb g2 nexF g3 nexF' g4, needOrdAllocRegs nb g = some (subNed, g1) →
      crdBlockMR b rin (flattenNeed subNed) goal g1 = some (cb, g2) →
      crdFqR (runLCMR env false msup) q (jmp0 cb) region g2 = some (nexF, g3) →
      pastL env.cod nexF p region g3 = some (nexF', g4) →
      RunAtRT (runLCMR env false msup) ctx Y x1 (A 1) (unitNoun Nomm.toNoun msup) p
        (CGoalL.next (Lazy.ofSure ⟨subNed, HoonSet.empty⟩) nexF'.th) region g4)
    (hcp : ∀ subNed g1 cb g2 nexF g3 nexF' g4 nexS g5, needOrdAllocRegs nb g = some (subNed, g1) →
      crdBlockMR b rin (flattenNeed subNed) goal g1 = some (cb, g2) →
      crdFqR (runLCMR env false msup) q (jmp0 cb) region g2 = some (nexF, g3) →
      pastL env.cod nexF p region g3 = some (nexF', g4) →
      runLCMR env false msup p (CGoalL.next (Lazy.ofSure ⟨subNed, HoonSet.empty⟩) nexF'.th) region g4
        = some (nexS, g5) →
      CopyH g5.re nexS.laz nexF'.laz) :
    ∃ x'', Y x x'' ∧ nock (crSubj (A 1) (Nomm.n2 p q (some (b, Option.none))).toNoun goal.toNoun (listNoun A region)
        (unitNoun Nomm.toNoun msup) (compCore g x ctx)) crDol
      = (runLCMR env false msup (Nomm.n2 p q (some (b, Option.none))) goal region g).map
          fun r => C r.1.goal.toNoun (genNoun r.2 x'') := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  obtain ⟨V, hgot, hv⟩ := hcd
  obtain ⟨x'', hy2, hcall⟩ := crd_callNTG h7 hcode (runLCMR env false msup) env.cod msup p q hpn b nb sur rin hrin
    x x' hx' hT (loob (env.pure b)) goal region g hr ht hinv hq hp hcp
  refine ⟨x'', ht hy hy2, ?_⟩
  rw [crd_model_n2NR env msup p q b nb goal region hdr hnb hsof, hri, crd_noun, cr_disp_n2, cr2_dir, crd_eq]
  have hpure := crd_pure hc hcode p.toNoun q.toNoun b.toNoun (unitNoun id Option.none) V _ (A 1)
    goal.toNoun (listNoun A region) (unitNoun Nomm.toNoun msup) g x hgot hv
  have ht0 := crd_test_all h7 (C (A 2) (C p.toNoun (C q.toNoun (C (A 0) (C b.toNoun (unitNoun id Option.none))))))
    (A 1) (listNoun A region) (unitNoun Nomm.toNoun msup) (env.pure b) goal g x
  rw [hdr] at ht0
  simp only [crdN] at hcall
  have hu : unitNoun (id : Noun → Noun) Option.none = A 0 := rfl
  rw [hu] at hpure ht0 ⊢
  have hl : loob false = A 1 := rfl
  rw [hl] at ht0
  unfold crDHead
  simp [nock_exec, hpure, ht0, hcall]

/-! ## The dropped call against `runLCMR` (it never reads `rin`) -/

/-- The model at `mono` `|` on a dropped call, rings included. -/
theorem crd_model_dropNR (env : CallEnv) (msup : Option Nomm) (p q : Nomm) (b : Bell) (key : Option Noun)
    (laz : Lazy CSet) (th : Jmp) (region : List Nat) (hpu : env.pure b = true)
    (hne : Lazy.noneEquivalentL laz = true) :
    (runLCMR env false msup (Nomm.n2 p q (some (b, key))) (CGoalL.next laz th) region
        : CM (TreapMap mugF) (NextL CSet))
      = crdTailMR (runLCMR env false msup) env.cod p q ⟨Lazy.ofSure Sure.bunt, th⟩ region := by
  rw [runLCMR_n2_directN, callLMR_false]
  simp only [callLR, hpu, hne, Bool.and_self, if_true]
  unfold crdTailMR crdFqR
  rfl

/-- **The case `%2` on a dropped call at `mono` `|` against `runLCMR`, threaded.** -/
theorem comp_run_n2_dropNTR (h7 : slot? 7 ctx = some compK) {cod : Noun} (hcode : slot? 52 ctx = some cod)
    (env : CallEnv) (msup : Option Nomm) (p q : Nomm)
    (hpn : PastAt ctx env.cod p) (b : Bell) (key : Option Noun) (hcd : CodePure cod env b)
    (laz : Lazy CSet) (th : Jmp) (region : List Nat) (g : Gen (TreapMap mugF)) (hpu : env.pure b = true)
    (hne : Lazy.noneEquivalentL laz = true) (x : GenRest) (mono sup : Noun) {Y : GenRest → GenRest → Prop}
    (hr : ∀ x, Y x x) (ht : ∀ {x y z : GenRest}, Y x y → Y y z → Y x z)
    (hq : RunAtRT (runLCMR env false msup) ctx Y x mono sup q (CGoalL.next (Lazy.ofSure Sure.bunt) th) region g)
    (hp : ∀ x1, Y x x1 → ∀ nexF g2 nexF' g3, crdFqR (runLCMR env false msup) q th region g = some (nexF, g2) →
      pastL env.cod nexF p region g2 = some (nexF', g3) →
      RunAtRT (runLCMR env false msup) ctx Y x1 mono sup p (CGoalL.next (Lazy.ofSure Sure.bunt) nexF'.th) region g3)
    (hcp : ∀ nexF g2 nexF' g3 nexS g4, crdFqR (runLCMR env false msup) q th region g = some (nexF, g2) →
      pastL env.cod nexF p region g2 = some (nexF', g3) →
      runLCMR env false msup p (CGoalL.next (Lazy.ofSure Sure.bunt) nexF'.th) region g3 = some (nexS, g4) →
      CopyH g4.re nexS.laz nexF'.laz) :
    RunAtRT (runLCMR env false msup) ctx Y x mono sup (Nomm.n2 p q (some (b, key))) (CGoalL.next laz th) region g := by
  obtain ⟨hc, -, -⟩ := comp_ctx_pill ctx h7
  obtain ⟨V, hgot, hv⟩ := hcd
  obtain ⟨x', hy, hdr⟩ := crd_dropRT h7 hcode (runLCMR env false msup) env.cod p q hpn region x mono
    (C (A 0) (C b.toNoun (unitNoun id key))) sup laz th g hr ht hq hp hcp
  refine ⟨x', hy, ?_⟩
  rw [crd_model_dropNR env msup p q b key laz th region hpu hne, crd_noun, cr_disp_n2, cr2_dir, crd_eq]
  have hpure := crd_pure hc hcode p.toNoun q.toNoun b.toNoun (unitNoun id key) V _ mono
    (CGoalL.next laz th).toNoun (listNoun A region) sup g x hgot hv
  rw [hpu] at hpure
  have ht0 := crd_test h7 (C (A 2) (C p.toNoun (C q.toNoun (C (A 0) (C b.toNoun (unitNoun id key)))))) mono
    (listNoun A region) sup laz th g x
  rw [hne] at ht0
  unfold crDHead
  simp [nock_exec, hpure, ht0, loob, hdr]

/-! ## What the call returns, ring or not -/

/-- The goals of the call's two runs after the blocks through a ring (`crd_goals`). -/
theorem crd_goalsR {nb : NeedOrd} {b : Bell} {rin : Option Noun} {goal : CGoalL CSet} {g g1 g2 : Gen (TreapMap mugF)}
    {subNed : Need} {cb : Nat} (hinv : GInv g goal) (e : needOrdAllocRegs nb g = some (subNed, g1))
    (eb : crdBlockMR b rin (flattenNeed subNed) goal g1 = some (cb, g2)) :
    GInv g2 (CGoalL.next (Lazy.ofSure Sure.bunt) (jmp0 cb)) ∧
      LInv g2.re g2.bo (Lazy.ofSure (⟨subNed, HoonSet.empty⟩ : Sure CSet)) ∧
      g.re ≤ g2.re ∧ g.bo ≤ g2.bo ∧ ∀ r, NMem subNed r → g.re ≤ r := by
  obtain ⟨⟨k, hk⟩, hre, hdist, hmem⟩ := needOrdAllocRegs_spec nb g g1 subNed e
  have hd0 : g.drop = false := ginv_drop hinv
  subst hk
  obtain ⟨l2, b2, d2⟩ := km_drop (km_crdBlockMR _ _ _ _) eb hd0
  refine ⟨ginv_bunt_j d2 (jmpIn_jmp0 _ _), linv_need (fun r hr => ?_) hdist, by simp at l2 hre ⊢; omega,
    by simpa using b2, fun r hr => (hmem r hr).1⟩
  have := (hmem r hr).2
  simp at l2 this
  omega

/-- **What the call at `mono` `|` through a ring returns** (`GRes`): not dropped, `env.need b =
some nb`, `sof` false, on every goal with `GInv`. -/
theorem res_n2_callNR {env : CallEnv} {msup : Option Nomm} {p q : Nomm} {region : List Nat}
    (ihp : ResForR (runLCMR env false msup) p region) (ihq : ResForR (runLCMR env false msup) q region)
    {b : Bell} {nb : NeedOrd} {goal : CGoalL CSet} (hdr : crdDrop (env.pure b) goal = false)
    (hnb : env.need b = some nb) (hsof : env.sof (made p msup) p q b nb = false)
    {g g' : Gen (TreapMap mugF)} {nex : NextL CSet} (hi : GInv g goal)
    (h : runLCMR env false msup (Nomm.n2 p q (some (b, Option.none))) goal region g = some (nex, g')) :
    GRes g goal g' nex := by
  rw [crd_model_n2NR env msup p q b nb goal region hdr hnb hsof] at h
  obtain ⟨subNed, g1, e, h⟩ := bind_some h
  unfold crdCallMNR at h
  obtain ⟨cb, g2, eb, h⟩ := bind_some h
  unfold crdTailMR at h
  simp only [crdArg] at h
  obtain ⟨nexF, g3, ef, h⟩ := bind_some h
  obtain ⟨nexF', g4, e3, h⟩ := bind_some h
  obtain ⟨nexS, g5, e4, e5⟩ := bind_some h
  obtain ⟨hq2, hp2, l2, b2, hm⟩ := crd_goalsR hi e eb
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

theorem res_n2_dropNR {env : CallEnv} {msup : Option Nomm} {p q : Nomm} {region : List Nat}
    (ihp : ResForR (runLCMR env false msup) p region) (ihq : ResForR (runLCMR env false msup) q region)
    {b : Bell} {key : Option Noun} {laz : Lazy CSet} {th : Jmp}
    (hpu : env.pure b = true) (hne : Lazy.noneEquivalentL laz = true) {g g' : Gen (TreapMap mugF)}
    {nex : NextL CSet} (hi : GInv g (CGoalL.next laz th))
    (h : runLCMR env false msup (Nomm.n2 p q (some (b, key))) (CGoalL.next laz th) region g = some (nex, g')) :
    GRes g (CGoalL.next laz th) g' nex := by
  have hd : g.drop = false := hi.2.1
  have hj : JmpIn (· < g.re) th := hi.2.2
  rw [crd_model_dropNR env msup p q b key laz th region hpu hne] at h
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

/-- **What the case `%2` on a direct call with no memo key at `mono` `|` returns against
`runLCMR`**, dropped or not, ring or not. -/
theorem res_n2_directNR {env : CallEnv} {msup : Option Nomm} {p q : Nomm} {region : List Nat}
    (ihp : ResForR (runLCMR env false msup) p region) (ihq : ResForR (runLCMR env false msup) q region)
    {b : Bell} {nb : NeedOrd} (hnb : env.need b = some nb) (hsof : env.sof (made p msup) p q b nb = false) :
    ResForR (runLCMR env false msup) (Nomm.n2 p q (some (b, Option.none))) region := by
  intro goal g g' nex hi h
  cases hdr : crdDrop (env.pure b) goal with
  | false => exact res_n2_callNR ihp ihq hdr hnb hsof hi h
  | true =>
    cases goal with
    | done => simp [crdDrop] at hdr
    | pick z o => simp [crdDrop] at hdr
    | next laz th =>
      simp only [crdDrop, Bool.and_eq_true] at hdr
      exact res_n2_dropNR ihp ihq hdr.1 hdr.2 hi h

/-! ## The call with its parts threaded, against `runLCMR` -/

/-- **A threaded part against `runLCMR env false`** (`PartRTN` with the ring model). -/
structure PartRTNR (env : CallEnv) (msup : Option Nomm) (ctx : Noun) (X : GenRest → Noun → Noun → Prop)
    (Y : GenRest → GenRest → Prop) (n : Nomm) (region : List Nat) : Prop where
  link : ∀ (goal : CGoalL CSet) (g : Gen (TreapMap mugF)), GInv g goal →
    CompRunAtXT (runLCMR env false msup) ctx X Y n goal region g
  res : ResForR (runLCMR env false msup) n region
  past : PastAt ctx env.cod n

/-- **The runs of `p` and `q` of the call through a ring at `mono` `|` from threaded parts.** -/
theorem crd_hpqNTR {E : GenRest → Prop} {Y : GenRest → GenRest → Prop} {msup : Option Nomm}
    (hYk : YOk (XN E msup) Y) (env : CallEnv) (p q : Nomm) {region : List Nat}
    (P : PartRTNR env msup ctx (XN E msup) Y p region) (Q : PartRTNR env msup ctx (XN E msup) Y q region) (b : Bell)
    (rin : Option Noun) (nb : NeedOrd) (goal : CGoalL CSet) (g : Gen (TreapMap mugF)) (hinv : GInv g goal)
    (x : GenRest) (hx : x.NoSoft) (hE : E x) :
    (∀ subNed g1 cb g2, needOrdAllocRegs nb g = some (subNed, g1) →
      crdBlockMR b rin (flattenNeed subNed) goal g1 = some (cb, g2) →
      RunAtRT (runLCMR env false msup) ctx Y x (A 1) (unitNoun Nomm.toNoun msup) q
        (CGoalL.next (Lazy.ofSure Sure.bunt) (jmp0 cb)) region g2) ∧
    (∀ x1, Y x x1 → ∀ subNed g1 cb g2 nexF g3 nexF' g4, needOrdAllocRegs nb g = some (subNed, g1) →
      crdBlockMR b rin (flattenNeed subNed) goal g1 = some (cb, g2) →
      crdFqR (runLCMR env false msup) q (jmp0 cb) region g2 = some (nexF, g3) →
      pastL env.cod nexF p region g3 = some (nexF', g4) →
      RunAtRT (runLCMR env false msup) ctx Y x1 (A 1) (unitNoun Nomm.toNoun msup) p
        (CGoalL.next (Lazy.ofSure ⟨subNed, HoonSet.empty⟩) nexF'.th) region g4) ∧
    (∀ subNed g1 cb g2 nexF g3 nexF' g4 nexS g5, needOrdAllocRegs nb g = some (subNed, g1) →
      crdBlockMR b rin (flattenNeed subNed) goal g1 = some (cb, g2) →
      crdFqR (runLCMR env false msup) q (jmp0 cb) region g2 = some (nexF, g3) →
      pastL env.cod nexF p region g3 = some (nexF', g4) →
      runLCMR env false msup p (CGoalL.next (Lazy.ofSure ⟨subNed, HoonSet.empty⟩) nexF'.th) region g4
        = some (nexS, g5) →
      CopyH g5.re nexS.laz nexF'.laz) := by
  have hX : XN E msup x (A 1) (unitNoun Nomm.toNoun msup) := ⟨hE, rfl, rfl⟩
  refine ⟨fun subNed g1 cb g2 e eb => Q.link _ g2 (crd_goalsR hinv e eb).1 x _ _ hx hX,
    fun x1 hy1 subNed g1 cb g2 nexF g3 nexF' g4 e eb ef e3 => ?_,
    fun subNed g1 cb g2 nexF g3 nexF' g4 nexS g5 e eb ef e3 e4 => ?_⟩
  · obtain ⟨hq2, hp2, -⟩ := crd_goalsR hinv e eb
    exact P.link _ _ (tail_pgoal hq2 hp2 (crd_fq_resR Q.res hq2.2.1 hq2.2.2 ef) e3).1 x1 _ _ (hYk.soft hx hy1)
      (hYk.pres hX hy1)
  · obtain ⟨hq2, hp2, -⟩ := crd_goalsR hinv e eb
    have R2 := crd_fq_resR Q.res hq2.2.1 hq2.2.2 ef
    have ap : (lregs (Lazy.ofSure (⟨subNed, HoonSet.empty⟩ : Sure CSet)) ++ lregs (Lazy.ofSure (Sure.bunt : Sure CSet))).Nodup := by
      rw [lregs_bunt, List.append_nil]; exact hp2.2.1
    exact (tail_copyH hq2 hp2 ap R2 e3 (P.res _ _ _ _ (tail_pgoal hq2 hp2 R2 e3).1 e4)).1

/-- **The direct call at `mono` `|` through a ring, threaded through its parts**: dropped
(`comp_run_n2_dropNTR`) or not (the need step to `x'` with the callee's `call.cole` entry `rin`
and no hot driver, then `comp_run_n2_callNTTG`), against `runLCMR env false msup`. -/
theorem comp_run_n2_directNTTG {E : GenRest → Prop} {Y : GenRest → GenRest → Prop} {msup : Option Nomm}
    (hYk : YOk (XN E msup) Y) (h7 : slot? 7 ctx = some compK) {cod : Noun}
    (hcode : slot? 52 ctx = some cod) (env : CallEnv) (p q : Nomm) {region : List Nat}
    (P : PartRTNR env msup ctx (XN E msup) Y p region) (Q : PartRTNR env msup ctx (XN E msup) Y q region) (b : Bell)
    (hcd : CodePure cod env b) (rin : Option Noun) (hrin : RinOkN rin)
    (nb : NeedOrd) (hE : ∀ x, x.NoSoft → E x → ∃ x' sur, Y x x' ∧
      CallNounMTG msup ctx p q b nb sur x x' (A 1) (A 1) rin)
    (hri : env.ring b = rin) (hnb : env.need b = some nb) (hsof : env.sof (made p msup) p q b nb = false)
    (goal : CGoalL CSet) (g : Gen (TreapMap mugF)) (hinv : GInv g goal) :
    CompRunAtXT (runLCMR env false msup) ctx (XN E msup) Y (Nomm.n2 p q (some (b, Option.none))) goal region g := by
  cases hdr : crdDrop (env.pure b) goal with
  | false =>
    rintro x mono sup hx ⟨hEx, rfl, rfl⟩
    obtain ⟨x', sur, hy, hT⟩ := hE x hx hEx
    have hx' := hYk.soft hx hy
    have hE' : E x' := (hYk.pres (show XN E msup x (A 1) (unitNoun Nomm.toNoun msup) from ⟨hEx, rfl, rfl⟩) hy).1
    obtain ⟨hq, hp, hcp⟩ := crd_hpqNTR hYk env p q P Q b rin nb goal g hinv x' hx' hE'
    exact comp_run_n2_callNTTG h7 hcode env msup p q P.past b hcd nb sur rin hrin goal region g hinv hdr hri hnb hsof
      hYk.refl hYk.trans x x' hy hx' hT hq hp hcp
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
      exact comp_run_n2_dropNTR h7 hcode env msup p q P.past b Option.none hcd laz th region g hpu hne x _ _
        hYk.refl hYk.trans
        (Q.link _ g (ginv_bunt_j hd hj) x _ _ hx hX)
        (fun x1 hy1 nexF g2 nexF' g3 e e3 =>
          P.link _ _ (tail_pgoal (ginv_bunt_j hd hj) (linv_bunt _ _) (crd_fq_resR Q.res hd hj e) e3).1 x1 _ _
            (hYk.soft hx hy1) (hYk.pres hX hy1))
        (fun nexF g2 nexF' g3 nexS g4 e e3 e4 => by
          have R2 := crd_fq_resR Q.res hd hj e
          exact (tail_copyH (ginv_bunt_j hd hj) (linv_bunt _ _) (by simp [lregs_bunt]) R2 e3
            (P.res _ _ _ _ (tail_pgoal (ginv_bunt_j hd hj) (linv_bunt _ _) R2 e3).1 e4)).1)

end Compiler
end Formalization
