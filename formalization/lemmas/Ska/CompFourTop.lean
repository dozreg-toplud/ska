import lemmas.Ska.CompOneLS

/-!
# `[4 p]` at the top, and the class with the increment

README Gaps 12.28.  Under `%done` the `%4` case is the block `[inc arg pro]
don pro` and the operand under `%next (lazy-from-reg arg)` into it
(`four_runD`); `unaryGB_ok` is `unaryGC_ok` for `RunOKGB`, the operand's
`RunOKGB` from its `LOKSF` at that goal (`RunOKLB.toGB`).

* `unaryGB_ok`, `four_doneB` (`[4 p]` under `%done` meets `DoneOK`),
  `unaryGTB_ok`, `three_doneB` (the same for `[3 p]`),
  `lokS_doneF`, `done_of_lokSF` (`lokS_done`, `done_of_lokS` for `LOKSF`).
* `CallTreeA` (`CallTree7` with `[4 p]` and `[3 p]`; the index `true` for the nomms
  with `LOKS false` at every goal) with `.annot`, `.cell`, `.sixCount`,
  `.hinted_of`, `.kind`, `lokS_callTreeA`, `callTreeA_done`,
  `finishLUC_contractCallTreeA`, `finishLUC_bellContractCallTreeA`,
  `CallTree7.toA`, the examples `fourInd_contract` (`[4 [2 [0 3] [0 2]]]`),
  `threeInd_contract` (`[3 [2 [0 3] [0 2]]]`)
  and `fourCons_contract` (`[[4 [0 2]] [2 [0 3] [0 2]]]`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- `omega` after reducing the projections of the states. -/
local macro "romega" : tactic =>
  `(tactic| first | omega | (simp only [emitted_re, emitted_bo] at *; omega) | (dsimp only at *; omega))

/-- **`unaryGC_ok` for `RunOKGB`** (the text of `unaryGC_ok`, with
`AgreeUB` for `AgreeU`).  A unary case whose operand may call: the operand's `RunOKGB` under
`%next (lazy-from-reg a) (jmp0 o)` and the blocks before it give `RunOKGB`
of the whole for the goal, the formula's `+mink` the increment of the
operand's (`MinkC4`), the block at `o` turning the operand's product `x`
held at `a` into `GoalSemCM` of `incTone tm (zero x)` (`hblk`). -/
theorem unaryGB_ok {lib : Lib} {N : Needs} {P : Noun → Prop} {f fb : Noun} (M : MinkC4 lib P f fb) {goal : CGoal S}
    {g0 g' g1 : Gen Map} {a o : Nat} {nexp : NextL S}
    (hpre : Ext g0 g') (hgr : GrowU g0 g') (hcnd : g'.cond = g0.cond) (ha : g0.re ≤ a ∧ a < g'.re)
    (ho : o < g'.bo) (hfr : Fresh g' (jmp0 o))
    (hp : RunOKGB (Map := Map) lib N P fb (CGoal.next (lazyReg a) (jmp0 o)) g' g1 nexp)
    (hfix : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g0.cond k) →
      ∀ k, g0.bo ≤ k → k < g'.bo → (HoonMap.get g'.blocks k).map (unproxyBlob cf) = HoonMap.get g'.blocks k)
    (hblk : ∀ (c : Straight Map), Agree c g0 g' → ∀ (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ)
      (gul : Noun) (st : σ) (regs : Map (Option Noun)) (t tm : Trace) (x : Noun), Inv st →
      Forall2 (FrameRel lib (ν st)) t tm → SkaModel.read a regs = some x →
      GoalSemCM lib O c gul Inv ν (Keep g0 g' goal) st regs t tm (jmp0 o) goal (incTone tm (Tone.zero x))) :
    RunOKGB lib N P f goal g0 g1 nexp := by
  have l1 := hp.ext.1
  have b1 := hp.ext.2.1
  have bad : ∀ {tm : Trace} {r : Tone}, BadC (CGoal.next (lazyReg a : Sure S) (jmp0 o)) tm r → r = Tone.two tm :=
    fun hb => by
      rcases hb with e | ⟨q, _, hq⟩
      · exact e
      · exact absurd (fitsS_lazyReg a q) hq
  -- the shared conversion of the operand's `GoalSemCM`
  have conv : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
      ∀ (c : Straight Map) (ned : Need) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ) (gul : Noun)
        (st : σ) (t tm : Trace) (s0 s : Noun), Inv st → Forall2 (FrameRel lib (ν st)) t tm →
      (∀ st' : σ, AgreeUB lib O c gul st' t cf ned g0 g1 nexp.laz s0 s) → (∀ x, NMem ned x → g1.re ≤ x) →
      ∀ regs (rb : Tone),
      GoalSemCM lib O c gul Inv ν (fun x => (x < g'.re ∨ NMem ned x) ∧ ¬ GMem (CGoal.next (lazyReg a : Sure S) (jmp0 o)) x)
        st regs t tm nexp.th (CGoal.next (lazyReg a : Sure S) (jmp0 o)) rb →
      GoalSemCM lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ GMem goal x) st regs t tm nexp.th goal
        (incTone tm rb) := by
    intro cf hcf c ned σ Inv ν O gul st t tm s0 s hI htr ag hned regs rb G
    have hcf0 : ∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g0.cond k := fun k hk =>
      (hcf k (Nat.lt_of_lt_of_le hk l1)).trans ((hp.cfr.get_lt hk).trans (by rw [hcnd]))
    have agQ : Agree c g0 g' := fun o' h0 h1 => by
      rw [(ag st).1 o' h0 (Nat.lt_of_lt_of_le h1 b1) (fun hm => ?_)]
      · rw [hp.ext.2.2.2 o' h1]; exact hfix cf hcf0 o' h0 h1
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
        have := (hp.labs e he).1; omega
    cases rb with
    | zero x =>
      obtain ⟨st', R, hI', hle, hR, hk, e1⟩ := G.1 (fitsS_lazyReg a x)
      have hR' : SkaModel.read a R = some x := hR
      have H := hblk c agQ σ Inv ν O gul st' R t tm x hI' (frames_mono hle htr) hR'
      refine goalSemCM_step hle (fun r hr => hk r ⟨?_, ?_⟩) e1 goal _
        (goalSemCM_monoK (fun r hr => ?_) goal _ H)
      · rcases hr.1 with h | h
        · exact Or.inl (by omega)
        · exact Or.inr h
      · intro ea
        have ea' : r = a := ea
        subst ea'
        rcases hr.1 with h | h
        · omega
        · have := hned _ h; omega
      · refine ⟨?_, hr.2⟩
        rcases hr.1 with h | h
        · exact Or.inl h
        · have := hned r h; exact Or.inr (by omega)
    | one q =>
      exact goalSemCM_of_returnsC goal _ (fun _ e => by cases e)
        (returnsC_of_goalSemCM _ (Tone.one q) (fun _ e => by cases e) G)
    | two tr =>
      exact goalSemCM_of_returnsC goal _ (fun _ e => by cases e)
        (returnsC_of_goalSemCM _ (Tone.two tr) (fun _ e => by cases e) G)
  have agP : ∀ (cf : Map (Nat × List Nat)) (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (gul : Noun)
      (st : σ) (t : Trace) (s0 s : Noun), AgreeUB lib O c gul st t cf ned g0 g1 nexp.laz s0 s →
      AgreeUB lib O c gul st t cf ned g' g1 nexp.laz s0 s :=
    fun cf c ned σ O gul st t s0 s ag => ⟨fun o' h0 h1 hnl => ag.1 o' (Nat.le_trans hpre.2.1 h0) h1 hnl, ag.2⟩
  refine ⟨hpre.trans hp.ext, hgr.trans hp.grow, (condFresh_of_eq hpre.1 hcnd).trans hp.cfr, hp.lo, hp.hi, ?_,
    fun r hr => ?_, hp.dist, fun e he => ⟨(hp.eregs e he).1, fun r hr => ⟨Or.inr ?_, ((hp.eregs e he).2 r hr).2⟩⟩,
    fun e he => ⟨by have := (hp.labs e he).1; have := hpre.2.1; omega, (hp.labs e he).2⟩, hp.nodup,
    fun s hs hf => ⟨fun gul n tm r hm => ?_, fun gul tm => ?_⟩, hp.ncond, hp.econd, ?_, ?_⟩
  · rcases hp.ent with fr | e
    · exact Or.inl fr
    · simp only [GoalJ] at e
      rw [e]; exact Or.inl (hfr.growU ho hp.grow)
  · rcases hp.regs r hr with h | h
    · have h' : r = a := h
      subst h'; exact Or.inr ⟨ha.1, by omega⟩
    · exact Or.inr ⟨by have := hpre.1; omega, h.2⟩
  · rcases ((hp.eregs e he).2 r hr).1 with h | h
    · have h' : r = a := h
      subst h'; exact ha.1
    · have := hpre.1; omega
  · obtain ⟨n', hn', rb, hb, rfl⟩ := M.fwd hs hm
    rw [bad ((hp.nec s hs hf).1 gul n' tm rb hb)]
    exact Or.inl rfl
  · obtain ⟨rb, hmb, hbad⟩ := (hp.nec s hs hf).2 gul tm
    refine ⟨_, M.bwd hs hmb, ?_⟩
    rw [bad hbad]
    exact Or.inl rfl
  · intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    obtain ⟨n', hn', rb, hb, rfl⟩ := M.fwd hs hm
    exact conv cf hcf c ned σ Inv ν O gul st t tm s0 s hI htr ag hned regs rb
      (hp.sem cf hcf c ned σ Inv ν O n' gul hN hS (oracleFwd_le hF hn') st t tm s0 s rb hI htr hs hb
        (fun st' => agP cf c ned σ O gul st' t s0 s (ag st')) hned regs hh hn)
  · intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨rb, hmb, G⟩ := hp.semB cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs
      (fun st' => agP cf c ned σ O gul st' t s0 s (ag st')) hned regs hh hn res hres
    exact ⟨_, M.bwd hs hmb, conv cf hcf c ned σ Inv ν O gul st t tm s0 s hI htr ag hned regs rb G⟩

/-- **`[4 p]` under `%done` with an operand that meets `LOKSF`**: the
block `[inc arg pro] don pro`, the operand's `LOKSF` under `%next
(lazy-from-reg arg)` (a goal with no entry), `RunOKLB.toGB`, `unaryGB_ok`
(the blocks as in `four_runD`). -/
theorem four_doneB (lib : Lib) {N : Needs} {p : Nomm} {env : CallEnv} {P : Noun → Prop} {f fb : Noun}
    (Sp : LOKSF (S := S) (Map := Map) lib N env P fb p) (M : MinkC4 lib P f fb) {sup : Option Nomm}
    {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S} (hcount : sixCount p ≤ 255) (b0 : 1 ≤ g0.bo)
    (d0 : g0.drop = false) (hu : UpBelow g0) (hcl0 : Clear g0) (hcb : CondBelow g0)
    (h : runLC env sup (Nomm.n4 p) CGoalL.done region g0 = some (nex, g1)) :
    DoneOK lib N P f g0 g1 nex := by
  have e4 : (runLC env sup (Nomm.n4 p) (CGoalL.done : CGoalL S) region : CM Map (NextL S)) = (do
      let pro ← re
      let arg ← re
      let o ← emit ⟨[], [Pole.inc arg pro], Termin.don pro⟩
      runLC env sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region) := by
    conv => lhs; unfold runLC
  rw [e4] at h
  simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
  have e0 : ∀ a : Nat, entries (ofSure (lazyReg a : Sure S)) = [] := fun a => entries_ofSure _
  have GU := ((grow_reg g0 (g0.re + 1 + 1)).trans (grow_emit (g := { g0 with re := g0.re + 1 + 1 })
    (b := ⟨[], [Pole.inc (g0.re + 1) g0.re], Termin.don g0.re⟩) (jumpsBelow_nil rfl _))).toU hu
  obtain ⟨⟨Qp, Rp⟩, pne, -, pfl, pec⟩ := Sp.run (L := ofSure (lazyReg _)) (th := jmp0 _) (Or.inr (e0 _)) hcount
    (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d0) (GU.up hu) (hcl0.growU GU)
    (CondFresh.below (condFresh_of_eq (g0 := g0) (by romega) rfl) hcb)
    (by simp only [jmp0]; omega) (by simp only [jmp0, emitted_bo]; omega) rfl (by rw [e0]; simp) trivial
    (fun r hr => by
      simp only [lazyReg, ofSure, NMem] at hr; subst hr
      exact ⟨by simp [emitted_re], condBelow_none hcb (by romega)⟩)
    (fun e he => by rw [e0] at he; cases he) (by rw [e0]; simp) (fun e he => by rw [e0] at he; cases he)
    (flat_ofSure _) trivial (fun e he => by rw [e0] at he; cases he) h
  have RG := Rp.toRunOKLB.toGB (fun r hr => by
    simp only [lazyReg, NMem] at hr; subst hr; simp [emitted_re])
  refine ⟨?_, pne, pfl, Sp.clean (L := ofSure (lazyReg _)) trivial h, pec⟩
  refine unaryGB_ok M ((ext_re _).trans ((ext_re _).trans (ext_emit _ _)))
    (((grow_reg g0 _).trans (grow_emit (jumpsBelow_nil rfl _))).toU hu) rfl
    ⟨Nat.le_succ _, by simp [emitted_re]⟩ (by simp [emitted_bo]) (fresh_emitted (by simpa using d0) rfl rfl) RG
    (fix_of_keeps (gs := g0) rfl ((keepsA_reg _ g0 _ (by romega)).trans (keepsA_emitted d0 (blobIn_one
      (fun x hx => by
        simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl
        <;> exact condBelow_none hcb (by romega)) (condBelow_none hcb (by romega)))))
      ((keeps_reg g0 _ (by romega)).trans (keeps_emitted d0 (blobIn_one
      (fun x hx => by
        simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl
        <;> romega) (by simp only [FinIn]; romega)))))
    ?_
  intro c hc σ Inv ν O gul st regs t tm x hI htr hx
  have hb := emitted_get' (by simpa using d0) (hc _ (by simp) (by simp [emitted_bo]))
  have hj := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
  cases x with
  | atom n =>
    rw [show [Pole.inc _ _] = [Pole.inc _ _] ++ [] from rfl, runs_inc hx] at hj
    refine ⟨Tone.zero (A (n + 1)), st, hI, Needs.le_refl _, ?_, ToneRel.zero _⟩
    rw [hj]; simp [execBlob_don', read_store_eq]
  | cell u v =>
    rw [show [Pole.inc _ _] = [Pole.inc _ _] ++ [] from rfl, crashes_inc hx] at hj
    exact ⟨Tone.two t, st, hI, Needs.le_refl _, hj, ToneRel.two htr⟩

/-- **`unaryGT_ok` for `RunOKGB`** (its text with `AgreeUB`): `unaryGC_ok` for a tone transform `T` that keeps the tones that are
no product (`hT`), with `+mink` on `f` the transform of `+mink` on `fb`
(`fw`, `bw`). -/
theorem unaryGTB_ok {lib : Lib} {N : Needs} {P : Noun → Prop} {f fb : Noun} {T : Trace → Tone → Tone}
    (hT : ∀ tm r, (∀ p, r ≠ Tone.zero p) → T tm r = r)
    (fw : ∀ {s gul : Noun} {n : Nat} {tm : Trace} {r : Tone}, P s → minkF lib gul n tm s f = some r →
      ∃ n', n' ≤ n ∧ ∃ rb, minkF lib gul n' tm s fb = some rb ∧ r = T tm rb)
    (bw : ∀ {s gul : Noun} {tm : Trace} {rb : Tone}, P s → Mink lib gul tm s fb rb → Mink lib gul tm s f (T tm rb))
    {goal : CGoal S} {g0 g' g1 : Gen Map} {a o : Nat} {nexp : NextL S}
    (hpre : Ext g0 g') (hgr : GrowU g0 g') (hcnd : g'.cond = g0.cond) (ha : g0.re ≤ a ∧ a < g'.re)
    (ho : o < g'.bo) (hfr : Fresh g' (jmp0 o))
    (hp : RunOKGB (Map := Map) lib N P fb (CGoal.next (lazyReg a) (jmp0 o)) g' g1 nexp)
    (hfix : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g0.cond k) →
      ∀ k, g0.bo ≤ k → k < g'.bo → (HoonMap.get g'.blocks k).map (unproxyBlob cf) = HoonMap.get g'.blocks k)
    (hblk : ∀ (c : Straight Map), Agree c g0 g' → ∀ (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ)
      (gul : Noun) (st : σ) (regs : Map (Option Noun)) (t tm : Trace) (x : Noun), Inv st →
      Forall2 (FrameRel lib (ν st)) t tm → SkaModel.read a regs = some x →
      GoalSemCM lib O c gul Inv ν (Keep g0 g' goal) st regs t tm (jmp0 o) goal (T tm (Tone.zero x))) :
    RunOKGB lib N P f goal g0 g1 nexp := by
  have l1 := hp.ext.1
  have b1 := hp.ext.2.1
  have bad : ∀ {tm : Trace} {r : Tone}, BadC (CGoal.next (lazyReg a : Sure S) (jmp0 o)) tm r → r = Tone.two tm :=
    fun hb => by
      rcases hb with e | ⟨q, _, hq⟩
      · exact e
      · exact absurd (fitsS_lazyReg a q) hq
  have conv : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g1.re → HoonMap.get cf k = HoonMap.get g1.cond k) →
      ∀ (c : Straight Map) (ned : Need) (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ) (gul : Noun)
        (st : σ) (t tm : Trace) (s0 s : Noun), Inv st → Forall2 (FrameRel lib (ν st)) t tm →
      (∀ st' : σ, AgreeUB lib O c gul st' t cf ned g0 g1 nexp.laz s0 s) → (∀ x, NMem ned x → g1.re ≤ x) →
      ∀ regs (rb : Tone),
      GoalSemCM lib O c gul Inv ν (fun x => (x < g'.re ∨ NMem ned x) ∧ ¬ GMem (CGoal.next (lazyReg a : Sure S) (jmp0 o)) x)
        st regs t tm nexp.th (CGoal.next (lazyReg a : Sure S) (jmp0 o)) rb →
      GoalSemCM lib O c gul Inv ν (fun x => (x < g0.re ∨ NMem ned x) ∧ ¬ GMem goal x) st regs t tm nexp.th goal
        (T tm rb) := by
    intro cf hcf c ned σ Inv ν O gul st t tm s0 s hI htr ag hned regs rb G
    have hcf0 : ∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g0.cond k := fun k hk =>
      (hcf k (Nat.lt_of_lt_of_le hk l1)).trans ((hp.cfr.get_lt hk).trans (by rw [hcnd]))
    have agQ : Agree c g0 g' := fun o' h0 h1 => by
      rw [(ag st).1 o' h0 (Nat.lt_of_lt_of_le h1 b1) (fun hm => ?_)]
      · rw [hp.ext.2.2.2 o' h1]; exact hfix cf hcf0 o' h0 h1
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
        have := (hp.labs e he).1; omega
    cases rb with
    | zero x =>
      obtain ⟨st', R, hI', hle, hR, hk, e1⟩ := G.1 (fitsS_lazyReg a x)
      have hR' : SkaModel.read a R = some x := hR
      have H := hblk c agQ σ Inv ν O gul st' R t tm x hI' (frames_mono hle htr) hR'
      refine goalSemCM_step hle (fun r hr => hk r ⟨?_, ?_⟩) e1 goal _
        (goalSemCM_monoK (fun r hr => ?_) goal _ H)
      · rcases hr.1 with h | h
        · exact Or.inl (by omega)
        · exact Or.inr h
      · intro ea
        have ea' : r = a := ea
        subst ea'
        rcases hr.1 with h | h
        · omega
        · have := hned _ h; omega
      · refine ⟨?_, hr.2⟩
        rcases hr.1 with h | h
        · exact Or.inl h
        · have := hned r h; exact Or.inr (by omega)
    | one q =>
      rw [hT tm _ (fun _ e => by cases e)]
      exact goalSemCM_of_returnsC goal _ (fun _ e => by cases e)
        (returnsC_of_goalSemCM _ (Tone.one q) (fun _ e => by cases e) G)
    | two tr =>
      rw [hT tm _ (fun _ e => by cases e)]
      exact goalSemCM_of_returnsC goal _ (fun _ e => by cases e)
        (returnsC_of_goalSemCM _ (Tone.two tr) (fun _ e => by cases e) G)
  have agP : ∀ (cf : Map (Nat × List Nat)) (c : Straight Map) (ned : Need) (σ : Type) (O : Oracle σ) (gul : Noun)
      (st : σ) (t : Trace) (s0 s : Noun), AgreeUB lib O c gul st t cf ned g0 g1 nexp.laz s0 s →
      AgreeUB lib O c gul st t cf ned g' g1 nexp.laz s0 s :=
    fun cf c ned σ O gul st t s0 s ag => ⟨fun o' h0 h1 hnl => ag.1 o' (Nat.le_trans hpre.2.1 h0) h1 hnl, ag.2⟩
  refine ⟨hpre.trans hp.ext, hgr.trans hp.grow, (condFresh_of_eq hpre.1 hcnd).trans hp.cfr, hp.lo, hp.hi, ?_,
    fun r hr => ?_, hp.dist, fun e he => ⟨(hp.eregs e he).1, fun r hr => ⟨Or.inr ?_, ((hp.eregs e he).2 r hr).2⟩⟩,
    fun e he => ⟨by have := (hp.labs e he).1; have := hpre.2.1; omega, (hp.labs e he).2⟩, hp.nodup,
    fun s hs hf => ⟨fun gul n tm r hm => ?_, fun gul tm => ?_⟩, hp.ncond, hp.econd, ?_, ?_⟩
  · rcases hp.ent with fr | e
    · exact Or.inl fr
    · simp only [GoalJ] at e
      rw [e]; exact Or.inl (hfr.growU ho hp.grow)
  · rcases hp.regs r hr with h | h
    · have h' : r = a := h
      subst h'; exact Or.inr ⟨ha.1, by omega⟩
    · exact Or.inr ⟨by have := hpre.1; omega, h.2⟩
  · rcases ((hp.eregs e he).2 r hr).1 with h | h
    · have h' : r = a := h
      subst h'; exact ha.1
    · have := hpre.1; omega
  · obtain ⟨n', hn', rb, hb, rfl⟩ := fw hs hm
    rw [bad ((hp.nec s hs hf).1 gul n' tm rb hb), hT tm _ (fun _ e => by cases e)]
    exact Or.inl rfl
  · obtain ⟨rb, hmb, hbad⟩ := (hp.nec s hs hf).2 gul tm
    refine ⟨_, bw hs hmb, ?_⟩
    rw [bad hbad, hT tm _ (fun _ e => by cases e)]
    exact Or.inl rfl
  · intro cf hcf c ned σ Inv ν O n gul hN hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    obtain ⟨n', hn', rb, hb, rfl⟩ := fw hs hm
    exact conv cf hcf c ned σ Inv ν O gul st t tm s0 s hI htr ag hned regs rb
      (hp.sem cf hcf c ned σ Inv ν O n' gul hN hS (oracleFwd_le hF hn') st t tm s0 s rb hI htr hs hb
        (fun st' => agP cf c ned σ O gul st' t s0 s (ag st')) hned regs hh hn)
  · intro cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨rb, hmb, G⟩ := hp.semB cf hcf c ned σ Inv ν O gul hN hS hB st t tm s0 s hI htr hs
      (fun st' => agP cf c ned σ O gul st' t s0 s (ag st')) hned regs hh hn res hres
    exact ⟨_, bw hs hmb, conv cf hcf c ned σ Inv ν O gul st t tm s0 s hI htr ag hned regs rb G⟩

/-! ## The runs of `[3 p]` -/

/-- **`[3 p]` under `%done` with an operand that meets `LOKSF`** (`three_runD`
with `RunOKLB.toGB`, `unaryGTB_ok`): `doneBlocks`,
the `clq` block, then the operand (`unaryGT_ok`, the blocks as in
`runOKV_n3D`). -/
theorem three_doneB (lib : Lib) {N : Needs} {p : Nomm} {env : CallEnv} {P : Noun → Prop} {f fb : Noun}
    (Sp : LOKSF (S := S) (Map := Map) lib N env P fb p) (M : MinkC3 lib P f fb) {sup : Option Nomm}
    {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S} (hcount : sixCount p ≤ 255) (b0 : 1 ≤ g0.bo)
    (d0 : g0.drop = false) (hu : UpBelow g0) (hcl0 : Clear g0) (hcb : CondBelow g0)
    (h : runLC env sup (Nomm.n3 p) CGoalL.done region g0 = some (nex, g1)) :
    DoneOK lib N P f g0 g1 nex := by
  have e3 : (runLC env sup (Nomm.n3 p) (CGoalL.done : CGoalL S) region : CM Map (NextL S)) = (do
      let (o0, o1) ← doneBlocks
      let r ← re
      let oc ← emit ⟨[], [], Termin.clq r (jmp0 o0) (jmp0 o1)⟩
      runLC env sup p (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region) := by
    conv => lhs; unfold runLC
  rw [e3] at h
  obtain ⟨⟨o0, o1⟩, g2, h2, h⟩ := bind_some h
  have B := doneBlocks_down h2 b0
  obtain ⟨D, er, eb, rfl, rfl, DB⟩ := doneBlocks_ok h2
  simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
  have d2 : g2.drop = false := D.2.2.1.trans d0
  have G : Grow g0 ({ g2 with re := g2.re + 1 }.emitted ⟨[], [], Termin.clq g2.re (jmp0 g0.bo) (jmp0 (g0.bo + 1))⟩) :=
    B.1.trans ((grow_re _).trans (grow_emit (jumpsBelow_two rfl B.2.1 B.2.2)))
  have e0 : ∀ a : Nat, entries (ofSure (lazyReg a : Sure S)) = [] := fun a => entries_ofSure _
  obtain ⟨⟨Qp, Rp⟩, pne, -, pfl, pec⟩ := Sp.run (L := ofSure (lazyReg _)) (th := jmp0 _) (Or.inr (e0 _)) hcount
    (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d2) ((G.toU hu).up hu)
    (hcl0.growU (G.toU hu))
    (CondFresh.below (condFresh_of_eq (g0 := g0) (Nat.le_trans D.1 (Nat.le_succ _))
      ((kc_doneBlocks.keep g0 _ g2 h2))) hcb)
    (by simp only [jmp0]; omega) (by simp only [jmp0, emitted_bo]; omega) rfl (by rw [e0]; simp) trivial
    (fun r hr => by
      simp only [lazyReg, ofSure, NMem] at hr; subst hr
      refine ⟨by simp [emitted_re], ?_⟩
      show HoonMap.get g2.cond _ = _
      rw [kc_doneBlocks.keep g0 _ g2 h2]; exact condBelow_none hcb D.1)
    (fun e he => by rw [e0] at he; cases he) (by rw [e0]; simp) (fun e he => by rw [e0] at he; cases he)
    (flat_ofSure _) trivial (fun e he => by rw [e0] at he; cases he) h
  have RG := Rp.toRunOKLB.toGB (fun r hr => by
    simp only [lazyReg, NMem] at hr; subst hr; simp [emitted_re])
  refine ⟨?_, pne, pfl, Sp.clean (L := ofSure (lazyReg _)) trivial h, pec⟩
  refine unaryGTB_ok (T := fun _ => wutTone) wutTone_keep M.fwd M.bwd (D.trans ((ext_re _).trans (ext_emit _ _)))
    (G.toU hu) (kc_doneBlocks.keep g0 _ g2 h2)
    ⟨by omega, by simp [emitted_re]⟩ (by simp [emitted_bo]) (fresh_emitted (by simpa using d2) rfl rfl) RG
    (fix_of_keeps (gs := g0) rfl ((keepsA_doneBlocks d0 (fun r hr => condBelow_none hcb hr) h2).trans
      ((keepsA_reg _ g2 _ (Nat.le_succ _)).trans (keepsA_emitted d2
        (blobIn_fin ⟨condBelow_none hcb D.1, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩))))
      ((keeps_doneBlocks d0 h2).trans ((keeps_reg g2 _ (Nat.le_succ _)).trans (keeps_emitted d2
        (blobIn_fin ⟨Nat.lt_succ_self _, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩)))))
    ?_
  intro c hc σ Inv ν O gul st regs t tm x hI htr hx
  have hb := emitted_get' (by simpa using d2) (hc _ (by show g0.bo ≤ g2.bo; omega) (by simp [emitted_bo]))
  have hj := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
  rw [execBlob_clq, hx, Option.bind_some] at hj
  have DB' := DB c d0 (hc.left D ((ext_re _).trans (ext_emit _ _))) lib σ O st regs t gul
  cases x with
  | atom n => exact ⟨Tone.zero (A 1), st, hI, Needs.le_refl _, hj.trans DB'.2, ToneRel.zero _⟩
  | cell u v => exact ⟨Tone.zero (A 0), st, hI, Needs.le_refl _, hj.trans DB'.1, ToneRel.zero _⟩

/-- **`LOKSF` at the goal a compile starts from** (`lokS_done`; the goal
has no entry).: the run under `%next
(lazy-from-reg re)` into the block `[don re]` meets every premise of
`LOKS.run` (a flat goal with no entry), so the run under `%done` that
begins with that block meets `DoneOK`. -/
theorem lokS_doneF {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (H : LOKSF (S := S) (Map := Map) lib N env P f nm) (hcount : sixCount nm ≤ 255)
    {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0) (hcb : CondBelow g0)
    (hr : runLC env sup nm (CGoalL.next (ofSure (lazyReg g0.re)) (jmp0 g0.bo)) region
        ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) = some (nex, g1)) :
    DoneOK lib N P f g0 g1 nex := by
  have e0 : entries (ofSure (lazyReg g0.re : Sure S)) = [] := entries_ofSure _
  have G1 : GrowU ({ g0 with re := g0.re + 1 } : Gen Map) ({ g0 with re := g0.re + 1 }.emitted ⟨[], [], Termin.don g0.re⟩) :=
    growU_emit (g := { g0 with re := g0.re + 1 }) (b := ⟨[], [], Termin.don g0.re⟩)
      (fun j hj => by simp [finJumps] at hj) hu
  obtain ⟨⟨Q, RS⟩, hne, -, hfl, hec⟩ := H.run (sup := sup) (L := ofSure (lazyReg g0.re)) (th := jmp0 g0.bo)
    (region := region) (Or.inr e0) hcount
    (by simp only [Gen.emitted]; omega) (by simp only [Gen.emitted]; exact d0) (G1.up hu)
    (Clear.growU (g := ({ g0 with re := g0.re + 1 } : Gen Map)) hcl G1)
    (fun k hk => by have := hcb k hk; simp only [Gen.emitted] at this ⊢; omega)
    b0 (by simp only [jmp0, Gen.emitted]; omega) rfl (by rw [e0]; simp) trivial
    (fun x hx => by
      simp only [lazyReg, ofSure, NMem] at hx; subst hx
      exact ⟨by simp only [Gen.emitted]; omega, condBelow_none hcb (Nat.le_refl _)⟩)
    (fun e he => by rw [e0] at he; cases he) (by rw [e0]; simp) (fun e he => by rw [e0] at he; cases he)
    (flat_ofSure _) trivial (fun e he => by rw [e0] at he; cases he) hr
  have hb : HoonMap.get g1.blocks g0.bo = some ⟨[], [], Termin.don g0.re⟩ := by
    rw [RS.keep _ (by simp only [Gen.emitted]; omega) (by rw [e0]; simp)]
    simp only [Gen.emitted, d0, Bool.false_eq_true, ↓reduceIte, HoonMap.get_put]
  have RG := RS.toRunOKLB.toGB (fun r hr => by
    simp only [lazyReg, NMem] at hr; subst hr; simp only [Gen.emitted]; omega)
  exact ⟨runOKGB_done hu hcb hb RG, hne, hfl, H.clean (L := ofSure (lazyReg g0.re)) trivial hr, hec⟩

/-- **A nomm with `LOKSF` that begins under `%done` with the block `[don
re]`** meets `DoneOK` (`runLC_done_next`, `lokS_done`). -/
theorem done_of_lokSF {lib : Lib} {N : Needs} {env : CallEnv} {P : Noun → Prop} {f : Noun} {nm : Nomm}
    (H : LOKSF (S := S) (Map := Map) lib N env P f nm) (hcount : sixCount nm ≤ 255)
    (hs : (∃ p q, nm = Nomm.cons p q) ∨ (∃ p q, nm = Nomm.n2 p q Option.none) ∨ (∃ ax, 1 ≤ ax ∧ nm = Nomm.n0 ax))
    {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl : Clear g0) (hcb : CondBelow g0)
    (hr : runLC env sup nm CGoalL.done region g0 = some (nex, g1)) : DoneOK lib N P f g0 g1 nex := by
  rw [runLC_done_next env sup hs region g0] at hr
  exact lokS_doneF H hcount b0 d0 hu hcl hcb hr

/-! ## The class with the increment -/

/-- **`CallTree7` with `[4 p]`, `[3 p]` and `[5 p q]` anywhere a flag-free
goal is**: `[0 axe]`, the cons, the indirect call, `[7 p q]`, `[4 p]`, `[3 p]`
and `[5 p q]`, with the formulas of `Annot`.  The index says whether the nomm
meets `LOKS false` at every goal (`true`) or `LOKSF` only (`false`): `[4 p]`,
`[3 p]` and `[5 p q]` read their goal's register, so they and a cons with
such a part are composed at flag-free goals only, and the `p` of `[7 p q]`,
run under `q`'s result, must have index `true`. -/
inductive CallTreeA : Bool → Noun → Nomm → Prop
  | n0 (axe : Nat) : CallTreeA true (slot axe) (Nomm.n0 axe)
  | cons {b1 b2 : Bool} {a1 a2 b : Noun} {p q : Nomm} : CallTreeA b1 (C a1 a2) p → CallTreeA b2 b q →
      CallTreeA (b2 && (b1 || !q.pure)) (C (C a1 a2) b) (Nomm.cons p q)
  | ind {b1 b2 : Bool} {b c : Noun} {p q : Nomm} : CallTreeA b1 b p → CallTreeA b2 c q →
      CallTreeA true (n3 (A 2) b c) (Nomm.n2 p q Option.none)
  | seven {b2 : Bool} {b c : Noun} {p q : Nomm} : CallTreeA true b p → CallTreeA b2 c q →
      CallTreeA b2 (n3 (A 7) b c) (Nomm.n7 p q)
  | four {b1 : Bool} {b : Noun} {p : Nomm} : CallTreeA b1 b p → CallTreeA false (n2 (A 4) b) (Nomm.n4 p)
  | three {b1 : Bool} {b : Noun} {p : Nomm} : CallTreeA b1 b p → CallTreeA false (n2 (A 3) b) (Nomm.n3 p)
  | five {b1 b2 : Bool} {b c : Noun} {p q : Nomm} : CallTreeA b1 b p → CallTreeA b2 c q →
      CallTreeA false (n3 (A 5) b c) (Nomm.n5 p q)
  | n1 (k : Noun) : CallTreeA true (quote k) (Nomm.n1 k)

theorem CallTreeA.annot {lib : Lib} {code : Bell → Option Nomm} {b : Bool} {f : Noun} {nm : Nomm}
    (h : CallTreeA b f nm) : ∀ P, Annot lib code P f nm := by
  induction h with
  | n0 axe => exact fun _ => Annot.n0
  | cons _ _ ihp ihq => exact fun P => Annot.cons (ihp P) (ihq P)
  | ind _ _ ihp ihq => exact fun P => Annot.indirect (ihp P) (ihq P)
  | @seven b2 b c p q _ _ ihp ihq => exact fun P => Annot.n7 (ihp P) (ihq (Img lib P b))
  | four _ ihp => exact fun P => Annot.n4 (ihp P)
  | three _ ihp => exact fun P => Annot.n3 (ihp P)
  | five _ _ ihp ihq => exact fun P => Annot.n5 (ihp P) (ihq P)
  | n1 k => exact fun _ => Annot.n1

theorem CallTreeA.cell {b : Bool} {f : Noun} {nm : Nomm} (h : CallTreeA b f nm) : ∃ a b, f = C a b := by
  cases h with
  | n0 axe => exact ⟨_, _, rfl⟩
  | cons _ _ => exact ⟨_, _, rfl⟩
  | ind _ _ => exact ⟨_, _, rfl⟩
  | seven _ _ => exact ⟨_, _, rfl⟩
  | four _ => exact ⟨_, _, rfl⟩
  | three _ => exact ⟨_, _, rfl⟩
  | five _ _ => exact ⟨_, _, rfl⟩
  | n1 k => exact ⟨_, _, rfl⟩

theorem CallTreeA.sixCount {b : Bool} {f : Noun} {nm : Nomm} (h : CallTreeA b f nm) : sixCount nm = 0 := by
  induction h with
  | n0 axe => rfl
  | cons _ _ ihp ihq => simp only [Comp.sixCount, ihp, ihq]
  | ind _ _ ihp ihq => simp only [Comp.sixCount, ihp, ihq]
  | seven _ _ ihp ihq => simp only [Comp.sixCount, ihp, ihq]
  | four _ ihp => simp only [Comp.sixCount, ihp]
  | three _ ihp => simp only [Comp.sixCount, ihp]
  | five _ _ ihp ihq => simp only [Comp.sixCount, ihp, ihq]
  | n1 k => rfl

theorem CallTreeA.hinted_of {b : Bool} {f : Noun} {nm : Nomm} (h : CallTreeA b f nm) (cod : Bell → Option Bool) :
    nm.pure = false → hinted cod nm = some true := by
  induction h with
  | n0 axe => intro e; cases e
  | @cons b1 b2 a1 a2 b p q _ _ ihp ihq =>
    intro e
    simp only [hinted]
    cases ep : p.pure
    · rw [ihp ep]; rfl
    · rw [hinted_pure cod p ep]
      exact ihq (by simpa only [Nomm.pure, ep, Bool.true_and] using e)
  | ind _ _ => intro _; rfl
  | @seven b2 b c p q _ _ ihp ihq =>
    intro e
    simp only [hinted]
    cases ep : p.pure
    · rw [ihp ep]; rfl
    · rw [hinted_pure cod p ep]
      exact ihq (by simpa only [Nomm.pure, ep, Bool.true_and] using e)
  | four _ ihp =>
    intro e
    simp only [hinted]
    exact ihp (by simpa only [Nomm.pure] using e)
  | three _ ihp =>
    intro e
    simp only [hinted]
    exact ihp (by simpa only [Nomm.pure] using e)
  | @five b1 b2 b c p q _ _ ihp ihq =>
    intro e
    simp only [hinted]
    cases ep : p.pure
    · rw [ihp ep]; rfl
    · rw [hinted_pure cod p ep]
      exact ihq (by simpa only [Nomm.pure, ep, Bool.true_and] using e)
  | n1 k => intro e; cases e

/-- **Each nomm of the class is call-free with `MinkEq`, or hinted.** -/
theorem CallTreeA.kind (lib : Lib) (cod : Bell → Option Bool) (P : Noun → Prop) {b : Bool} {f : Noun} {nm : Nomm}
    (h : CallTreeA b f nm) : (nm.pure = true ∧ MinkEq lib P f nm) ∨ hinted cod nm = some true := by
  have hok : CodeOK lib (fun _ => Option.none) := fun _ _ h => by cases h
  cases hp : nm.pure
  · exact Or.inr (h.hinted_of cod hp)
  · exact Or.inl ⟨rfl, fun s hs gul tm r => mink_pure hok hp (h.annot P) hs gul tm r⟩

/-- **Every nomm of `CallTreeA` meets `LOKSF`** on any subjects (a hinted one
`JNewLSF`), and one of index `true` `LOKS false` (a hinted one `JNewLS`),
with only the premises of `LOKS.run` on the starting goal and state. -/
theorem lokS_callTreeA (lib : Lib) {N : Needs} (env : CallEnv) {b : Bool} {f : Noun} {nm : Nomm} (h : CallTreeA b f nm) :
    ∀ P, (LOKSF (S := S) (Map := Map) lib N env P f nm ∧
        (hinted env.cod nm = some true → JNewLSF (S := S) (Map := Map) env nm)) ∧
      (b = true → LOKS (S := S) (Map := Map) false lib N env P f nm ∧
        (hinted env.cod nm = some true → JNewLS (S := S) (Map := Map) env nm)) := by
  induction h with
  | n0 axe =>
    intro P
    have M := ((CallTreeA.n0 axe).kind lib env.cod P).elim (fun h => h.2) (fun h => by cases h)
    have H : LOKS (S := S) (Map := Map) false lib N env P (slot axe) (Nomm.n0 axe) := by
      rcases Nat.eq_zero_or_pos axe with rfl | ha
      · exact lokS_n00 lib env M
      · exact lokS_n0 lib env ha M
    exact ⟨⟨H.toF, fun h => by cases h⟩, fun _ => ⟨H, fun h => by cases h⟩⟩
  | @cons b1 b2 a1 a2 b p q hp hq ihp ihq =>
    intro P
    have Kp := hp.kind lib env.cod P
    have Kq := hq.kind lib env.cod P
    refine ⟨⟨lokS_consF lib env ⟨_, _, rfl⟩ Kp Kq (ihq P).1.2 (ihp P).1.1 (ihq P).1.1,
      fun _ => jNewLSF_cons lib env ⟨_, _, rfl⟩ Kp Kq (ihq P).1.2 (ihp P).1.1 (ihq P).1.1⟩, fun hb => ?_⟩
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hb
    obtain ⟨Lq, Jq⟩ := (ihq P).2 hb.1
    rcases hb.2 with h1 | h1
    · obtain ⟨Lp, -⟩ := (ihp P).2 h1
      exact ⟨lokS_consS lib env ⟨_, _, rfl⟩ Kp Kq Jq Lp Lq, fun _ => jNewLS_cons lib env ⟨_, _, rfl⟩ Kp Kq Jq Lp Lq⟩
    · have hqh := hq.hinted_of env.cod h1
      exact ⟨lokS_consH lib env ⟨_, _, rfl⟩ Kp Kq Jq hqh (ihp P).1.1 Lq,
        fun _ => jNewLS_consH lib env ⟨_, _, rfl⟩ Kp Kq Jq hqh (ihp P).1.1 Lq⟩
  | @ind b1 b2 b c p q hp hq ihp ihq =>
    intro P
    have Kp := hp.kind lib env.cod P
    have L := lokS_indirectF lib env (minkC2_indirect lib P b c) hp.cell Kp (ihp P).1.1 (ihq P).1.1
    have J : JNewLS (S := S) (Map := Map) env (Nomm.n2 p q Option.none) := jNewLS_indirectF lib env (minkC2_indirect lib P b c) hp.cell Kp (ihp P).1.1 (ihq P).1.1
    exact ⟨⟨L.toF, fun _ => J.toF⟩, fun _ => ⟨L, fun _ => J⟩⟩
  | @seven b2 b c p q hp hq ihp ihq =>
    intro P
    obtain ⟨Lp, Jp⟩ := (ihp P).2 rfl
    refine ⟨⟨lokS_sevenF (ihq (Img lib P b)).1.1 Lp, jNewLSF_seven (ihq (Img lib P b)).1.1 Lp (ihq (Img lib P b)).1.2 Jp⟩,
      fun hb => ?_⟩
    obtain ⟨Lq, Jq⟩ := (ihq (Img lib P b)).2 hb
    exact ⟨lokS_seven Lq Lp, jNewLS_seven Lq Lp Jq Jp⟩
  | @four b1 b p hp ihp =>
    intro P
    have L := lokS_four lib env (minkC4_four lib P b) (ihp P).1.1
    have J : JNewLS (S := S) (Map := Map) env (Nomm.n4 p) := jNewLS_four lib env (minkC4_four lib P b) (ihp P).1.1
    exact ⟨⟨L.toF, fun _ => J.toF⟩, fun h => by cases h⟩
  | @three b1 b p hp ihp =>
    intro P
    have L := lokS_three lib env (minkC3_three lib P b) (ihp P).1.1
    have J : hinted env.cod (Nomm.n3 p) = some true → JNewLS (S := S) (Map := Map) env (Nomm.n3 p) :=
      jNewLS_three lib env (minkC3_three lib P b) (ihp P).1.1 (ihp P).1.2
    exact ⟨⟨L.toF, fun hh => JNewLS.toF (J hh)⟩, fun h => by cases h⟩
  | @five b1 b2 b c p q hp hq ihp ihq =>
    intro P
    have Kp := hp.kind lib env.cod P
    have L := lokS_five lib env (minkC5_five lib P b c) hp.cell Kp (ihp P).1.1 (ihq P).1.1
    have J : JNewLS (S := S) (Map := Map) env (Nomm.n5 p q) :=
      jNewLS_five (N := N) lib env (minkC5_five lib P b c) hp.cell Kp (ihp P).1.1 (ihq P).1.1
    exact ⟨⟨L.toF, fun _ => J.toF⟩, fun h => by cases h⟩
  | n1 k =>
    intro P
    have M := ((CallTreeA.n1 k).kind lib env.cod P).elim (fun h => h.2) (fun h => by cases h)
    have H : LOKS (S := S) (Map := Map) false lib N env P (quote k) (Nomm.n1 k) := lokS_n1 lib env M
    exact ⟨⟨H.toF, fun h => by cases h⟩, fun _ => ⟨H, fun h => by cases h⟩⟩

/-- **Every nomm of `CallTreeA` under `%done` meets `DoneOK`**: `[0 axe]`
by `callTree_done`, the cons and the indirect call by `done_of_lokSF`,
`[7 p q]` as in `callTree7_done`, `[4 p]` by `four_doneB`. -/
theorem callTreeA_done (lib : Lib) {N : Needs} (env : CallEnv) {b : Bool} {f : Noun} {nm : Nomm} (h : CallTreeA b f nm) :
    ∀ (P : Noun → Prop) {sup : Option Nomm} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S},
    1 ≤ g0.bo → g0.drop = false → UpBelow g0 → Clear g0 → CondBelow g0 →
    runLC env sup nm CGoalL.done region g0 = some (nex, g1) → DoneOK (S := S) (Map := Map) lib N P f g0 g1 nex := by
  induction h with
  | n0 axe =>
    intro P sup region g0 g1 nex b0 d0 hu hcl hcb hr
    exact callTree_done lib env P (CallTree.n0 axe) b0 d0 hu hcl hcb hr
  | @cons b1 b2 a1 a2 b p q hp hq _ _ =>
    intro P sup region g0 g1 nex b0 d0 hu hcl hcb hr
    have hc := CallTreeA.cons hp hq
    exact done_of_lokSF (lokS_callTreeA lib env hc P).1.1 (by rw [hc.sixCount]; omega) (Or.inl ⟨_, _, rfl⟩)
      b0 d0 hu hcl hcb hr
  | @ind b1 b2 b c p q hp hq _ _ =>
    intro P sup region g0 g1 nex b0 d0 hu hcl hcb hr
    have hc := CallTreeA.ind hp hq
    exact done_of_lokSF (lokS_callTreeA lib env hc P).1.1 (by rw [hc.sixCount]; omega)
      (Or.inr (Or.inl ⟨_, _, rfl⟩)) b0 d0 hu hcl hcb hr
  | @seven b2 b c p q hp hq _ ihq =>
    intro P sup region g0 g1 nex b0 d0 hu hcl hcb hr
    rw [runLC_n7] at hr
    obtain ⟨nx, ga, h1, h2⟩ := bind_some hr
    have D := ihq (Img lib P b) b0 d0 hu hcl hcb h1
    have Rq := D.run
    have Lp := ((lokS_callTreeA (S := S) (Map := Map) lib (N := N) env hp P).2 rfl).1
    have hj : nx.th.args = [] := by
      rcases Rq.ent with ⟨_, _, _, ha⟩ | e
      · exact ha
      · exact e.elim
    obtain ⟨⟨Q, RS⟩, hne, -, hfl, hec⟩ := Lp.run (sup := sup) (L := nx.laz) (th := nx.th) (region := region)
      (by rw [hp.sixCount]; omega) (by have := Rq.ext.2.1; omega) (Rq.ext.2.2.1.trans d0) (Rq.grow.up hu)
      (Clear.growU hcl Rq.grow) (Rq.cfr.below hcb) Rq.lo Rq.hi hj D.nent Rq.dist
      (fun x hx => ⟨by
        rcases Rq.regs x hx with e | e
        · exact e.elim
        · exact e.2, Rq.ncond x hx⟩)
      (fun e he => ⟨(Rq.labs e he).2.1, (Rq.labs e he).2.2⟩) Rq.nodup
      (fun e he => ⟨(Rq.eregs e he).1, fun x hx => ⟨((Rq.eregs e he).2 x hx).2, Rq.econd e he x hx⟩⟩)
      D.flat D.clean D.eclean h2
    exact ⟨runOKGB_sevenL (minkC7_seven lib P b c) Rq RS.toRunOKLB (fun r hr => hr.elim), hne, hfl,
      Lp.clean (L := nx.laz) D.clean h2, hec⟩
  | @four b1 b p hp _ =>
    intro P sup region g0 g1 nex b0 d0 hu hcl hcb hr
    exact four_doneB lib (lokS_callTreeA lib env hp P).1.1 (minkC4_four lib P b) (by rw [hp.sixCount]; omega)
      b0 d0 hu hcl hcb hr
  | @three b1 b p hp _ =>
    intro P sup region g0 g1 nex b0 d0 hu hcl hcb hr
    exact three_doneB lib (lokS_callTreeA lib env hp P).1.1 (minkC3_three lib P b) (by rw [hp.sixCount]; omega)
      b0 d0 hu hcl hcb hr
  | @five b1 b2 b c p q hp hq _ _ =>
    intro P sup region g0 g1 nex b0 d0 hu hcl hcb hr
    exact five_doneB lib (minkC5_five lib P b c) hp.cell (hp.kind lib env.cod P) (lokS_callTreeA lib env hp P).1.1
      (lokS_callTreeA lib env hq P).1.1 (by rw [(CallTreeA.five hp hq).sixCount]; omega) b0 d0 hu hcl hcb hr
  | n1 k =>
    intro P sup region g0 g1 nex b0 d0 hu hcl hcb hr
    exact n1_doneB lib env (((CallTreeA.n1 k).kind lib env.cod P).elim (fun h => h.2) (fun h => by cases h))
      b0 d0 hu hcl hcb hr

/-- **The contract of `CallTreeA` at the top**: the whole-subject code of
every nomm of the class meets both halves of the contract for its formula,
on every subject, with no hypothesis about the run. -/
theorem finishLUC_contractCallTreeA (lib : Lib) (env : CallEnv) (P : Noun → Prop) {b : Bool} {f : Noun} {nm : Nomm}
    (h : CallTreeA b f nm) {c : Straight Map} (hc : finishLUC (S := S) env nm = some c) (N : Needs) :
    c.need = NeedOrd.this ∧ ∀ s, P s → ContractFwd lib N s f [s] c ∧ ContractBwd lib N s f [s] c :=
  finishLUC_contractGB lib N (fun hr => (callTreeA_done (S := S) (Map := Map) lib env h P (by simp [gen0]) rfl
    upBelow_gen0 clear_gen0 condBelow_gen0 hr).run) hc

/-- **The bell contract of `CallTreeA`** (`finishLUC_contractNC`'s form). -/
theorem finishLUC_bellContractCallTreeA {lib : Lib} {bl : Bell} {b : Bool} {nm : Nomm} (h : CallTreeA b bl.fol nm)
    {env : CallEnv} {cd : Straight Map} (hc : finishLUC (S := S) env nm = some cd) (N : Needs) :
    cd.need = NeedOrd.this ∧ BellContract lib N bl true cd := by
  have H := finishLUC_contractCallTreeA (S := S) lib env (SkaModel.Fits bl.less) h hc N
  refine ⟨H.1, fun s hs args hargs => ?_⟩
  simp only [if_true, Option.some.injEq] at hargs
  subst hargs
  exact H.2 s hs

/-- `CallTree7` is inside `CallTreeA` (index `true`). -/
theorem CallTree7.toA {f : Noun} {nm : Nomm} (h : CallTree7 f nm) : CallTreeA true f nm := by
  induction h with
  | n0 axe => exact CallTreeA.n0 axe
  | cons _ _ ihp ihq => exact CallTreeA.cons ihp ihq
  | ind _ _ ihp ihq => exact CallTreeA.ind ihp ihq
  | seven _ _ ihp ihq => exact CallTreeA.seven ihp ihq

/-! ## Examples -/

/-- `[4 [2 [0 3] [0 2]]]`: the increment of an indirect call. -/
theorem fourInd_contract (lib : Lib) (env : CallEnv) {c : Straight Map}
    (hc : finishLUC (S := S) (Map := Map) env (Nomm.n4 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) = some c)
    (N : Needs) : c.need = NeedOrd.this ∧ ∀ s,
      ContractFwd lib N s (n2 (A 4) (n3 (A 2) (slot 3) (slot 2))) [s] c ∧
      ContractBwd lib N s (n2 (A 4) (n3 (A 2) (slot 3) (slot 2))) [s] c :=
  have H := finishLUC_contractCallTreeA lib env (fun _ => True)
    (CallTreeA.four (CallTreeA.ind (CallTreeA.n0 3) (CallTreeA.n0 2))) hc N
  ⟨H.1, fun s => H.2 s trivial⟩

/-- `[3 [2 [0 3] [0 2]]]`: the cell test of an indirect call. -/
theorem threeInd_contract (lib : Lib) (env : CallEnv) {c : Straight Map}
    (hc : finishLUC (S := S) (Map := Map) env (Nomm.n3 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) = some c)
    (N : Needs) : c.need = NeedOrd.this ∧ ∀ s,
      ContractFwd lib N s (n2 (A 3) (n3 (A 2) (slot 3) (slot 2))) [s] c ∧
      ContractBwd lib N s (n2 (A 3) (n3 (A 2) (slot 3) (slot 2))) [s] c :=
  have H := finishLUC_contractCallTreeA lib env (fun _ => True)
    (CallTreeA.three (CallTreeA.ind (CallTreeA.n0 3) (CallTreeA.n0 2))) hc N
  ⟨H.1, fun s => H.2 s trivial⟩

/-- `[5 [2 [0 3] [0 2]] [0 1]]`: the equality test of an indirect call and
the subject. -/
theorem fiveInd_contract (lib : Lib) (env : CallEnv) {c : Straight Map}
    (hc : finishLUC (S := S) (Map := Map) env
      (Nomm.n5 (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none) (Nomm.n0 1)) = some c)
    (N : Needs) : c.need = NeedOrd.this ∧ ∀ s,
      ContractFwd lib N s (n3 (A 5) (n3 (A 2) (slot 3) (slot 2)) (slot 1)) [s] c ∧
      ContractBwd lib N s (n3 (A 5) (n3 (A 2) (slot 3) (slot 2)) (slot 1)) [s] c :=
  have H := finishLUC_contractCallTreeA lib env (fun _ => True)
    (CallTreeA.five (CallTreeA.ind (CallTreeA.n0 3) (CallTreeA.n0 2)) (CallTreeA.n0 1)) hc N
  ⟨H.1, fun s => H.2 s trivial⟩

/-- `[[4 [0 2]] [2 [0 3] [0 2]]]`: an increment as the head of a cons whose
tail calls (the head runs under the parked goal, whose sure part is the
bunt). -/
theorem fourCons_contract (lib : Lib) (env : CallEnv) {c : Straight Map}
    (hc : finishLUC (S := S) (Map := Map) env
      (Nomm.cons (Nomm.n4 (Nomm.n0 2)) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) = some c)
    (N : Needs) : c.need = NeedOrd.this ∧ ∀ s,
      ContractFwd lib N s (C (n2 (A 4) (slot 2)) (n3 (A 2) (slot 3) (slot 2))) [s] c ∧
      ContractBwd lib N s (C (n2 (A 4) (slot 2)) (n3 (A 2) (slot 3) (slot 2))) [s] c :=
  have H := finishLUC_contractCallTreeA lib env (fun _ => True)
    (CallTreeA.cons (CallTreeA.four (CallTreeA.n0 2)) (CallTreeA.ind (CallTreeA.n0 3) (CallTreeA.n0 2))) hc N
  ⟨H.1, fun s => H.2 s trivial⟩


/-- `[7 [[1 5] [0 1]] [2 [0 3] [0 2]]]`: a constant under `%next` in the
head of a cons that `[7 p q]` puts under the result of an indirect call (the
form of `%dt`'s outer `%7`, README Gaps 12.31). -/
theorem oneSeven_contract (lib : Lib) (env : CallEnv) {c : Straight Map}
    (hc : finishLUC (S := S) (Map := Map) env
      (Nomm.n7 (Nomm.cons (Nomm.n1 (A 5)) (Nomm.n0 1)) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) = some c)
    (N : Needs) : c.need = NeedOrd.this ∧ ∀ s,
      ContractFwd lib N s (n3 (A 7) (C (quote (A 5)) (slot 1)) (n3 (A 2) (slot 3) (slot 2))) [s] c ∧
      ContractBwd lib N s (n3 (A 7) (C (quote (A 5)) (slot 1)) (n3 (A 2) (slot 3) (slot 2))) [s] c :=
  have H := finishLUC_contractCallTreeA lib env (fun _ => True)
    (CallTreeA.seven (CallTreeA.cons (CallTreeA.n1 (A 5)) (CallTreeA.n0 1))
      (CallTreeA.ind (CallTreeA.n0 3) (CallTreeA.n0 2))) hc N
  ⟨H.1, fun s => H.2 s trivial⟩

/-- `[[1 0] [4 [0 1]]]`: a constant as the head of a cons whose tail is an
increment. -/
theorem oneCons_contract (lib : Lib) (env : CallEnv) {c : Straight Map}
    (hc : finishLUC (S := S) (Map := Map) env (Nomm.cons (Nomm.n1 (A 0)) (Nomm.n4 (Nomm.n0 1))) = some c)
    (N : Needs) : c.need = NeedOrd.this ∧ ∀ s,
      ContractFwd lib N s (C (quote (A 0)) (n2 (A 4) (slot 1))) [s] c ∧
      ContractBwd lib N s (C (quote (A 0)) (n2 (A 4) (slot 1))) [s] c :=
  have H := finishLUC_contractCallTreeA lib env (fun _ => True)
    (CallTreeA.cons (CallTreeA.n1 (A 0)) (CallTreeA.four (CallTreeA.n0 1))) hc N
  ⟨H.1, fun s => H.2 s trivial⟩


/-- `[7 [[4 [0 2]] [2 [0 3] [0 2]]] [2 [0 3] [0 2]]]`: a cons with an
increment head and a calling tail (index `true`, README Gaps 12.31) as the
`p` of `[7 p q]`. -/
theorem fourConsSeven_contract (lib : Lib) (env : CallEnv) {c : Straight Map}
    (hc : finishLUC (S := S) (Map := Map) env
      (Nomm.n7 (Nomm.cons (Nomm.n4 (Nomm.n0 2)) (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none))
        (Nomm.n2 (Nomm.n0 3) (Nomm.n0 2) Option.none)) = some c)
    (N : Needs) : c.need = NeedOrd.this ∧ ∀ s,
      ContractFwd lib N s (n3 (A 7) (C (n2 (A 4) (slot 2)) (n3 (A 2) (slot 3) (slot 2)))
        (n3 (A 2) (slot 3) (slot 2))) [s] c ∧
      ContractBwd lib N s (n3 (A 7) (C (n2 (A 4) (slot 2)) (n3 (A 2) (slot 3) (slot 2)))
        (n3 (A 2) (slot 3) (slot 2))) [s] c :=
  have H := finishLUC_contractCallTreeA lib env (fun _ => True)
    (CallTreeA.seven (CallTreeA.cons (CallTreeA.four (CallTreeA.n0 2)) (CallTreeA.ind (CallTreeA.n0 3) (CallTreeA.n0 2)))
      (CallTreeA.ind (CallTreeA.n0 3) (CallTreeA.n0 2))) hc N
  ⟨H.1, fun s => H.2 s trivial⟩

end Comp
end SkaModel
end Formalization
