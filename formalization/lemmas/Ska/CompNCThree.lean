import lemmas.Ska.CompNCFour

/-!
# `[3 p]` with a calling `p` at level `0`

README Gaps 12.22, the case `[3 p]` with calls of the table of
`CompNC.lean`.  The raw blocks (`tools/hoon/calldump4.hoon`, `%i3`, `[3 [2
[0 3] [0 2]]]`): `0: v0 -> cel, hed -> v6, tal -> v5, hop 5`; `5: nok v5 v6
-> v4`; `4: mov v4 v3` (the call's `+kerf` into `v3`); `3: clq v3 -> 1 | 2`;
`1: imm 0 v1, don v1`; `2: imm 1 v2, don v2` (the two blocks of
`doneBlocks`).  Under a fork-free `%next` that asks something, the `clq`
goes to the two blocks of `+forl`, which write `0` or `1` into the register
of `+collapse-lazy-atom`; under one that asks nothing, `p` runs under the
goal itself.

* `wutTone`, `MinkC3`, `minkC3_three`: `+mink` on `[3 b]`.
* `unaryGT_ok`: `unaryGC_ok` for any tone transform that keeps the tones
  that are no product.
* `three_runD`, `three_runN` (both branches of the case), `okc_threeC`,
  `uokc_threeC`, `uokc_threeA`.
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

/-! ## `+mink` on `[3 b]` -/

/-- The tone of `[3 b]` from the tone of `b`. -/
def wutTone : Tone → Tone
  | Tone.zero x => Tone.zero (wut x)
  | r => r

/-- **`+mink` on `f` is the cell test of `+mink` on `fb`.** -/
structure MinkC3 (lib : Lib) (P : Noun → Prop) (f fb : Noun) : Prop where
  fwd : ∀ {s gul : Noun} {n : Nat} {tm : Trace} {r : Tone}, P s → minkF lib gul n tm s f = some r →
    ∃ n', n' ≤ n ∧ ∃ rb, minkF lib gul n' tm s fb = some rb ∧ r = wutTone rb
  bwd : ∀ {s gul : Noun} {tm : Trace} {rb : Tone}, P s → Mink lib gul tm s fb rb → Mink lib gul tm s f (wutTone rb)

theorem minkC3_three (lib : Lib) (P : Noun → Prop) (b : Noun) : MinkC3 lib P (n2 (A 3) b) b where
  fwd := fun {s gul n tm r} _ h => by
    obtain ⟨m, rfl⟩ := minkF_pos h
    rw [minkF_succ_eq] at h
    simp only [n2, minkStep] at h
    rcases tbind_eq_some h with ⟨y, hy, h1⟩ | ⟨hb, hnz⟩
    · refine ⟨m, Nat.le_succ m, _, hy, ?_⟩
      simp only [Option.some.injEq] at h1; rw [← h1]; rfl
    · refine ⟨m, Nat.le_succ m, r, hb, ?_⟩
      cases r with
      | zero p => exact absurd rfl (hnz p)
      | one _ => rfl
      | two _ => rfl
  bwd := fun {s gul tm rb} _ hb => by
    obtain ⟨n, h⟩ := hb
    refine ⟨n + 1, ?_⟩
    rw [minkF_succ_eq]
    simp only [n2, minkStep]
    rw [h]
    cases rb with
    | zero y => rfl
    | one _ => rfl
    | two _ => rfl

/-! ## The composition for any tone transform -/

/-- **`unaryGC_ok` for a tone transform `T`** that keeps the tones that are
no product (`hT`), with `+mink` on `f` the transform of `+mink` on `fb`
(`fw`, `bw`). -/
theorem unaryGT_ok {lib : Lib} {P : Noun → Prop} {f fb : Noun} {T : Trace → Tone → Tone}
    (hT : ∀ tm r, (∀ p, r ≠ Tone.zero p) → T tm r = r)
    (fw : ∀ {s gul : Noun} {n : Nat} {tm : Trace} {r : Tone}, P s → minkF lib gul n tm s f = some r →
      ∃ n', n' ≤ n ∧ ∃ rb, minkF lib gul n' tm s fb = some rb ∧ r = T tm rb)
    (bw : ∀ {s gul : Noun} {tm : Trace} {rb : Tone}, P s → Mink lib gul tm s fb rb → Mink lib gul tm s f (T tm rb))
    {goal : CGoal S} {g0 g' g1 : Gen Map} {a o : Nat} {nexp : NextL S}
    (hpre : Ext g0 g') (hgr : GrowU g0 g') (hcnd : g'.cond = g0.cond) (ha : g0.re ≤ a ∧ a < g'.re)
    (ho : o < g'.bo) (hfr : Fresh g' (jmp0 o))
    (hp : RunOKGC (Map := Map) lib P fb (CGoal.next (lazyReg a) (jmp0 o)) g' g1 nexp)
    (hfix : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g0.cond k) →
      ∀ k, g0.bo ≤ k → k < g'.bo → (HoonMap.get g'.blocks k).map (unproxyBlob cf) = HoonMap.get g'.blocks k)
    (hblk : ∀ (c : Straight Map), Agree c g0 g' → ∀ (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ)
      (gul : Noun) (st : σ) (regs : Map (Option Noun)) (t tm : Trace) (x : Noun), Inv st →
      Forall2 (FrameRel lib (ν st)) t tm → SkaModel.read a regs = some x →
      GoalSemCM lib O c gul Inv ν (Keep g0 g' goal) st regs t tm (jmp0 o) goal (T tm (Tone.zero x))) :
    RunOKGC lib P f goal g0 g1 nexp := by
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
      (∀ st' : σ, AgreeU lib O c gul st' t cf ned g0 g1 nexp.laz s0 s) → (∀ x, NMem ned x → g1.re ≤ x) →
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
      (st : σ) (t : Trace) (s0 s : Noun), AgreeU lib O c gul st t cf ned g0 g1 nexp.laz s0 s →
      AgreeU lib O c gul st t cf ned g' g1 nexp.laz s0 s :=
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
  · intro cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    obtain ⟨n', hn', rb, hb, rfl⟩ := fw hs hm
    exact conv cf hcf c ned σ Inv ν O gul st t tm s0 s hI htr ag hned regs rb
      (hp.sem cf hcf c ned σ Inv ν O n' gul hS (oracleFwd_le hF hn') st t tm s0 s rb hI htr hs hb
        (fun st' => agP cf c ned σ O gul st' t s0 s (ag st')) hned regs hh hn)
  · intro cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨rb, hmb, G⟩ := hp.semB cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs
      (fun st' => agP cf c ned σ O gul st' t s0 s (ag st')) hned regs hh hn res hres
    exact ⟨_, bw hs hmb, conv cf hcf c ned σ Inv ν O gul st t tm s0 s hI htr ag hned regs rb G⟩

/-! ## The runs of `[3 p]` -/

theorem wutTone_keep (tm : Trace) (r : Tone) (hr : ∀ p, r ≠ Tone.zero p) : (fun _ => wutTone) tm r = r := by
  cases r with
  | zero p => exact absurd rfl (hr p)
  | one _ => rfl
  | two _ => rfl

/-- **`[3 p]` for `%done` with an operand that may call**: `doneBlocks`,
the `clq` block, then the operand (`unaryGT_ok`, the blocks as in
`runOKV_n3D`). -/
theorem three_runD (lib : Lib) {p : Nomm} {env : CallEnv} {P : Noun → Prop} {f fb : Noun}
    (Up : UOKC (S := S) (Map := Map) lib env P fb p) (M : MinkC3 lib P f fb) {sup : Option Nomm}
    {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S} (hcount : sixCount p ≤ 255) (b0 : 1 ≤ g0.bo)
    (d0 : g0.drop = false) (hu : UpBelow g0) (hcl0 : Clear g0) (hcb : CondBelow g0)
    (h : runLC env sup (Nomm.n3 p) (CGoal.toL (CGoal.done : CGoal S)) region g0 = some (nex, g1)) :
    RunOKGC lib P f (CGoal.done : CGoal S) g0 g1 nex := by
  have e3 : (runLC env sup (Nomm.n3 p) (CGoal.toL (CGoal.done : CGoal S)) region : CM Map (NextL S)) = (do
      let (o0, o1) ← doneBlocks
      let r ← re
      let oc ← emit ⟨[], [], Termin.clq r (jmp0 o0) (jmp0 o1)⟩
      runLC env sup p (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region) := by
    conv => lhs; unfold runLC
    rfl
  rw [e3] at h
  obtain ⟨⟨o0, o1⟩, g2, h2, h⟩ := bind_some h
  have B := doneBlocks_down h2 b0
  obtain ⟨D, er, eb, rfl, rfl, DB⟩ := doneBlocks_ok h2
  simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
  have d2 : g2.drop = false := D.2.2.1.trans d0
  have G : Grow g0 ({ g2 with re := g2.re + 1 }.emitted ⟨[], [], Termin.clq g2.re (jmp0 g0.bo) (jmp0 (g0.bo + 1))⟩) :=
    B.1.trans ((grow_re _).trans (grow_emit (jumpsBelow_two rfl B.2.1 B.2.2)))
  have Rp := Up.run (goal := CGoal.next (lazyReg _) (jmp0 _)) trivial rfl
    ⟨by simp only [jmp0]; omega, by simp only [jmp0, emitted_bo]; omega⟩
    (by exact ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; simp [emitted_re]⟩) (by exact trivial)
    hcount (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d2) ((G.toU hu).up hu)
    (hcl0.growU (G.toU hu))
    (CondFresh.below (condFresh_of_eq (g0 := g0) (Nat.le_trans D.1 (Nat.le_succ _))
      ((kc_doneBlocks.keep g0 _ g2 h2))) hcb)
    (fun r hr => by
      simp only [lazyReg, NMem] at hr; subst hr
      show HoonMap.get g2.cond _ = _
      rw [kc_doneBlocks.keep g0 _ g2 h2]; exact condBelow_none hcb D.1) h
  refine unaryGT_ok (T := fun _ => wutTone) wutTone_keep M.fwd M.bwd (D.trans ((ext_re _).trans (ext_emit _ _)))
    (G.toU hu) (kc_doneBlocks.keep g0 _ g2 h2)
    ⟨by omega, by simp [emitted_re]⟩ (by simp [emitted_bo]) (fresh_emitted (by simpa using d2) rfl rfl) Rp
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

/-- **`[3 p]` under a fork-free `%next` that asks nothing**: `p` runs under
the goal itself, and the goal takes any product. -/
theorem three_of_none {lib : Lib} {P : Noun → Prop} {f fb : Noun} (M : MinkC3 lib P f fb) {sur : Sure S} {th : Jmp}
    {g0 g1 : Gen Map} {nex : NextL S} (hn : sur.ned = Need.none) (hl : ∀ x ∈ HoonSet.toList sur.lok, x = 1)
    (hp : RunOKGC (Map := Map) lib P fb (CGoal.next sur th) g0 g1 nex) :
    RunOKGC lib P f (CGoal.next sur th) g0 g1 nex := by
  have hfit : ∀ v, FitsS sur v := fun v => ⟨by rw [hn]; trivial, fun y hy => by rw [hl y hy]; simp⟩
  have conv : ∀ {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {Inv : σ → Prop} {ν : σ → Needs}
      {K : Nat → Prop} {st : σ} {regs : Map (Option Noun)} {t tm : Trace} {je : Jmp} (rb : Tone),
      GoalSemCM lib O c gul Inv ν K st regs t tm je (CGoal.next sur th) rb →
      GoalSemCM lib O c gul Inv ν K st regs t tm je (CGoal.next sur th) (wutTone rb) := by
    intro σ O c gul Inv ν K st regs t tm je rb G
    cases rb with
    | zero x =>
      obtain ⟨st', R, hI, hle, _, hk, e⟩ := G.1 (hfit x)
      exact ⟨fun _ => ⟨st', R, hI, hle, by rw [hn]; trivial, hk, e⟩, fun hf => absurd (hfit _) hf⟩
    | one q => exact G
    | two tr => exact G
  have bad : ∀ {tm : Trace} {r : Tone}, BadC (CGoal.next sur th) tm r → r = Tone.two tm := fun hb => by
    rcases hb with e | ⟨q, _, hq⟩
    · exact e
    · exact absurd (hfit q) hq
  refine ⟨hp.ext, hp.grow, hp.cfr, hp.lo, hp.hi, hp.ent, hp.regs, hp.dist, hp.eregs, hp.labs, hp.nodup,
    fun s hs hf => ⟨fun gul n tm r hm => ?_, fun gul tm => ?_⟩, hp.ncond, hp.econd, ?_, ?_⟩
  · obtain ⟨n', _, rb, hb, rfl⟩ := M.fwd hs hm
    rw [bad ((hp.nec s hs hf).1 gul n' tm rb hb)]
    exact Or.inl rfl
  · obtain ⟨rb, hmb, hbad⟩ := (hp.nec s hs hf).2 gul tm
    refine ⟨_, M.bwd hs hmb, ?_⟩
    rw [bad hbad]
    exact Or.inl rfl
  · intro cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn'
    obtain ⟨n', hn'', rb, hb, rfl⟩ := M.fwd hs hm
    exact conv rb (hp.sem cf hcf c ned σ Inv ν O n' gul hS (oracleFwd_le hF hn'') st t tm s0 s rb hI htr hs hb ag
      hned regs hh hn')
  · intro cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn' res hres
    obtain ⟨rb, hmb, G⟩ := hp.semB cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn' res hres
    exact ⟨_, M.bwd hs hmb, conv rb G⟩

/-- **`[3 p]` under a fork-free `%next` with an operand that may call**: the
operand under the goal itself when it asks nothing (`three_of_none`); else
`+collapse-lazy-atom`, `+forl`, the `clq` block, then the operand
(`unaryGT_ok`, the blocks as in `runOKNV_n3`). -/
theorem three_runN (lib : Lib) {p : Nomm} {env : CallEnv} {P : Noun → Prop} {f fb : Noun}
    (Up : UOKC (S := S) (Map := Map) lib env P fb p) (M : MinkC3 lib P f fb) {sup : Option Nomm}
    {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (hj : GJ g0.bo (CGoal.next sur th)) (hth : th.args = []) (hok : GoalOK g0 (CGoal.next sur th))
    (hcl : Clean sur.ned) (hcount : sixCount p ≤ 255)
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl0 : Clear g0) (hcb : CondBelow g0)
    (hkg : ∀ r, NMem sur.ned r → HoonMap.get g0.cond r = Option.none)
    (h : runLC env sup (Nomm.n3 p) (CGoalL.next (ofSure sur) th) region g0 = some (nex, g1)) :
    RunOKGC lib P f (CGoal.next sur th) g0 g1 nex := by
  have e3 : (runLC env sup (Nomm.n3 p) (CGoalL.next (ofSure sur) th) region : CM Map (NextL S)) =
      if noneEquivalentL (ofSure sur) then runLC env sup p (CGoalL.next (ofSure sur) th) region else (do
        let a ← collapseLazyAtomL ⟨ofSure sur, th⟩
        match a with
        | Option.none => fun _ => Option.none
        | some (r, o) => do
            let (z, o') ← forl r o
            let r' ← re
            let oc ← emit ⟨[], [], Termin.clq r' (jmp0 z) (jmp0 o')⟩
            runLC env sup p (CGoalL.next (ofSure (lazyReg r')) (jmp0 oc)) region) := by
    conv => lhs; unfold runLC
    rfl
  rw [e3, noneEquivalentL_ofSure] at h
  by_cases en : noneEquivalent sur = true
  · rw [if_pos en] at h
    have en' := en
    simp only [noneEquivalent, Bool.and_eq_true, decide_eq_true_eq, HoonSet.small_iff] at en'
    exact three_of_none M en'.1 en'.2
      (Up.run (goal := CGoal.next sur th) trivial hth hj hok hcl hcount b0 d0 hu hcl0 hcb hkg h)
  rw [if_neg en, collapseLazyAtomL_mk] at h
  obtain ⟨a, g2, h2, h⟩ := bind_some h
  obtain ⟨E2, ea, _, hsome⟩ := collapse_ok h2
  have C := collapse_down h2 hj.1 hj.2 b0
  have c2 : g2.cond = g0.cond := (kc_collapseLazyAtom _).keep g0 a g2 h2
  rcases a with _ | ⟨r, o⟩
  · cases h
  obtain ⟨hmr, _, hs⟩ := hsome r o rfl
  obtain ⟨ka, ra⟩ := keepsA_collapseLazyAtom (P := (fun r => HoonMap.get g0.cond r = Option.none)) (nex := ⟨sur, th⟩)
    d0 hkg (fun r hr => condBelow_none hcb hr) h2
  have kb := (keeps_collapseLazyAtom (nex := ⟨sur, th⟩) d0 (fun r hr => hok.2 r hr) h2).1
  obtain ⟨⟨z, o'⟩, g3, h3, h⟩ := bind_some h
  have hr : r < g2.re := by
    rcases hmr with hm | ⟨_, h2⟩
    · exact Nat.lt_of_lt_of_le (hok.2 r hm) E2.1
    · exact h2
  obtain ⟨E3, er3, eb3, F⟩ := forl_ok h3 hr
  have Co := C.2 r o rfl
  have Fd := forl_down h3 Co.1 Co.2 (Nat.le_trans b0 C.1.bo)
  have c3 : g3.cond = g2.cond := (kc_forl r o).keep g2 _ g3 h3
  simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
  have Ep := (ext_re g3).trans (ext_emit { g3 with re := g3.re + 1 } ⟨[], [], Termin.clq g3.re (jmp0 z) (jmp0 o')⟩)
  have d2 : g2.drop = false := E2.2.2.1.trans d0
  have d3 : g3.drop = false := E3.2.2.1.trans d2
  have bo3 : g0.bo ≤ g3.bo := Nat.le_trans C.1.bo E3.2.1
  have G : Grow g0 ({ g3 with re := g3.re + 1 }.emitted ⟨[], [], Termin.clq g3.re (jmp0 z) (jmp0 o')⟩) :=
    C.1.trans (Fd.1.trans ((grow_re _).trans (grow_emit (jumpsBelow_two rfl Fd.2.1 Fd.2.2))))
  have Rp := Up.run (goal := CGoal.next (lazyReg _) (jmp0 _)) trivial rfl
    ⟨by simp only [jmp0]; omega, by simp only [jmp0, emitted_bo]; omega⟩
    (by exact ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; simp [emitted_re]⟩) (by exact trivial)
    hcount (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d3) ((G.toU hu).up hu)
    (hcl0.growU (G.toU hu))
    (CondFresh.below (condFresh_of_eq (g0 := g0) (Nat.le_trans (Nat.le_trans E2.1 E3.1) (Nat.le_succ _))
      (c3.trans c2)) hcb)
    (fun r hr => by
      simp only [lazyReg, NMem] at hr; subst hr
      show HoonMap.get g3.cond _ = _
      rw [c3, c2]; exact condBelow_none hcb (Nat.le_trans E2.1 E3.1)) h
  refine unaryGT_ok (T := fun _ => wutTone) wutTone_keep M.fwd M.bwd (E2.trans (E3.trans Ep)) (G.toU hu) (c3.trans c2)
    ⟨by have := E2.1; have := E3.1; omega, by simp [emitted_re]⟩ (by simp [emitted_bo])
    (fresh_emitted (by simpa using d3) rfl rfl) Rp
    (fix_of_keeps (gs := g0) rfl (ka.trans ((keepsA_forl d2 (ra r o rfl) (fun r' hr' => condBelow_none hcb
        (Nat.le_trans E2.1 hr')) h3).trans ((keepsA_reg _ g3 _ (Nat.le_succ _)).trans (keepsA_emitted d3
        (blobIn_fin ⟨condBelow_none hcb (Nat.le_trans E2.1 E3.1), jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩)))))
      (kb.trans ((keeps_forl d2 hr h3).trans ((keeps_reg g3 _ (Nat.le_succ _)).trans (keeps_emitted d3
        (blobIn_fin ⟨Nat.lt_succ_self _, jmpIn_jmp0 _ _, jmpIn_jmp0 _ _⟩))))))
    ?_
  intro c hc σ Inv ν O gul st regs t tm x hI htr hx
  have hb := emitted_get' (by simpa using d3) (hc _ bo3 (by simp [emitted_bo]))
  have hj' := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
  rw [execBlob_clq, hx, Option.bind_some] at hj'
  have F' := F d2 c ((hc.right E2).left E3 Ep) lib σ O st regs t gul
  have hag2 : Agree c g0 g2 := hc.left E2 (E3.trans Ep)
  have keep : ∀ (v : Noun) (k : Nat) (rr : Nat), (k = g2.re ∨ k = g2.re + 1) → (rr < g0.re ∨ g3.re + 1 ≤ rr) →
      ¬ NMem sur.ned rr → SkaModel.read rr (store r v (store k v regs)) = SkaModel.read rr regs := by
    intro v k rr hk k1 k2
    have := er3
    have hne : rr ≠ r := fun e => by
      subst e
      rcases hmr with hm | ⟨hm, _⟩
      · exact k2 hm
      · omega
    rw [read_store_ne hne, read_store_ne (show rr ≠ k by have := E2.1; omega)]
  cases x with
  | cell u v =>
    exact goalSemC_of_goalSem hI htr (CGoal.next sur th) (some (A 0)) (GoalSem.transfer (hj'.trans F'.1)
      (fun rr ⟨k1, k2⟩ => keep (A 0) g2.re rr (Or.inl rfl) (by simpa [emitted_re] using k1) k2)
      (hs d0 c hag2 lib σ O st (store r (A 0) (store g2.re (A 0) regs)) t gul 0 (read_store_eq _ _ _)))
  | atom n =>
    exact goalSemC_of_goalSem hI htr (CGoal.next sur th) (some (A 1)) (GoalSem.transfer (hj'.trans F'.2)
      (fun rr ⟨k1, k2⟩ => keep (A 1) (g2.re + 1) rr (Or.inr rfl) (by simpa [emitted_re] using k1) k2)
      (hs d0 c hag2 lib σ O st (store r (A 1) (store (g2.re + 1) (A 1) regs)) t gul 1 (read_store_eq _ _ _)))

/-- **The last step of a run of `[3 p]` for a fork-free goal** (not
`%pick`): the run of `p` under a fork-free `%next` that is clean when the
goal is. -/
theorem runLC_n3_last {env : CallEnv} {sup : Option Nomm} {p : Nomm} {goal : CGoal S} {region : List Nat}
    {g0 g1 : Gen Map} {nex : NextL S} (hnp : NoPick goal) (hcl : GClean goal)
    (h : runLC env sup (Nomm.n3 p) (CGoal.toL goal) region g0 = some (nex, g1)) :
    ∃ (goal' : CGoal S) (gX : Gen Map), NoPick goal' ∧ GClean goal' ∧
      runLC env sup p (CGoal.toL goal') region gX = some (nex, g1) := by
  cases goal with
  | done =>
    have e3 : (runLC env sup (Nomm.n3 p) (CGoal.toL (CGoal.done : CGoal S)) region : CM Map (NextL S)) = (do
        let (o0, o1) ← doneBlocks
        let r ← re
        let oc ← emit ⟨[], [], Termin.clq r (jmp0 o0) (jmp0 o1)⟩
        runLC env sup p (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region) := by
      conv => lhs; unfold runLC
      rfl
    rw [e3] at h
    obtain ⟨⟨o0, o1⟩, g2, h2, h⟩ := bind_some h
    simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
    exact ⟨CGoal.next (lazyReg _) (jmp0 _), _, trivial, trivial, h⟩
  | next sur th =>
    have e3 : (runLC env sup (Nomm.n3 p) (CGoalL.next (ofSure sur) th) region : CM Map (NextL S)) =
        if noneEquivalentL (ofSure sur) then runLC env sup p (CGoalL.next (ofSure sur) th) region else (do
          let a ← collapseLazyAtomL ⟨ofSure sur, th⟩
          match a with
          | Option.none => fun _ => Option.none
          | some (r, o) => do
              let (z, o') ← forl r o
              let r' ← re
              let oc ← emit ⟨[], [], Termin.clq r' (jmp0 z) (jmp0 o')⟩
              runLC env sup p (CGoalL.next (ofSure (lazyReg r')) (jmp0 oc)) region) := by
      conv => lhs; unfold runLC
      rfl
    simp only [CGoal.toL] at h
    rw [e3] at h
    split at h
    · exact ⟨CGoal.next sur th, g0, trivial, hcl, h⟩
    · obtain ⟨a, g2, h2, h⟩ := bind_some h
      rcases a with _ | ⟨r, o⟩
      · cases h
      obtain ⟨_, g3, _, h⟩ := bind_some h
      simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
      exact ⟨CGoal.next (lazyReg _) (jmp0 _), _, trivial, trivial, h⟩
  | pick z o => exact hnp.elim

/-- **`[3 p]` with an operand meeting `UOKC` meets `OKCN`** for a formula
with `MinkC3`. -/
theorem okc_threeC (lib : Lib) (env : CallEnv) {p : Nomm} {P : Noun → Prop} {f fb : Noun}
    (Up : UOKC (S := S) (Map := Map) lib env P fb p) (M : MinkC3 lib P f fb) :
    OKCN (S := S) (Map := Map) lib env P f (Nomm.n3 p) := by
  intro sup goal region g0 g1 nex hnp ha hj hok hcl hcount b0 d0 hu hcl0 hcb hkg h
  have hc : sixCount p ≤ 255 := hcount
  cases goal with
  | next sur th => exact three_runN lib Up M hj ha hok hcl hc b0 d0 hu hcl0 hcb hkg h
  | done => exact three_runD lib Up M hc b0 d0 hu hcl0 hcb h
  | pick z o => exact hnp.elim

/-- **`[3 p]` with a hinted operand meeting `UOKC` meets `UOKC`.** -/
theorem uokc_threeC (lib : Lib) (env : CallEnv) {p : Nomm} {P : Noun → Prop} {f fb : Noun}
    (Up : UOKC (S := S) (Map := Map) lib env P fb p) (M : MinkC3 lib P f fb)
    (hh : hinted env.cod (Nomm.n3 p) = some true) : UOKC (S := S) (Map := Map) lib env P f (Nomm.n3 p) := by
  refine ⟨Or.inr hh, fun {sup goal region g0 g1 nex} hnp hcl h => ?_, okc_threeC lib env Up M⟩
  obtain ⟨goal', gX, hnp', hcl', h'⟩ := runLC_n3_last hnp hcl h
  exact Up.clean hnp' hcl' h'

/-- **`[3 p]` with a hinted operand on every `Annot`**: `Annot.n3` gives
`uokc_threeC` with `minkC3_three`, the wrappers `UOKC.wrap`. -/
theorem uokc_threeA {lib : Lib} {code : Bell → Option Nomm} (env : CallEnv) {p : Nomm}
    (ihp : ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f p → UOKC (S := S) (Map := Map) lib env P f p)
    (hh : hinted env.cod (Nomm.n3 p) = some true)
    {P : Noun → Prop} {f : Noun} {nm : Nomm} (hA : Annot lib code P f nm) :
    nm = Nomm.n3 p → UOKC (S := S) (Map := Map) lib env P f nm := by
  induction hA with
  | n3 hb _ => intro e; cases e; exact uokc_threeC lib env (ihp hb) (minkC3_three lib _ _) hh
  | memo hm _ ih' => intro e; exact UOKC.wrap (wrapRel_memo hm) (ih' e)
  | six0 hb' _ ih' => intro e; exact UOKC.wrap (wrapRel_six hb' (Or.inl ⟨rfl, rfl⟩)) (ih' e)
  | six1 hb' _ ih' => intro e; exact UOKC.wrap (wrapRel_six hb' (Or.inr ⟨rfl, rfl⟩)) (ih' e)
  | cons => intro e; cases e
  | n0 => intro e; cases e
  | n1 => intro e; cases e
  | indirect => intro e; cases e
  | direct => intro e; cases e
  | inline => intro e; cases e
  | n4 => intro e; cases e
  | n5 => intro e; cases e
  | n6 => intro e; cases e
  | n7 => intro e; cases e
  | n8 => intro e; cases e
  | n9 => intro e; cases e
  | n10 => intro e; cases e
  | n11s => intro e; cases e
  | n11d => intro e; cases e
  | mean => intro e; cases e
  | n12 => intro e; cases e
  | bare => intro e; cases e
  | crash => intro e; cases e
  | fold => intro e; cases e
  | n8g => intro e; cases e
  | n8l => intro e; cases e
  | bareLit => intro e; cases e

end Comp
end SkaModel
end Formalization
