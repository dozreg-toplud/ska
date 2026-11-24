import lemmas.Ska.CompNCLeaf

/-!
# `[4 p]` with a calling `p` at level `0`

README Gaps 12.22, the case `[4 p]` with calls of the table of
`CompNC.lean`.  The raw blocks (`tools/hoon/calldump4.hoon`, `%i4`, `[4 [2
[0 3] [0 2]]]`): `0: v0 -> cel, hed -> v5, tal -> v4, hop 3`; `3: nok v4 v5
-> v3, hop 2`; `2: mov v3 v2, hop 1` (the call's `+kerf` into `arg = v2`);
`1: inc v2 v1, don v1` (the block of the increment, `pro = v1`).  Under a
fork-free `%next` the block of the increment hops to the goal's jump (or to
the block of `+bomb` of `+collapse-lazy-atom` when the goal asks a cell).

* `incTone`, `MinkC4`, `minkC4_four`: `+mink` on `[4 b]` from `+mink` on
  `b` (forward with no more fuel, backward).
* `goalSemCM_of_returnsC`, `unaryGC_ok`: a run of the operand under `%next`
  of one register into the block of the increment, and the blocks before it
  (left alone by unproxying, `hfix`), give `RunOKGC` of the whole for any
  goal, through `hblk` (what the block does with the operand's product).
* `four_runD` (`%done`), `four_runN` (a fork-free `%next`, with
  `+collapse-lazy-atom` as in `runOKNV_n4`), `okc_fourC`, `uokc_fourC`,
  `uokc_fourA` (every `Annot`).
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

/-! ## `+mink` on `[4 b]` -/

/-- The tone of `[4 b]` from the tone of `b`. -/
def incTone (tm : Trace) : Tone → Tone
  | Tone.zero (Noun.atom n) => Tone.zero (A (n + 1))
  | Tone.zero (Noun.cell _ _) => Tone.two tm
  | r => r

/-- **`+mink` on `f` is the increment of `+mink` on `fb`**: forward with no
more fuel, backward. -/
structure MinkC4 (lib : Lib) (P : Noun → Prop) (f fb : Noun) : Prop where
  fwd : ∀ {s gul : Noun} {n : Nat} {tm : Trace} {r : Tone}, P s → minkF lib gul n tm s f = some r →
    ∃ n', n' ≤ n ∧ ∃ rb, minkF lib gul n' tm s fb = some rb ∧ r = incTone tm rb
  bwd : ∀ {s gul : Noun} {tm : Trace} {rb : Tone}, P s → Mink lib gul tm s fb rb → Mink lib gul tm s f (incTone tm rb)

theorem minkC4_four (lib : Lib) (P : Noun → Prop) (b : Noun) : MinkC4 lib P (n2 (A 4) b) b where
  fwd := fun {s gul n tm r} _ h => by
    obtain ⟨m, rfl⟩ := minkF_pos h
    rw [minkF_succ_eq] at h
    simp only [n2, minkStep] at h
    rcases tbind_eq_some h with ⟨y, hy, h1⟩ | ⟨hb, hnz⟩
    · refine ⟨m, Nat.le_succ m, _, hy, ?_⟩
      cases y with
      | atom a => simp only [Option.some.injEq] at h1; rw [← h1]; rfl
      | cell u v => simp only [Option.some.injEq] at h1; rw [← h1]; rfl
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
    | zero y => cases y <;> rfl
    | one _ => rfl
    | two _ => rfl

/-! ## The composition -/

section Exec
variable {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {Inv : σ → Prop} {ν : σ → Needs}

theorem goalSemCM_of_returnsC {K : Nat → Prop} {st : σ} {regs : Map (Option Noun)} {t tm : Trace} {je : Jmp} :
    ∀ (goal : CGoal S) (r : Tone), (∀ p, r ≠ Tone.zero p) → ReturnsC lib O c gul Inv ν st regs t je r →
      GoalSemCM lib O c gul Inv ν K st regs t tm je goal r
  | CGoal.done, _, _, H => H
  | CGoal.next _ _, Tone.zero p, hn, _ => absurd rfl (hn p)
  | CGoal.next _ _, Tone.one _, _, H => H
  | CGoal.next _ _, Tone.two _, _, H => H
  | CGoal.pick _ _, Tone.zero p, hn, _ => absurd rfl (hn p)
  | CGoal.pick _ _, Tone.one _, _, H => H
  | CGoal.pick _ _, Tone.two _, _, H => H

end Exec

/-- **A unary case whose operand may call**: the operand's `RunOKGC` under
`%next (lazy-from-reg a) (jmp0 o)` and the blocks before it give `RunOKGC`
of the whole for the goal, the formula's `+mink` the increment of the
operand's (`MinkC4`), the block at `o` turning the operand's product `x`
held at `a` into `GoalSemCM` of `incTone tm (zero x)` (`hblk`). -/
theorem unaryGC_ok {lib : Lib} {P : Noun → Prop} {f fb : Noun} (M : MinkC4 lib P f fb) {goal : CGoal S}
    {g0 g' g1 : Gen Map} {a o : Nat} {nexp : NextL S}
    (hpre : Ext g0 g') (hgr : GrowU g0 g') (hcnd : g'.cond = g0.cond) (ha : g0.re ≤ a ∧ a < g'.re)
    (ho : o < g'.bo) (hfr : Fresh g' (jmp0 o))
    (hp : RunOKGC (Map := Map) lib P fb (CGoal.next (lazyReg a) (jmp0 o)) g' g1 nexp)
    (hfix : ∀ (cf : Map (Nat × List Nat)), (∀ k, k < g'.re → HoonMap.get cf k = HoonMap.get g0.cond k) →
      ∀ k, g0.bo ≤ k → k < g'.bo → (HoonMap.get g'.blocks k).map (unproxyBlob cf) = HoonMap.get g'.blocks k)
    (hblk : ∀ (c : Straight Map), Agree c g0 g' → ∀ (σ : Type) (Inv : σ → Prop) (ν : σ → Needs) (O : Oracle σ)
      (gul : Noun) (st : σ) (regs : Map (Option Noun)) (t tm : Trace) (x : Noun), Inv st →
      Forall2 (FrameRel lib (ν st)) t tm → SkaModel.read a regs = some x →
      GoalSemCM lib O c gul Inv ν (Keep g0 g' goal) st regs t tm (jmp0 o) goal (incTone tm (Tone.zero x))) :
    RunOKGC lib P f goal g0 g1 nexp := by
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
      (∀ st' : σ, AgreeU lib O c gul st' t cf ned g0 g1 nexp.laz s0 s) → (∀ x, NMem ned x → g1.re ≤ x) →
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
  · obtain ⟨n', hn', rb, hb, rfl⟩ := M.fwd hs hm
    rw [bad ((hp.nec s hs hf).1 gul n' tm rb hb)]
    exact Or.inl rfl
  · obtain ⟨rb, hmb, hbad⟩ := (hp.nec s hs hf).2 gul tm
    refine ⟨_, M.bwd hs hmb, ?_⟩
    rw [bad hbad]
    exact Or.inl rfl
  · intro cf hcf c ned σ Inv ν O n gul hS hF st t tm s0 s r hI htr hs hm ag hned regs hh hn
    obtain ⟨n', hn', rb, hb, rfl⟩ := M.fwd hs hm
    exact conv cf hcf c ned σ Inv ν O gul st t tm s0 s hI htr ag hned regs rb
      (hp.sem cf hcf c ned σ Inv ν O n' gul hS (oracleFwd_le hF hn') st t tm s0 s rb hI htr hs hb
        (fun st' => agP cf c ned σ O gul st' t s0 s (ag st')) hned regs hh hn)
  · intro cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs ag hned regs hh hn res hres
    obtain ⟨rb, hmb, G⟩ := hp.semB cf hcf c ned σ Inv ν O gul hS hB st t tm s0 s hI htr hs
      (fun st' => agP cf c ned σ O gul st' t s0 s (ag st')) hned regs hh hn res hres
    exact ⟨_, M.bwd hs hmb, conv cf hcf c ned σ Inv ν O gul st t tm s0 s hI htr ag hned regs rb G⟩

/-! ## The runs of `[4 p]` -/

/-- **`[4 p]` for `%done` with an operand that may call**: the block
`[inc arg pro] don pro`, then the operand under `%next (lazy-from-reg arg)`
(`unaryGC_ok`, the blocks as in `runOKV_n4D`). -/
theorem four_runD (lib : Lib) {p : Nomm} {env : CallEnv} {P : Noun → Prop} {f fb : Noun}
    (Up : UOKC (S := S) (Map := Map) lib env P fb p) (M : MinkC4 lib P f fb) {sup : Option Nomm}
    {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S} (hcount : sixCount p ≤ 255) (b0 : 1 ≤ g0.bo)
    (d0 : g0.drop = false) (hu : UpBelow g0) (hcl0 : Clear g0) (hcb : CondBelow g0)
    (h : runLC env sup (Nomm.n4 p) (CGoal.toL (CGoal.done : CGoal S)) region g0 = some (nex, g1)) :
    RunOKGC lib P f (CGoal.done : CGoal S) g0 g1 nex := by
  have e4 : (runLC env sup (Nomm.n4 p) (CGoal.toL (CGoal.done : CGoal S)) region : CM Map (NextL S)) = (do
      let pro ← re
      let arg ← re
      let o ← emit ⟨[], [Pole.inc arg pro], Termin.don pro⟩
      runLC env sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region) := by
    conv => lhs; unfold runLC
    rfl
  rw [e4] at h
  simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
  have Rp := Up.run (goal := CGoal.next (lazyReg _) (jmp0 _)) trivial rfl
    ⟨by simp only [jmp0]; omega, by simp only [jmp0, emitted_bo]; omega⟩
    (by exact ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; simp [emitted_re]⟩) (by exact trivial)
    hcount
    (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d0)
    (((grow_reg g0 _).trans (grow_emit (jumpsBelow_nil rfl _))).toU hu |>.up hu)
    (hcl0.growU (((grow_reg g0 _).trans (grow_emit (jumpsBelow_nil rfl _))).toU hu))
    (CondFresh.below (condFresh_of_eq (g0 := g0) (by romega) rfl) hcb)
    (fun r hr => by simp only [lazyReg, NMem] at hr; subst hr; exact condBelow_none hcb (by romega)) h
  refine unaryGC_ok M ((ext_re _).trans ((ext_re _).trans (ext_emit _ _)))
    (((grow_reg g0 _).trans (grow_emit (jumpsBelow_nil rfl _))).toU hu) rfl
    ⟨Nat.le_succ _, by simp [emitted_re]⟩ (by simp [emitted_bo]) (fresh_emitted (by simpa using d0) rfl rfl) Rp
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

/-- **`[4 p]` under a fork-free `%next` with an operand that may call**:
`+collapse-lazy-atom`, the block of the increment, then the operand
(`unaryGC_ok`, the blocks as in `runOKNV_n4`). -/
theorem four_runN (lib : Lib) {p : Nomm} {env : CallEnv} {P : Noun → Prop} {f fb : Noun}
    (Up : UOKC (S := S) (Map := Map) lib env P fb p) (M : MinkC4 lib P f fb) {sup : Option Nomm}
    {sur : Sure S} {th : Jmp} {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S}
    (hj : GJ g0.bo (CGoal.next sur th)) (hok : GoalOK g0 (CGoal.next sur th)) (hcount : sixCount p ≤ 255)
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl0 : Clear g0) (hcb : CondBelow g0)
    (hkg : ∀ r, NMem sur.ned r → HoonMap.get g0.cond r = Option.none)
    (h : runLC env sup (Nomm.n4 p) (CGoalL.next (ofSure sur) th) region g0 = some (nex, g1)) :
    RunOKGC lib P f (CGoal.next sur th) g0 g1 nex := by
  have e4 : (runLC env sup (Nomm.n4 p) (CGoalL.next (ofSure sur) th) region : CM Map (NextL S)) = (do
      let a ← collapseLazyAtomL ⟨ofSure sur, th⟩
      let (pro, th') ← (match a with
        | some x => pure x
        | Option.none => do
            let r ← re
            if th.args = [] then pure (r, th.there) else fun _ => Option.none : CM Map (Nat × Nat))
      let arg ← re
      let o ← emit ⟨[], [Pole.inc arg pro], Termin.hop (jmp0 th')⟩
      runLC env sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region) := by
    conv => lhs; unfold runLC
    rfl
  rw [e4, collapseLazyAtomL_mk] at h
  obtain ⟨a, g2, h2, h⟩ := bind_some h
  obtain ⟨E2, ea, hnone, hsome⟩ := collapse_ok h2
  have C := collapse_down h2 hj.1 hj.2 b0
  have c2 : g2.cond = g0.cond := (kc_collapseLazyAtom _).keep g0 a g2 h2
  obtain ⟨⟨pro, th'⟩, g3, h3, h⟩ := bind_some h
  have P' : Ext g2 g3 ∧ g3.cond = g2.cond ∧ Grow g2 g3 ∧ (1 ≤ th' ∧ th' < g3.bo) ∧
      (NMem sur.ned pro ∨ (g0.re ≤ pro ∧ pro < g3.re)) ∧
      (g0.drop = false → ∀ (c : Straight Map), Agree c g0 g2 → ∀ (σ : Type) (O : Oracle σ) (st : σ) regs t gul n,
        SkaModel.read pro regs = some (A n) → ∀ {K : Nat → Prop},
        GoalSem lib O c gul st K regs t (jmp0 th') (CGoal.next sur th) (some (A n))) := by
    cases a with
    | some x =>
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
      obtain ⟨e1, rfl⟩ := h3
      subst e1
      obtain ⟨hm, _, hs⟩ := hsome pro th' rfl
      exact ⟨Ext.refl _, rfl, Grow.refl _, C.2 pro th' rfl, hm,
        fun hd c hc σ O st regs t gul n hr => hs hd c hc lib σ O st regs t gul n hr⟩
    | none =>
      obtain ⟨hn, hl⟩ := hnone rfl
      simp only [bind_apply, re_apply, Option.bind_some, ea, if_true, pure_apply, Option.some.injEq,
        Prod.mk.injEq] at h3
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h3
      refine ⟨ext_re _, rfl, grow_re _, ⟨hj.1, by have := C.1.bo; have := hj.2; show th.there < g2.bo; omega⟩,
        Or.inr ⟨E2.1, Nat.lt_succ_self _⟩, fun _ c _ σ O st regs t gul n hr => ?_⟩
      refine ⟨fun _ => ⟨regs, by rw [hn]; trivial, fun _ _ => rfl, by rw [jmp0_of_args ea]⟩, fun hf => ?_⟩
      exact absurd ⟨by rw [hn]; trivial, fun y hy => by rw [hl y hy]; simp⟩ hf
  have AB : (KeepsA (fun r => HoonMap.get g0.cond r = Option.none) g0 g3 ∧ HoonMap.get g0.cond pro = Option.none) ∧
      (Keeps g0 g3 ∧ pro < g3.re) := by
    obtain ⟨ka, ra⟩ := keepsA_collapseLazyAtom (P := (fun r => HoonMap.get g0.cond r = Option.none)) (nex := ⟨sur, th⟩)
      d0 hkg (fun r hr => condBelow_none hcb hr) h2
    obtain ⟨kb, rb⟩ := keeps_collapseLazyAtom (nex := ⟨sur, th⟩) d0 (fun r hr => hok.2 r hr) h2
    cases a with
    | some x =>
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3
      obtain ⟨rfl, rfl⟩ := h3
      exact ⟨⟨ka, ra _ _ rfl⟩, ⟨kb, rb _ _ rfl⟩⟩
    | none =>
      simp only [bind_apply, re_apply, Option.bind_some, ea, if_true, pure_apply, Option.some.injEq,
        Prod.mk.injEq] at h3
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h3
      exact ⟨⟨ka.trans (keepsA_reg _ _ _ (Nat.le_succ _)), condBelow_none hcb ka.le⟩,
        ⟨kb.trans (keeps_reg _ _ (Nat.le_succ _)), Nat.lt_succ_self _⟩⟩
  simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
  have d3 : g3.drop = false := P'.1.2.2.1.trans (E2.2.2.1.trans d0)
  have bo3 : g0.bo ≤ g3.bo := Nat.le_trans C.1.bo P'.1.2.1
  have G : Grow g0 ({ g3 with re := g3.re + 1 }.emitted ⟨[], [Pole.inc g3.re pro], Termin.hop (jmp0 th')⟩) :=
    C.1.trans (P'.2.2.1.trans ((grow_re _).trans (grow_emit (jumpsBelow_hop P'.2.2.2.1.1 P'.2.2.2.1.2))))
  have Rp := Up.run (goal := CGoal.next (lazyReg _) (jmp0 _)) trivial rfl
    ⟨by simp only [jmp0]; omega, by simp only [jmp0, emitted_bo]; omega⟩
    (by exact ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; simp [emitted_re]⟩) (by exact trivial)
    hcount (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d3) ((G.toU hu).up hu)
    (hcl0.growU (G.toU hu))
    (CondFresh.below (condFresh_of_eq (g0 := g0) (Nat.le_trans AB.2.1.le (Nat.le_succ _)) (P'.2.1.trans c2)) hcb)
    (fun r hr => by
      simp only [lazyReg, NMem] at hr; subst hr
      show HoonMap.get g3.cond _ = _
      rw [P'.2.1, c2]; exact condBelow_none hcb AB.2.1.le) h
  refine unaryGC_ok M (E2.trans (P'.1.trans ((ext_re _).trans (ext_emit _ _)))) (G.toU hu)
    (P'.2.1.trans c2) ⟨by have := E2.1; have := P'.1.1; omega, by simp [emitted_re]⟩ (by simp [emitted_bo])
    (fresh_emitted (by simpa using d3) rfl rfl) Rp
    (fix_of_keeps (gs := g0) rfl (AB.1.1.trans ((keepsA_reg _ g3 _ (Nat.le_succ _)).trans (keepsA_emitted d3
      (blobIn_one (fun x hx => by
        simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl
        · exact condBelow_none hcb AB.2.1.le
        · exact AB.1.2) (jmpIn_jmp0 _ _)))))
      (AB.2.1.trans ((keeps_reg g3 _ (Nat.le_succ _)).trans (keeps_emitted d3
      (blobIn_one (fun x hx => by
        simp only [poleRegs, List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl
        · exact Nat.lt_succ_self _
        · exact Nat.lt_succ_of_lt AB.2.2) (jmpIn_jmp0 _ _))))))
    ?_
  intro c hc σ Inv ν O gul st regs t tm x hI htr hx
  have hb := emitted_get' (by simpa using d3) (hc _ bo3 (by simp [emitted_bo]))
  have hj' := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
  cases x with
  | atom n =>
    rw [show [Pole.inc _ _] = [Pole.inc _ _] ++ [] from rfl, runs_inc hx, execBlob_hop] at hj'
    refine goalSemC_of_goalSem hI htr (CGoal.next sur th) (some (A (n + 1)))
      (GoalSem.transfer hj' (fun r hr => read_store_ne (fun e => ?_) _ _)
        (P'.2.2.2.2.2 d0 c (hc.left E2 (P'.1.trans ((ext_re _).trans (ext_emit _ _)))) σ O st
          (store pro (A (n + 1)) regs) t gul (n + 1) (read_store_eq _ _ _)))
    obtain ⟨h1, h2⟩ := hr
    subst e
    rcases P'.2.2.2.2.1 with hm | ⟨hm, hm'⟩
    · exact h2 hm
    · simp [emitted_re] at h1; omega
  | cell u v =>
    rw [show [Pole.inc _ _] = [Pole.inc _ _] ++ [] from rfl, crashes_inc hx] at hj'
    exact ⟨Tone.two t, st, hI, Needs.le_refl _, hj', ToneRel.two htr⟩

/-- **The last step of a run of `[4 p]`** (not for `%pick`): the run of `p`
under `%next (lazy-from-reg arg)`. -/
theorem runLC_n4_last {env : CallEnv} {sup : Option Nomm} {p : Nomm} {goal : CGoalL S} {region : List Nat}
    {g0 g1 : Gen Map} {nex : NextL S} (hnp : ∀ z o, goal ≠ CGoalL.pick z o)
    (h : runLC env sup (Nomm.n4 p) goal region g0 = some (nex, g1)) :
    ∃ arg o gX, runLC env sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region gX = some (nex, g1) := by
  cases goal with
  | done =>
    have e4 : (runLC env sup (Nomm.n4 p) (CGoalL.done : CGoalL S) region : CM Map (NextL S)) = (do
        let pro ← re
        let arg ← re
        let o ← emit ⟨[], [Pole.inc arg pro], Termin.don pro⟩
        runLC env sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region) := by
      conv => lhs; unfold runLC
    rw [e4] at h
    simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
    exact ⟨_, _, _, h⟩
  | next laz th =>
    have e4 : (runLC env sup (Nomm.n4 p) (CGoalL.next laz th) region : CM Map (NextL S)) = (do
        let a ← collapseLazyAtomL ⟨laz, th⟩
        let (pro, th') ← (match a with
          | some x => pure x
          | Option.none => do
              let r ← re
              if th.args = [] then pure (r, th.there) else fun _ => Option.none : CM Map (Nat × Nat))
        let arg ← re
        let o ← emit ⟨[], [Pole.inc arg pro], Termin.hop (jmp0 th')⟩
        runLC env sup p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region) := by
      conv => lhs; unfold runLC
      rfl
    rw [e4] at h
    obtain ⟨a, g2, _, h⟩ := bind_some h
    obtain ⟨_, g3, _, h⟩ := bind_some h
    simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
    exact ⟨_, _, _, h⟩
  | pick z o => exact absurd rfl (hnp z o)

/-- **`[4 p]` with an operand meeting `UOKC` meets `OKCN`** for a formula
with `MinkC4`. -/
theorem okc_fourC (lib : Lib) (env : CallEnv) {p : Nomm} {P : Noun → Prop} {f fb : Noun}
    (Up : UOKC (S := S) (Map := Map) lib env P fb p) (M : MinkC4 lib P f fb) :
    OKCN (S := S) (Map := Map) lib env P f (Nomm.n4 p) := by
  intro sup goal region g0 g1 nex hnp ha hj hok hcl hcount b0 d0 hu hcl0 hcb hkg h
  have hc : sixCount p ≤ 255 := hcount
  cases goal with
  | next sur th => exact four_runN lib Up M hj hok hc b0 d0 hu hcl0 hcb hkg h
  | done => exact four_runD lib Up M hc b0 d0 hu hcl0 hcb h
  | pick z o => exact hnp.elim

/-- **`[4 p]` with a hinted operand meeting `UOKC` meets `UOKC`.** -/
theorem uokc_fourC (lib : Lib) (env : CallEnv) {p : Nomm} {P : Noun → Prop} {f fb : Noun}
    (Up : UOKC (S := S) (Map := Map) lib env P fb p) (M : MinkC4 lib P f fb)
    (hh : hinted env.cod (Nomm.n4 p) = some true) : UOKC (S := S) (Map := Map) lib env P f (Nomm.n4 p) := by
  refine ⟨Or.inr hh, fun {sup goal region g0 g1 nex} hnp hcl h => ?_, okc_fourC lib env Up M⟩
  obtain ⟨arg, o, gX, h'⟩ := runLC_n4_last (fun z o e => by cases goal <;> simp_all [CGoal.toL, NoPick]) h
  exact Up.clean (goal := CGoal.next (lazyReg arg) (jmp0 o)) trivial trivial h'

/-- **`[4 p]` with a hinted operand on every `Annot`**: `Annot.n4` gives
`uokc_fourC` with `minkC4_four`, the wrappers `UOKC.wrap`. -/
theorem uokc_fourA {lib : Lib} {code : Bell → Option Nomm} (env : CallEnv) {p : Nomm}
    (ihp : ∀ {P : Noun → Prop} {f : Noun}, Annot lib code P f p → UOKC (S := S) (Map := Map) lib env P f p)
    (hh : hinted env.cod (Nomm.n4 p) = some true)
    {P : Noun → Prop} {f : Noun} {nm : Nomm} (hA : Annot lib code P f nm) :
    nm = Nomm.n4 p → UOKC (S := S) (Map := Map) lib env P f nm := by
  induction hA with
  | n4 hb _ => intro e; cases e; exact uokc_fourC lib env (ihp hb) (minkC4_four lib _ _) hh
  | memo hm _ ih' => intro e; exact UOKC.wrap (wrapRel_memo hm) (ih' e)
  | six0 hb' _ ih' => intro e; exact UOKC.wrap (wrapRel_six hb' (Or.inl ⟨rfl, rfl⟩)) (ih' e)
  | six1 hb' _ ih' => intro e; exact UOKC.wrap (wrapRel_six hb' (Or.inr ⟨rfl, rfl⟩)) (ih' e)
  | cons => intro e; cases e
  | n0 => intro e; cases e
  | n1 => intro e; cases e
  | indirect => intro e; cases e
  | direct => intro e; cases e
  | inline => intro e; cases e
  | n3 => intro e; cases e
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
