import lemmas.Ska.CompRelBinary

/-!
# `[4 p]` and `[3 p]` with the relaxed `sem`

README Gaps 12.2.  The relaxed `sem` (`SemNR`, `SemPR` of `CompLeafRel.lean`)
of `[4 p]` and `[3 p]` for every goal, from the relaxed `sem` of `p` (`OKNR`).
The blocks are those of `runOKN_n4`, `runOKN_n3` (`CompFragM.lean`),
`runOKP_n4`, `runOKP_n3` (`CompSevenN.lean`), `runOKP_n4p` and `runOKP_n3p`,
with the keep set extended by the operand register `a`: in `[4 [0 1]]` the
input need may hold `a`, which lies in the result's sure need, and the block
of the increment stores only into the product register, which is not `a`.

`unaryG_semR`: the shape of `unaryG_ok` for `%done` and `%pick`, the
counterpart of `unaryN_semR` (`CompRelBinary.lean`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock Lazy

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- **A unary case for `%done` or `%pick` with the relaxed `sem`**, from the
relaxed `sem` of `p` and a block that keeps the operand register `a` besides
`Keep`. -/
theorem unaryG_semR {lib : Lib} {nm p : Nomm} {goal : CGoal S} (hg : NotNext goal) {g0 g' g1 : Gen Map}
    {a o : Nat} {nexp : NextL S} {f : Noun → Option Noun} (hev : ∀ s, pureEval nm s = (pureEval p s).bind f)
    (hpre : Ext g0 g') (ha : g0.re ≤ a ∧ a < g'.re)
    (hp : RunOKN (Map := Map) lib p (lazyReg a) (jmp0 o) g' g1 nexp)
    (Sp : SemNR (Map := Map) lib p (lazyReg a) (jmp0 o) g' g1 nexp)
    (hblk : ∀ (c : Straight Map), Agree c g0 g' → ∀ (σ : Type) (O : Oracle σ) st regs t gul x,
      SkaModel.read a regs = some x →
      GoalSem lib O c gul st (fun r => Keep g0 g' goal r ∨ r = a) regs t (jmp0 o) goal (f x)) :
    SemPR (Map := Map) lib nm goal g0 g1 nexp := by
  intro c ned σ O st t gul s0 s ag hned regs hh hn
  have hN : ∀ r, NMem ned r → g1.re ≤ r ∨ (r < g0.re ∧ ¬ GMem goal r) ∨ NMem nexp.laz.sure.ned r := hned
  have l0 := hpre.1
  have l1 := hp.ext.1
  have agP : AgreeP lib O c gul st t ned g' g1 nexp.laz s0 s :=
    ⟨fun o' h0 h1 hnl => ag.1 o' (Nat.le_trans hpre.2.1 h0) h1 hnl, ag.2⟩
  have inP : ∀ r, NMem ned r → InR (CGoal.next (lazyReg a : Sure S) (jmp0 o)) g' g1 nexp.laz.sure.ned r := by
    intro r hr
    show g1.re ≤ r ∨ (r < g'.re ∧ ¬ NMem (Need.this a) r) ∨ NMem nexp.laz.sure.ned r
    rcases hN r hr with e | ⟨e, _⟩ | e
    · exact Or.inl e
    · exact Or.inr (Or.inl ⟨by omega, fun hm => by simp only [NMem] at hm; omega⟩)
    · exact Or.inr (Or.inr e)
  have Hp := Sp c ned σ O st t gul s0 s agP inP regs hh hn
  have agQ : Agree c g0 g' := fun o' h0 h1 => by
    rw [ag.1 o' h0 (Nat.lt_of_lt_of_le h1 hp.ext.2.1) (fun hm => ?_)]
    · exact hp.ext.2.2.2 o' h1
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
      have := (hp.labs e he).1; omega
  rw [hev]
  cases e : pureEval p s with
  | none => rw [e] at Hp; exact goalSem_none _ Hp
  | some x =>
    rw [e] at Hp
    obtain ⟨R, hR, k, he⟩ := Hp.1 ⟨trivial, looks_empty x⟩
    refine goalSem_pre (fun r hr => k r ?_) he _ _
      (goalSem_mono (fun r hr => ?_) _ _ (hblk c agQ σ O st R t gul x hR))
    · show (r < g'.re ∧ ¬ NMem (Need.this a) r) ∨ NMem ned r
      rcases hr with h1 | h1
      · exact Or.inl ⟨by omega, fun hm => by simp only [NMem] at hm; omega⟩
      · exact Or.inr h1
    · show Keep g0 g' goal r ∨ r = a
      rcases hr with h1 | h1
      · exact Or.inl ⟨Or.inl h1, notNext_gmem hg r⟩
      · rcases hN r h1 with e | ⟨e, e'⟩ | e
        · exact Or.inl ⟨Or.inr (by omega), notNext_gmem hg r⟩
        · exact Or.inl ⟨Or.inl e, e'⟩
        · rcases hp.regs r e with b | ⟨b, _⟩
          · simp only [lazyReg, NMem] at b; exact Or.inr b
          · exact Or.inl ⟨Or.inr b, notNext_gmem hg r⟩

/-! ## `[4 p]` and `[3 p]` under a fork-free `%next` -/

/-- **`[4 p]` for a fork-free `%next` with the relaxed `sem`.** -/
theorem runOKN_n4_semR (lib : Lib) {p : Nomm} (hp : NextOK (S := S) (Map := Map) lib p)
    (sp : OKNR (S := S) (Map := Map) lib p) {sur : Sure S} {th : Jmp}
    {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S} (hj : GJ g0.bo (CGoal.next sur th))
    (hok : GoalOK g0 (CGoal.next sur th))
    (hcount : sixCount p ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl0 : Clear g0)
    (h : runL (Nomm.n4 p) (CGoalL.next (ofSure sur) th) region g0 = some (nex, g1)) :
    SemNR (Map := Map) lib (Nomm.n4 p) sur th g0 g1 nex := by
  have e4 : (runL (Nomm.n4 p) (CGoalL.next (ofSure sur) th) region : CM Map (NextL S)) = (do
      let a ← collapseLazyAtomL ⟨ofSure sur, th⟩
      let (pro, th') ← (match a with
        | some x => pure x
        | Option.none => do
            let r ← re
            if th.args = [] then pure (r, th.there) else fun _ => Option.none : CM Map (Nat × Nat))
      let arg ← re
      let o ← emit ⟨[], [Pole.inc arg pro], Termin.hop (jmp0 th')⟩
      runL p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region) := by
    conv => lhs; unfold runL
    rfl
  rw [e4, collapseLazyAtomL_mk] at h
  obtain ⟨a, g2, h2, h⟩ := bind_some h
  obtain ⟨E2, ea, hnone, hsome⟩ := collapse_ok h2
  have C := collapse_down h2 hj.1 hj.2 b0
  have c2 : g2.cond = g0.cond := (kc_collapseLazyAtom _).keep g0 a g2 h2
  obtain ⟨⟨pro, th'⟩, g3, h3, h⟩ := bind_some h
  have P : Ext g2 g3 ∧ g3.cond = g2.cond ∧ Grow g2 g3 ∧ (1 ≤ th' ∧ th' < g3.bo) ∧
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
  simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
  have d3 : g3.drop = false := P.1.2.2.1.trans (E2.2.2.1.trans d0)
  have bo3 : g0.bo ≤ g3.bo := Nat.le_trans C.1.bo P.1.2.1
  have G : Grow g0 ({ g3 with re := g3.re + 1 }.emitted ⟨[], [Pole.inc g3.re pro], Termin.hop (jmp0 th')⟩) :=
    C.1.trans (P.2.2.1.trans ((grow_re _).trans (grow_emit (jumpsBelow_hop P.2.2.2.1.1 P.2.2.2.1.2))))
  have Rp := hp ⟨by simp only [jmp0]; omega, by simp only [jmp0, emitted_bo]; omega⟩ rfl
    (by exact ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; simp [emitted_re]⟩) (by exact trivial)
    hcount (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d3) ((G.toU hu).up hu) h
  have Sp := sp ⟨by simp only [jmp0]; omega, by simp only [jmp0, emitted_bo]; omega⟩ rfl
    (by exact ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; simp [emitted_re]⟩) (by exact trivial)
    hcount (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d3) ((G.toU hu).up hu)
    (hcl0.growU (G.toU hu)) h
  refine unaryN_semR (pureEval_n4 p) (E2.trans (P.1.trans ((ext_re _).trans (ext_emit _ _))))
    ⟨by have := E2.1; have := P.1.1; omega, by simp [emitted_re]⟩ hok.2 Rp Sp ?_
  intro c hc σ O st regs t gul x hx
  have hb := emitted_get' (by simpa using d3) (hc _ bo3 (by simp [emitted_bo]))
  have hj' := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
  cases x with
  | atom n =>
    rw [show [Pole.inc _ _] = [Pole.inc _ _] ++ [] from rfl, runs_inc hx, execBlob_hop] at hj'
    refine GoalSem.transfer hj' (fun r hr => read_store_ne (fun e => ?_) _ _)
      (P.2.2.2.2.2 d0 c (hc.left E2 (P.1.trans ((ext_re _).trans (ext_emit _ _)))) σ O st
        (store pro (A (n + 1)) regs) t gul (n + 1) (read_store_eq _ _ _))
    have l2 := E2.1
    have l3 := P.1.1
    rcases hr with ⟨h1, h2⟩ | h1
    · rcases P.2.2.2.2.1 with hm | ⟨hm, hm'⟩
      · rw [e] at h2; exact h2 hm
      · simp [emitted_re] at h1; omega
    · rcases P.2.2.2.2.1 with hm | ⟨hm, hm'⟩
      · have := hok.2 _ hm; omega
      · omega
  | cell u v =>
    apply goalSem_crash
    rw [hj', show [Pole.inc _ _] = [Pole.inc _ _] ++ [] from rfl, crashes_inc hx]

/-- `[3 p]` for a fork-free `%next` that asks nothing of the product, with
the relaxed `sem`. -/
theorem semN_n3_of_none {lib : Lib} {p : Nomm} {sur : Sure S} {th : Jmp} {g0 g1 : Gen Map} {nex : NextL S}
    (hn : sur.ned = Need.none) (hl : ∀ x ∈ HoonSet.toList sur.lok, x = 1)
    (Sp : SemNR (Map := Map) lib p sur th g0 g1 nex) : SemNR (Map := Map) lib (Nomm.n3 p) sur th g0 g1 nex := by
  have hfit : ∀ v, FitsS sur v := fun v => ⟨by rw [hn]; trivial, fun y hy => by rw [hl y hy]; simp⟩
  intro c ned σ O st t gul s0 s ag hned regs hh hn'
  have H := Sp c ned σ O st t gul s0 s ag hned regs hh hn'
  rw [pureEval_n3]
  cases e : pureEval p s with
  | none => rw [e] at H; exact goalSem_none _ H
  | some x =>
    rw [e] at H
    obtain ⟨regs', _, hk, he⟩ := H.1 (hfit x)
    exact ⟨fun _ => ⟨regs', by rw [hn]; trivial, hk, he⟩, fun hf => absurd (hfit _) hf⟩

/-- **`[3 p]` for a fork-free `%next` with the relaxed `sem`.** -/
theorem runOKN_n3_semR (lib : Lib) {p : Nomm} (hp : NextOK (S := S) (Map := Map) lib p)
    (sp : OKNR (S := S) (Map := Map) lib p) {sur : Sure S} {th : Jmp}
    {region : List Nat} {g0 g1 : Gen Map} {nex : NextL S} (hj : GJ g0.bo (CGoal.next sur th)) (hth : th.args = [])
    (hok : GoalOK g0 (CGoal.next sur th)) (hcl : Clean sur.ned)
    (hcount : sixCount p ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl0 : Clear g0)
    (h : runL (Nomm.n3 p) (CGoalL.next (ofSure sur) th) region g0 = some (nex, g1)) :
    SemNR (Map := Map) lib (Nomm.n3 p) sur th g0 g1 nex := by
  have e3 : (runL (Nomm.n3 p) (CGoalL.next (ofSure sur) th) region : CM Map (NextL S)) =
      if noneEquivalentL (ofSure sur) then runL p (CGoalL.next (ofSure sur) th) region else (do
        let a ← collapseLazyAtomL ⟨ofSure sur, th⟩
        match a with
        | Option.none => fun _ => Option.none
        | some (r, o) => do
            let (z, o') ← forl r o
            let r' ← re
            let oc ← emit ⟨[], [], Termin.clq r' (jmp0 z) (jmp0 o')⟩
            runL p (CGoalL.next (ofSure (lazyReg r')) (jmp0 oc)) region) := by
    conv => lhs; unfold runL
    rfl
  rw [e3, noneEquivalentL_ofSure] at h
  by_cases en : noneEquivalent sur = true
  · rw [if_pos en] at h
    have en' := en
    simp only [noneEquivalent, Bool.and_eq_true, decide_eq_true_eq, HoonSet.small_iff] at en'
    exact semN_n3_of_none en'.1 en'.2 (sp hj hth hok hcl hcount b0 d0 hu hcl0 h)
  rw [if_neg en, collapseLazyAtomL_mk] at h
  obtain ⟨a, g2, h2, h⟩ := bind_some h
  obtain ⟨E2, ea, _, hsome⟩ := collapse_ok h2
  have C := collapse_down h2 hj.1 hj.2 b0
  have c2 : g2.cond = g0.cond := (kc_collapseLazyAtom _).keep g0 a g2 h2
  rcases a with _ | ⟨r, o⟩
  · cases h
  obtain ⟨hmr, _, hs⟩ := hsome r o rfl
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
  have Rp := hp ⟨by simp only [jmp0]; omega, by simp only [jmp0, emitted_bo]; omega⟩ rfl
    (by exact ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; simp [emitted_re]⟩) (by exact trivial)
    hcount (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d3) ((G.toU hu).up hu) h
  have Sp := sp ⟨by simp only [jmp0]; omega, by simp only [jmp0, emitted_bo]; omega⟩ rfl
    (by exact ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; simp [emitted_re]⟩) (by exact trivial)
    hcount (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d3) ((G.toU hu).up hu)
    (hcl0.growU (G.toU hu)) h
  refine unaryN_semR (pureEval_n3 p) (E2.trans (E3.trans Ep))
    ⟨by have := E2.1; have := E3.1; omega, by simp [emitted_re]⟩ hok.2 Rp Sp ?_
  intro c hc σ O st regs t gul x hx
  have hb := emitted_get' (by simpa using d3) (hc _ bo3 (by simp [emitted_bo]))
  have hj' := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
  rw [execBlob_clq, hx, Option.bind_some] at hj'
  have F' := F d2 c ((hc.right E2).left E3 Ep) lib σ O st regs t gul
  have hag2 : Agree c g0 g2 := hc.left E2 (E3.trans Ep)
  have keep : ∀ (v : Noun) (k : Nat) (rr : Nat), (k = g2.re ∨ k = g2.re + 1) →
      (Keep g0 ({ g3 with re := g3.re + 1 }.emitted ⟨[], [], Termin.clq g3.re (jmp0 z) (jmp0 o')⟩)
        (CGoal.next sur th) rr ∨ rr = g3.re) →
      SkaModel.read rr (store r v (store k v regs)) = SkaModel.read rr regs := by
    intro v k rr hk hK
    have := er3
    have := E2.1
    rcases hK with ⟨k1, k2⟩ | k1
    · simp only [emitted_re] at k1
      have hne : rr ≠ r := fun e => by
        subst e
        rcases hmr with hm | ⟨hm, _⟩
        · exact k2 hm
        · omega
      rw [read_store_ne hne, read_store_ne (show rr ≠ k by omega)]
    · rw [read_store_ne (show rr ≠ r by omega), read_store_ne (show rr ≠ k by omega)]
  cases x with
  | cell u v =>
    exact GoalSem.transfer (hj'.trans F'.1) (keep (A 0) g2.re · (Or.inl rfl))
      (hs d0 c hag2 lib σ O st (store r (A 0) (store g2.re (A 0) regs)) t gul 0 (read_store_eq _ _ _))
  | atom n =>
    exact GoalSem.transfer (hj'.trans F'.2) (keep (A 1) (g2.re + 1) · (Or.inr rfl))
      (hs d0 c hag2 lib σ O st (store r (A 1) (store (g2.re + 1) (A 1) regs)) t gul 1 (read_store_eq _ _ _))

/-! ## `[4 p]` and `[3 p]` under `%done` and `%pick` -/

/-- **`[4 p]` for `%done` with the relaxed `sem`.** -/
theorem runOKP_n4_semR (lib : Lib) {p : Nomm} (hp : NextOK (S := S) (Map := Map) lib p)
    (sp : OKNR (S := S) (Map := Map) lib p) {region : List Nat} {g0 g1 : Gen Map}
    {nex : NextL S} (hcount : sixCount p ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0)
    (hcl0 : Clear g0) (h : runL (Nomm.n4 p) (CGoal.toL (CGoal.done : CGoal S)) region g0 = some (nex, g1)) :
    SemPR (Map := Map) lib (Nomm.n4 p) CGoal.done g0 g1 nex := by
  have e4 : (runL (Nomm.n4 p) (CGoal.toL (CGoal.done : CGoal S)) region : CM Map (NextL S)) = (do
      let pro ← re
      let arg ← re
      let o ← emit ⟨[], [Pole.inc arg pro], Termin.don pro⟩
      runL p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o)) region) := by
    conv => lhs; unfold runL
    rfl
  rw [e4] at h
  simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
  have G := ((grow_reg g0 (g0.re + 1 + 1)).trans (grow_emit (b := ⟨[], [Pole.inc (g0.re + 1) g0.re],
    Termin.don g0.re⟩) (jumpsBelow_nil rfl _)))
  have Rp := hp ⟨by simp only [jmp0]; omega, by simp only [jmp0, emitted_bo]; omega⟩ rfl
    (by exact ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; simp [emitted_re]⟩) (by exact trivial)
    hcount (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d0) ((G.toU hu).up hu) h
  have Sp := sp ⟨by simp only [jmp0]; omega, by simp only [jmp0, emitted_bo]; omega⟩ rfl
    (by exact ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; simp [emitted_re]⟩) (by exact trivial)
    hcount (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d0) ((G.toU hu).up hu)
    (hcl0.growU (G.toU hu)) h
  refine unaryG_semR (goal := CGoal.done) trivial (pureEval_n4 p)
    ((ext_re _).trans ((ext_re _).trans (ext_emit _ _))) ⟨Nat.le_succ _, by simp [emitted_re]⟩ Rp Sp ?_
  intro c hc σ O st regs t gul x hx
  have hb := emitted_get' (by simpa using d0) (hc _ (by simp) (by simp [emitted_bo]))
  show goJ lib O c gul st regs t _ = some (toneOf t (incF x), st)
  rw [goJ_jmp0 _ _ _ _ hb]
  cases x with
  | atom n =>
    rw [show [Pole.inc _ _] = [Pole.inc _ _] ++ [] from rfl, runs_inc hx]
    simp [incF, toneOf, execBlob_don', read_store_eq]
  | cell u v =>
    rw [show [Pole.inc _ _] = [Pole.inc _ _] ++ [] from rfl, crashes_inc hx]
    rfl

/-- **`[3 p]` for `%done` with the relaxed `sem`.** -/
theorem runOKP_n3_semR (lib : Lib) {p : Nomm} (hp : NextOK (S := S) (Map := Map) lib p)
    (sp : OKNR (S := S) (Map := Map) lib p) {region : List Nat}
    {g0 g1 : Gen Map} {nex : NextL S} (hcount : sixCount p ≤ 255) (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false)
    (hu : UpBelow g0) (hcl0 : Clear g0)
    (h : runL (Nomm.n3 p) (CGoal.toL (CGoal.done : CGoal S)) region g0 = some (nex, g1)) :
    SemPR (Map := Map) lib (Nomm.n3 p) CGoal.done g0 g1 nex := by
  have e3 : (runL (Nomm.n3 p) (CGoal.toL (CGoal.done : CGoal S)) region : CM Map (NextL S)) = (do
      let (o0, o1) ← doneBlocks
      let r ← re
      let oc ← emit ⟨[], [], Termin.clq r (jmp0 o0) (jmp0 o1)⟩
      runL p (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region) := by
    conv => lhs; unfold runL
    rfl
  rw [e3] at h
  obtain ⟨⟨o0, o1⟩, g2, h2, h⟩ := bind_some h
  have B := doneBlocks_down h2 b0
  obtain ⟨D, er, eb, rfl, rfl, DB⟩ := doneBlocks_ok h2
  simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
  have d2 : g2.drop = false := D.2.2.1.trans d0
  have G : Grow g0 ({ g2 with re := g2.re + 1 }.emitted ⟨[], [], Termin.clq g2.re (jmp0 g0.bo) (jmp0 (g0.bo + 1))⟩) :=
    B.1.trans ((grow_re _).trans (grow_emit (jumpsBelow_two rfl B.2.1 B.2.2)))
  have Rp := hp ⟨by simp only [jmp0]; omega, by simp only [jmp0, emitted_bo]; omega⟩ rfl
    (by exact ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; simp [emitted_re]⟩) (by exact trivial)
    hcount (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d2) ((G.toU hu).up hu) h
  have Sp := sp ⟨by simp only [jmp0]; omega, by simp only [jmp0, emitted_bo]; omega⟩ rfl
    (by exact ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; simp [emitted_re]⟩) (by exact trivial)
    hcount (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d2) ((G.toU hu).up hu)
    (hcl0.growU (G.toU hu)) h
  refine unaryG_semR (goal := CGoal.done) trivial (pureEval_n3 p) (D.trans ((ext_re _).trans (ext_emit _ _)))
    ⟨by omega, by simp [emitted_re]⟩ Rp Sp ?_
  intro c hc σ O st regs t gul x hx
  have hb := emitted_get' (by simpa using d2) (hc _ (by show g0.bo ≤ g2.bo; omega) (by simp [emitted_bo]))
  have hj := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
  rw [execBlob_clq, hx, Option.bind_some] at hj
  have DB' := DB c d0 (hc.left D ((ext_re _).trans (ext_emit _ _))) lib σ O st regs t gul
  show goJ lib O c gul st regs t _ = some (toneOf t (some (wut x)), st)
  refine hj.trans ?_
  cases x with
  | atom n => exact DB'.2
  | cell u v => exact DB'.1

/-- **`[4 p]` for `%pick` with the relaxed `sem`.** -/
theorem runOKP_n4p_semR (lib : Lib) {p : Nomm} (hp : NextOK (S := S) (Map := Map) lib p)
    (sp : OKNR (S := S) (Map := Map) lib p) {z o : Jmp} {region : List Nat}
    {g0 g1 : Gen Map} {nex : NextL S} (hj : GJ g0.bo (CGoal.pick z o : CGoal S)) (hcount : sixCount p ≤ 255)
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl0 : Clear g0)
    (h : runL (Nomm.n4 p) (CGoal.toL (CGoal.pick z o : CGoal S)) region g0 = some (nex, g1)) :
    SemPR (Map := Map) lib (Nomm.n4 p) (CGoal.pick z o) g0 g1 nex := by
  have e4 : (runL (Nomm.n4 p) (CGoal.toL (CGoal.pick z o : CGoal S)) region : CM Map (NextL S)) = (do
      let pro ← re
      let arg ← re
      let o' ← emit ⟨[], [Pole.inc arg pro], Termin.brn pro z o⟩
      runL p (CGoalL.next (ofSure (lazyReg arg)) (jmp0 o')) region) := by
    conv => lhs; unfold runL
    rfl
  rw [e4] at h
  simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
  have G := (grow_reg g0 (g0.re + 1 + 1)).trans (grow_emit (b := ⟨[], [Pole.inc (g0.re + 1) g0.re],
    Termin.brn g0.re z o⟩) (jumpsBelow_two rfl hj.1 hj.2))
  have Rp := hp ⟨by simp only [jmp0]; omega, by simp only [jmp0, emitted_bo]; omega⟩ rfl
    (by exact ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; simp [emitted_re]⟩) (by exact trivial)
    hcount (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d0) ((G.toU hu).up hu) h
  have Sp := sp ⟨by simp only [jmp0]; omega, by simp only [jmp0, emitted_bo]; omega⟩ rfl
    (by exact ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; simp [emitted_re]⟩) (by exact trivial)
    hcount (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d0) ((G.toU hu).up hu)
    (hcl0.growU (G.toU hu)) h
  refine unaryG_semR (goal := CGoal.pick z o) trivial (pureEval_n4 p)
    ((ext_re _).trans ((ext_re _).trans (ext_emit _ _))) ⟨Nat.le_succ _, by simp [emitted_re]⟩ Rp Sp ?_
  intro c hc σ O st regs t gul x hx
  have hb := emitted_get' (by simpa using d0) (hc _ (by simp) (by simp [emitted_bo]))
  have hj' := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
  cases x with
  | atom n =>
    rw [show [Pole.inc _ _] = [Pole.inc _ _] ++ [] from rfl, runs_inc hx, execBlob_brn, read_store_eq,
      Option.bind_some] at hj'
    rcases n with _ | n
    · simp only [incF]
      refine ⟨store g0.re (A (0 + 1)) regs, fun r hr => read_store_ne (show r ≠ g0.re by
        rcases hr with ⟨h1, _⟩ | h1
        · simp [emitted_re] at h1; omega
        · omega) _ _, ?_⟩
      rw [hj']; simp
    · simp only [incF]
      exact goalSem_pick_other (by simp) (by simp) (by rw [hj']; simp)
  | cell u v =>
    simp only [incF]
    apply goalSem_crash
    rw [hj', show [Pole.inc _ _] = [Pole.inc _ _] ++ [] from rfl, crashes_inc hx]

/-- **`[3 p]` for `%pick` with the relaxed `sem`.** -/
theorem runOKP_n3p_semR (lib : Lib) {p : Nomm} (hp : NextOK (S := S) (Map := Map) lib p)
    (sp : OKNR (S := S) (Map := Map) lib p) {z o : Jmp} {region : List Nat}
    {g0 g1 : Gen Map} {nex : NextL S} (hj : GJ g0.bo (CGoal.pick z o : CGoal S)) (hcount : sixCount p ≤ 255)
    (b0 : 1 ≤ g0.bo) (d0 : g0.drop = false) (hu : UpBelow g0) (hcl0 : Clear g0)
    (h : runL (Nomm.n3 p) (CGoal.toL (CGoal.pick z o : CGoal S)) region g0 = some (nex, g1)) :
    SemPR (Map := Map) lib (Nomm.n3 p) (CGoal.pick z o) g0 g1 nex := by
  have e3 : (runL (Nomm.n3 p) (CGoal.toL (CGoal.pick z o : CGoal S)) region : CM Map (NextL S)) = (do
      let r ← re
      let oc ← emit ⟨[], [], Termin.clq r z o⟩
      runL p (CGoalL.next (ofSure (lazyReg r)) (jmp0 oc)) region) := by
    conv => lhs; unfold runL
    rfl
  rw [e3] at h
  simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
  have G := (grow_re g0).trans (grow_emit (b := ⟨[], [], Termin.clq g0.re z o⟩) (jumpsBelow_two rfl hj.1 hj.2))
  have Rp := hp ⟨by simp only [jmp0]; omega, by simp only [jmp0, emitted_bo]; omega⟩ rfl
    (by exact ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; simp [emitted_re]⟩) (by exact trivial)
    hcount (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d0) ((G.toU hu).up hu) h
  have Sp := sp ⟨by simp only [jmp0]; omega, by simp only [jmp0, emitted_bo]; omega⟩ rfl
    (by exact ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; simp [emitted_re]⟩) (by exact trivial)
    hcount (by simp only [emitted_bo]; omega) (by simpa [emitted_drop] using d0) ((G.toU hu).up hu)
    (hcl0.growU (G.toU hu)) h
  refine unaryG_semR (goal := CGoal.pick z o) trivial (pureEval_n3 p) ((ext_re _).trans (ext_emit _ _))
    ⟨Nat.le_refl _, by simp [emitted_re]⟩ Rp Sp ?_
  intro c hc σ O st regs t gul x hx
  have hb := emitted_get' (by simpa using d0) (hc _ (by simp) (by simp [emitted_bo]))
  have hj' := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
  rw [execBlob_clq, hx, Option.bind_some] at hj'
  cases x with
  | atom n => exact ⟨regs, fun _ _ => rfl, by rw [hj']⟩
  | cell u v => exact ⟨regs, fun _ _ => rfl, by rw [hj']⟩

end Comp
end SkaModel
end Formalization
