import lemmas.Ska.CompBinary

/-!
# `[5 p q]` for every goal

`run_n5_ok`: the case `%5` of `run` meets `RunOK` for every goal.  The block
it emits before compiling the operands compares the two registers: for
`%pick` it branches to the goal's jumps, for `%done` to two blocks that
return `0` and `1`, for `%next` through `+collapse-lazy-atom` and `+forl`,
or, when the goal asks nothing of the product, it only reads both registers
(`%equ`) and goes on.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

section
variable {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ}

theorem execBlob_eqq (regs : Map Noun) (t : Trace) (l r : Nat) (z o : Jmp) :
    execBlob lib O c gul st regs t ⟨[], [], Termin.eqq l r z o⟩ [] =
      (SkaModel.read l regs).bind fun x => (SkaModel.read r regs).bind fun y =>
        if x = y then goJ lib O c gul st regs t z else goJ lib O c gul st regs t o := by
  rw [execBlob]; simp only [goJ]
  cases SkaModel.read l regs with
  | none => rfl
  | some x =>
    cases SkaModel.read r regs with
    | none => rfl
    | some y => by_cases e : x = y <;> simp [e]

/-- Fewer registers kept. -/
theorem GoalSem.mono {K K' : Nat → Prop} {regs : Map Noun} {t : Trace} {je : Jmp} {goal : CGoal S}
    {v : Option Noun} (hK : ∀ r, K' r → K r) (h : GoalSem lib O c gul st K regs t je goal v) :
    GoalSem lib O c gul st K' regs t je goal v := by
  cases goal with
  | done => exact h
  | next laz th =>
    cases v with
    | none => exact h
    | some p => exact ⟨fun hf => let ⟨r2, h1, h2, h3⟩ := h.1 hf; ⟨r2, h1, fun r hr => h2 r (hK r hr), h3⟩, h.2⟩
  | pick z o =>
    rcases v with _ | ⟨⟨_ | _ | k⟩ | ⟨a, b⟩⟩
    · exact h
    · obtain ⟨r2, h2, h3⟩ := h; exact ⟨r2, fun r hr => h2 r (hK r hr), h3⟩
    · obtain ⟨r2, h2, h3⟩ := h; exact ⟨r2, fun r hr => h2 r (hK r hr), h3⟩
    · exact h
    · exact h

end

theorem pureEval_n5 (p q : Nomm) (s : Noun) :
    pureEval (Nomm.n5 p q) s = (pureEval p s).bind fun x => (pureEval q s).bind fun y => some (eqCode x y) := rfl

theorem fitsS_lazyReg (r : Nat) (x : Noun) : FitsS (lazyReg r : Sure S) x := ⟨trivial, looks_empty x⟩

/-- `%5` once its block is made. -/
theorem n5_of_block {lib : Lib} {p q : Nomm} {goal : CGoal S} {g0 g2 g3 g4 g1 : Gen Map} {o : Nat}
    {nexq nexp nex : Next S}
    (hg : GoalOK g0 goal) (E : Ext g0 g2) (hre : g0.re + 2 ≤ g2.re)
    (hblk : ∀ (c : Straight Map), Agree c g0 g2 → g0.drop = false → ∀ (σ : Type) (O : Oracle σ) st regs t gul x y,
      SkaModel.read g0.re regs = some x → SkaModel.read (g0.re + 1) regs = some y →
      GoalSem lib O c gul st (Keep g0 goal) regs t (jmp0 o) goal (some (eqCode x y)))
    (h3 : run q (CGoal.next (lazyReg (g0.re + 1)) (jmp0 o)) g2 = some (nexq, g3))
    (h4 : run p (CGoal.next (lazyReg g0.re) nexq.th) g3 = some (nexp, g4))
    (h : copy nexp nexq.laz g4 = some (nex, g1))
    (ihp : ∀ (laz : Sure S) (th : Jmp) (g g' : Gen Map) (nex' : Next S), GoalOK g (CGoal.next laz th) → Clean laz.ned →
      run p (CGoal.next laz th) g = some (nex', g') → RunOK lib p (CGoal.next laz th) g g' nex')
    (ihq : ∀ (laz : Sure S) (th : Jmp) (g g' : Gen Map) (nex' : Next S), GoalOK g (CGoal.next laz th) → Clean laz.ned →
      run q (CGoal.next laz th) g = some (nex', g') → RunOK lib q (CGoal.next laz th) g g' nex') :
    RunOK lib (Nomm.n5 p q) goal g0 g1 nex := by
  have hq := ihq (lazyReg (g0.re + 1)) _ _ _ _ ⟨trivial, fun r hr => by simp only [lazyReg, NMem] at hr; omega⟩ trivial h3
  have hp := ihp (lazyReg g0.re) _ _ _ _ ⟨trivial, fun r hr => by
    simp only [lazyReg, NMem] at hr; have := hq.ext.1; omega⟩ trivial h4
  refine binary_ok (pureEval_n5 p q) hg E (fun r hr => ?_) (fun r hr => ?_) (fun r h1 h2 => ?_) hq hp
    (run_clean q _ _ _ _ (by trivial) h3) (run_clean p _ _ _ _ (by trivial) h4) h
    (fun x y hn => absurd (hn.elim (fun a => a (fitsS_lazyReg _ x)) (fun a => a (fitsS_lazyReg _ y))) id)
    (fun c hc hd σ O st regs t gul x y _ _ hx hy => hblk c hc hd σ O st regs t gul x y hx hy)
  · simp only [lazyReg, NMem] at hr; exact Or.inr ⟨by omega, by omega⟩
  · simp only [lazyReg, NMem] at hr; exact Or.inr ⟨by omega, by omega⟩
  · simp only [lazyReg, NMem] at h1 h2; omega

/-- **`[5 p q]`.** -/
theorem run_n5_ok {lib : Lib} {p q : Nomm} {goal : CGoal S} {g0 g1 : Gen Map} {nex : Next S}
    (h : run (Nomm.n5 p q) goal g0 = some (nex, g1)) (hg : GoalOK g0 goal)
    (ihp : ∀ (laz : Sure S) (th : Jmp) (g g' : Gen Map) (nex' : Next S), GoalOK g (CGoal.next laz th) → Clean laz.ned →
      run p (CGoal.next laz th) g = some (nex', g') → RunOK lib p (CGoal.next laz th) g g' nex')
    (ihq : ∀ (laz : Sure S) (th : Jmp) (g g' : Gen Map) (nex' : Next S), GoalOK g (CGoal.next laz th) → Clean laz.ned →
      run q (CGoal.next laz th) g = some (nex', g') → RunOK lib q (CGoal.next laz th) g g' nex') :
    RunOK lib (Nomm.n5 p q) goal g0 g1 nex := by
  simp only [run, bind_apply, re_apply, Option.bind_some] at h
  obtain ⟨⟨o, g2⟩, h2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨nexq, g3⟩, h3, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨nexp, g4⟩, h4, h⟩ := Option.bind_eq_some_iff.mp h
  have G0 : Ext g0 { { g0 with re := g0.re + 1 } with re := g0.re + 1 + 1 } := (ext_re _).trans (ext_re _)
  suffices B : Ext g0 g2 ∧ g0.re + 2 ≤ g2.re ∧ ∀ (c : Straight Map), Agree c g0 g2 → g0.drop = false →
      ∀ (σ : Type) (O : Oracle σ) st regs t gul x y, SkaModel.read g0.re regs = some x →
      SkaModel.read (g0.re + 1) regs = some y →
      GoalSem lib O c gul st (Keep g0 goal) regs t (jmp0 o) goal (some (eqCode x y)) from
    n5_of_block hg B.1 B.2.1 B.2.2 h3 h4 h ihp ihq
  clear h3 h4 h
  cases goal with
  | pick z o' =>
    simp only [emit_apply, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    refine ⟨G0.trans (ext_emit _ _), by simp [emitted_re], fun c hc hd σ O st regs t gul x y hx hy => ?_⟩
    have hb := emitted_get' (by simpa using hd) (hc _ (by simp) (by simp [emitted_bo]))
    have hj := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
    rw [execBlob_eqq, hx, hy] at hj
    simp only [Option.bind_some] at hj
    by_cases e : x = y
    · rw [if_pos e] at hj
      simp only [eqCode, if_pos e]
      exact ⟨regs, fun _ _ => rfl, hj⟩
    · rw [if_neg e] at hj
      simp only [eqCode, if_neg e]
      exact ⟨regs, fun _ _ => rfl, hj⟩
  | done =>
    obtain ⟨⟨o0, o1⟩, g5, h5, h2⟩ := bind_some h2
    obtain ⟨D, er, eb, rfl, rfl, DB⟩ := doneBlocks_ok h5
    rw [emit_apply] at h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    refine ⟨G0.trans (D.trans (ext_emit _ _)), by simp only [emitted_re, er]; omega,
      fun c hc hd σ O st regs t gul x y hx hy => ?_⟩
    have hd5 : g5.drop = false := D.2.2.1.trans hd
    have hb := emitted_get' hd5 (hc _ (by simp only [eb]; omega) (by simp [emitted_bo]))
    have hj := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
    rw [execBlob_eqq, hx, hy] at hj
    simp only [Option.bind_some] at hj
    have DB' := DB c hd ((hc.right G0).left D (ext_emit _ _)) lib σ O st regs t gul
    show goJ lib O c gul st regs t (jmp0 g5.bo) = some (toneOf t (some (eqCode x y)), st)
    by_cases e : x = y
    · rw [if_pos e] at hj; simp only [eqCode, if_pos e]; exact hj.trans DB'.1
    · rw [if_neg e] at hj; simp only [eqCode, if_neg e]; exact hj.trans DB'.2
  | next laz th =>
    obtain ⟨a, g5, h5, h2⟩ := bind_some h2
    obtain ⟨E5, ea, hnone, hsome⟩ := collapse_ok h5
    have l5 := E5.1
    simp only at l5
    cases a with
    | none =>
      obtain ⟨hn, hl⟩ := hnone rfl
      simp only at h2
      rw [if_pos ea, emit_apply] at h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      refine ⟨G0.trans (E5.trans (ext_emit _ _)), by simp only [emitted_re]; omega,
        fun c hc hd σ O st regs t gul x y hx hy => ?_⟩
      have hd5 : g5.drop = false := E5.2.2.1.trans hd
      have hb := emitted_get' hd5 (hc _ (by have := E5.2.1; simp at this; omega) (by simp [emitted_bo]))
      have hj := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
      rw [show [Pole.equ g0.re (g0.re + 1)] = [Pole.equ g0.re (g0.re + 1)] ++ [] from rfl, runs_equ hx hy,
        execBlob_hop, jmp0_of_args ea] at hj
      exact ⟨fun _ => ⟨regs, by rw [hn]; trivial, fun _ _ => rfl, hj⟩,
        fun hf => absurd ⟨by rw [hn]; trivial, fun y hy => by rw [hl y hy]; simp⟩ hf⟩
    | some ro =>
      obtain ⟨r, o''⟩ := ro
      obtain ⟨hmr, _, hs⟩ := hsome r o'' rfl
      simp only at h2
      obtain ⟨⟨z, o'⟩, g6, h6, h2⟩ := bind_some h2
      have hr : r < g5.re := by
        rcases hmr with hm | ⟨_, h⟩
        · have := hg.2 r hm; omega
        · exact h
      obtain ⟨E6, er6, eb6, F⟩ := forl_ok h6 hr
      rw [emit_apply] at h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      have Ep := ext_emit g6 ⟨[], [], Termin.eqq g0.re (g0.re + 1) (jmp0 z) (jmp0 o')⟩
      refine ⟨G0.trans (E5.trans (E6.trans Ep)), by simp only [emitted_re, er6]; omega,
        fun c hc hd σ O st regs t gul x y hx hy => ?_⟩
      have hd5 : g5.drop = false := E5.2.2.1.trans hd
      have hd6 : g6.drop = false := E6.2.2.1.trans hd5
      have hb := emitted_get' hd6 (hc _ (by have := E5.2.1; have := E6.2.1; simp at *; omega)
        (by simp [emitted_bo]))
      have hj := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
      rw [execBlob_eqq, hx, hy] at hj
      simp only [Option.bind_some] at hj
      have F' := F hd5 c ((hc.right (G0.trans E5)).left E6 Ep) lib σ O st regs t gul
      have hagX := (hc.right G0).left E5 (E6.trans Ep)
      have keepX : ∀ rr, Keep g0 (CGoal.next laz th) rr →
          Keep { { g0 with re := g0.re + 1 } with re := g0.re + 1 + 1 } (CGoal.next laz th) rr :=
        fun rr ⟨k1, k2⟩ => ⟨by simp; omega, k2⟩
      have keep : ∀ (v : Noun) (k rr : Nat), g5.re ≤ k → Keep g0 (CGoal.next laz th) rr →
          SkaModel.read rr (store r v (store k v regs)) = SkaModel.read rr regs := by
        intro v k rr hk ⟨k1, k2⟩
        have hne : rr ≠ r := fun e => by
          subst e
          rcases hmr with hm | ⟨hm, _⟩
          · exact k2 hm
          · simp at hm; omega
        rw [read_store_ne hne, read_store_ne (show rr ≠ k by omega)]
      by_cases e : x = y
      · rw [if_pos e] at hj
        simp only [eqCode, if_pos e]
        exact GoalSem.transfer (hj.trans F'.1) (keep (A 0) g5.re · (Nat.le_refl _))
          (GoalSem.mono keepX (hs hd c hagX lib σ O st _ t gul 0 (read_store_eq _ _ _)))
      · rw [if_neg e] at hj
        simp only [eqCode, if_neg e]
        exact GoalSem.transfer (hj.trans F'.2) (keep (A 1) (g5.re + 1) · (Nat.le_succ _))
          (GoalSem.mono keepX (hs hd c hagX lib σ O st _ t gul 1 (read_store_eq _ _ _)))

end Comp
end SkaModel
end Formalization
