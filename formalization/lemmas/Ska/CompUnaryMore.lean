import lemmas.Ska.CompUnary

/-!
# More unary cases of `run`

`doneBlocks_ok`: the two blocks that `[3 p]` and `[5 p q]` make for the
goal `%done` return `0` and `1`.  `run_n3_done_ok`: `[3 p]` for `%done`
meets `RunOK`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

theorem goJ_imm_don {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ}
    {o : Nat} {k : Noun} {r : Nat} (hb : HoonMap.get c.blocks o = some ⟨[], [Pole.imm k r], Termin.don r⟩)
    (regs : Map Noun) (t : Trace) :
    goJ lib O c gul st regs t (jmp0 o) = some (Tone.zero k, st) := by
  rw [goJ_jmp0 _ _ _ _ hb, show [Pole.imm k r] = [Pole.imm k r] ++ [] from rfl, runs_imm, execBlob_don',
    read_store_eq]
  rfl

/-- **The blocks of `%done` for a loobean.** -/
theorem doneBlocks_ok {g g' : Gen Map} {o0 o1 : Nat}
    (h : (doneBlocks : CM Map (Nat × Nat)) g = some ((o0, o1), g')) :
    Ext g g' ∧ g'.re = g.re + 2 ∧ g'.bo = g.bo + 2 ∧ o0 = g.bo ∧ o1 = g.bo + 1 ∧
      ∀ (c : Straight Map), g.drop = false → Agree c g g' → ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (st : σ) regs t gul,
        goJ lib O c gul st regs t (jmp0 o0) = some (Tone.zero (A 0), st) ∧
        goJ lib O c gul st regs t (jmp0 o1) = some (Tone.zero (A 1), st) := by
  simp only [doneBlocks, bind_apply, re_apply, emit_apply, Option.bind_some, pure_apply, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  have e1 := (ext_re g).trans ((ext_re _).trans (ext_emit _ ⟨[], [Pole.imm (A 0) g.re], Termin.don g.re⟩))
  have e2 := ext_emit ({ { g with re := g.re + 1 } with re := g.re + 1 + 1 }.emitted
    ⟨[], [Pole.imm (A 0) g.re], Termin.don g.re⟩) ⟨[], [Pole.imm (A 1) (g.re + 1)], Termin.don (g.re + 1)⟩
  refine ⟨e1.trans e2, by simp [emitted_re], by simp [emitted_bo], rfl, rfl, ?_⟩
  intro c hd hc lib σ O st regs t gul
  have hb0 : HoonMap.get c.blocks g.bo = some ⟨[], [Pole.imm (A 0) g.re], Termin.don g.re⟩ := by
    rw [hc g.bo (Nat.le_refl _) (by simp only [Gen.emitted]; omega), e2.2.2.2 g.bo (by simp only [Gen.emitted]; omega)]
    exact emitted_get _ _ (by simp only [Gen.emitted]; exact hd)
  have hb1 : HoonMap.get c.blocks (g.bo + 1) = some ⟨[], [Pole.imm (A 1) (g.re + 1)], Termin.don (g.re + 1)⟩ := by
    rw [hc (g.bo + 1) (by omega) (by simp only [Gen.emitted]; omega)]
    exact emitted_get _ _ (by simp only [Gen.emitted]; exact hd)
  exact ⟨goJ_imm_don hb0 regs t, goJ_imm_don hb1 regs t⟩

/-- **`[3 p]` for `%done`.** -/
theorem run_n3_done_ok {lib : Lib} {p : Nomm} {g0 g1 : Gen Map} {nex : Next S}
    (h : run (Nomm.n3 p) (CGoal.done : CGoal S) g0 = some (nex, g1))
    (ih : ∀ (laz : Sure S) (th : Jmp) (g g' : Gen Map) (nex' : Next S), GoalOK g (CGoal.next laz th) → Clean laz.ned →
      run p (CGoal.next laz th) g = some (nex', g') → RunOK lib p (CGoal.next laz th) g g' nex') :
    RunOK lib (Nomm.n3 p) CGoal.done g0 g1 nex := by
  simp only [run] at h
  obtain ⟨⟨o0, o1⟩, g2, h2, h⟩ := bind_some h
  try simp only at h
  try simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
  obtain ⟨D, er, eb, rfl, rfl, DB⟩ := doneBlocks_ok h2
  refine unary_ok (pureEval_n3 p) (D.trans ((ext_re _).trans (ext_emit _ _)))
    ⟨by omega, by simp [emitted_re]⟩ (by simp [emitted_bo])
    (ih _ _ _ _ _ ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; simp [emitted_re]⟩ trivial h) ?_
    (show g0.bo ≤ g2.bo by omega)
  intro c hc hd σ O st regs t gul x hx
  have hd2 : g2.drop = false := D.2.2.1.trans hd
  have hb := emitted_get' (by simpa using hd2) (hc _ (by simp; omega) (by simp [emitted_bo]))
  have hj := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
  rw [execBlob_clq, hx, Option.bind_some] at hj
  have DB' := DB c hd (hc.left D ((ext_re _).trans (ext_emit _ _))) lib σ O st regs t gul
  show goJ lib O c gul st regs t (jmp0 g2.bo) = some (toneOf t (some (wut x)), st)
  refine hj.trans ?_
  cases x with
  | atom n => exact DB'.2
  | cell u v => exact DB'.1

end Comp
end SkaModel
end Formalization
