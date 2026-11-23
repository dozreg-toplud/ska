import lemmas.Ska.CompCollapse

/-!
# `+forl` and `[3 p]` for `%next`

`forl_ok`: the two blocks that `+forl` returns put `0` or `1` in the
register it was given and go on to the block it was given.
`run_n3_next_ok`: `[3 p]` for the goal `%next` meets `RunOK`, both when the
goal asks nothing of the product (`+none-equivalent`) and when it does.
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

/-- A block with one parameter `p` and no ops, entered with the argument `a`. -/
theorem execBlob_par1 (regs : Map Noun) (t : Trace) {a p : Nat} (j : Jmp) {v : Noun}
    (hv : SkaModel.read a regs = some v) (hne : a ≠ p) :
    execBlob lib O c gul st regs t ⟨[p], [], Termin.hop j⟩ [some a] =
      goJ lib O c gul st (store p v regs) t j := by
  rw [execBlob]
  have hp : evalPass [some a] [p] regs = some (store p v regs) := by
    simp [evalPass, evalPassLoop, move, hv, hne]
  simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_or, if_true, hp, Option.bind_eq_bind,
    Option.bind_some]
  exact execBlob_hop _ _ _

end

/-- **`+forl`.**  Entering the first block it returns puts `0` in `r` (and
in a fresh register), the second `1`, and both go on to `o`. -/
theorem forl_ok {r o : Nat} {g g' : Gen Map} {z o' : Nat}
    (h : (forl r o : CM Map (Nat × Nat)) g = some ((z, o'), g')) (hr : r < g.re) :
    Ext g g' ∧ g'.re = g.re + 2 ∧ g'.bo = g.bo + 3 ∧
    (g.drop = false → ∀ (c : Straight Map), Agree c g g' → ∀ (lib : Lib) (σ : Type) (O : Oracle σ) (st : σ)
      regs t gul,
      goJ lib O c gul st regs t (jmp0 z) = goJ lib O c gul st (store r (A 0) (store g.re (A 0) regs)) t (jmp0 o) ∧
      goJ lib O c gul st regs t (jmp0 o') =
        goJ lib O c gul st (store r (A 1) (store (g.re + 1) (A 1) regs)) t (jmp0 o)) := by
  simp only [forl, bind_apply, re_apply, emit_apply, Option.bind_some, pure_apply, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  refine ⟨?_, by simp [emitted_re], by simp [emitted_bo], ?_⟩
  · exact (ext_re _).trans ((ext_re _).trans ((ext_emit _ _).trans ((ext_emit _ _).trans (ext_emit _ _))))
  intro hd c hc lib σ O st regs t gul
  have E1 := ext_emit ({ { g with re := g.re + 1 } with re := g.re + 1 + 1 }.emitted
    ⟨[r], [], Termin.hop (jmp0 o)⟩) ⟨[], [Pole.imm (A 0) g.re], Termin.hop ⟨[some g.re], g.bo⟩⟩
  have E2 := ext_emit (({ { g with re := g.re + 1 } with re := g.re + 1 + 1 }.emitted
    ⟨[r], [], Termin.hop (jmp0 o)⟩).emitted ⟨[], [Pole.imm (A 0) g.re], Termin.hop ⟨[some g.re], g.bo⟩⟩)
    ⟨[], [Pole.imm (A 1) (g.re + 1)], Termin.hop ⟨[some (g.re + 1)], g.bo⟩⟩
  have hbarg : HoonMap.get c.blocks g.bo = some ⟨[r], [], Termin.hop (jmp0 o)⟩ := by
    rw [hc g.bo (Nat.le_refl _) (by simp only [Gen.emitted]; omega),
      E2.2.2.2 g.bo (by simp only [Gen.emitted]; omega), E1.2.2.2 g.bo (by simp only [Gen.emitted]; omega)]
    exact emitted_get _ _ (by simp only [Gen.emitted]; exact hd)
  have hb0 : HoonMap.get c.blocks (g.bo + 1) =
      some ⟨[], [Pole.imm (A 0) g.re], Termin.hop ⟨[some g.re], g.bo⟩⟩ := by
    rw [hc (g.bo + 1) (by omega) (by simp only [Gen.emitted]; omega),
      E2.2.2.2 (g.bo + 1) (by simp only [Gen.emitted]; omega)]
    exact emitted_get _ _ (by simp only [Gen.emitted]; exact hd)
  have hb1 : HoonMap.get c.blocks (g.bo + 1 + 1) =
      some ⟨[], [Pole.imm (A 1) (g.re + 1)], Termin.hop ⟨[some (g.re + 1)], g.bo⟩⟩ := by
    rw [hc (g.bo + 1 + 1) (by omega) (by simp only [Gen.emitted]; omega)]
    exact emitted_get _ _ (by simp only [Gen.emitted]; exact hd)
  simp only [emitted_bo]
  constructor
  · rw [goJ_jmp0 _ _ _ _ hb0, show [Pole.imm (A 0) g.re] = [Pole.imm (A 0) g.re] ++ [] from rfl, runs_imm,
      execBlob_hop]
    simp only [goJ, hbarg, Option.bind_some]
    exact execBlob_par1 _ _ _ (read_store_eq _ _ _) (by omega)
  · rw [goJ_jmp0 _ _ _ _ hb1, show [Pole.imm (A 1) (g.re + 1)] = [Pole.imm (A 1) (g.re + 1)] ++ [] from rfl,
      runs_imm, execBlob_hop]
    simp only [goJ, hbarg, Option.bind_some]
    exact execBlob_par1 _ _ _ (read_store_eq _ _ _) (by omega)

/-- `[3 p]` when the goal asks nothing of the product: the code of `p` for
the same goal does. -/
theorem runOK_n3_of_none {lib : Lib} {p : Nomm} {laz : Sure S} {th : Jmp} {g0 g1 : Gen Map} {nex : Next S}
    (hn : laz.ned = Need.none) (hl : ∀ x ∈ HoonSet.toList laz.lok, x = 1)
    (hp : RunOK lib p (CGoal.next laz th) g0 g1 nex) :
    RunOK lib (Nomm.n3 p) (CGoal.next laz th) g0 g1 nex := by
  have hfit : ∀ v, FitsS laz v := fun v => ⟨by rw [hn]; trivial, fun y hy => by rw [hl y hy]; simp⟩
  exact {
    ext := hp.ext
    regs := hp.regs
    nec := fun s hs => by
      rw [pureEval_n3]
      rcases hp.nec s hs with h | ⟨x, _, h2⟩
      · rw [h]; exact Or.inl rfl
      · exact absurd (hfit x) h2
    dist := hp.dist
    sem := fun hd c hag σ O st s regs t gul hh => by
      have H := hp.sem hd c hag σ O st s regs t gul hh
      rw [pureEval_n3]
      cases e : pureEval p s with
      | none => rw [e] at H; exact goalSem_crash _ H
      | some x =>
        rw [e] at H
        obtain ⟨regs', _, hk, he⟩ := H.1 (hfit x)
        exact ⟨fun _ => ⟨regs', by rw [hn]; trivial, hk, he⟩, fun hf => absurd (hfit _) hf⟩ }

/-- **`[3 p]` for `%next`.** -/
theorem run_n3_next_ok {lib : Lib} {p : Nomm} {laz : Sure S} {th : Jmp} {g0 g1 : Gen Map} {nex : Next S}
    (h : run (Nomm.n3 p) (CGoal.next laz th) g0 = some (nex, g1))
    (hg : GoalOK g0 (CGoal.next laz th))
    (ih : ∀ (laz : Sure S) (th : Jmp) (g g' : Gen Map) (nex' : Next S), GoalOK g (CGoal.next laz th) →
      run p (CGoal.next laz th) g = some (nex', g') → RunOK lib p (CGoal.next laz th) g g' nex') :
    RunOK lib (Nomm.n3 p) (CGoal.next laz th) g0 g1 nex := by
  by_cases en : noneEquivalent laz = true
  · simp only [run, en, if_true] at h
    have en' := en
    simp only [noneEquivalent, Bool.and_eq_true, decide_eq_true_eq, HoonSet.small_iff] at en'
    exact runOK_n3_of_none en'.1 en'.2 (ih _ _ _ _ _ hg h)
  simp only [run, en, Bool.false_eq_true, if_false] at h
  obtain ⟨a, g2, h2, h⟩ := bind_some h
  obtain ⟨E2, ea, _, hsome⟩ := collapse_ok h2
  rcases a with _ | ⟨r, o⟩
  · cases h
  obtain ⟨hmr, _, hs⟩ := hsome r o rfl
  obtain ⟨⟨z, o'⟩, g3, h3, h⟩ := bind_some h
  have hr : r < g2.re := by
    rcases hmr with hm | ⟨_, h2⟩
    · exact Nat.lt_of_lt_of_le (hg.2 r hm) E2.1
    · exact h2
  obtain ⟨E3, er3, eb3, F⟩ := forl_ok h3 hr
  simp only [bind_apply, re_apply, emit_apply, Option.bind_some] at h
  have Ep := (ext_re g3).trans (ext_emit { g3 with re := g3.re + 1 } ⟨[], [], Termin.clq g3.re (jmp0 z) (jmp0 o')⟩)
  refine unary_ok (pureEval_n3 p) (E2.trans (E3.trans Ep))
    ⟨by have := E2.1; have := E3.1; omega, by simp [emitted_re]⟩ (by simp [emitted_bo])
    (ih _ _ _ _ _ ⟨trivial, fun r hr => by simp [lazyReg, NMem] at hr; subst hr; simp [emitted_re]⟩ h) ?_
    (by have := E2.2.1; have := E3.2.1; show g0.bo ≤ g3.bo; omega)
  intro c hc hd σ O st regs t gul x hx
  have hd2 : g2.drop = false := E2.2.2.1.trans hd
  have hd3 : g3.drop = false := E3.2.2.1.trans hd2
  have hb := emitted_get' (by simpa using hd3)
    (hc _ (by have := E2.2.1; have := E3.2.1; show g0.bo ≤ g3.bo; omega) (by simp [emitted_bo]))
  have hj := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
  rw [execBlob_clq, hx, Option.bind_some] at hj
  have F' := F hd2 c ((hc.right E2).left E3 Ep) lib σ O st regs t gul
  have hag2 : Agree c g0 g2 := hc.left E2 (E3.trans Ep)
  -- the kept registers are neither `r` nor the fresh register of `+forl`
  have keep : ∀ (v : Noun) (rr : Nat), Keep g0 (CGoal.next laz th) rr →
      SkaModel.read rr (store r v (store g2.re v regs)) = SkaModel.read rr regs := by
    intro v rr ⟨k1, k2⟩
    have hne : rr ≠ r := fun e => by
      subst e
      rcases hmr with hm | ⟨hm, _⟩
      · exact k2 hm
      · omega
    rw [read_store_ne hne, read_store_ne (show rr ≠ g2.re by have := E2.1; omega)]
  have keep1 : ∀ (rr : Nat), Keep g0 (CGoal.next laz th) rr →
      SkaModel.read rr (store r (A 1) (store (g2.re + 1) (A 1) regs)) = SkaModel.read rr regs := by
    intro rr ⟨k1, k2⟩
    have hne : rr ≠ r := fun e => by
      subst e
      rcases hmr with hm | ⟨hm, _⟩
      · exact k2 hm
      · omega
    rw [read_store_ne hne, read_store_ne (show rr ≠ g2.re + 1 by have := E2.1; omega)]
  cases x with
  | cell u v =>
    have G := hs hd c hag2 lib σ O st (store r (A 0) (store g2.re (A 0) regs)) t gul 0 (read_store_eq _ _ _)
    exact GoalSem.transfer (hj.trans F'.1) (keep (A 0)) G
  | atom n =>
    have G := hs hd c hag2 lib σ O st (store r (A 1) (store (g2.re + 1) (A 1) regs)) t gul 1 (read_store_eq _ _ _)
    exact GoalSem.transfer (hj.trans F'.2) keep1 G

end Comp
end SkaModel
end Formalization
