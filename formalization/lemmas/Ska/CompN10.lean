import lemmas.Ska.CompInto

/-!
# `[10 [a v] q]` for every goal

`run_n10_ok`: the case `%10` of `run` meets `RunOK` for every goal.  It is
`binary_ok` with the recipient `q` as the operand that runs first and the
donor `v` as the second, and the edit as the operation: `+into` splits the
goal's need into the donor's and the recipient's, `v` is compiled for the
donor's, then `q` for the recipient's, then `+copy`.  The code runs the
recipient before the donor, as `+mink` does (the order of f6a76c2).  For
`%done` and `%pick`, `+simple-next` makes the goal `%next` into a register
that a `%don` or a `%brn` block reads.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

theorem pureEval_n10 {a : Nat} (ha : a ≠ 0) (v q : Nomm) (s : Noun) :
    pureEval (Nomm.n10 a v q) s = (pureEval q s).bind fun x => (pureEval v s).bind fun y => edit? a y x := by
  simp only [pureEval, if_neg ha]

/-- `%10` for a goal `%next`, once `+simple-next` returned it. -/
theorem n10_next_ok {lib : Lib} {a : Nat} {v q : Nomm} {laz : Sure S} {th : Jmp} {g0 g2 g3 g4 g1 : Gen Map}
    {don rec : Sure S} {o : Nat} {nexRec nexDon nex : Next S}
    (hg : GoalOK g0 (CGoal.next laz th)) (hc : Clean laz.ned)
    (h1 : into ⟨laz, th⟩ a g0 = some ((don, rec, o), g2))
    (h2 : run v (CGoal.next don (jmp0 o)) g2 = some (nexDon, g3))
    (h3 : run q (CGoal.next rec nexDon.th) g3 = some (nexRec, g4))
    (h4 : copy nexRec nexDon.laz g4 = some (nex, g1))
    (ihv : ∀ (laz : Sure S) (th : Jmp) (g g' : Gen Map) (nex' : Next S), GoalOK g (CGoal.next laz th) →
      Clean laz.ned → run v (CGoal.next laz th) g = some (nex', g') → RunOK lib v (CGoal.next laz th) g g' nex')
    (ihq : ∀ (laz : Sure S) (th : Jmp) (g g' : Gen Map) (nex' : Next S), GoalOK g (CGoal.next laz th) →
      Clean laz.ned → run q (CGoal.next laz th) g = some (nex', g') → RunOK lib q (CGoal.next laz th) g g' nex') :
    RunOK lib (Nomm.n10 a v q) (CGoal.next laz th) g0 g1 nex := by
  obtain ⟨a1, eo, E2, _, Md, Mr, Fe, SP⟩ := into_ok h1
  subst eo
  obtain ⟨Dd, Dr, Ddr, F, B⟩ := SP hg.1 hg.2
  have lt2 : ∀ (n : Need), (∀ y, NMem n y → NMem laz.ned y ∨ (g0.re ≤ y ∧ y < g2.re)) →
      ∀ y, NMem n y → y < g2.re := fun n M y hy => by
    rcases M y hy with e | ⟨_, e⟩
    · exact Nat.lt_of_lt_of_le (hg.2 y e) E2.1
    · exact e
  have CI := clean_into h1 hc
  have hv := ihv don (jmp0 g0.bo) g2 g3 nexDon ⟨Dd, lt2 _ Md⟩ CI.1 h2
  have hq := ihq rec nexDon.th g3 g4 nexRec ⟨Dr, fun y hy => Nat.lt_of_lt_of_le (lt2 _ Mr y hy) hv.ext.1⟩
    CI.2 h3
  refine binary_ok (pureEval_n10 (by omega) v q) hg E2 Mr Md (fun r hr hd => Ddr r hd hr) hv hq
    (run_clean v _ _ _ _ (by exact CI.1) h2) (run_clean q _ _ _ _ (by exact CI.2) h3) h4
    (fun x y hn => ?_) (fun c hc hd σ O st regs t gul x y fx fy hx hy => ?_)
  · cases e : edit? a y x with
    | none => exact Or.inl rfl
    | some n =>
      refine Or.inr ⟨n, rfl, fun hf => ?_⟩
      rcases hn with b | b
      · exact b ((F y x n e).mp hf).2
      · exact b ((F y x n e).mp hf).1
  · obtain ⟨n, e⟩ := Option.isSome_iff_exists.mp (Fe y x fx)
    rw [e]
    refine ⟨fun _ => ?_, fun hn => absurd ((F y x n e).mpr ⟨fy, fx⟩) hn⟩
    obtain ⟨R', hl, u, ej⟩ := B hd c hc lib σ O st t regs y x n gul e hy hx
    exact ⟨R', hl, fun r ⟨k1, k2⟩ => u r k2 k1, ej⟩

/-- **`[10 [a v] q]`**, for every goal. -/
theorem run_n10_ok {lib : Lib} {a : Nat} {v q : Nomm} {goal : CGoal S} {g0 g1 : Gen Map} {nex : Next S}
    (h : run (Nomm.n10 a v q) goal g0 = some (nex, g1)) (hg : GoalOK g0 goal) (hc : GClean goal)
    (ihv : ∀ (laz : Sure S) (th : Jmp) (g g' : Gen Map) (nex' : Next S), GoalOK g (CGoal.next laz th) →
      Clean laz.ned → run v (CGoal.next laz th) g = some (nex', g') → RunOK lib v (CGoal.next laz th) g g' nex')
    (ihq : ∀ (laz : Sure S) (th : Jmp) (g g' : Gen Map) (nex' : Next S), GoalOK g (CGoal.next laz th) →
      Clean laz.ned → run q (CGoal.next laz th) g = some (nex', g') → RunOK lib q (CGoal.next laz th) g g' nex') :
    RunOK lib (Nomm.n10 a v q) goal g0 g1 nex := by
  simp only [run] at h
  obtain ⟨nex0, gs, hs, h⟩ := bind_some h
  obtain ⟨⟨don, rec, o⟩, g2, h1, h⟩ := bind_some h
  simp only at h
  obtain ⟨nexR, g2', hpr, h⟩ := bind_some h
  obtain ⟨rfl, rfl⟩ := past_some hpr
  obtain ⟨nexDon, g3, h2, h⟩ := bind_some h
  obtain ⟨nexDon', g3', hpd, h⟩ := bind_some h
  obtain ⟨rfl, rfl⟩ := past_some hpd
  obtain ⟨nexRec, g4, h3, h4⟩ := bind_some h
  cases goal with
  | next laz th =>
    simp only [simpleNext, pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact n10_next_ok hg hc h1 h2 h3 h4 ihv ihq
  | done =>
    simp only [simpleNext, bind_apply, re_apply, emit_apply, Option.bind_some, pure_apply,
      Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    have Hn := n10_next_ok (lib := lib) (laz := lazyReg g0.re) ⟨trivial, fun r hr => by
      simp only [lazyReg, NMem] at hr; simp [hr, emitted_re]⟩ trivial h1 h2 h3 h4 ihv ihq
    refine unary_ok (f := some) (fun s => by cases pureEval (Nomm.n10 a v q) s <;> rfl)
      ((ext_re _).trans (ext_emit _ _)) ⟨Nat.le_refl _, by simp [emitted_re]⟩ (by simp [emitted_bo]) Hn ?_
      (by simp)
    intro c hc hd σ O st regs t gul x hx
    have hb := emitted_get' (by simpa using hd) (hc _ (by simp) (by simp [emitted_bo]))
    show goJ lib O c gul st regs t (jmp0 _) = some (toneOf t (some x), st)
    rw [goJ_jmp0 _ _ _ _ hb, execBlob_don', hx]; rfl
  | pick z o' =>
    simp only [simpleNext, bind_apply, re_apply, emit_apply, Option.bind_some, pure_apply,
      Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    have Hn := n10_next_ok (lib := lib) (laz := lazyReg g0.re) ⟨trivial, fun r hr => by
      simp only [lazyReg, NMem] at hr; simp [hr, emitted_re]⟩ trivial h1 h2 h3 h4 ihv ihq
    refine unary_ok (f := some) (fun s => by cases pureEval (Nomm.n10 a v q) s <;> rfl)
      ((ext_re _).trans (ext_emit _ _)) ⟨Nat.le_refl _, by simp [emitted_re]⟩ (by simp [emitted_bo]) Hn ?_
      (by simp)
    intro c hc hd σ O st regs t gul x hx
    have hb := emitted_get' (by simpa using hd) (hc _ (by simp) (by simp [emitted_bo]))
    have hj := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _ hb
    rw [execBlob_brn, hx, Option.bind_some] at hj
    by_cases x0 : x = A 0
    · subst x0
      exact ⟨regs, fun _ _ => rfl, by rw [hj]; simp⟩
    by_cases x1 : x = A 1
    · subst x1
      exact ⟨regs, fun _ _ => rfl, by rw [hj]; simp⟩
    exact goalSem_pick_other x0 x1 (by rw [hj]; simp [x0, x1])

end Comp
end SkaModel
end Formalization
