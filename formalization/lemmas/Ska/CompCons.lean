import lemmas.Ska.CompSplit

/-!
# Cons for every goal

`run_cons_ok`: the case `[^ *]` of `run` meets `RunOK` for every goal.  For
`%next` the goal's need is split into the needs of the head and the tail;
for `%done` the goal is first turned into `%next` into a register that a
`%don` block returns; for `%pick` (a cell as a loobean) the code crashes
after computing both halves.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

theorem pureEval_cons (p q : Nomm) (s : Noun) :
    pureEval (Nomm.cons p q) s = (pureEval p s).bind fun x => (pureEval q s).bind fun y => some (C x y) := rfl

/-- Cons for a goal `%next`. -/
theorem cons_next_ok {lib : Lib} {p q : Nomm} {laz : Sure S} {th : Jmp} {g0 g1 : Gen Map} {nex : Next S}
    (hg : GoalOK g0 (CGoal.next laz th)) (hc : Clean laz.ned)
    (h : (do
      let (hed, tel, o) ← Comp.split ⟨laz, th⟩
      let nexh : Next S := ⟨hed, jmp0 o⟩
      let nex2 ← run q (CGoal.next tel nexh.th)
      let nex1 ← run p (CGoal.next nexh.laz nex2.th)
      copy nex1 nex2.laz : CM Map (Next S)) g0 = some (nex, g1))
    (ihp : ∀ (laz : Sure S) (th : Jmp) (g g' : Gen Map) (nex' : Next S), GoalOK g (CGoal.next laz th) → Clean laz.ned →
      run p (CGoal.next laz th) g = some (nex', g') → RunOK lib p (CGoal.next laz th) g g' nex')
    (ihq : ∀ (laz : Sure S) (th : Jmp) (g g' : Gen Map) (nex' : Next S), GoalOK g (CGoal.next laz th) → Clean laz.ned →
      run q (CGoal.next laz th) g = some (nex', g') → RunOK lib q (CGoal.next laz th) g g' nex') :
    RunOK lib (Nomm.cons p q) (CGoal.next laz th) g0 g1 nex := by
  obtain ⟨⟨hed, tel, o⟩, g2, h2, h⟩ := bind_some h
  obtain ⟨eo, E2, _, Mh, Mt, SP⟩ := split_ok h2
  obtain ⟨Dh, Dt, Dht, F, B⟩ := SP hg.1 hg.2
  simp only at h
  obtain ⟨nex2, g3, h3, h⟩ := bind_some h
  obtain ⟨nex1, g4, h4, h⟩ := bind_some h
  have lt2 : ∀ (n : Need), (∀ y, NMem n y → NMem laz.ned y ∨ (g0.re ≤ y ∧ y < g2.re)) →
      ∀ y, NMem n y → y < g2.re := fun n M y hy => by
    rcases M y hy with a | ⟨_, a⟩
    · exact Nat.lt_of_lt_of_le (hg.2 y a) E2.1
    · exact a
  have CS := clean_split h2 hc
  have hq := ihq tel (jmp0 o) g2 g3 nex2 ⟨Dt, lt2 _ Mt⟩ CS.2 h3
  have hp := ihp hed nex2.th g3 g4 nex1 ⟨Dh, fun y hy => Nat.lt_of_lt_of_le (lt2 _ Mh y hy) hq.ext.1⟩ CS.1 h4
  refine binary_ok (pureEval_cons p q) hg E2 Mh Mt Dht hq hp (run_clean q _ _ _ _ (by exact CS.2) h3)
    (run_clean p _ _ _ _ (by exact CS.1) h4) h (fun x y hn => Or.inr ⟨C x y, rfl, fun hf => ?_⟩)
    (fun c hc hd σ O st regs t gul x y fx fy hx hy => ?_)
  · rcases hn with a | a
    · exact a ((F x y).mp hf).1
    · exact a ((F x y).mp hf).2
  · refine ⟨fun _ => ?_, fun hn => absurd ((F x y).mpr ⟨fx, fy⟩) hn⟩
    obtain ⟨R', hl, u, e⟩ := B hd c hc lib σ O st t regs x y gul hx hy
    exact ⟨R', hl, fun r ⟨_, k⟩ => u r k, e⟩

/-- **Cons**, for every goal. -/
theorem run_cons_ok {lib : Lib} {p q : Nomm} {goal : CGoal S} {g0 g1 : Gen Map} {nex : Next S}
    (h : run (Nomm.cons p q) goal g0 = some (nex, g1)) (hg : GoalOK g0 goal) (hc : GClean goal)
    (ihp : ∀ (laz : Sure S) (th : Jmp) (g g' : Gen Map) (nex' : Next S), GoalOK g (CGoal.next laz th) → Clean laz.ned →
      run p (CGoal.next laz th) g = some (nex', g') → RunOK lib p (CGoal.next laz th) g g' nex')
    (ihq : ∀ (laz : Sure S) (th : Jmp) (g g' : Gen Map) (nex' : Next S), GoalOK g (CGoal.next laz th) → Clean laz.ned →
      run q (CGoal.next laz th) g = some (nex', g') → RunOK lib q (CGoal.next laz th) g g' nex') :
    RunOK lib (Nomm.cons p q) goal g0 g1 nex := by
  cases goal with
  | next laz th =>
    simp only [run, bind_apply, pure_apply, Option.bind_some] at h
    exact cons_next_ok hg hc h ihp ihq
  | done =>
    simp only [run, bind_apply, re_apply, emit_apply, Option.bind_some, pure_apply] at h
    have Hn := cons_next_ok (lib := lib) (laz := lazyReg g0.re) ⟨trivial, fun r hr => by
      simp only [lazyReg, NMem] at hr; simp [hr, emitted_re]⟩ trivial h ihp ihq
    refine unary_ok (f := some) (fun s => by cases pureEval (Nomm.cons p q) s <;> rfl)
      ((ext_re _).trans (ext_emit _ _)) ⟨Nat.le_refl _, by simp [emitted_re]⟩ (by simp [emitted_bo]) Hn ?_
      (by simp)
    intro c hc hd σ O st regs t gul x hx
    have hb := emitted_get' (by simpa using hd) (hc _ (by simp) (by simp [emitted_bo]))
    show goJ lib O c gul st regs t (jmp0 _) = some (toneOf t (some x), st)
    rw [goJ_jmp0 _ _ _ _ hb, execBlob_don', hx]; rfl
  | pick z o =>
    simp only [run, bind_apply, pure_apply, emit_apply, Option.bind_some] at h
    obtain ⟨⟨nex2, g3⟩, h3, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨nex1, g4⟩, h4, h⟩ := Option.bind_eq_some_iff.mp h
    have hq := ihq Sure.bunt _ _ g3 nex2 ⟨trivial, fun r hr => hr.elim⟩ trivial h3
    have hp := ihp Sure.bunt nex2.th g3 g4 nex1 ⟨trivial, fun r hr => hr.elim⟩ trivial h4
    refine binary_ok (pureEval_cons p q) hg (ext_emit _ _) (fun r hr => by exact hr.elim)
      (fun r hr => by exact hr.elim) (fun r hr => by exact hr.elim) hq hp (run_clean q _ _ _ _ (by trivial) h3)
      (run_clean p _ _ _ _ (by trivial) h4) h
      (fun x y hn => absurd (hn.elim (fun a => a (fitsS_bunt x)) (fun a => a (fitsS_bunt y))) id) ?_
    intro c hc hd σ O st regs t gul x y _ _ _ _
    have hb := emitted_get' hd (hc _ (by simp) (by simp [emitted_bo]))
    show goJ lib O c gul st regs t (jmp0 g0.bo) = some (Tone.two t, st)
    rw [goJ_jmp0 _ _ _ _ hb, execBlob_bom']

end Comp
end SkaModel
end Formalization
