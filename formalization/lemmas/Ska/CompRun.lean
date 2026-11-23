import lemmas.Ska.CompSem

/-!
# The relation for the leaves of `run`: `%0` and `%1`

`RunOK` (`CompSem.lean`) for the cases `[%0 *]` and `[%1 *]` of the model
of `run`, each goal: `+simple-next`, `+from` and `+bomb` for `%0`, the
blocks of `%1` for `%done` and `%pick`.
-/

set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Comp

open Nock

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map]

theorem bind_some {α β : Type} {x : CM Map α} {f : α → CM Map β} {g : Gen Map} {r : β × Gen Map}
    (h : (x >>= f) g = some r) : ∃ a g', x g = some (a, g') ∧ f a g' = some r := by
  rw [bind_apply] at h
  obtain ⟨⟨a, g'⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨a, g', h1, h2⟩

theorem emitted_get (g : Gen Map) (b : Blob) (hd : g.drop = false) :
    HoonMap.get (g.emitted b).blocks g.bo = some b := by
  simp [Gen.emitted, hd, HoonMap.get_put]

theorem emitted_bo (g : Gen Map) (b : Blob) : (g.emitted b).bo = g.bo + 1 := rfl
theorem emitted_re (g : Gen Map) (b : Blob) : (g.emitted b).re = g.re := rfl
theorem emitted_drop (g : Gen Map) (b : Blob) : (g.emitted b).drop = g.drop := rfl

section
variable {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ}

/-- Where the code crashes, it does what every goal asks of no value. -/
theorem goalSem_crash {K : Nat → Prop} {regs : Map Noun} {t : Trace} {je : Jmp} (goal : CGoal S)
    (h : goJ lib O c gul st regs t je = some (Tone.two t, st)) :
    GoalSem lib O c gul st K regs t je goal none := by
  cases goal <;> simp only [GoalSem, toneOf] <;> exact h

/-- A product that is no loobean, on `%pick`. -/
theorem goalSem_pick_other {K : Nat → Prop} {regs : Map Noun} {t : Trace} {je z o : Jmp} {k : Noun}
    (h0 : k ≠ A 0) (h1 : k ≠ A 1) (h : goJ lib O c gul st regs t je = some (Tone.two t, st)) :
    GoalSem lib O c gul st K regs t je (CGoal.pick z o : CGoal S) (some k) := by
  rcases k with ⟨_ | _ | k⟩ | ⟨a, b⟩
  · exact absurd rfl h0
  · exact absurd rfl h1
  · exact h
  · exact h

end

/-- A code that always crashes. -/
theorem crash_ok {lib : Lib} {nm : Nomm} {goal : CGoal S} {g0 : Gen Map} {miss : Option Nat}
    (hnm : ∀ s, pureEval nm s = none) :
    RunOK lib nm goal g0 (g0.emitted ⟨[], [], Termin.bom miss⟩) ⟨Sure.bunt, jmp0 g0.bo⟩ where
  ext := ext_emit _ _
  regs := fun r hr => by simp [Sure.bunt, NMem] at hr
  nec := fun s hs => absurd (fitsS_bunt s) hs
  dist := trivial
  sem := by
    intro hd c hag σ O st s regs t gul _
    rw [hnm s]
    apply goalSem_crash
    rw [goJ_jmp0 _ _ _ _ ((hag g0.bo (Nat.le_refl _) (by simp [emitted_bo])).trans (emitted_get _ _ hd)),
      execBlob_bom']

theorem bomb_eq (miss : Option Nat) (g0 : Gen Map) :
    (bomb miss : CM Map (Next S)) g0 = some (⟨Sure.bunt, jmp0 g0.bo⟩, g0.emitted ⟨[], [], Termin.bom miss⟩) := by
  simp only [bomb, bind_apply, emit_apply, Option.bind_some, pure_apply]

/-- **`+simple-next`**: the code of `[0 1]` for every goal. -/
theorem simpleNext_ok {lib : Lib} {goal : CGoal S} {g0 g1 : Gen Map} {nex : Next S}
    (h : simpleNext goal g0 = some (nex, g1)) (hg : GoalOK g0 goal) : RunOK lib (Nomm.n0 1) goal g0 g1 nex := by
  cases goal with
  | next laz th =>
    simp only [simpleNext, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact {
      ext := Ext.refl _
      regs := fun r hr => Or.inl hr
      nec := fun s hs => Or.inr ⟨s, by simp [pureEval, slot?_one], hs⟩
      dist := hg.1
      sem := fun _ c _ σ O st s regs t gul hh => by
        simp only [pureEval, slot?_one, GoalSem]
        exact ⟨fun _ => ⟨regs, hh.1, fun _ _ => rfl, rfl⟩, fun hn => absurd (fitsS_of_holdsS hh) hn⟩ }
  | done =>
    simp only [simpleNext, bind_apply, re_apply, emit_apply, pure_apply, Option.bind_some,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact {
      ext := (ext_re g0).trans (ext_emit _ _)
      regs := fun r hr => by simp only [NMem] at hr; subst hr; right; simp [emitted_re]
      nec := fun s hs => absurd ⟨trivial, looks_empty s⟩ hs
      dist := trivial
      sem := fun hd c hag σ O st s regs t gul hh => by
        simp only [pureEval, slot?_one, GoalSem, toneOf]
        rw [goJ_jmp0 _ _ _ _ ((hag g0.bo (Nat.le_refl _) (by simp [emitted_bo])).trans (emitted_get _ _ hd)),
          execBlob_don']
        simp only [HoldsS, HoldsN] at hh
        simp [hh.1] }
  | pick z o =>
    simp only [simpleNext, bind_apply, re_apply, emit_apply, pure_apply, Option.bind_some,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact {
      ext := (ext_re g0).trans (ext_emit _ _)
      regs := fun r hr => by simp only [NMem] at hr; subst hr; right; simp [emitted_re]
      nec := fun s hs => absurd ⟨trivial, looks_empty s⟩ hs
      dist := trivial
      sem := fun hd c hag σ O st s regs t gul hh => by
        simp only [pureEval, slot?_one]
        have hb := goJ_jmp0 (lib := lib) (O := O) (gul := gul) (st := st) regs t _ _
          ((hag g0.bo (Nat.le_refl _) (by simp [emitted_bo])).trans (emitted_get _ _ hd))
        rw [execBlob_brn] at hb
        simp only [HoldsS, HoldsN] at hh
        rw [hh.1, Option.bind_some] at hb
        rcases s with ⟨_ | _ | k⟩ | ⟨a, b⟩
        · exact ⟨regs, fun _ _ => rfl, by rw [hb]; simp⟩
        · exact ⟨regs, fun _ _ => rfl, by rw [hb]; simp⟩
        · simp only [GoalSem]; rw [hb]; simp
        · simp only [GoalSem]; rw [hb]; simp }

theorem distinct_fromPath (ned : Need) (hd : Distinct ned) : ∀ axe, Distinct (fromPath ned axe) := by
  intro axe
  induction axe using Nat.strongRecOn with
  | ind axe ih =>
    by_cases h1 : axe ≤ 1
    · rw [fromPath]; simp [h1, hd]
    · rw [fromPath_step ned (by omega)]
      have := ih _ (mas_lt axe (by omega))
      split <;> simp [Distinct, NMem, this]

/-- **`+from`**: the code of `[0 1]` for a goal is the code of `[0 axe]`
for it, with the need of the subject moved under `axe`. -/
theorem from_ok {lib : Lib} {goal : CGoal S} {g0 g1 : Gen Map} {nex : Next S} {axe : Nat} {laz : Sure S}
    (hr : RunOK lib (Nomm.n0 1) goal g0 g1 nex) (hf : fromSure axe nex.laz = some laz) :
    RunOK lib (Nomm.n0 axe) goal g0 g1 ⟨laz, nex.th⟩ := by
  obtain ⟨ha, hhold, hfit, hmem⟩ := fromSure_spec (Map := Map) hf
  refine ⟨hr.ext, fun r h => hr.regs r (hmem r h), ?_, ?_, ?_⟩
  · intro s hs
    simp only [pureEval]
    cases e : slot? axe s with
    | none => exact Or.inl rfl
    | some p =>
      refine Or.inr ⟨p, rfl, ?_⟩
      have hn : ¬ FitsS nex.laz p := fun hp => hs (hfit s p e hp)
      rcases hr.nec p hn with h | ⟨q, hq, hq'⟩
      · simp [pureEval, slot?_one] at h
      · simp only [pureEval, slot?_one, Option.some.injEq] at hq; subst hq; exact hq'
  · unfold fromSure at hf
    by_cases hn : nex.laz.ned = Need.none
    · simp only [show axe ≠ 0 by omega, if_false, hn, if_true] at hf
      split at hf
      · cases hf
      · cases hf; trivial
    · simp only [show axe ≠ 0 by omega, if_false, hn] at hf
      cases hf; exact distinct_fromPath _ hr.dist axe
  · intro hd c hag σ O st s regs t gul hh
    obtain ⟨p, hp, hh'⟩ := hhold regs s hh
    have := hr.sem hd c hag σ O st p regs t gul hh'
    simp only [pureEval, slot?_one] at this
    simp only [pureEval, hp]
    exact this

/-- **The case `%0` of `run`**, every goal. -/
theorem run_n0_ok {lib : Lib} {axe : Nat} {goal : CGoal S} {g0 g1 : Gen Map} {nex : Next S}
    (h : run (Nomm.n0 axe) goal g0 = some (nex, g1)) (hg : GoalOK g0 goal) :
    RunOK lib (Nomm.n0 axe) goal g0 g1 nex := by
  simp only [run] at h
  by_cases h0 : axe = 0
  · subst h0
    simp only [if_true, bomb_eq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact crash_ok fun s => by simp [pureEval, slot?_zero]
  · simp only [h0, if_false] at h
    obtain ⟨nex0, g0', h1, h2⟩ := bind_some h
    have hs := simpleNext_ok (lib := lib) h1 hg
    by_cases ha : axe = 1
    · subst ha; simp only [if_true, pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2; exact hs
    · simp only [ha, if_false] at h2
      cases e : «from» axe nex0.laz with
      | none => rw [e] at h2; cases h2
      | some laz =>
        rw [e] at h2
        simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, rfl⟩ := h2
        exact from_ok hs e

/-- **The case `%1` of `run` for `%done` and `%pick`.** -/
theorem run_n1_done_ok {lib : Lib} {k : Noun} {g0 g1 : Gen Map} {nex : Next S}
    (h : run (Nomm.n1 k) (CGoal.done : CGoal S) g0 = some (nex, g1)) :
    RunOK lib (Nomm.n1 k) CGoal.done g0 g1 nex := by
  simp only [run, bind_apply, re_apply, emit_apply, pure_apply, Option.bind_some,
    Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact {
    ext := (ext_re g0).trans (ext_emit _ _)
    regs := fun r hr => by simp [Sure.bunt, NMem] at hr
    nec := fun s hs => absurd (fitsS_bunt s) hs
    dist := trivial
    sem := fun hd c hag σ O st s regs t gul _ => by
      simp only [pureEval, GoalSem, toneOf]
      rw [goJ_jmp0 _ _ _ _ ((hag g0.bo (Nat.le_refl _) (by simp [emitted_bo])).trans (emitted_get _ _ hd)),
        execBlob_cons]
      simp [execPole_imm, execBlob_don', read_store_eq] }

theorem run_n1_pick_ok {lib : Lib} {k : Noun} {z o : Jmp} {g0 g1 : Gen Map} {nex : Next S}
    (h : run (Nomm.n1 k) (CGoal.pick z o : CGoal S) g0 = some (nex, g1)) :
    RunOK lib (Nomm.n1 k) (CGoal.pick z o) g0 g1 nex := by
  simp only [run] at h
  by_cases h0 : k = A 0
  · subst h0
    simp only [if_true, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Ext.refl _, fun r hr => by simp [Sure.bunt, NMem] at hr, fun s hs => absurd (fitsS_bunt s) hs,
      trivial, fun _ c _ σ O st s regs t gul _ => by
        simp only [pureEval, GoalSem]; exact ⟨regs, fun _ _ => rfl, rfl⟩⟩
  by_cases h1 : k = A 1
  · subst h1
    simp only [h0, if_true, if_false, pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Ext.refl _, fun r hr => by simp [Sure.bunt, NMem] at hr, fun s hs => absurd (fitsS_bunt s) hs,
      trivial, fun _ c _ σ O st s regs t gul _ => by
        simp only [pureEval, GoalSem]; exact ⟨regs, fun _ _ => rfl, rfl⟩⟩
  simp only [h0, h1, if_false, bomb_eq, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact {
    ext := ext_emit _ _
    regs := fun r hr => by simp [Sure.bunt, NMem] at hr
    nec := fun s hs => absurd (fitsS_bunt s) hs
    dist := trivial
    sem := fun hd c hag σ O st s regs t gul _ => by
      simp only [pureEval]
      apply goalSem_pick_other h0 h1
      rw [goJ_jmp0 _ _ _ _ ((hag g0.bo (Nat.le_refl _) (by simp [emitted_bo])).trans (emitted_get _ _ hd)),
        execBlob_bom'] }

/-! ## Composition: `%7` -/

section
variable {lib : Lib} {σ : Type} {O : Oracle σ} {c : Straight Map} {gul : Noun} {st : σ}

/-- What the code does for a goal, a code that goes on as it does does too. -/
theorem GoalSem.transfer {K : Nat → Prop} {regs regs' : Map Noun} {t : Trace} {je je' : Jmp}
    {goal : CGoal S} {v : Option Noun}
    (he : goJ lib O c gul st regs t je = goJ lib O c gul st regs' t je')
    (hk : ∀ r, K r → SkaModel.read r regs' = SkaModel.read r regs)
    (h : GoalSem lib O c gul st K regs' t je' goal v) : GoalSem lib O c gul st K regs t je goal v := by
  cases goal with
  | done => simp only [GoalSem] at h ⊢; rw [he]; exact h
  | next laz th =>
    cases v with
    | none => simp only [GoalSem] at h ⊢; rw [he]; exact h
    | some p =>
      exact ⟨fun hf => let ⟨r2, h1, h2, h3⟩ := h.1 hf
        ⟨r2, h1, fun r hr => (h2 r hr).trans (hk r hr), he.trans h3⟩, fun hf => he.trans (h.2 hf)⟩
  | pick z o =>
    rcases v with _ | ⟨⟨_ | _ | k⟩ | ⟨a, b⟩⟩
    · simp only [GoalSem] at h ⊢; rw [he]; exact h
    · obtain ⟨r2, h2, h3⟩ := h; exact ⟨r2, fun r hr => (h2 r hr).trans (hk r hr), he.trans h3⟩
    · obtain ⟨r2, h2, h3⟩ := h; exact ⟨r2, fun r hr => (h2 r hr).trans (hk r hr), he.trans h3⟩
    · simp only [GoalSem] at h ⊢; rw [he]; exact h
    · simp only [GoalSem] at h ⊢; rw [he]; exact h

/-- A product without the goal's shape or looks: the code must crash. -/
theorem goalSem_not {K : Nat → Prop} {regs : Map Noun} {t : Trace} {je : Jmp} {goal : CGoal S} {p : Noun}
    (hn : GNot goal p) (h : goJ lib O c gul st regs t je = some (Tone.two t, st)) :
    GoalSem lib O c gul st K regs t je goal (some p) := by
  cases goal with
  | next laz th => exact ⟨fun hf => absurd hf hn, fun _ => h⟩
  | _ => exact hn.elim

end

theorem goalOK_of_runOK {lib : Lib} {nm : Nomm} {goal : CGoal S} {g0 g1 : Gen Map} {nex : Next S}
    (hg : GoalOK g0 goal) (h : RunOK lib nm goal g0 g1 nex) : GoalOK g1 nex.goal := by
  refine ⟨h.dist, fun r hr => ?_⟩
  rcases h.regs r hr with hm | ⟨_, h2⟩
  · cases goal with
    | next laz th => exact Nat.lt_of_lt_of_le (hg.2 r hm) h.ext.1
    | _ => exact hm.elim
  · exact h2

theorem keep_mono {g0 g1 : Gen Map} {goal : CGoal S} {nex : Next S} (he : Ext g0 g1)
    (hregs : ∀ r, NMem nex.laz.ned r → GMem goal r ∨ (g0.re ≤ r ∧ r < g1.re)) :
    ∀ r, Keep g0 goal r → Keep g1 nex.goal r := by
  intro r ⟨h1, h2⟩
  refine ⟨Nat.lt_of_lt_of_le h1 he.1, fun hm => ?_⟩
  rcases hregs r hm with h | ⟨h3, _⟩
  · exact h2 h
  · omega

/-- **`[7 p q]`**: `q` for the goal, then `p` for the `next` of `q`. -/
theorem run_n7_ok {lib : Lib} {p q : Nomm} {goal : CGoal S} {g0 g1 g2 : Gen Map} {nexq nex : Next S}
    (hq : RunOK lib q goal g0 g1 nexq) (hp : RunOK lib p nexq.goal g1 g2 nex) :
    RunOK lib (Nomm.n7 p q) goal g0 g2 nex where
  ext := hq.ext.trans hp.ext
  regs := fun r hr => by
    rcases hp.regs r hr with h | ⟨h1, h2⟩
    · rcases hq.regs r h with h' | ⟨h1', h2'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨h1', Nat.lt_of_lt_of_le h2' hp.ext.1⟩
    · exact Or.inr ⟨Nat.le_trans hq.ext.1 h1, h2⟩
  nec := fun s hs => by
    simp only [pureEval]
    rcases hp.nec s hs with h | ⟨s', h1, h2⟩
    · rw [h]; exact Or.inl rfl
    · rw [h1, Option.bind_some]; exact hq.nec s' h2
  dist := hp.dist
  sem := fun hd c hag σ O st s regs t gul hh => by
    have hd1 : g1.drop = false := hq.ext.2.2.1.trans hd
    have Hp := hp.sem hd1 c (hag.right hq.ext) σ O st s regs t gul hh
    simp only [pureEval]
    cases e : pureEval p s with
    | none => rw [e] at Hp; exact goalSem_crash goal Hp
    | some s' =>
      rw [e] at Hp
      simp only [Option.bind_some]
      by_cases hf : FitsS nexq.laz s'
      · obtain ⟨regs', hh', hk, he⟩ := Hp.1 hf
        exact GoalSem.transfer he (fun r hr => hk r (keep_mono hq.ext hq.regs r hr))
          (hq.sem hd c (hag.left hq.ext hp.ext) σ O st s' regs' t gul ⟨hh', hf.2⟩)
      · have hc := Hp.2 hf
        rcases hq.nec s' hf with h | ⟨v, h1, h2⟩
        · rw [h]; exact goalSem_crash goal hc
        · rw [h1]; exact goalSem_not h2 hc

end Comp
end SkaModel
end Formalization
