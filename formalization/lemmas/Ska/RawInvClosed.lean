import lemmas.Ska.RawInvTop
import lemmas.Ska.CompLeafKeep

/-!
# Raw `+comp` output: a run's code jumps only into itself or to its goal

README Gaps 14.  `ClosedR lo T bl`: every block at a label from `lo` on
jumps to a label from `lo` on or to a label of `T`.  `run_closed`: the blocks
a run of `run` makes (at labels from the state's `bo` on) jump only to its
own blocks or to the targets of its goal (`GTgt`), and its entry is one of
them.  This is what lets liveness at a run's entry be cut at the goal's
targets after later code changed those targets (`RawInvRobust.lean`).

The bundle `CS lo T g` (closure, no block from `bo` on, `lo ≤ bo`, not
dropping, `1 ≤ bo`) is kept by the quiet steps of track C (`Quiet`), by a
new block whose jumps go from `lo` on or into `T` (`cs_emit`), and by a
sub-run that is closed for its own goal (`cs_sub`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Formalization
namespace SkaModel
namespace Raw

open Nock Opt Comp

variable {S : Type} [HoonSet S] {Map : Type → Type} [HoonMap Map] [HoonMapKeys Map]

/-- The labels a goal jumps to. -/
def GTgt : CGoal S → Nat → Prop
  | CGoal.next _ th, t => t = th.there
  | CGoal.pick z o, t => t = z.there ∨ t = o.there
  | CGoal.done, _ => False

/-- Every block from `lo` on jumps from `lo` on or into `T`. -/
def ClosedR (lo : Nat) (T : Nat → Prop) (bl : Map Blob) : Prop :=
  ∀ k b, lo ≤ k → HoonMap.get bl k = some b → ∀ j ∈ getJmps b.fin, lo ≤ j.there ∨ T j.there

/-- The bundle the steps keep. -/
structure CS (lo : Nat) (T : Nat → Prop) (g : Comp.Gen Map) : Prop where
  cl : ClosedR lo T g.blocks
  clear : Clear g
  le : lo ≤ g.bo
  drop : g.drop = false
  bo1 : 1 ≤ g.bo

theorem cs_start {T : Nat → Prop} {g : Comp.Gen Map} (hc : Clear g) (hd : g.drop = false) (h1 : 1 ≤ g.bo) :
    CS g.bo T g :=
  ⟨fun k b hk hb => (by rw [hc k hk] at hb; cases hb), hc, Nat.le_refl _, hd, h1⟩

theorem cs_quiet {lo : Nat} {T : Nat → Prop} {g g' : Comp.Gen Map} (h : CS lo T g) (q : Quiet g g') : CS lo T g' := by
  refine ⟨fun k b hk hb => ?_, h.clear.grow q.1, by rw [q.2]; exact h.le, by rw [q.1.drop]; exact h.drop,
    by rw [q.2]; exact h.bo1⟩
  rcases q.1.new k b hb with ⟨b0, hb0, -, hf⟩ | ⟨l, u, -⟩
  · rw [hf]; exact h.cl k b0 hk hb0
  · rw [q.2] at u; omega

theorem quiet_of_re {g g' : Comp.Gen Map} {r : Nat} (h : (re : CM Map Nat) g = some (r, g')) :
    Quiet g g' ∧ g'.bo = g.bo ∧ r = g.re ∧ g'.re = g.re + 1 := by
  rw [re_apply] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨quiet_re g, rfl, rfl, rfl⟩

theorem cs_emit {lo : Nat} {T : Nat → Prop} {g g' : Comp.Gen Map} {b : Blob} {o : Nat} (h : CS lo T g)
    (hj : ∀ j ∈ getJmps b.fin, lo ≤ j.there ∨ T j.there) (he : (emit b : CM Map Nat) g = some (o, g')) :
    CS lo T g' ∧ o = g.bo ∧ g'.bo = g.bo + 1 ∧ g'.re = g.re := by
  rw [emit_apply] at he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have eb : (g.emitted b).blocks = HoonMap.put g.blocks g.bo b := by simp [Gen.emitted, h.drop]
  refine ⟨⟨fun k b' hk hb => ?_, fun k hk => ?_, by simp [Gen.emitted]; have := h.le; omega, h.drop,
    by simp [Gen.emitted]⟩, rfl, rfl, rfl⟩
  · rw [eb] at hb
    rcases get_put_cases hb with ⟨rfl, rfl⟩ | ⟨-, hb⟩
    · exact hj
    · exact h.cl k b' hk hb
  · simp only [Gen.emitted] at hk
    rw [eb, get_put_ne (by omega)]; exact h.clear k (by omega)

theorem cs_sub {lo : Nat} {T T' : Nat → Prop} {g g' : Comp.Gen Map} (h : CS lo T g) (G : Grow g g')
    (hc : ClosedR g.bo T' g'.blocks) (ht : ∀ t, T' t → lo ≤ t ∨ T t) : CS lo T g' := by
  refine ⟨fun k b hk hb => ?_, h.clear.grow G, Nat.le_trans h.le G.bo, by rw [G.drop]; exact h.drop,
    Nat.le_trans h.bo1 G.bo⟩
  rcases G.new k b hb with ⟨b0, hb0, -, hf⟩ | ⟨l, -, -⟩
  · rw [hf]; exact h.cl k b0 hk hb0
  · intro j hj
    rcases hc k b l hb j hj with e | e
    · exact Or.inl (Nat.le_trans h.le e)
    · exact ht _ e

theorem getJmps_hop (t : Jmp) : getJmps (Termin.hop t) = [t] := rfl

theorem hop_ok {lo : Nat} {T : Nat → Prop} {t : Jmp} (h : lo ≤ t.there ∨ T t.there) :
    ∀ j ∈ getJmps (Termin.hop t), lo ≤ j.there ∨ T j.there := by
  intro j hj; simp [getJmps] at hj; subst hj; exact h

theorem none_ok {lo : Nat} {T : Nat → Prop} {f : Termin} (h : getJmps f = []) :
    ∀ j ∈ getJmps f, lo ≤ j.there ∨ T j.there := by
  intro j hj; rw [h] at hj; cases hj

/-! ## The arms -/

theorem cs_split {lo : Nat} {T : Nat → Prop} {nex : Next S} {g g' : Comp.Gen Map} {x : Sure S × Sure S × Nat}
    (h : CS lo T g) (ht : lo ≤ nex.th.there ∨ T nex.th.there) (hs : Comp.split nex g = some (x, g')) :
    CS lo T g' ∧ x.2.2 = g.bo ∧ g'.bo = g.bo + 1 := by
  simp only [Comp.split] at hs
  obtain ⟨o, g1, h1, hs⟩ := bind_some hs
  obtain ⟨C1, rfl, b1, -⟩ := cs_emit h (hop_ok ht) h1
  obtain ⟨⟨sh, st⟩, g2, h2, hs⟩ := bind_some hs
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  simp only [splitSure] at h2
  obtain ⟨⟨lh, lt⟩, _, h2⟩ := Option.bind_eq_some_iff.mp h2
  obtain ⟨⟨⟨nh, nt⟩, g3⟩, h3, h4⟩ := Option.map_eq_some_iff.mp h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
  exact ⟨cs_quiet C1 (quiet_splitNeed h3), rfl, by rw [(quiet_splitNeed h3).2, b1]⟩

theorem cs_into {lo : Nat} {T : Nat → Prop} {nex : Next S} {axe : Nat} {g g' : Comp.Gen Map}
    {x : Sure S × Sure S × Nat} (h : CS lo T g) (ht : lo ≤ nex.th.there ∨ T nex.th.there)
    (hs : into nex axe g = some (x, g')) : CS lo T g' ∧ x.2.2 = g.bo ∧ g'.bo = g.bo + 1 := by
  simp only [into] at hs
  obtain ⟨o, g1, h1, hs⟩ := bind_some hs
  obtain ⟨C1, rfl, b1, -⟩ := cs_emit h (hop_ok ht) h1
  obtain ⟨⟨sd, sr⟩, g2, h2, hs⟩ := bind_some hs
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  simp only [intoSure] at h2
  obtain ⟨⟨ld, lr⟩, _, h2⟩ := Option.bind_eq_some_iff.mp h2
  obtain ⟨⟨⟨nd, nr⟩, g3⟩, h3, h4⟩ := Option.map_eq_some_iff.mp h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h4
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
  simp only [intoNeed] at h3
  split at h3
  · cases h3
  split at h3
  · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h3; rw [← h3.2]; exact ⟨C1, rfl, b1⟩
  · exact ⟨cs_quiet C1 (quiet_intoLoop _ _ _ _ _ _ _ h3), rfl, by rw [(quiet_intoLoop _ _ _ _ _ _ _ h3).2, b1]⟩

theorem cs_copy {lo : Nat} {T : Nat → Prop} {first : Next S} {second : Sure S} {g g' : Comp.Gen Map}
    {nex : Next S} (h : CS lo T g) (ht : lo ≤ first.th.there ∨ T first.th.there)
    (hs : copy first second g = some (nex, g')) : CS lo T g' ∧ lo ≤ nex.th.there ∧ nex.th.there < g'.bo := by
  simp only [copy] at hs
  obtain ⟨o, g1, h1, hs⟩ := bind_some hs
  obtain ⟨C1, rfl, b1, -⟩ := cs_emit h (hop_ok ht) h1
  obtain ⟨laz, g2, h2, hs⟩ := bind_some hs
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  simp only [copyLazy] at h2
  obtain ⟨⟨ned, ops⟩, g3, h3, h2⟩ := bind_some h2
  obtain ⟨u, g4, h4, h2⟩ := bind_some h2
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl⟩ := h2
  have q3 := quiet_copyNeed _ _ _ _ _ _ h3
  have q4 := quiet_addOps h4
  refine ⟨cs_quiet (cs_quiet C1 q3) q4, by simp [jmp0]; exact h.le, ?_⟩
  simp only [jmp0]; rw [q4.2, q3.2]; omega

theorem cs_mede {lo : Nat} {T : Nat → Prop} {th : Jmp} {som : Noun} {laz : Sure S} {g g' : Comp.Gen Map} {o : Nat}
    (h : CS lo T g) (ht : lo ≤ th.there ∨ T th.there) (hs : mede th som laz g = some (o, g')) :
    CS lo T g' ∧ lo ≤ o := by
  simp only [mede] at hs
  obtain ⟨o', g1, h1, hs⟩ := bind_some hs
  obtain ⟨C1, rfl, -, -⟩ := cs_emit h (hop_ok ht) h1
  obtain ⟨g2, g2', h2, hs⟩ := bind_some hs
  rw [get_apply] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl⟩ := h2
  rw [C1.drop] at hs
  simp only [Bool.false_eq_true, if_false] at hs
  obtain ⟨ned, g3, h3, hs⟩ := bind_some hs
  obtain ⟨u, g4, h4, hs⟩ := bind_some hs
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  exact ⟨cs_quiet (cs_quiet C1 (quiet_sure h3)) (quiet_medeLoop _ _ _ _ _ h4), h.le⟩

theorem cs_bomb {lo : Nat} {T : Nat → Prop} {miss : Option Nat} {g g' : Comp.Gen Map} {nex : Next S}
    (h : CS lo T g) (hs : (bomb miss : CM Map (Next S)) g = some (nex, g')) : CS lo T g' ∧ lo ≤ nex.th.there := by
  simp only [bomb] at hs
  obtain ⟨o, g1, h1, hs⟩ := bind_some hs
  obtain ⟨C1, rfl, -, -⟩ := cs_emit h (none_ok rfl) h1
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  exact ⟨C1, by simp [jmp0]; exact h.le⟩

theorem cs_doneBlocks {lo : Nat} {T : Nat → Prop} {g g' : Comp.Gen Map} {x : Nat × Nat} (h : CS lo T g)
    (hs : (doneBlocks : CM Map (Nat × Nat)) g = some (x, g')) : CS lo T g' ∧ lo ≤ x.1 ∧ lo ≤ x.2 ∧
      x.1 < g'.bo ∧ x.2 < g'.bo := by
  simp only [doneBlocks] at hs
  obtain ⟨r0, g1, h1, hs⟩ := bind_some hs
  obtain ⟨q1, b1, -, -⟩ := quiet_of_re h1
  have C1 := cs_quiet h q1
  obtain ⟨r1, g2, h2, hs⟩ := bind_some hs
  obtain ⟨q2, b2, -, -⟩ := quiet_of_re h2
  have C2 := cs_quiet C1 q2
  obtain ⟨o0, g3, h3, hs⟩ := bind_some hs
  obtain ⟨C3, rfl, b3, -⟩ := cs_emit C2 (none_ok rfl) h3
  obtain ⟨o1, g4, h4, hs⟩ := bind_some hs
  obtain ⟨C4, rfl, b4, -⟩ := cs_emit C3 (none_ok rfl) h4
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  have := h.le
  exact ⟨C4, by simp; omega, by simp; omega, by simp; omega, by simp; omega⟩

theorem cs_simpleNext {lo : Nat} {goal : CGoal S} {g g' : Comp.Gen Map} {nex : Next S}
    (h : CS lo (GTgt goal) g) (hs : (simpleNext goal : CM Map (Next S)) g = some (nex, g')) :
    CS lo (GTgt goal) g' ∧ (lo ≤ nex.th.there ∨ GTgt goal nex.th.there) := by
  cases goal with
  | next laz th =>
    simp only [simpleNext, pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨h, Or.inr rfl⟩
  | done =>
    simp only [simpleNext] at hs
    obtain ⟨r, g1, h1, hs⟩ := bind_some hs
    obtain ⟨q1, b1, -, -⟩ := quiet_of_re h1
    have C1 := cs_quiet h q1
    obtain ⟨o, g2, h2, hs⟩ := bind_some hs
    obtain ⟨C2, rfl, -, -⟩ := cs_emit C1 (none_ok rfl) h2
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨C2, Or.inl (by simp [jmp0]; have := h.le; omega)⟩
  | pick z o =>
    simp only [simpleNext] at hs
    obtain ⟨r, g1, h1, hs⟩ := bind_some hs
    obtain ⟨q1, b1, -, -⟩ := quiet_of_re h1
    have C1 := cs_quiet h q1
    obtain ⟨o', g2, h2, hs⟩ := bind_some hs
    obtain ⟨C2, rfl, -, -⟩ := cs_emit C1 (fun j hj => by
      simp [getJmps] at hj; rcases hj with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)) h2
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨C2, Or.inl (by simp [jmp0]; have := h.le; omega)⟩

theorem cs_forl {lo : Nat} {T : Nat → Prop} {r o : Nat} {g g' : Comp.Gen Map} {x : Nat × Nat} (h : CS lo T g)
    (ht : lo ≤ o ∨ T o) (hf : forl r o g = some (x, g')) : CS lo T g' ∧ lo ≤ x.1 ∧ lo ≤ x.2 ∧ x.1 < g'.bo ∧
      x.2 < g'.bo := by
  simp only [forl] at hf
  obtain ⟨r0, g1, h1, hf⟩ := bind_some hf
  obtain ⟨q1, b1, -, -⟩ := quiet_of_re h1
  have C1 := cs_quiet h q1
  obtain ⟨r1, g2, h2, hf⟩ := bind_some hf
  obtain ⟨q2, b2, -, -⟩ := quiet_of_re h2
  have C2 := cs_quiet C1 q2
  obtain ⟨barg, g3, h3, hf⟩ := bind_some hf
  obtain ⟨C3, rfl, b3, -⟩ := cs_emit C2 (hop_ok (t := jmp0 o) (by simpa [jmp0] using ht)) h3
  obtain ⟨if0, g4, h4, hf⟩ := bind_some hf
  obtain ⟨C4, rfl, b4, -⟩ := cs_emit C3 (hop_ok (Or.inl (by simp; have := h.le; omega))) h4
  obtain ⟨if1, g5, h5, hf⟩ := bind_some hf
  obtain ⟨C5, rfl, b5, -⟩ := cs_emit C4 (hop_ok (Or.inl (by simp; have := h.le; omega))) h5
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, rfl⟩ := hf
  have := h.le
  exact ⟨C5, by simp; omega, by simp; omega, by simp; omega, by simp; omega⟩

theorem cs_collapse {lo : Nat} {T : Nat → Prop} {laz : Sure S} {th : Jmp} {g g' : Comp.Gen Map}
    {a : Option (Nat × Nat)} (h : CS lo T g) (ht : lo ≤ th.there ∨ T th.there)
    (hc : collapseLazyAtom ⟨laz, th⟩ g = some (a, g')) :
    CS lo T g' ∧ ∀ r o, a = some (r, o) → lo ≤ o ∨ T o := by
  unfold collapseLazyAtom at hc
  by_cases ha : th.args ≠ []
  · rw [if_pos ha] at hc; cases hc
  rw [if_neg ha] at hc
  by_cases hne : noneEquivalent laz = true
  · rw [if_pos hne] at hc
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact ⟨h, fun r o e => by cases e⟩
  rw [if_neg hne] at hc
  obtain ⟨ns, g1, h1, hc⟩ := bind_some hc
  have C1 := cs_quiet h (quiet_sure h1)
  obtain ⟨⟨r, there⟩, g2, h2, hc⟩ := bind_some hc
  have P : CS lo T g2 ∧ (lo ≤ there ∨ T there) := by
    cases ns with
    | this r0 =>
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      exact ⟨C1, ht⟩
    | none =>
      obtain ⟨r0, g3, h3, h2⟩ := bind_some h2
      obtain ⟨q3, -, -, -⟩ := quiet_of_re h3
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      exact ⟨cs_quiet C1 q3, ht⟩
    | pair p q =>
      obtain ⟨r0, g3, h3, h2⟩ := bind_some h2
      obtain ⟨q3, b3, -, -⟩ := quiet_of_re h3
      have C3 := cs_quiet C1 q3
      obtain ⟨o, g4, h4, h2⟩ := bind_some h2
      obtain ⟨C4, rfl, -, -⟩ := cs_emit C3 (none_ok rfl) h4
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      exact ⟨C4, Or.inl C3.le⟩
    | both r0 p q =>
      obtain ⟨o, g4, h4, h2⟩ := bind_some h2
      obtain ⟨C4, rfl, -, -⟩ := cs_emit C1 (none_ok rfl) h4
      simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h2
      exact ⟨C4, Or.inl C1.le⟩
  obtain ⟨C2, tl⟩ := P
  obtain ⟨g3, g3', h3, hc⟩ := bind_some hc
  rw [get_apply] at h3
  simp only [Option.some.injEq, Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  rw [C2.drop] at hc
  simp only [Bool.false_eq_true, if_false] at hc
  obtain ⟨ned', g4, h4, hc⟩ := bind_some hc
  have C4 := cs_quiet C2 (quiet_sure h4)
  have fin : ∀ g5 : Comp.Gen Map, CS lo T g5 → (pure (some (r, there)) : CM Map (Option (Nat × Nat))) g5 = some (a, g') →
      CS lo T g' ∧ ∀ r o, a = some (r, o) → lo ≤ o ∨ T o := fun g5 C5 e5 => by
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at e5
    obtain ⟨rfl, rfl⟩ := e5
    exact ⟨C5, fun r' o' e => by simp only [Option.some.injEq, Prod.mk.injEq] at e; rw [← e.2]; exact tl⟩
  cases ned' with
  | none => exact fin g4 C4 hc
  | this r' =>
    simp only at hc
    by_cases e : r = r'
    · rw [if_pos e] at hc; exact fin g4 C4 hc
    · rw [if_neg e] at hc
      obtain ⟨u, g5, h5, hc⟩ := bind_some hc
      exact fin g5 (cs_quiet C4 (quiet_addOps h5)) hc
  | pair p q =>
    simp only at hc
    obtain ⟨u, g5, h5, hc⟩ := bind_some hc
    exact fin g5 (cs_quiet C4 (quiet_crashNeed h5)) hc
  | both r0 p q =>
    simp only at hc
    obtain ⟨u, g5, h5, hc⟩ := bind_some hc
    exact fin g5 (cs_quiet C4 (quiet_crashNeed h5)) hc

/-! ## The run -/

/-- **The blocks of a run jump only into the run or to its goal.** -/
def ClosedIH (S : Type) [HoonSet S] (Map : Type → Type) [HoonMap Map] [HoonMapKeys Map] (nm : Nomm) : Prop :=
  ∀ (goal : CGoal S) (g0 g1 : Comp.Gen Map) (nex : Next S), g0.drop = false → 1 ≤ g0.bo → GJ g0.bo goal →
    Clear g0 → run nm goal g0 = some (nex, g1) →
    ClosedR g0.bo (GTgt goal) g1.blocks ∧ (g0.bo ≤ nex.th.there ∨ GTgt goal nex.th.there)

/-- A sub-run inside a closed region. -/
theorem cs_run {lo : Nat} {T : Nat → Prop} {nm : Nomm} (ih : ClosedIH S Map nm) {goal : CGoal S}
    {g g' : Comp.Gen Map} {nex : Next S} (h : CS lo T g) (hj : GJ g.bo goal)
    (ht : ∀ t, GTgt goal t → lo ≤ t ∨ T t) (hr : run nm goal g = some (nex, g')) :
    CS lo T g' ∧ (lo ≤ nex.th.there ∨ T nex.th.there) ∧ 1 ≤ nex.th.there ∧ nex.th.there < g'.bo := by
  obtain ⟨hc, he⟩ := ih goal g g' nex h.drop h.bo1 hj h.clear hr
  have D := run_down nm goal g g' nex hj h.bo1 h.drop hr
  refine ⟨cs_sub h D.grow hc ht, ?_, D.lo, D.hi⟩
  rcases he with e | e
  · exact Or.inl (Nat.le_trans h.le e)
  · exact ht _ e

theorem gtgt_next {lo : Nat} {T : Nat → Prop} {laz : Sure S} {j : Jmp} (h : lo ≤ j.there ∨ T j.there) :
    ∀ t, GTgt (CGoal.next laz j) t → lo ≤ t ∨ T t := fun t e => by simp only [GTgt] at e; subst e; exact h

theorem gj_next {bo : Nat} {laz : Sure S} {j : Jmp} (h1 : 1 ≤ j.there) (h2 : j.there < bo) :
    GJ bo (CGoal.next laz j) := ⟨h1, h2⟩

end Raw
end SkaModel
end Formalization
